// clippy (correctly) tells us that we can sometimes elide lifetimes, but many
// of these cases make the declarations way more clear than with implicit
// lifetimes.
#![allow(clippy::needless_lifetimes)]

use std::{
    collections::HashMap,
    ffi::OsString,
    io,
    ops::DerefMut,
    path::PathBuf,
    process::ExitCode,
    sync::{Arc, Mutex},
    time::{Duration, Instant},
};

use crate::{
    ast::TyKind,
    driver::mk_z3_ctx,
    front::{resolve::Resolve, tycheck::Tycheck},
    smt::{translate_exprs::TranslateExprs, SmtCtx},
    timing::TimingLayer,
    tyctx::TyCtx,
    vc::vcgen::Vcgen,
};
use ast::{DeclKind, Diagnostic, FileId};
use clap::{crate_description, Args, CommandFactory, Parser, Subcommand, ValueEnum};
use driver::{Item, SourceUnit, VerifyUnit};
use intrinsic::{annotations::init_calculi, distributions::init_distributions, list::init_lists};
use mc::run_storm::{run_storm, storm_result_to_diagnostic};
use proof_rules::init_encodings;
use regex::Regex;
use resource_limits::{await_with_resource_limits, LimitError, LimitsRef, MemorySize};
use servers::{run_lsp_server, CliServer, LspServer, Server, ServerError};
use slicing::init_slicing;
use thiserror::Error;
use timing::DispatchBuilder;
use tokio::task::JoinError;
use tracing::{error, info, warn};

use vc::explain::VcExplanation;
use z3rro::{
    prover::{ProveResult, ProverCommandError},
    util::ReasonUnknown,
};

pub mod ast;
mod driver;
pub mod front;
pub mod intrinsic;
pub mod mc;
pub mod opt;
pub mod pretty;
mod procs;
mod proof_rules;
mod resource_limits;
mod scope_map;
mod servers;
mod slicing;
mod smt;
mod timing;
pub mod tyctx;
pub mod vc;
mod version;

#[derive(Debug, Parser)]
#[command(
    name = "caesar",
    about = crate_description!(),
    long_about = "Caesar is a deductive verifier for probabilistic programs. Run the caesar binary with a subcommand to use it. Usually, you'll want to use the `verify` command.",
    version = version::detailed_version_info_string()
)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Command,
}

impl Cli {
    fn parse_and_normalize() -> Self {
        let cli = Self::parse();
        match cli.command {
            Command::Other(vec) => {
                // if it's an unrecognized command, parse as "verify" command
                Self::parse_from(
                    std::iter::once(std::env::args().next().unwrap().into())
                        .chain(std::iter::once("verify".into()))
                        .chain(vec),
                )
            }
            command => Cli { command },
        }
    }

    fn debug_options(&self) -> Option<&DebugOptions> {
        match &self.command {
            Command::Verify(verify_options) => Some(&verify_options.debug_options),
            Command::Lsp(verify_options) => Some(&verify_options.debug_options),
            Command::Mc(mc_options) => Some(&mc_options.debug_options),
            Command::ShellCompletions(_) => None,
            Command::Other(_vec) => unreachable!(),
        }
    }
}

#[derive(Debug, Subcommand)]
pub enum Command {
    /// Verify HeyVL files with Caesar.
    Verify(VerifyCommand),
    /// Model checking via JANI, can run Storm directly.
    #[clap(visible_alias = "to-jani")]
    Mc(ToJaniCommand),
    /// Run Caesar's LSP server.
    Lsp(VerifyCommand),
    /// Generate shell completions for the Caesar binary.
    ShellCompletions(ShellCompletionsCommand),
    /// This is to support the default `verify` command.
    #[command(external_subcommand)]
    #[command(hide(true))]
    Other(Vec<OsString>),
}

#[derive(Debug, Default, Args)]
pub struct VerifyCommand {
    #[command(flatten)]
    pub input_options: InputOptions,

    #[command(flatten)]
    pub rlimit_options: ResourceLimitOptions,

    #[command(flatten)]
    pub model_checking_options: ModelCheckingOptions,

    #[command(flatten)]
    pub opt_options: OptimizationOptions,

    #[command(flatten)]
    pub lsp_options: LanguageServerOptions,

    #[command(flatten)]
    pub slice_options: SliceOptions,

    #[command(flatten)]
    pub debug_options: DebugOptions,

    #[command(flatten)]
    pub smt_solver_options: SMTSolverOptions,
}

#[derive(Debug, Args)]
pub struct ToJaniCommand {
    #[command(flatten)]
    pub input_options: InputOptions,

    #[command(flatten)]
    pub rlimit_options: ResourceLimitOptions,

    #[command(flatten)]
    pub model_checking_options: ModelCheckingOptions,

    #[command(flatten)]
    pub debug_options: DebugOptions,
}

#[derive(Debug, Default, Args)]
#[command(next_help_heading = "Input Options")]
pub struct InputOptions {
    /// The files to verify.
    #[arg(name = "FILE")]
    pub files: Vec<PathBuf>,

    /// Raw verification of just HeyVL statements without any declarations.
    #[arg(short, long)]
    pub raw: bool,

    /// Treat warnings as errors.
    #[arg(long)]
    pub werr: bool,

    /// Only verify/translate (co)procs that match the given filter.
    /// The filter is a regular expression.
    #[arg(short, long)]
    pub filter: Option<String>,
}

#[derive(Debug, Default, Args)]
#[command(next_help_heading = "Resource Limit Options")]
pub struct ResourceLimitOptions {
    /// Time limit in seconds.
    #[arg(long, default_value = "300")]
    pub timeout: u64,

    /// Memory usage limit in megabytes.
    #[arg(long = "mem", default_value = "8192")]
    pub mem_limit: usize,
}

impl ResourceLimitOptions {
    fn timeout(&self) -> Duration {
        Duration::from_secs(self.timeout)
    }

    fn mem_limit(&self) -> MemorySize {
        MemorySize::megabytes(self.mem_limit)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum RunWhichStorm {
    /// Look for the Storm binary in the PATH.
    Path,
    /// Run Storm using Docker, with the `movesrwth/storm:stable` image.
    DockerStable,
    /// Run Storm using Docker, with the `movesrwth/storm:ci` image.
    DockerCI,
}

#[derive(Debug, Default, Clone, Args)]
#[command(next_help_heading = "JANI Output Options")]
pub struct ModelCheckingOptions {
    /// Export declarations to JANI files in the provided directory.
    #[arg(long)]
    pub jani_dir: Option<PathBuf>,

    /// During extraction of the pre for JANI generation, skip the quantitative
    /// pres (instead of failing with an error).
    #[arg(long)]
    pub jani_skip_quant_pre: bool,

    /// Declare procedure inputs as JANI variables, not constants.
    #[arg(long)]
    pub jani_no_constants: bool,

    /// By default, Caesar assigns arbitrary initial values to output variables.
    /// This means that the model does not reflect the possible effects of
    /// initial values of output variables on the program. Usually, this is not
    /// the case anyway and assigning initial values speeds up the model
    /// checking quite a bit. To disable this behavior, use this flag.
    #[arg(long)]
    pub jani_uninit_outputs: bool,

    /// Run Storm, indicating which version to execute.
    #[arg(long)]
    pub run_storm: Option<RunWhichStorm>,

    /// Pass the `--exact` flag to Storm. Otherwise Storm will use floating
    /// point numbers, which may be arbitrarily imprecise (but are usually good
    /// enough).
    #[arg(long)]
    pub storm_exact: bool,

    /// Pass the `--state-limit [number]` option to Storm. This is useful to
    /// approximate infinite-state models.
    #[arg(long)]
    pub storm_state_limit: Option<usize>,

    /// Pass the `--constants [constants]` option to Storm, containing values
    /// for constants in the model.
    #[arg(long)]
    pub storm_constants: Option<String>,

    /// Timeout in seconds for running Storm.
    ///
    /// Caesar uses the minimum of this value and the remaining time from the
    /// `--timeout` option.
    #[arg(long)]
    pub storm_timeout: Option<u64>,
}

impl ModelCheckingOptions {
    pub fn storm_timeout(&self) -> Option<Duration> {
        self.storm_timeout.map(Duration::from_secs)
    }
}

#[derive(Debug, Default, Args)]
#[command(next_help_heading = "Optimization Options")]
pub struct OptimizationOptions {
    /// Disable quantifier elimination. You'll never want to do this, except to see why quantifier elimination is important.
    #[arg(long)]
    pub no_qelim: bool,

    /// Do e-graph optimization of the generated verification conditions.
    /// The result is not used at the moment.
    #[arg(long)]
    pub egraph: bool,

    /// Don't do SMT-powered reachability checks during unfolding of
    /// verification conditions to eliminate unreachable branches. Instead,
    /// unfold all branches.
    #[arg(long)]
    pub strict: bool,

    /// Run the "relational view" optimization. Defaults to off.
    #[arg(long)]
    pub opt_rel: bool,

    /// Don't run the "boolify" optimization pass.
    #[arg(long)]
    pub no_boolify: bool,

    /// Don't apply Z3's simplification pass. This may help with interpreting
    /// the current solver state.
    #[arg(long)]
    pub no_simplify: bool,
}

#[derive(Debug, Default, Args)]
#[command(next_help_heading = "Language Server Options")]
pub struct LanguageServerOptions {
    /// Produce explanations of verification conditions.
    #[arg(long)]
    pub explain_vc: bool,

    /// Produce explanations of verification conditions for the core HeyVL
    /// that's produced after proof rules have been desugared.
    #[arg(long)]
    pub explain_core_vc: bool,

    /// Run the language server.
    #[arg(long)]
    pub language_server: bool,
}

#[derive(Debug, Default, Args)]
#[command(next_help_heading = "Debug Options")]
pub struct DebugOptions {
    /// Emit tracing events as json instead of (ANSI) text.
    #[arg(long)]
    pub json: bool,

    /// Emit timing information from tracing events. The tracing events need to
    /// be enabled for this to work.
    #[arg(long)]
    pub timing: bool,

    /// Print version information to standard error.
    #[arg(short, long)]
    pub debug: bool,

    /// Print the parsed HeyVL code to the command-line.
    #[arg(long)]
    pub print_parsed: bool,

    /// Print the raw HeyVL program to the command-line after desugaring.
    #[arg(long)]
    pub print_core: bool,

    /// Print the HeyVL program with generated procs after annotation desugaring
    #[arg(long)]
    pub print_core_procs: bool,

    /// Print the theorem that is sent to the SMT solver to prove. That is, the
    /// result of preparing `vc(S)[⊤] = ⊤`. Note that axioms are not included.
    #[arg(long)]
    pub print_theorem: bool,

    /// Print the SMT solver state for each verify unit in the SMT-LIB format to
    /// standard output.
    #[arg(long)]
    pub print_smt: bool,

    /// Print the SMT solver state for each verify unit in the SMT-LIB format to
    /// a file in the given directory.
    #[arg(long)]
    pub smt_dir: Option<PathBuf>,

    /// Do not pretty-print the output of the `--smt-dir` and `--smt-out` options.
    #[arg(long)]
    pub no_pretty_smtlib: bool,

    /// Do not run the final SMT check to verify the program. This is useful to
    /// obtain just the SMT-LIB output.
    #[arg(long)]
    pub no_verify: bool,

    /// Enable Z3 tracing for the final SAT check.
    #[arg(long)]
    pub z3_trace: bool,

    /// Print Z3's statistics after the final SAT check.
    #[arg(long)]
    pub print_z3_stats: bool,

    /// Run a bunch of probes on the SMT solver.
    #[arg(long)]
    pub probe: bool,
}

#[derive(Debug, Default, Args)]
#[command(next_help_heading = "SMT Solver Options")]
pub struct SMTSolverOptions {
    #[arg(long, default_value = "z3")]
    pub smt_solver: SMTSolverType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, ValueEnum)]
pub enum SMTSolverType {
    #[default]
    #[value(name = "z3")]
    Z3,
    #[value(name = "swine")]
    Swine,
    #[value(name = "cvc5")]
    CVC5,
}

#[derive(Debug, Default, Args)]
#[command(next_help_heading = "Slicing Options")]
pub struct SliceOptions {
    /// Do not try to slice when an error occurs.
    #[arg(long)]
    pub no_slice_error: bool,

    /// Do not try to minimize the error slice and just return the first
    /// counterexample.
    #[arg(long)]
    pub slice_error_first: bool,

    /// If the SMT solver provides a model for an "unknown" result, use that to
    /// obtain an error slice. The slice is not guaranteed to be an actual error
    /// slice, because the model might not be a real counterexample. However, it
    /// is often a helpful indicator of where the SMT solver got stuck.
    #[arg(long)]
    pub slice_error_inconsistent: bool,

    /// Enable slicing tick/reward statements during slicing for errors.
    #[arg(long)]
    pub slice_ticks: bool,

    /// Enable slicing sampling statements (must also be selected via
    /// annotations).
    #[arg(long)]
    pub slice_sampling: bool,

    /// Slice if the program verifies to return a smaller, verifying program.
    /// This is not enabled by default.
    #[arg(long)]
    pub slice_verify: bool,

    /// If slicing for correctness is enabled, slice via these methods.
    #[arg(long, default_value = "core")]
    pub slice_verify_via: SliceVerifyMethod,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, ValueEnum)]
pub enum SliceVerifyMethod {
    /// Slice for correctness using unsat cores. This approach does not minimize
    /// the result. However, it is applicable all the time and has a very small
    /// overhead. All other methods are much slower or not always applicable.
    #[default]
    #[value(name = "core")]
    UnsatCore,
    /// Slice by doing a search for minimal unsatisfiable subsets. The result
    /// might not be globally optimal - the method returns the first slice from
    /// which nothing can be removed without making the program not verify anymore.
    #[value(name = "mus")]
    MinimalUnsatSubset,
    /// Slice by doing a search for the smallest unsatisfiable subset. This will
    /// enumerate all minimal unsat subsets and return the globally smallest one.
    #[value(name = "sus")]
    SmallestUnsatSubset,
    /// Slice for correctness by encoding a direct exists-forall query into the
    /// SMT solver and then run the minimization algorithm. This approach does
    /// not support using uninterpreted functions. This approach is usually not
    /// good.
    #[value(name = "exists-forall")]
    ExistsForall,
}

#[derive(Debug, Default, Args)]
pub struct ShellCompletionsCommand {
    /// The shell for which to generate completions.
    #[arg(required(true), value_enum)]
    shell: Option<clap_complete::Shell>,
}

#[tokio::main]
async fn main() -> ExitCode {
    let options = Cli::parse_and_normalize();

    if let Some(debug_options) = options.debug_options() {
        if debug_options.debug {
            let mut stderr = io::stderr().lock();
            version::write_detailed_version_info(&mut stderr).unwrap();
        }
        // install global collector configured based on RUST_LOG env var.
        setup_tracing(debug_options);
    }

    match options.command {
        Command::Verify(options) => run_cli(options).await,
        Command::Mc(options) => run_model_checking_main(options),
        Command::Lsp(options) => run_server(options).await,
        Command::ShellCompletions(options) => run_generate_completions(options),
        Command::Other(_) => unreachable!(),
    }
}

async fn run_cli(options: VerifyCommand) -> ExitCode {
    let (user_files, server) = match mk_cli_server(&options.input_options) {
        Ok(value) => value,
        Err(value) => return value,
    };
    let options = Arc::new(options);
    let verify_result = verify_files(&options, &server, user_files).await;

    if options.debug_options.timing {
        print_timings();
    }

    finalize_verify_result(server, &options.rlimit_options, verify_result)
}

type SharedServer = Arc<Mutex<dyn Server>>;

fn finalize_verify_result(
    server: SharedServer,
    rlimit_options: &ResourceLimitOptions,
    verify_result: Result<bool, VerifyError>,
) -> ExitCode {
    let (timeout, mem_limit) = (rlimit_options.timeout(), rlimit_options.mem_limit());
    match verify_result {
        #[allow(clippy::bool_to_int_with_if)]
        Ok(all_verified) => {
            let server_exit_code = server.lock().unwrap().exit_code();
            if server_exit_code != ExitCode::SUCCESS {
                return server_exit_code;
            }
            ExitCode::from(if all_verified { 0 } else { 1 })
        }
        Err(VerifyError::Diagnostic(diagnostic)) => {
            server.lock().unwrap().add_diagnostic(diagnostic).unwrap();
            ExitCode::from(1)
        }
        Err(VerifyError::IoError(err)) => {
            eprintln!("IO Error: {}", err);
            ExitCode::from(1)
        }
        Err(VerifyError::LimitError(LimitError::Timeout)) => {
            tracing::error!("Timed out after {} seconds, exiting.", timeout.as_secs());
            std::process::exit(2); // exit ASAP
        }
        Err(VerifyError::LimitError(LimitError::Oom)) => {
            tracing::error!(
                "Exhausted {} megabytes of memory, exiting.",
                mem_limit.as_megabytes()
            );
            std::process::exit(3); // exit ASAP
        }
        Err(VerifyError::UserError(err)) => {
            eprintln!("Error: {}", err);
            ExitCode::from(1)
        }
        Err(VerifyError::ServerError(err)) => panic!("{}", err),
        Err(VerifyError::Panic(join_error)) => panic!("{}", join_error),
        Err(VerifyError::Interrupted) => {
            tracing::error!("Interrupted");
            ExitCode::from(130) // 130 seems to be a standard exit code for CTRL+C
        }
        Err(VerifyError::ProverError(err)) => {
            eprintln!("{}", err.to_string());
            ExitCode::from(1)
        }
    }
}

fn mk_cli_server(input_options: &InputOptions) -> Result<(Vec<FileId>, SharedServer), ExitCode> {
    if input_options.files.is_empty() {
        eprintln!("Error: list of files must not be empty.\n");
        return Err(ExitCode::from(1));
    }
    let mut client = CliServer::new(input_options);
    let user_files: Vec<FileId> = input_options
        .files
        .iter()
        .map(|path| client.load_file(path))
        .collect();
    let server: SharedServer = Arc::new(Mutex::new(client));
    Ok((user_files, server))
}

async fn run_server(mut options: VerifyCommand) -> ExitCode {
    let (mut server, _io_threads) = LspServer::connect_stdio(&options);
    server.initialize().unwrap();
    let server = Arc::new(Mutex::new(server));
    options.lsp_options.language_server = true;
    let options = Arc::new(options);

    let res = run_lsp_server(server.clone(), |user_files| {
        let server: SharedServer = server.clone();
        let options = options.clone();
        Box::pin(async move {
            let res = verify_files(&options, &server, user_files.to_vec()).await;
            match res {
                Ok(_) => Ok(()),
                Err(VerifyError::Diagnostic(diag)) => {
                    server.lock().unwrap().add_diagnostic(diag).unwrap();
                    Ok(())
                }
                Err(err) => Err(err),
            }
        })
    })
    .await;

    match res {
        Ok(()) => ExitCode::SUCCESS,
        Err(VerifyError::Diagnostic(diag)) => {
            server.lock().unwrap().add_diagnostic(diag).unwrap();
            ExitCode::FAILURE
        }
        Err(err) => panic!("{}", err), // TODO
    }
}

/// Errors that can occur in the verifier.
///
/// Note that some unit not verifying (solver yielding unknown or a
/// counter-example) is not actually considered a [`VerifyError`].
#[derive(Debug, Error)]
pub enum VerifyError {
    /// A diagnostic to be emitted.
    #[error("{0}")]
    Diagnostic(#[from] Diagnostic),
    /// An I/O error.
    #[error("io error")]
    IoError(#[from] io::Error),
    /// An error due to resource limits.
    #[error("{0}")]
    LimitError(#[from] LimitError),
    /// An error by the user, to be printed via the error message.
    #[error("{0}")]
    UserError(Box<dyn std::error::Error + Send + Sync>),
    /// An internal server error, e.g. because of logic or IO errors.
    #[error("{0}")]
    ServerError(ServerError),
    /// A panic occurred somewhere.
    #[error("panic: {0}")]
    Panic(#[from] JoinError),
    /// The verifier was interrupted.
    #[error("interrupted")]
    Interrupted,
    #[error("{0}")]
    ProverError(#[from] ProverCommandError),
}

/// Verify a list of `user_files`. The `options.files` value is ignored here.
pub async fn verify_files(
    options: &Arc<VerifyCommand>,
    server: &SharedServer,
    user_files: Vec<FileId>,
) -> Result<bool, VerifyError> {
    let handle = |limits_ref: LimitsRef| {
        let options = options.clone();
        let server = server.clone();
        tokio::task::spawn_blocking(move || {
            // execute the verifier with a larger stack size of 50MB. the
            // default stack size might be quite small and we need to do quite a
            // lot of recursion.
            let stack_size = 50 * 1024 * 1024;
            stacker::maybe_grow(stack_size, stack_size, move || {
                let mut server = server.lock().unwrap();
                verify_files_main(&options, limits_ref, server.deref_mut(), &user_files)
            })
        })
    };
    // Unpacking lots of Results with `.await??` :-)
    await_with_resource_limits(
        Some(options.rlimit_options.timeout()),
        Some(options.rlimit_options.mem_limit()),
        handle,
    )
    .await??
}

fn parse_and_tycheck(
    input_options: &InputOptions,
    debug_options: &DebugOptions,
    server: &mut dyn Server,
    user_files: &[FileId],
) -> Result<(Vec<Item<SourceUnit>>, TyCtx), VerifyError> {
    let mut source_units: Vec<Item<SourceUnit>> = Vec::new();
    for file_id in user_files {
        let file = server.get_file(*file_id).unwrap();
        let new_units = SourceUnit::parse(&file, input_options.raw)
            .map_err(|parse_err| parse_err.diagnostic())?;

        // Print the result of parsing if requested
        if debug_options.print_parsed {
            println!("{}: Parsed file:\n", file.path);
            for unit in &new_units {
                println!("{}", unit);
            }
        }

        source_units.extend(new_units);
    }
    let mut tcx = TyCtx::new(TyKind::EUReal);
    let mut files = server.get_files_internal().lock().unwrap();
    init_calculi(&mut files, &mut tcx);
    init_encodings(&mut files, &mut tcx);
    init_distributions(&mut files, &mut tcx);
    init_lists(&mut files, &mut tcx);
    init_slicing(&mut tcx);
    drop(files);
    let mut resolve = Resolve::new(&mut tcx);
    for source_unit in &mut source_units {
        source_unit.enter().forward_declare(&mut resolve)?;
    }
    for source_unit in &mut source_units {
        source_unit.enter().resolve(&mut resolve)?;
    }
    let mut tycheck = Tycheck::new(&mut tcx);
    for source_unit in &mut source_units {
        let mut source_unit = source_unit.enter();
        source_unit.tycheck(&mut tycheck)?;

        let monotonicity_res = source_unit.check_monotonicity();
        if let Err(err) = monotonicity_res {
            server.add_or_throw_diagnostic(err)?;
        }
    }

    // filter source units if requested
    if let Some(filter) = &input_options.filter {
        let filter = Regex::new(filter).map_err(|err| {
            VerifyError::UserError(format!("Invalid filter regex: {}", err).into())
        })?;
        source_units.retain(|source_unit| filter.is_match(&source_unit.name().to_string()));
    };

    Ok((source_units, tcx))
}

/// Synchronously verify the given source code. This is used for tests. The
/// `--werr` option is enabled by default.
#[cfg(test)]
pub(crate) fn verify_test(source: &str) -> (Result<bool, VerifyError>, servers::TestServer) {
    use ast::SourceFilePath;

    let mut options = VerifyCommand::default();
    options.input_options.werr = true;

    let mut server = servers::TestServer::new(&options);
    let file_id = server
        .get_files_internal()
        .lock()
        .unwrap()
        .add(SourceFilePath::Builtin, source.to_owned())
        .id;

    let options = Arc::new(options);
    let limits_ref = LimitsRef::new(None, None);
    let res = verify_files_main(&options, limits_ref, &mut server, &[file_id]);
    (res, server)
}

#[cfg(test)]
pub(crate) fn single_desugar_test(source: &str) -> Result<String, VerifyError> {
    use ast::SourceFilePath;

    let mut options = VerifyCommand::default();
    options.input_options.werr = true;

    let mut server = servers::TestServer::new(&options);
    let file_id = server
        .get_files_internal()
        .lock()
        .unwrap()
        .add(SourceFilePath::Builtin, source.to_owned())
        .id;

    let (source_units, mut tcx) = parse_and_tycheck(
        &options.input_options,
        &options.debug_options,
        &mut server,
        &[file_id],
    )?;

    assert_eq!(source_units.len(), 1);
    let mut source_unit = source_units.into_iter().next().unwrap();

    let mut new_source_units: Vec<Item<SourceUnit>> = vec![];
    source_unit
        .enter()
        .apply_encodings(&mut tcx, &mut new_source_units)?;

    new_source_units.push(source_unit);

    Ok(new_source_units
        .into_iter()
        .map(|unit: Item<SourceUnit>| unit.to_string())
        .collect::<Vec<String>>()
        .join("\n"))
}

/// Synchronously verify the given files.
fn verify_files_main(
    options: &VerifyCommand,
    limits_ref: LimitsRef,
    server: &mut dyn Server,
    user_files: &[FileId],
) -> Result<bool, VerifyError> {
    let (mut source_units, mut tcx) = parse_and_tycheck(
        &options.input_options,
        &options.debug_options,
        server,
        user_files,
    )?;

    // Register all relevant source units with the server
    for source_unit in &mut source_units {
        let source_unit = source_unit.enter();
        match *source_unit {
            SourceUnit::Decl(ref decl) => {
                // only register procs since we do not check any other decls
                if let DeclKind::ProcDecl(proc_decl) = decl {
                    server.register_source_unit(proc_decl.borrow().name.span)?;
                }
            }
            SourceUnit::Raw(ref block) => server.register_source_unit(block.span)?,
        }
    }

    // explain high-level HeyVL if requested
    if options.lsp_options.explain_vc {
        for source_unit in &mut source_units {
            let source_unit = source_unit.enter();
            source_unit.explain_vc(&tcx, server, &limits_ref)?;
        }
    }

    // write to JANI if requested
    run_model_checking(
        &options.model_checking_options,
        &mut source_units,
        server,
        &limits_ref,
        &tcx,
        false,
    )?;

    // Desugar encodings from source units. They might generate new source
    // units (for side conditions).
    let mut source_units_buf = vec![];
    for source_unit in &mut source_units {
        source_unit
            .enter()
            .apply_encodings(&mut tcx, &mut source_units_buf)?;
    }
    source_units.extend(source_units_buf);

    if options.debug_options.print_core_procs {
        println!("HeyVL query with generated procs:");
        for source_unit in &mut source_units {
            println!("{}", source_unit);
        }
    }

    // If `--no-verify` is set and we don't need to print SMT-LIB or explain the
    // core VC, we can return early.
    if options.debug_options.no_verify
        && !options.lsp_options.explain_core_vc
        && !options.debug_options.probe
        && !options.debug_options.print_smt
        && !options.debug_options.print_core
        && !options.debug_options.print_core_procs
        && options.debug_options.smt_dir.is_none()
    {
        return Ok(true);
    }

    let mut verify_units: Vec<Item<VerifyUnit>> = source_units
        .into_iter()
        .flat_map(|item| item.flat_map(SourceUnit::into_verify_unit))
        .collect();

    if options.debug_options.z3_trace && verify_units.len() > 1 {
        warn!("Z3 tracing is enabled with multiple verification units. Intermediate tracing results will be overwritten.");
    }

    let mut num_proven: usize = 0;
    let mut num_failures: usize = 0;

    for verify_unit in &mut verify_units {
        let (name, mut verify_unit) = verify_unit.enter_with_name();

        limits_ref.check_limits()?;

        // Set the current unit as ongoing
        server.set_ongoing_unit(verify_unit.span)?;

        // 4. Desugaring: transforming spec calls to procs
        verify_unit.desugar_spec_calls(&mut tcx, name.to_string())?;

        // 5. Prepare slicing
        let slice_vars = verify_unit.prepare_slicing(&options.slice_options, &mut tcx, server)?;

        // print HeyVL core after desugaring if requested
        if options.debug_options.print_core {
            println!("{}: HeyVL core query:\n{}\n", name, *verify_unit);
        }

        // 6. Generating verification conditions.
        let explanations = options
            .lsp_options
            .explain_core_vc
            .then(|| VcExplanation::new(verify_unit.direction));
        let mut vcgen = Vcgen::new(&tcx, &limits_ref, explanations);
        let mut vc_expr = verify_unit.vcgen(&mut vcgen)?;
        if let Some(explanation) = vcgen.explanation {
            server.add_vc_explanation(explanation)?;
        }

        // 7. Unfolding
        vc_expr.unfold(options, &limits_ref, &tcx)?;

        // 8. Quantifier elimination
        if !options.opt_options.no_qelim {
            vc_expr.qelim(&mut tcx, &limits_ref)?;
        }

        // In-between, gather some stats about the vc expression
        vc_expr.trace_expr_stats();

        // 9. Create the "vc[S] is valid" expression
        let mut vc_is_valid = vc_expr.into_bool_vc();

        if options.opt_options.egraph {
            vc_is_valid.egraph_simplify();
        }

        // 10. Optimizations
        if !options.opt_options.no_boolify || options.opt_options.opt_rel {
            vc_is_valid.remove_parens();
        }
        if !options.opt_options.no_boolify {
            vc_is_valid.opt_boolify();
        }
        if options.opt_options.opt_rel {
            vc_is_valid.opt_relational();
        }

        // print theorem to prove if requested
        if options.debug_options.print_theorem {
            vc_is_valid.print_theorem(name);
        }

        // 11. Translate to Z3
        let ctx = mk_z3_ctx(options);
        let smt_ctx = SmtCtx::new(&ctx, &tcx);
        let mut translate = TranslateExprs::new(&smt_ctx);
        let mut vc_is_valid = vc_is_valid.into_smt_vc(&mut translate);

        // 12. Simplify
        if !options.opt_options.no_simplify {
            vc_is_valid.simplify();
        }

        // 13. Create Z3 solver with axioms, solve
        let mut result = vc_is_valid.run_solver(
            options,
            &limits_ref,
            name,
            &ctx,
            &mut translate,
            &slice_vars,
        )?;

        if options.debug_options.z3_trace {
            info!("Z3 tracing output will be written to `z3.log`.");
        }

        // Handle reasons to stop the verifier.
        match result.prove_result {
            ProveResult::Unknown(ReasonUnknown::Interrupted) => {
                return Err(VerifyError::Interrupted)
            }

            ProveResult::Unknown(ReasonUnknown::Timeout) => return Err(LimitError::Timeout.into()),
            _ => {}
        }

        // Increment counters
        match result.prove_result {
            ProveResult::Proof => num_proven += 1,
            ProveResult::Counterexample | ProveResult::Unknown(_) => num_failures += 1,
        }

        limits_ref.check_limits()?;

        server
            .handle_vc_check_result(name, verify_unit.span, &mut result, &mut translate)
            .map_err(VerifyError::ServerError)?;
    }

    if !options.lsp_options.language_server {
        println!();
        let ending = if num_failures == 0 {
            " veni, vidi, vici!"
        } else {
            ""
        };
        println!(
            "{} verified, {} failed.{}",
            num_proven, num_failures, ending
        );
    }

    Ok(num_failures == 0)
}

fn run_model_checking_main(options: ToJaniCommand) -> ExitCode {
    let (user_files, server) = match mk_cli_server(&options.input_options) {
        Ok(value) => value,
        Err(value) => return value,
    };
    let res = model_checking_main(&options, user_files, &server).map(|_| true);
    finalize_verify_result(server, &options.rlimit_options, res)
}

fn model_checking_main(
    options: &ToJaniCommand,
    user_files: Vec<FileId>,
    server: &Mutex<dyn Server>,
) -> Result<(), VerifyError> {
    let mut server_lock = server.lock().unwrap();
    let (mut source_units, tcx) = parse_and_tycheck(
        &options.input_options,
        &options.debug_options,
        &mut *server_lock,
        &user_files,
    )?;
    let timeout = Instant::now() + options.rlimit_options.timeout();
    let mem_limit = options.rlimit_options.mem_limit();
    let limits_ref = LimitsRef::new(Some(timeout), Some(mem_limit));
    run_model_checking(
        &options.model_checking_options,
        &mut source_units,
        server_lock.deref_mut(),
        &limits_ref,
        &tcx,
        true,
    )
}

fn run_model_checking(
    options: &ModelCheckingOptions,
    source_units: &mut Vec<Item<SourceUnit>>,
    server: &mut dyn Server,
    limits_ref: &LimitsRef,
    tcx: &TyCtx,
    is_jani_command: bool,
) -> Result<(), VerifyError> {
    let mut options = options.clone();

    let mut temp_dir = None;
    if options.jani_dir.is_none() {
        if is_jani_command && options.run_storm.is_none() {
            return Err(VerifyError::UserError(
                "Either --jani-dir or --run-storm must be provided.".into(),
            ));
        }
        if options.run_storm.is_some() {
            temp_dir = Some(tempfile::tempdir().map_err(|err| {
                VerifyError::UserError(
                    format!("Could not create temporary directory: {}", err).into(),
                )
            })?);
            options.jani_dir = temp_dir.as_ref().map(|dir| dir.path().to_owned());
        }
    }

    for source_unit in source_units {
        let source_unit = source_unit.enter();
        let jani_res = source_unit.write_to_jani_if_requested(&options, tcx);
        match jani_res {
            Err(VerifyError::Diagnostic(diagnostic)) => server.add_diagnostic(diagnostic)?,
            Err(err) => Err(err)?,
            Ok(Some(path)) => {
                tracing::debug!(file=?path.display(), "wrote JANI file");
                if options.run_storm.is_some() {
                    let res = run_storm(&options, &path, vec!["reward".to_owned()], limits_ref);
                    server.add_diagnostic(storm_result_to_diagnostic(
                        &res,
                        source_unit.diagnostic_span(),
                    ))?;
                }
            }
            Ok(None) => (),
        }
    }

    // only drop (and thus remove) the temp dir after we're done using it.
    drop(temp_dir);

    Ok(())
}

fn setup_tracing(options: &DebugOptions) {
    timing::init_tracing(
        DispatchBuilder::default()
            .json(options.json)
            .timing(options.timing),
    )
}

fn print_timings() {
    let timings = TimingLayer::read_active().unwrap();
    let timings: HashMap<&'static str, String> = timings
        .iter()
        .map(|(key, value)| (*key, format!("{}", value.as_nanos())))
        .collect();
    eprintln!("Timings: {:?}", timings);
}

fn run_generate_completions(options: ShellCompletionsCommand) -> ExitCode {
    let binary_name = std::env::args().next().unwrap();
    clap_complete::aot::generate(
        options.shell.unwrap(),
        &mut Cli::command(),
        binary_name,
        &mut std::io::stdout(),
    );
    ExitCode::SUCCESS
}
