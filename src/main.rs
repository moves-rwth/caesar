// clippy (correctly) tells us that we can sometimes elide lifetimes, but many
// of these cases make the declarations way more clear than with implicit
// lifetimes.
#![allow(clippy::needless_lifetimes)]

use std::{
    collections::HashMap,
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
use ast::{Diagnostic, FileId};
use driver::{Item, SourceUnit, VerifyUnit};
use intrinsic::{annotations::init_calculi, distributions::init_distributions, list::init_lists};
use procs::add_default_specs;
use proof_rules::init_encodings;
use resource_limits::{await_with_resource_limits, LimitError, LimitsRef};
use servers::{CliServer, LspServer, Server, ServerError};
use slicing::init_slicing;
use thiserror::Error;
use timing::DispatchBuilder;
use tokio::task::JoinError;
use tracing::{error, info, warn};

use structopt::StructOpt;
use z3rro::{prover::ProveResult, util::ReasonUnknown};

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

#[derive(StructOpt, Debug, Default)]
#[structopt(
    name = "caesar",
    about = "A deductive verifier for probabilistic programs."
)]
pub struct Options {
    /// Raw verification of just HeyVL statements without any declarations.
    #[structopt(short, long)]
    pub raw: bool,

    /// The files to verify.
    #[structopt(name = "FILE", parse(from_os_str))]
    pub files: Vec<PathBuf>,

    /// Disable quantifier elimination. You'll never want to do this, except to see why quantifier elimination is important.
    #[structopt(long)]
    pub no_qelim: bool,

    /// Time limit in seconds.
    #[structopt(long, default_value = "300")]
    pub timeout: u64,

    /// Memory usage limit in megabytes.
    #[structopt(long = "mem", default_value = "8192")]
    pub mem_limit: u64,

    /// Emit tracing events as json instead of (ANSI) text.
    #[structopt(long)]
    pub json: bool,

    /// Emit timing information from tracing events. The tracing events need to
    /// be enabled for this to work.
    #[structopt(long)]
    pub timing: bool,

    /// Do e-graph optimization of the generated verification conditions.
    /// The result is not used at the moment.
    #[structopt(long)]
    pub egraph: bool,

    /// Don't do reachability checks during unfolding of verification conditions
    /// to eliminate unreachable branches. Instead, unfold all branches.
    #[structopt(long)]
    pub strict: bool,

    /// Run the "relational view" optimization. Defaults to off.
    #[structopt(long)]
    pub opt_rel: bool,

    /// Don't run the "boolify" optimization pass.
    #[structopt(long)]
    pub no_boolify: bool,

    /// Don't apply Z3's simplification pass. This may help with interpreting
    /// the current solver state.
    #[structopt(long)]
    pub no_simplify: bool,

    /// Print version information to standard error.
    #[structopt(short, long)]
    pub debug: bool,

    /// Treat warnings as errors.
    #[structopt(long)]
    pub werr: bool,

    /// Print the SMT solver state for each verify unit in the SMT-LIB format to
    /// standard output.
    #[structopt(long)]
    pub print_smt: bool,

    /// Print the SMT solver state for each verify unit in the SMT-LIB format to
    /// a file in the given directory.
    #[structopt(long, parse(from_os_str))]
    pub smt_dir: Option<PathBuf>,

    /// Do not pretty-print the output of the `--smt-dir` and `--smt-out` options.
    #[structopt(long)]
    pub no_pretty_smtlib: bool,

    /// Enable Z3 tracing for the final SAT check.
    #[structopt(long)]
    pub z3_trace: bool,

    /// Print the parsed HeyVL code to the command-line.
    #[structopt(long)]
    pub print_parsed: bool,

    /// Print the raw HeyVL program to the command-line after desugaring.
    #[structopt(long)]
    pub print_core: bool,

    /// Print the HeyVL program with generated procs after annotation desugaring
    #[structopt(long)]
    pub print_core_procs: bool,

    /// Print the theorem that is sent to the SMT solver to prove. That is, the
    /// result of preparing `vc(S)[⊤] = ⊤`. Note that axioms are not included.
    #[structopt(long)]
    pub print_theorem: bool,

    /// Produce explanations of verification conditions.
    #[structopt(long)]
    pub explain_vc: bool,

    /// Produce explanations of verification conditions for the core HeyVL
    /// that's produced after proof rules have been desugared.
    #[structopt(long)]
    pub explain_core_vc: bool,

    /// Run the language server.
    #[structopt(long)]
    pub language_server: bool,

    /// Export declarations to JANI files in the provided directory.
    #[structopt(long, parse(from_os_str))]
    pub jani_dir: Option<PathBuf>,

    /// During extraction of the pre for JANI generation, skip the quantitative
    /// pres (instead of failing with an error).
    #[structopt(long)]
    pub jani_skip_quant_pre: bool,

    /// Do not try to slice after an error occurs. Just return the first
    /// counterexample.
    #[structopt(long)]
    pub no_slice_error: bool,

    /// Slice if the program verifies to return a smaller, verifying program.
    /// This is not enabled by default.
    #[structopt(long)]
    pub slice_verify: bool,
}

#[tokio::main]
async fn main() -> ExitCode {
    // add version to options config
    let version_info = version::caesar_version_info();
    let clap = Options::clap().version(version_info.as_str());
    // now parse options
    let options = Options::from_clap(&clap.get_matches());

    if options.debug {
        let mut stderr = io::stderr().lock();
        version::write_detailed_version_info(&mut stderr).unwrap();
    }
    // install global collector configured based on RUST_LOG env var.
    setup_tracing(&options);

    if !options.language_server {
        run_cli(options).await
    } else {
        run_server(&options).await
    }
}

async fn run_cli(options: Options) -> ExitCode {
    if options.files.is_empty() {
        eprintln!("Error: list of files must not be empty.\n");
        return ExitCode::from(1);
    }

    let mut client = CliServer::new(&options);
    let user_files: Vec<FileId> = options
        .files
        .iter()
        .map(|path| client.load_file(path))
        .collect();

    let options = Arc::new(options);
    let server: Arc<Mutex<dyn Server>> = Arc::new(Mutex::new(client));
    let verify_result = verify_files(&options, &server, user_files).await;

    if options.timing {
        print_timings();
    }

    let (timeout, mem_limit) = (options.timeout, options.mem_limit);
    match verify_result {
        #[allow(clippy::bool_to_int_with_if)]
        Ok(all_verified) => ExitCode::from(if all_verified { 0 } else { 1 }),
        Err(VerifyError::Diagnostic(diagnostic)) => {
            server.lock().unwrap().add_diagnostic(diagnostic).unwrap();
            ExitCode::from(1)
        }
        Err(VerifyError::IoError(err)) => {
            eprintln!("IO Error: {}", err);
            ExitCode::from(1)
        }
        Err(VerifyError::LimitError(LimitError::Timeout)) => {
            tracing::error!("Timed out after {} seconds, exiting.", timeout);
            std::process::exit(2); // exit ASAP
        }
        Err(VerifyError::LimitError(LimitError::Oom)) => {
            tracing::error!("Exhausted {} megabytes of memory, exiting.", mem_limit);
            std::process::exit(3); // exit ASAP
        }
        Err(VerifyError::ServerError(err)) => panic!("{}", err),
        Err(VerifyError::Panic(join_error)) => panic!("{}", join_error),
        Err(VerifyError::Interrupted) => {
            tracing::error!("Interrupted");
            ExitCode::from(130) // 130 seems to be a standard exit code for CTRL+C
        }
    }
}

async fn run_server(options: &Options) -> ExitCode {
    let (mut server, _io_threads) = LspServer::connect_stdio(options);
    server.initialize().unwrap();
    let res = server.run_server(|server, user_files| {
        let limits_ref =
            LimitsRef::new(Some(Instant::now() + Duration::from_secs(options.timeout)));
        let res = verify_files_main(options, limits_ref, server, user_files);
        match res {
            Ok(_) => Ok(()),
            Err(VerifyError::Diagnostic(diag)) => {
                server.add_diagnostic(diag).unwrap();
                Ok(())
            }
            Err(err) => Err(err),
        }
    });
    match res {
        Ok(()) => ExitCode::SUCCESS,
        Err(VerifyError::Diagnostic(diag)) => {
            server.add_diagnostic(diag).unwrap();
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
    #[error("{0}")]
    Diagnostic(#[from] Diagnostic),
    #[error("io error")]
    IoError(#[from] io::Error),
    #[error("{0}")]
    LimitError(#[from] LimitError),
    #[error("{0}")]
    ServerError(ServerError),
    #[error("panic: {0}")]
    Panic(#[from] JoinError),
    #[error("interrupted")]
    Interrupted,
}

/// Verify a list of `user_files`. The `options.files` value is ignored here.
pub async fn verify_files(
    options: &Arc<Options>,
    server: &Arc<Mutex<dyn Server>>,
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
    await_with_resource_limits(Some(options.timeout), Some(options.mem_limit), handle).await??
}

/// Synchronously verify the given source code. This is used for tests. The
/// `--werr` option is enabled by default.
#[cfg(test)]
pub(crate) fn verify_test(source: &str) -> (Result<bool, VerifyError>, servers::TestServer) {
    use ast::SourceFilePath;

    let mut options = Options::default();
    options.werr = true;

    let mut server = servers::TestServer::new(&options);
    let file_id = server
        .get_files_internal()
        .lock()
        .unwrap()
        .add(SourceFilePath::Builtin, source.to_owned())
        .id;

    let options = Arc::new(options);
    let limits_ref = LimitsRef::new(None);
    let res = verify_files_main(&options, limits_ref, &mut server, &[file_id]);
    (res, server)
}

#[cfg(test)]
pub(crate) fn single_desugar_test(source: &str) -> Result<String, VerifyError> {
    use ast::SourceFilePath;

    let mut options = Options::default();
    options.werr = true;

    let mut client = servers::TestServer::new(&options);
    let file_id = client
        .get_files_internal()
        .lock()
        .unwrap()
        .add(SourceFilePath::Builtin, source.to_owned())
        .id;

    let mut source_units: Vec<Item<SourceUnit>> =
        SourceUnit::parse(&client.get_file(file_id).unwrap(), options.raw)
            .map_err(|parse_err| parse_err.diagnostic())?;

    let mut source_unit = source_units.remove(0);

    // 2. Resolving (and declaring) idents
    let mut tcx = TyCtx::new(TyKind::EUReal);
    let mut files = client.get_files_internal().lock().unwrap();
    init_calculi(&mut files, &mut tcx);
    init_encodings(&mut files, &mut tcx);
    init_distributions(&mut files, &mut tcx);
    init_lists(&mut files, &mut tcx);
    init_slicing(&mut tcx);
    drop(files);

    let mut resolve = Resolve::new(&mut tcx);
    // first, do forward declarations
    source_unit.enter().forward_declare(&mut resolve)?;
    // then, the actual resolving
    source_unit.enter().resolve(&mut resolve)?;

    // 3. Type checking
    add_default_specs(&mut tcx);

    let mut tycheck = Tycheck::new(&mut tcx);

    let mut entered = source_unit.enter();
    entered.tycheck(&mut tycheck)?;
    entered.check_monotonicity()?;
    drop(entered);

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
    options: &Options,
    limits_ref: LimitsRef,
    server: &mut dyn Server,
    user_files: &[FileId],
) -> Result<bool, VerifyError> {
    // 1. Parsing
    let mut source_units: Vec<Item<SourceUnit>> = Vec::new();
    for file_id in user_files {
        let file = server.get_file(*file_id).unwrap();
        let new_units =
            SourceUnit::parse(&file, options.raw).map_err(|parse_err| parse_err.diagnostic())?;

        // Print the result of parsing if requested
        if options.print_parsed {
            println!("{}: Parsed file:\n", file.path);
            for unit in &new_units {
                println!("{}", unit);
            }
        }

        source_units.extend(new_units);
    }

    // 2. Resolving (and declaring) idents
    let mut tcx = TyCtx::new(TyKind::EUReal);
    let mut files = server.get_files_internal().lock().unwrap();
    init_calculi(&mut files, &mut tcx);
    init_encodings(&mut files, &mut tcx);
    init_distributions(&mut files, &mut tcx);
    init_lists(&mut files, &mut tcx);
    init_slicing(&mut tcx);
    drop(files);

    let mut resolve = Resolve::new(&mut tcx);
    // first, do forward declarations
    for source_unit in &mut source_units {
        source_unit.enter().forward_declare(&mut resolve)?;
    }
    // then, the actual resolving
    for source_unit in &mut source_units {
        source_unit.enter().resolve(&mut resolve)?;
    }

    // 3. Type checking
    add_default_specs(&mut tcx);

    let mut tycheck = Tycheck::new(&mut tcx);
    for source_unit in &mut source_units {
        let mut source_unit = source_unit.enter();
        source_unit.tycheck(&mut tycheck)?;

        let monotonicity_res = source_unit.check_monotonicity();
        if let Err(err) = monotonicity_res {
            server.add_or_throw_diagnostic(err)?;
        }
    }

    // explain high-level HeyVL if requested
    if options.explain_vc {
        for source_unit in &mut source_units {
            let source_unit = source_unit.enter();
            source_unit.explain_vc(&tcx, server)?;
        }
    }

    // write to JANI if requested
    for source_unit in &mut source_units {
        let source_unit = source_unit.enter();
        let jani_res = source_unit.write_to_jani_if_requested(options, &tcx);
        match jani_res {
            Err(VerifyError::Diagnostic(diagnostic)) => server.add_diagnostic(diagnostic)?,
            Err(err) => Err(err)?,
            _ => (),
        }
    }

    // Desugar encodings from source units. They might generate new source
    // units (for side conditions).
    let mut source_units_buf = vec![];
    for source_unit in &mut source_units {
        source_unit
            .enter()
            .apply_encodings(&mut tcx, &mut source_units_buf)?;
    }
    source_units.extend(source_units_buf);

    if options.print_core_procs {
        println!("HeyVL query with generated procs:");
        for source_unit in &mut source_units {
            println!("{}", source_unit);
        }
    }

    let mut verify_units: Vec<Item<VerifyUnit>> = source_units
        .into_iter()
        .flat_map(|item| item.flat_map(SourceUnit::into_verify_unit))
        .collect();

    if options.z3_trace && verify_units.len() > 1 {
        warn!("Z3 tracing is enabled with multiple verification units. Intermediate tracing results will be overwritten.");
    }

    let mut num_proven: usize = 0;
    let mut num_failures: usize = 0;

    for verify_unit in &mut verify_units {
        let (name, mut verify_unit) = verify_unit.enter_with_name();

        // 4. Desugaring: transforming spec calls to procs
        verify_unit.desugar_spec_calls(&mut tcx).unwrap();

        // print HeyVL core after desugaring if requested
        if options.print_core {
            println!("{}: HeyVL core query:\n{}\n", name, *verify_unit);
        }

        // 5. Prepare slicing
        let slice_vars = verify_unit.prepare_slicing(options, &mut tcx, server)?;

        // 6. Generating verification conditions.
        let mut vcgen = Vcgen::new(&tcx, options.explain_core_vc);
        let mut vc_expr = verify_unit.vcgen(&mut vcgen)?;
        if let Some(explanation) = vcgen.explanation {
            server.add_vc_explanation(explanation)?;
        }

        // 7. Unfolding
        vc_expr.unfold(options, &limits_ref, &tcx)?;

        // 8. Quantifier elimination
        if !options.no_qelim {
            vc_expr.qelim(&mut tcx);
        }

        // In-between, gather some stats about the vc expression
        vc_expr.trace_expr_stats();

        // 9. Create the "vc[S] is valid" expression
        let mut vc_is_valid = vc_expr.into_bool_vc();

        if options.egraph {
            vc_is_valid.egraph_simplify();
        }

        // 10. Optimizations
        if !options.no_boolify || options.opt_rel {
            vc_is_valid.remove_parens();
        }
        if !options.no_boolify {
            vc_is_valid.opt_boolify();
        }
        if options.opt_rel {
            vc_is_valid.opt_relational();
        }

        // print theorem to prove if requested
        if options.print_theorem {
            vc_is_valid.print_theorem(name);
        }

        // 11. Translate to Z3
        let ctx = mk_z3_ctx(options);
        let smt_ctx = SmtCtx::new(&ctx, &tcx);
        let mut translate = TranslateExprs::new(&smt_ctx);
        let mut vc_is_valid = vc_is_valid.into_smt_vc(&mut translate);

        // 12. Simplify
        if !options.no_simplify {
            vc_is_valid.simplify();
        }

        // 13. Create Z3 solver with axioms, solve
        let mut result =
            vc_is_valid.run_solver(options, &limits_ref, &ctx, &mut translate, &slice_vars)?;

        server
            .handle_vc_check_result(name, verify_unit.span, &mut result, &mut translate)
            .map_err(VerifyError::ServerError)?;

        // If requested, write the SMT-LIB output.
        result.write_smtlib(options, name)?;

        if options.z3_trace {
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
            ProveResult::Counterexample(_) | ProveResult::Unknown(_) => num_failures += 1,
        }
    }

    if !options.language_server {
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

fn setup_tracing(options: &Options) {
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
