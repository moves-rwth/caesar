// clippy (correctly) tells us that we can sometimes elide lifetimes, but many
// of these cases make the declarations way more clear than with implicit
// lifetimes.
#![allow(clippy::needless_lifetimes)]

use std::{
    collections::HashMap,
    io,
    ops::DerefMut,
    process::ExitCode,
    sync::{Arc, Mutex},
    time::Instant,
};

use crate::{
    driver::{
        commands::{
            CaesarCli, CaesarCommand, DebugOptions, InputOptions, ModelCheckingOptions,
            ResourceLimitOptions, ShellCompletionsCommand, ToJaniCommand, VerifyCommand,
        },
        core_verify::CoreVerifyTask,
        front::{init_tcx, Module},
        item::Item,
        smt_proof::{mk_function_encoder, set_global_z3_params},
    },
    front::{resolve::Resolve, tycheck::Tycheck},
    smt::{translate_exprs::TranslateExprs, DepConfig, SmtCtx},
    timing::TimingLayer,
    tyctx::TyCtx,
    vc::vcgen::Vcgen,
};
use ast::{Diagnostic, FileId};
use clap::CommandFactory;
use mc::run_storm::{run_storm, storm_result_to_diagnostic};
use refinement::run_verify_entailment_command;
use resource_limits::{await_with_resource_limits, LimitError, LimitsRef};
use servers::{run_lsp_server, CliServer, LspServer, Server, ServerError};
use thiserror::Error;
use timing::DispatchBuilder;
use tokio::task::JoinError;
use tracing::{error, info, warn};
use vc::explain::VcExplanation;
use z3::{Config, Context};
use z3rro::{prover::ProveResult, util::ReasonUnknown};

pub mod ast;
pub mod depgraph;
mod driver;
pub mod front;
pub mod intrinsic;
pub mod mc;
pub mod opt;
pub mod pretty;
mod procs;
mod proof_rules;
mod refinement;
mod resource_limits;
mod scope_map;
mod servers;
mod slicing;
mod smt;
mod timing;
pub mod tyctx;
pub mod vc;
mod version;

#[tokio::main]
async fn main() -> ExitCode {
    let options = CaesarCli::parse_and_normalize();

    if let Some(debug_options) = options.debug_options() {
        if debug_options.debug {
            let mut stderr = io::stderr().lock();
            version::write_detailed_command_info(&mut stderr).unwrap();
        }
        // install global collector configured based on RUST_LOG env var.
        setup_tracing(debug_options);
    }

    match options.command {
        CaesarCommand::Verify(options) => run_verify_command(options).await,
        CaesarCommand::Entailment(options) => run_verify_entailment_command(options).await,
        CaesarCommand::Mc(options) => run_model_checking_command(options),
        CaesarCommand::Lsp(options) => run_lsp_command(options).await,
        CaesarCommand::ShellCompletions(options) => run_shell_completions_command(options),
        CaesarCommand::Other(_) => unreachable!(),
    }
}

async fn run_verify_command(options: VerifyCommand) -> ExitCode {
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
    verify_result: Result<bool, CaesarError>,
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
        Err(CaesarError::Diagnostic(diagnostic)) => {
            server.lock().unwrap().add_diagnostic(diagnostic).unwrap();
            ExitCode::from(1)
        }
        Err(CaesarError::IoError(err)) => {
            eprintln!("IO Error: {err}");
            ExitCode::from(1)
        }
        Err(CaesarError::LimitError(LimitError::Timeout)) => {
            tracing::error!("Timed out after {} seconds, exiting.", timeout.as_secs());
            std::process::exit(2); // exit ASAP
        }
        Err(CaesarError::LimitError(LimitError::Oom)) => {
            tracing::error!(
                "Exhausted {} megabytes of memory, exiting.",
                mem_limit.as_megabytes()
            );
            std::process::exit(3); // exit ASAP
        }
        Err(CaesarError::UserError(err)) => {
            eprintln!("Error: {err}");
            ExitCode::from(1)
        }
        Err(CaesarError::ServerError(err)) => panic!("{}", err),
        Err(CaesarError::Panic(join_error)) => panic!("{}", join_error),
        Err(CaesarError::Interrupted) => {
            tracing::error!("Interrupted");
            ExitCode::from(130) // 130 seems to be a standard exit code for CTRL+C
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

async fn run_lsp_command(mut options: VerifyCommand) -> ExitCode {
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
                Err(CaesarError::Diagnostic(diag)) => {
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
        Err(CaesarError::Diagnostic(diag)) => {
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
pub enum CaesarError {
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
}

/// Verify a list of `user_files`. The `options.files` value is ignored here.
pub async fn verify_files(
    options: &Arc<VerifyCommand>,
    server: &SharedServer,
    user_files: Vec<FileId>,
) -> Result<bool, CaesarError> {
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
) -> Result<(Module, TyCtx), CaesarError> {
    let mut module = Module::new();
    for file_id in user_files {
        let file = server.get_file(*file_id).unwrap();
        let new_units = module
            .parse(&file, input_options.raw)
            .map_err(|parse_err| parse_err.diagnostic())?;

        // Print the result of parsing if requested
        if debug_options.print_parsed {
            println!("{}: Parsed file:\n", file.path);
            for unit in new_units {
                println!("{unit}");
            }
        }
    }

    let mut files = server.get_files_internal().lock().unwrap();
    let mut tcx = init_tcx(&mut files);
    drop(files);

    let mut resolve = Resolve::new(&mut tcx);
    module.resolve(&mut resolve)?;
    let mut tycheck = Tycheck::new(&mut tcx);
    module.tycheck(&mut tycheck, server)?;

    // filter if requested
    if let Some(filter) = &input_options.filter {
        module.filter(filter)?;
    };

    Ok((module, tcx))
}

/// Synchronously verify the given source code. This is used for tests. The
/// `--werr` option is enabled by default.
#[cfg(test)]
pub(crate) fn verify_test(source: &str) -> (Result<bool, CaesarError>, servers::TestServer) {
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
pub(crate) fn single_desugar_test(source: &str) -> Result<String, CaesarError> {
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

    let (mut module, mut tcx) = parse_and_tycheck(
        &options.input_options,
        &options.debug_options,
        &mut server,
        &[file_id],
    )?;

    assert_eq!(module.items.len(), 1);

    module.apply_encodings(&mut tcx, &mut server)?;

    Ok(module.to_string())
}

/// Synchronously verify the given files.
fn verify_files_main(
    options: &VerifyCommand,
    limits_ref: LimitsRef,
    server: &mut dyn Server,
    user_files: &[FileId],
) -> Result<bool, CaesarError> {
    let (mut module, mut tcx) = parse_and_tycheck(
        &options.input_options,
        &options.debug_options,
        server,
        user_files,
    )?;

    // Register all relevant source units with the server
    module.register_with_server(server)?;

    // explain high-level HeyVL if requested
    if options.lsp_options.explain_vc {
        module.explain_high_level_vc(&tcx, &limits_ref, server)?;
    }

    // write to JANI if requested
    run_model_checking(
        &options.model_checking_options,
        &mut module,
        server,
        &limits_ref,
        &tcx,
        false,
    )?;

    // Visit every source unit and check possible cases of unsoundness
    // based on the provided calculus annotations
    module.check_calculus_rules(&mut tcx)?;

    // Desugar encodings from source units.
    module.apply_encodings(&mut tcx, server)?;

    if options.debug_options.print_core_procs {
        println!("HeyVL verification task with generated procs:");
        println!("{module}");
    }

    // If `--no-verify` is set and we don't need to print SMT-LIB or explain the
    // core VC, we can return early.
    if options.debug_options.no_verify
        && !options.lsp_options.explain_core_vc
        && !options.debug_options.z3_probe
        && !options.debug_options.print_smt
        && !options.debug_options.print_core
        && !options.debug_options.print_core_procs
        && options.debug_options.smt_dir.is_none()
    {
        return Ok(true);
    }

    // generate dependency graph to determine which declarations are needed for
    // the SMT translation later
    let mut depgraph = module.generate_depgraph(&options.opt_options.function_encoding)?;

    let mut verify_units: Vec<Item<CoreVerifyTask>> = module
        .items
        .into_iter()
        .flat_map(|item| {
            item.flat_map(|unit| CoreVerifyTask::from_source_unit(unit, &mut depgraph))
        })
        .collect();

    if options.debug_options.z3_trace && verify_units.len() > 1 {
        warn!("Z3 tracing is enabled with multiple verification units. Intermediate tracing results will be overwritten.");
    }

    // set requested global z3 options
    set_global_z3_params(options, &limits_ref);

    let mut num_proven: usize = 0;
    let mut num_failures: usize = 0;

    for verify_unit in &mut verify_units {
        let (name, mut verify_unit) = verify_unit.enter_with_name();

        limits_ref.check_limits()?;

        // Set the current unit as ongoing
        server.set_ongoing_unit(name)?;

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

        // 7. Unfolding (applies substitutions)
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
        let ctx = Context::new(&Config::default());
        let function_encoder = mk_function_encoder(&tcx, &depgraph, options)?;
        let dep_config = DepConfig::Set(vc_is_valid.get_dependencies());
        let smt_ctx = SmtCtx::new(&ctx, &tcx, function_encoder, dep_config);
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
                return Err(CaesarError::Interrupted)
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
            .handle_vc_check_result(name, &mut result, &mut translate)
            .map_err(CaesarError::ServerError)?;
    }

    if !options.lsp_options.language_server {
        println!();
        let ending = if num_failures == 0 {
            " veni, vidi, vici!"
        } else {
            ""
        };
        println!("{num_proven} verified, {num_failures} failed.{ending}");
    }

    Ok(num_failures == 0)
}

fn run_model_checking_command(options: ToJaniCommand) -> ExitCode {
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
) -> Result<(), CaesarError> {
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
    module: &mut Module,
    server: &mut dyn Server,
    limits_ref: &LimitsRef,
    tcx: &TyCtx,
    is_jani_command: bool,
) -> Result<(), CaesarError> {
    let mut options = options.clone();

    let mut temp_dir = None;
    if options.jani_dir.is_none() {
        if is_jani_command && options.run_storm.is_none() {
            return Err(CaesarError::UserError(
                "Either --jani-dir or --run-storm must be provided.".into(),
            ));
        }
        if options.run_storm.is_some() {
            temp_dir = Some(tempfile::tempdir().map_err(|err| {
                CaesarError::UserError(
                    format!("Could not create temporary directory: {err}").into(),
                )
            })?);
            options.jani_dir = temp_dir.as_ref().map(|dir| dir.path().to_owned());
        }
    }

    for source_unit in &mut module.items {
        let source_unit = source_unit.enter_mut();
        let jani_res = source_unit.write_to_jani_if_requested(&options, tcx);
        match jani_res {
            Err(CaesarError::Diagnostic(diagnostic)) => server.add_diagnostic(diagnostic)?,
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
    eprintln!("Timings: {timings:?}");
}

fn run_shell_completions_command(options: ShellCompletionsCommand) -> ExitCode {
    let binary_name = std::env::args().next().unwrap();
    clap_complete::aot::generate(
        options.shell.unwrap(),
        &mut CaesarCli::command(),
        binary_name,
        &mut std::io::stdout(),
    );
    ExitCode::SUCCESS
}
