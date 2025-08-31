use std::{ops::DerefMut, process::ExitCode, sync::Mutex, time::Instant};

use clap::Args;
use tracing::trace;

use crate::{
    ast::FileId,
    driver::{
        commands::{
            mk_cli_server,
            options::{DebugOptions, InputOptions, ModelCheckingOptions, ResourceLimitOptions},
        },
        error::{finalize_caesar_result, CaesarError},
        front::{parse_and_tycheck, Module},
    },
    mc::run_storm::{run_storm, storm_result_to_diagnostic},
    resource_limits::LimitsRef,
    servers::Server,
    tyctx::TyCtx,
};

#[derive(Debug, Args)]
pub struct ModelCheckCommand {
    #[command(flatten)]
    pub input_options: InputOptions,

    #[command(flatten)]
    pub rlimit_options: ResourceLimitOptions,

    #[command(flatten)]
    pub model_checking_options: ModelCheckingOptions,

    #[command(flatten)]
    pub debug_options: DebugOptions,
}

/// Run the model checking command.
pub fn run_model_checking_command(options: ModelCheckCommand) -> ExitCode {
    let (user_files, server) = match mk_cli_server(&options.input_options) {
        Ok(value) => value,
        Err(value) => return value,
    };
    let res = model_checking_main(&options, user_files, &server).map(|_| true);
    finalize_caesar_result(server, &options.rlimit_options, res)
}

fn model_checking_main(
    options: &ModelCheckCommand,
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

/// Actually handle the model checking, whether as part of the model checking
/// command ([`run_model_checking_command`]) or as part of another command.
pub fn run_model_checking(
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
                    trace!("Result from storm: {:?}", res);
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
