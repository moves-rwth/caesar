use std::{ops::DerefMut, process::ExitCode, sync::Mutex, time::Instant};

use clap::Args;

use crate::{
    ast::FileId,
    dafny::translate_to_dafny,
    driver::{
        commands::{
            mk_cli_server,
            options::{DafnyOptions, DebugOptions, InputOptions, ResourceLimitOptions},
        },
        error::{finalize_caesar_result, CaesarError},
        front::parse_and_tycheck,
    },
    resource_limits::LimitsRef,
    servers::Server,
};

#[derive(Debug, Default, Args)]
pub struct DafnyCommand {
    #[command(flatten)]
    pub input_options: InputOptions,

    #[command(flatten)]
    pub rlimit_options: ResourceLimitOptions,

    #[command(flatten)]
    pub dafny_options: DafnyOptions,

    #[command(flatten)]
    pub debug_options: DebugOptions,
}

pub fn run_dafny_command(options: DafnyCommand) -> ExitCode {
    let (user_files, server) = match mk_cli_server(&options.input_options) {
        Ok(value) => value,
        Err(value) => return value,
    };
    let res = dafny_main(&options, user_files, &server).map(|_| true);
    finalize_caesar_result(server, &options.rlimit_options, res)
}

fn dafny_main(
    options: &DafnyCommand,
    user_files: Vec<FileId>,
    server: &Mutex<dyn Server>,
) -> Result<(), CaesarError> {
    if options.input_options.raw {
        return Err(CaesarError::UserError(
            "The Dafny backend does not support `--raw`; pass HeyVL declarations instead.".into(),
        ));
    }

    let parse_input_options = InputOptions {
        files: options.input_options.files.clone(),
        raw: options.input_options.raw,
        parser_mode: options.input_options.parser_mode,
        werr: options.input_options.werr,
        filter: None,
    };

    let mut server_lock = server.lock().unwrap();
    let (mut module, tcx) = parse_and_tycheck(
        &parse_input_options,
        &options.debug_options,
        &mut *server_lock,
        &user_files,
    )?;

    let timeout = Instant::now() + options.rlimit_options.timeout();
    let mem_limit = options.rlimit_options.mem_limit();
    let limits_ref = LimitsRef::new(Some(timeout), Some(mem_limit));

    translate_to_dafny(
        &options.dafny_options,
        &options.input_options,
        &mut module,
        server_lock.deref_mut(),
        &limits_ref,
        &tcx,
        &user_files,
    )
}
