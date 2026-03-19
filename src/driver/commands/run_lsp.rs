use std::{
    process::ExitCode,
    sync::{Arc, Mutex},
};

use crate::{
    driver::{commands::verify::VerifyCommand, error::CaesarError},
    servers::{run_lsp_server, LspServer, Server},
};

/// Run the language server.
pub async fn run_lsp_command(mut options: VerifyCommand) -> ExitCode {
    let (mut server, _io_threads) = LspServer::connect_stdio(&options);
    server.initialize().unwrap();
    let server = Arc::new(Mutex::new(server));
    options.lsp_options.language_server = true;
    let options = Arc::new(options);
    let res = run_lsp_server(server.clone(), options).await;

    match res {
        Ok(()) => ExitCode::SUCCESS,
        Err(CaesarError::Diagnostic(diag)) => {
            server.lock().unwrap().add_diagnostic(diag).unwrap();
            ExitCode::FAILURE
        }
        Err(err) => panic!("{}", err), // TODO
    }
}
