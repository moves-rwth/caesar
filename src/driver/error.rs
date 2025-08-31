use std::{io, process::ExitCode};

use tokio::task::JoinError;

use crate::{
    ast::Diagnostic,
    driver::commands::options::ResourceLimitOptions,
    resource_limits::LimitError,
    servers::{ServerError, SharedServer},
};

/// Errors that can occur in the verifier.
///
/// Note that some unit not verifying (solver yielding unknown or a
/// counter-example) is not actually considered a [`VerifyError`].
#[derive(Debug, thiserror::Error)]
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

/// As the last step of the CLI, process a result of Caesar - either success
/// (`Ok(true)`), failure (`Ok(false)`), or an error.
pub fn finalize_caesar_result(
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
