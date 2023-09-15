//! Pretty-printing SMT-LIB code.

use std::{io::Write, process::Command};

use tempfile::NamedTempFile;
use thiserror::Error;
use z3::Solver;

/// Get the SMT solver's state as an SMT-LIB benchmark with a `(check-sat)`
/// command at the end.
pub fn get_solver_smtlib(solver: &Solver) -> String {
    format!("{}\n(check-sat)", solver)
}

/// Tries to pretty-print the SMT solver's state as an SMT-LIB benchmark with a
/// `(check-sat)` command at the end. If `raco read` is installed, it will try
/// to run it. If not, this function just returns the unmodified input.
///
/// `raco read` is Racket's Lisp formatter. It can be installed by installing
/// Racket and then running `raco pkg install compiler-lib`.
pub fn get_pretty_solver_smtlib(solver: &Solver) -> String {
    let smtlib = get_solver_smtlib(solver);

    if !is_raco_read_installed() {
        return smtlib;
    }
    match raco_read(&smtlib) {
        Ok(smtlib) => smtlib,
        Err(err) => {
            tracing::error!(err= ?err, "Error formatting SMT-LIB");
            smtlib
        }
    }
}

fn is_raco_read_installed() -> bool {
    Command::new("raco").arg("read").output().is_ok()
}

#[derive(Debug, Error)]
pub enum RacoReadError {
    #[error("{0}")]
    IoError(#[from] std::io::Error),
    #[error("{0}")]
    ReadError(String),
}

/// Run `raco read` on the input.
pub fn raco_read(input: &str) -> Result<String, RacoReadError> {
    let mut command = Command::new("raco");
    command.arg("read");

    let mut input_file = NamedTempFile::new()?;
    input_file.write_all(input.as_bytes())?;
    let input_path = input_file.into_temp_path();
    command.arg(&input_path);

    let output = command.output()?;
    if !output.status.success() {
        let stderr = String::from_utf8(output.stderr).unwrap();
        return Err(RacoReadError::ReadError(stderr));
    }

    input_path.close()?;

    Ok(String::from_utf8(output.stdout).unwrap())
}
