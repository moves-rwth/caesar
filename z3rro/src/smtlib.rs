//! Pretty-printing SMT-LIB code.

use std::{io::Write, process::Command};

use tempfile::NamedTempFile;
use thiserror::Error;
use z3::Solver;

use crate::{params::SmtParams, prover::ProveResult};

#[derive(Debug, Error)]
pub enum RacoReadError {
    #[error("{0}")]
    IoError(#[from] std::io::Error),
    #[error("{0}")]
    ReadError(String),
}

/// SMT-LIB output from the solver.
#[derive(Debug, Clone)]
pub struct Smtlib {
    /// (Optional) parameters to include in the output.
    params: Option<SmtParams>,
    /// SMT-LIB output from the solver and any additional commands added via
    /// functions.
    body: String,
}

impl Smtlib {
    pub fn from_solver(params: Option<SmtParams>, solver: &Solver<'_>) -> Self {
        Smtlib {
            params,
            body: format!("{solver}"),
        }
    }

    /// Add a `(check-sat)` command at the end.
    pub fn add_check_sat(&mut self) {
        self.body.push_str("\n(check-sat)");
    }

    /// Add a `(check-sat)` command at the end.
    pub fn add_details_query(&mut self, prove_result: &ProveResult) {
        match prove_result {
            ProveResult::Proof => {}
            ProveResult::Counterexample => self.body.push_str("\n(get-model)\n"),
            ProveResult::Unknown(_) => self.body.push_str("\n(get-info :reason-unknown)\n"),
        }
    }

    /// Run `raco read` to format this SMT-LIB.
    pub fn pretty_raco_read(&mut self) -> Result<(), RacoReadError> {
        let mut command = Command::new("raco");
        command.arg("read");

        let mut input_file = NamedTempFile::new()?;
        input_file.write_all(self.body.as_bytes())?;
        let input_path = input_file.into_temp_path();
        command.arg(&input_path);

        let output = command.output()?;
        if !output.status.success() {
            let stderr = String::from_utf8(output.stderr).unwrap();
            return Err(RacoReadError::ReadError(stderr));
        }

        input_path.close()?;

        self.body = String::from_utf8(output.stdout).unwrap();

        Ok(())
    }

    /// Return the SMT-LIB as a String.
    pub fn into_string(self) -> String {
        match self.params {
            Some(params) => format!("{}\n{}", params, self.body),
            None => self.body,
        }
    }
}
