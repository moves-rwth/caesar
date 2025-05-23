//! Pretty-printing SMT-LIB code.

use std::{io::Write, process::Command};

use tempfile::NamedTempFile;
use thiserror::Error;
use z3::Solver;

use crate::{prover::ProveResult, util::PrefixWriter};

#[derive(Debug, Error)]
pub enum RacoReadError {
    #[error("{0}")]
    IoError(#[from] std::io::Error),
    #[error("{0}")]
    ReadError(String),
}

/// SMT-LIB output from the solver.
#[derive(Debug, Clone)]
pub struct Smtlib(String);

impl Smtlib {
    pub fn from_solver(solver: &Solver<'_>) -> Self {
        Smtlib(format!("{}", solver))
    }

    /// Add a `(check-sat)` command at the end.
    pub fn add_check_sat(&mut self) {
        self.0.push_str("\n(check-sat)");
    }

    pub fn add_check_sat_assuming(&mut self, assumptions: Vec<String>) {
        let assumptions_str: Vec<String> = assumptions.iter().map(|a| a.to_string()).collect();

        self.0.push_str(&format!(
            "\n(check-sat-assuming ({}))",
            assumptions_str.join(" ").as_str()
        ));
    }

    /// Add a `(check-sat)` command at the end.
    pub fn add_details_query(&mut self, prove_result: &ProveResult) {
        match prove_result {
            ProveResult::Proof => {}
            ProveResult::Counterexample => self.0.push_str("\n(get-model)\n"),
            ProveResult::Unknown(_) => self.0.push_str("\n(get-info :reason-unknown)\n"),
        }
    }

    /// Run `raco read` to format this SMT-LIB.
    pub fn pretty_raco_read(&mut self) -> Result<(), RacoReadError> {
        let mut command = Command::new("raco");
        command.arg("read");

        let mut input_file = NamedTempFile::new()?;
        input_file.write_all(self.0.as_bytes())?;
        let input_path = input_file.into_temp_path();
        command.arg(&input_path);

        let output = command.output()?;
        if !output.status.success() {
            let stderr = String::from_utf8(output.stderr).unwrap();
            return Err(RacoReadError::ReadError(stderr));
        }

        input_path.close()?;

        self.0 = String::from_utf8(output.stdout).unwrap();

        Ok(())
    }

    /// Return the underlying String.
    pub fn into_string(self) -> String {
        self.0
    }

    /// Build a new writer that wraps every line in an SMT-LIB comment.
    pub fn comment_writer<W>(writer: W) -> PrefixWriter<'static, W> {
        PrefixWriter::new(b"; ", writer)
    }
}
