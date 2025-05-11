use std::{
    error::Error,
    process::ExitCode,
    sync::{Arc, Mutex},
};

use crate::{
    ast::{Diagnostic, FileId, Files, Span, StoredFile},
    driver::{SmtVcCheckResult, SourceUnitName},
    smt::translate_exprs::TranslateExprs,
    vc::explain::VcExplanation,
    VerifyError,
};

mod cli;
mod lsp;
#[cfg(test)]
mod test;

use ariadne::ReportKind;
pub use cli::CliServer;
pub use lsp::run_lsp_server;
pub use lsp::LspServer;
use serde::{Deserialize, Serialize};
#[cfg(test)]
pub use test::TestServer;
use z3rro::prover::ProveResult;

pub type ServerError = Box<dyn Error + Send + Sync>;

#[derive(Debug, Serialize, Deserialize, Clone, Copy)]
#[serde(rename_all = "lowercase")]
pub enum VerifyResult {
    // If the verification is not done yet the result is Todo
    Todo,
    Ongoing,
    Verified,
    Failed,
    Unknown,
    Timeout,
}

impl VerifyResult {
    pub fn from_prove_result(result: &ProveResult) -> Self {
        match &result {
            ProveResult::Proof => VerifyResult::Verified,
            ProveResult::Counterexample => VerifyResult::Failed,
            ProveResult::Unknown(_) => VerifyResult::Unknown,
        }
    }
}

/// A server that serves information to a client, such as the CLI or an LSP
/// client.
pub trait Server: Send {
    /// Send our custom `serverReady` notification to the client.
    fn send_server_ready(&self) -> Result<(), ServerError>;

    fn get_file(&self, file_id: FileId) -> Option<Arc<StoredFile>>;

    fn get_files_internal(&mut self) -> &Mutex<Files>;

    /// Add a new [`Diagnostic`].
    fn add_diagnostic(&mut self, diagnostic: Diagnostic) -> Result<(), VerifyError>;

    /// Add a new [`Diagnostic`], but throw it as a [`VerifyError::Diagnostic`]
    /// if it is a fatal error.
    fn add_or_throw_diagnostic(&mut self, diagnostic: Diagnostic) -> Result<(), VerifyError>;

    /// Add an explanation for vc calculations.
    fn add_vc_explanation(&mut self, explanation: VcExplanation) -> Result<(), VerifyError>;

    /// Register a source unit span with the server.
    fn register_source_unit(&mut self, span: Span) -> Result<(), VerifyError>;

    /// Register a verify unit span as the current verifying with the server.
    fn set_ongoing_unit(&mut self, span: Span) -> Result<(), VerifyError>;

    /// Send a verification status message to the client (a custom notification).
    fn handle_vc_check_result<'smt, 'ctx>(
        &mut self,
        name: &SourceUnitName,
        span: Span,
        result: &mut SmtVcCheckResult<'ctx>,
        translate: &mut TranslateExprs<'smt, 'ctx>,
    ) -> Result<(), ServerError>;

    /// Return an exit code for the process.
    ///
    /// Default implementation returns `ExitCode::SUCCESS`.
    fn exit_code(&self) -> ExitCode {
        ExitCode::SUCCESS
    }
}

fn unless_fatal_error(werr: bool, diagnostic: Diagnostic) -> Result<Diagnostic, VerifyError> {
    if diagnostic.kind() == ReportKind::Error || werr {
        Err(VerifyError::Diagnostic(diagnostic))
    } else {
        Ok(diagnostic)
    }
}
