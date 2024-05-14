use std::{
    error::Error,
    sync::{Arc, Mutex},
};

use crate::{
    ast::{Diagnostic, FileId, Files, Span, StoredFile},
    VerifyError,
};

mod cli;
mod lsp;
#[cfg(test)]
mod test;

use ariadne::ReportKind;
pub use cli::CliServer;
pub use lsp::LspServer;
use serde::{Deserialize, Serialize};
#[cfg(test)]
pub use test::TestServer;

pub type ServerError = Box<dyn Error + Send + Sync>;

#[derive(Debug, Serialize, Deserialize, Clone, Copy)]
#[serde(rename_all = "lowercase")]
pub enum VerifyResult {
    Verified,
    Failed,
    Unknown,
}

/// A server that serves information to a client, such as the CLI or an LSP
/// client.
pub trait Server: Send {
    /// Send our custom `serverReady` notification to the client.
    fn send_server_ready(&self) -> Result<(), ServerError>;

    fn get_file(&self, file_id: FileId) -> Option<Arc<StoredFile>>;

    fn get_files_internal(&mut self) -> &Mutex<Files>;

    /// Add a new [`Diagnostic`]. Abort with a [`VerifyError::Diagnostic`] if
    /// the diagnostic is fatal.
    fn add_diagnostic(&mut self, diagnostic: Diagnostic) -> Result<(), VerifyError>;

    /// Send a verification status message to the client (a custom notification).
    fn set_verify_status(&mut self, span: Span, status: VerifyResult) -> Result<(), ServerError>;
}

fn unless_fatal_error(werr: bool, diagnostic: Diagnostic) -> Result<Diagnostic, VerifyError> {
    if diagnostic.kind() == ReportKind::Error || werr {
        Err(VerifyError::Diagnostic(diagnostic))
    } else {
        Ok(diagnostic)
    }
}
