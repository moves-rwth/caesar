use std::{
    error::Error,
    sync::{Arc, Mutex},
};

use crate::ast::{Diagnostic, FileId, Files, Span, StoredFile};

mod cli;
mod lsp;
#[cfg(test)]
mod test;

pub use cli::CliServer;
pub use lsp::LspServer;
#[cfg(test)]
pub use test::TestServer;

pub type ServerError = Box<dyn Error + Send + Sync>;

/// A server that serves information to a client, such as the CLI or an LSP
/// client.
pub trait Server: Send {
    /// Send our custom `serverReady` notification to the client.
    fn send_server_ready(&self) -> Result<(), ServerError>;

    fn get_file(&self, file_id: FileId) -> Option<Arc<StoredFile>>;

    fn get_files_internal(&mut self) -> &Mutex<Files>;

    /// Add a new [`Diagnostic`].
    fn add_diagnostic(&mut self, diagnostic: Diagnostic) -> Result<(), ServerError>;

    /// Send a verification status message to the client (a custom notification).
    fn set_verify_status(&mut self, span: Span, status: bool) -> Result<(), ServerError>;
}
