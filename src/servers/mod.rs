use std::{
    error::Error,
    process::ExitCode,
    sync::{Arc, Mutex},
};

use crate::{
    ast::{Diagnostic, FileId, Files, Span, SpanVariant, StoredFile},
    driver::{
        error::CaesarError,
        front::SourceUnit,
        item::{Item, SourceUnitName},
        smt_proof::SmtVcCheckResult,
    },
    smt::translate_exprs::TranslateExprs,
    vc::explain::VcExplanation,
};

mod cli;
mod lsp;
#[cfg(test)]
mod test;

use ariadne::ReportKind;
pub use cli::CliServer;
use indexmap::IndexMap;
pub use lsp::run_lsp_server;
pub use lsp::LspServer;
use serde::{Deserialize, Serialize};
#[cfg(test)]
pub use test::TestServer;
use z3rro::prover::ProveResult;

pub type ServerError = Box<dyn Error + Send + Sync>;

#[derive(Debug, Serialize, Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum VerifyStatus {
    /// The verification task is scheduled, but not started.
    Todo,
    /// The verification task is in progress.
    Ongoing,
    /// The verification was successful.
    Verified,
    /// The verification yielded a counterexample.
    Failed,
    /// The SMT solver returned an unknown result.
    Unknown,
    /// The verification task was cancelled.
    Timeout,
}

impl VerifyStatus {
    pub fn from_prove_result(result: &ProveResult) -> Self {
        match &result {
            ProveResult::Proof => VerifyStatus::Verified,
            ProveResult::Counterexample => VerifyStatus::Failed,
            ProveResult::Unknown(_) => VerifyStatus::Unknown,
        }
    }

    /// Returns true if the verification status is not `Todo` or `Ongoing`.
    fn is_completed(&self) -> bool {
        self != &VerifyStatus::Todo && self != &VerifyStatus::Ongoing
    }

    /// Combine two statuses into one, choosing the most imformative one.
    fn combine(&self, other: &Self) -> Self {
        match (self, other) {
            (VerifyStatus::Failed, _) | (_, VerifyStatus::Failed) => VerifyStatus::Failed,
            (VerifyStatus::Verified, VerifyStatus::Verified) => VerifyStatus::Verified,
            (VerifyStatus::Unknown, _) | (_, VerifyStatus::Unknown) => VerifyStatus::Unknown,
            (VerifyStatus::Timeout, _) | (_, VerifyStatus::Timeout) => VerifyStatus::Timeout,
            (VerifyStatus::Ongoing, _) | (_, VerifyStatus::Ongoing) => VerifyStatus::Ongoing,
            (VerifyStatus::Todo, _) | (_, VerifyStatus::Todo) => VerifyStatus::Todo,
        }
    }
}

/// Collects verification statuses for source units and groups them by their
/// spans, aggregating the statuses for each span.
#[derive(Debug, Default)]
pub struct VerifyStatusList {
    results: IndexMap<SourceUnitName, VerifyStatus>,
}

impl VerifyStatusList {
    pub fn update_status(&mut self, name: &SourceUnitName, result: VerifyStatus) {
        let prev = self.results.insert(name.clone(), result);
        if prev.is_none() && result != VerifyStatus::Todo {
            panic!("Must first register the source unit with Todo result before adding any other result");
        }
    }

    // Set all uncompleted source units to `Timeout` status, returning the
    // modified source unit names and the previous status.
    pub fn timeout_all(&mut self) -> impl Iterator<Item = (&SourceUnitName, VerifyStatus)> {
        self.results
            .iter_mut()
            .filter(|(_, status)| !status.is_completed())
            .map(|(name, status)| {
                let old_status = *status;
                *status = VerifyStatus::Timeout;
                (name, old_status)
            })
    }

    pub fn iter_spans(&self) -> impl Iterator<Item = (Span, VerifyStatus)> {
        let mut by_span: IndexMap<Span, VerifyStatus> = IndexMap::new();
        for (name, result) in &self.results {
            // Drop the variant information from the span, as we properly need
            // to combine the results for all spans that are related to the same
            // location, regardless of the metadata.
            let span = name.span().variant(SpanVariant::Combined);
            if let Some(prev) = by_span.get_mut(&span) {
                *prev = prev.combine(result);
            } else {
                by_span.insert(span, *result);
            }
        }
        by_span.into_iter()
    }

    pub fn remove_file(&mut self, file_id: FileId) {
        self.results.retain(|name, _| name.span().file != file_id);
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
    fn add_diagnostic(&mut self, diagnostic: Diagnostic) -> Result<(), CaesarError>;

    /// Add a new [`Diagnostic`], but throw it as a [`VerifyError::Diagnostic`]
    /// if it is a fatal error.
    fn add_or_throw_diagnostic(&mut self, diagnostic: Diagnostic) -> Result<(), CaesarError>;

    /// Add an explanation for vc calculations.
    fn add_vc_explanation(&mut self, explanation: VcExplanation) -> Result<(), CaesarError>;

    /// Register a source unit span with the server.
    fn register_source_unit(
        &mut self,
        source_unit: &mut Item<SourceUnit>,
    ) -> Result<(), CaesarError>;

    /// Register a verify unit span as the current verifying with the server.
    fn set_ongoing_unit(&mut self, name: &SourceUnitName) -> Result<(), CaesarError>;

    /// Send a verification status message to the client (a custom notification).
    fn handle_vc_check_result<'smt, 'ctx>(
        &mut self,
        name: &SourceUnitName,
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

/// A shared server instance, protected by a mutex.
pub type SharedServer = Arc<Mutex<dyn Server>>;

fn unless_fatal_error(werr: bool, diagnostic: Diagnostic) -> Result<Diagnostic, CaesarError> {
    if diagnostic.kind() == ReportKind::Error || werr {
        Err(CaesarError::Diagnostic(diagnostic))
    } else {
        Ok(diagnostic)
    }
}
