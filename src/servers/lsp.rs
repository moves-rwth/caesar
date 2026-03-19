use std::{
    collections::HashMap,
    mem,
    ops::Deref,
    sync::{Arc, Mutex},
    time::Instant,
};

use ariadne::ReportKind;
use itertools::Itertools;
use lsp_server::{Connection, ErrorCode, IoThreads, Message, Request, RequestId, Response};
use lsp_types::{
    DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    InitializeParams, ServerCapabilities, TextDocumentItem, TextDocumentSyncCapability,
    TextDocumentSyncKind, VersionedTextDocumentIdentifier,
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

use crate::{
    ast::{DeclKind, Diagnostic, FileId, Files, SourceFilePath, StoredFile},
    driver::{
        commands::verify::{verify_files_with_limits, VerifyCommand},
        error::CaesarError,
        front::SourceUnit,
        item::{Item, SourceUnitName},
        smt_proof::SmtVcProveResult,
    },
    proof_rules::calculus::ProcSoundness,
    resource_limits::{LimitError, LimitsRef, MemorySize},
    servers::{FileStatus, FileStatusType},
    smt::translate_exprs::TranslateExprs,
    vc::explain::VcExplanation,
    version::caesar_semver_version,
};

use super::{unless_fatal_error, Server, ServerError, SharedServer, VerifyStatus};

#[derive(Debug, Serialize, Deserialize)]
struct VerifyRequest {
    text_document: VersionedTextDocumentIdentifier,
}

impl VerifyRequest {
    fn extract(request: Request) -> Result<(lsp_server::RequestId, Self), CaesarError> {
        request
            .extract::<Self>("custom/verify")
            .map_err(|e| CaesarError::ServerError(e.into()))
    }
}

#[derive(Debug, Serialize, Deserialize)]
struct DocumentVerifyStatusUpdate {
    document: VersionedTextDocumentIdentifier,
    status_type: FileStatusType,
    verify_statuses: Vec<(lsp_types::Range, VerifyStatus)>,
    status_counts: Vec<(VerifyStatus, usize)>,
}

#[derive(Debug, Serialize, Deserialize)]
struct ComputedPreUpdate {
    document: VersionedTextDocumentIdentifier,
    #[allow(clippy::type_complexity)]
    pres: Vec<(lsp_types::Range, bool, Vec<(String, String)>)>,
}

/// A connection to an LSP client.
pub struct LspServer {
    werr: bool,
    request_timeout: std::time::Duration,
    request_mem_limit: MemorySize,
    project_root: Option<VersionedTextDocumentIdentifier>,
    files: Arc<Mutex<Files>>,
    connection: Connection,
    #[allow(clippy::type_complexity)]
    file_statuses: HashMap<FileId, FileStatus>,
}

impl LspServer {
    const HEYVL_LANGUAGE_IDENTIFIER: &'static str = "heyvl";

    /// Create a new client connection on stdin and stdout.
    pub fn connect_stdio(options: &VerifyCommand) -> (LspServer, IoThreads) {
        let (connection, io_threads) = Connection::stdio();
        let connection = LspServer {
            werr: options.input_options.werr,
            request_timeout: options.rlimit_options.timeout(),
            request_mem_limit: options.rlimit_options.mem_limit(),
            project_root: None,
            files: Default::default(),
            connection,
            file_statuses: Default::default(),
        };
        (connection, io_threads)
    }

    pub fn initialize(&mut self) -> Result<(), ServerError> {
        let server_capabilities = ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
            ..ServerCapabilities::default()
        };

        let (id, params) = self.connection.initialize_start()?;
        let init_params: InitializeParams = serde_json::from_value(params)?;
        if let Some(Value::Object(obj)) = init_params.initialization_options {
            if let Some(Value::String(version)) = obj.get("vscodeExtensionVersion") {
                tracing::info!("initializing with VSCode extension {}", version)
            }
        }
        let initialize_data = serde_json::json!({
            "capabilities": server_capabilities,
            "caesarVersion": caesar_semver_version(),
        });
        self.connection.initialize_finish(id, initialize_data)?;

        // TODO: just use the initialization result in the client
        let start_notification = lsp_server::Notification::new(
            "custom/caesarReady".to_string(),
            json!({
                "version": caesar_semver_version(),
            }),
        );
        self.connection
            .sender
            .send(Message::Notification(start_notification))?;

        Ok(())
    }

    fn handle_notification(
        &mut self,
        notification: lsp_server::Notification,
    ) -> Result<Option<lsp_server::Notification>, ServerError> {
        match notification.method.as_str() {
            "textDocument/didOpen" => {
                let params: DidOpenTextDocumentParams =
                    notification.extract("textDocument/didOpen")?;
                self.update_text_document(params.text_document);
                Ok(None)
            }
            "textDocument/didChange" => {
                let params: DidChangeTextDocumentParams =
                    notification.extract("textDocument/didChange")?;
                assert_eq!(params.content_changes.len(), 1);
                let latest = params.content_changes.into_iter().next_back().unwrap();
                let text_document = TextDocumentItem {
                    uri: params.text_document.uri,
                    language_id: Self::HEYVL_LANGUAGE_IDENTIFIER.to_owned(),
                    version: params.text_document.version,
                    text: latest.text,
                };
                self.update_text_document(text_document);
                Ok(None)
            }
            "textDocument/didClose" => {
                let params: DidCloseTextDocumentParams =
                    notification.extract("textDocument/didClose")?;

                let file_id = self
                    .files
                    .lock()
                    .unwrap()
                    .find_uri(params.text_document.clone())
                    .unwrap_or_else(|| {
                        panic!(
                            "Could not find file id for document {:?}",
                            params.text_document
                        )
                    })
                    .id;
                self.clear_reported_file_state(file_id)?;
                Ok(None)
            }
            _ => Ok(Some(notification)),
        }
    }

    fn update_text_document(&mut self, document: TextDocumentItem) {
        if document.language_id != Self::HEYVL_LANGUAGE_IDENTIFIER {
            return;
        }
        let document_id = VersionedTextDocumentIdentifier {
            uri: document.uri,
            version: document.version,
        };
        self.files
            .lock()
            .unwrap()
            .add_or_update_uri(document_id, document.text);
    }

    fn publish_diagnostics(&mut self) -> Result<(), ServerError> {
        let files = self.files.lock().unwrap();
        let diags_by_document = self.file_statuses.iter().flat_map(|(file_id, status)| {
            let diags = &status.diagnostics;
            let document_id = files.get(*file_id).unwrap().path.to_lsp_identifier()?;
            Some((document_id, diags))
        });
        for (document_id, diagnostics) in diags_by_document {
            let diagnostics = diagnostics
                .iter()
                .map(|diag| diag.as_lsp_diagnostic(&files).unwrap().1)
                .collect();
            let params = lsp_types::PublishDiagnosticsParams {
                uri: document_id.uri,
                diagnostics,
                version: Some(document_id.version),
            };
            let notification = lsp_server::Notification::new(
                "textDocument/publishDiagnostics".to_string(),
                params,
            );
            self.connection
                .sender
                .send(lsp_server::Message::Notification(notification))?;
        }
        Ok(())
    }

    fn publish_explanations(&mut self) -> Result<(), ServerError> {
        let files = self.files.lock().unwrap();
        let by_document = self.file_statuses.iter().flat_map(|(file_id, status)| {
            let explanations = &status.vc_explanations;
            let document_id = files.get(*file_id).unwrap().path.to_lsp_identifier()?;
            Some((document_id, explanations))
        });
        for (document_id, explanations) in by_document {
            let explanations = explanations
                .iter()
                .flat_map(|(span, is_block_itself, expls)| {
                    Some((span.to_lsp(&files)?.1, *is_block_itself, expls.clone()))
                })
                .collect();
            let params = ComputedPreUpdate {
                document: document_id,
                pres: explanations,
            };
            let notification =
                lsp_server::Notification::new("custom/computedPre".to_string(), params);
            self.connection
                .sender
                .send(lsp_server::Message::Notification(notification))?;
        }
        Ok(())
    }

    fn publish_document_statuses(&self) -> Result<(), ServerError> {
        let files = self.files.lock().unwrap();

        let statuses_by_document = self
            .file_statuses
            .iter()
            .flat_map(|(file_id, file_status)| {
                let document_id = files.get(*file_id).unwrap().path.to_lsp_identifier()?;
                Some((
                    document_id,
                    file_status.status_type,
                    file_status
                        .verify_statuses
                        .iter_spans()
                        .flat_map(|(span, status)| {
                            let (_, range) = span.to_lsp(&files)?;
                            Some((range, status))
                        })
                        .collect_vec(),
                ))
            });

        for (document_id, file_status_type, verify_statuses) in statuses_by_document {
            let status_counts = verify_statuses
                .iter()
                .counts_by(|(_, status)| *status)
                .iter()
                .map(|(status, count)| (*status, *count))
                .collect_vec();

            let params = DocumentVerifyStatusUpdate {
                document: document_id,
                status_type: file_status_type,

                verify_statuses,
                status_counts,
            };
            let notification =
                lsp_server::Notification::new("custom/documentStatus".to_string(), params);
            self.connection
                .sender
                .send(lsp_server::Message::Notification(notification))?;
        }
        Ok(())
    }

    /// Convert `VerifyResult::Todo` and `VerifyResult::Verifying` statuses to `VerifyResult::Timeout`, send the results to the client and emit diagnostics for them.
    fn handle_timeout_for_results(&mut self) -> Result<(), ServerError> {
        let mut diagnostics: Vec<Diagnostic> = Vec::new();

        // Transform results and collect diagnostics for timed out procedures
        for (name, status) in self
            .file_statuses
            .iter_mut()
            .flat_map(|(_, status)| status.verify_statuses.timeout_all())
        {
            match status {
                VerifyStatus::Ongoing => {
                    diagnostics.push(
                        Diagnostic::new(ReportKind::Error, name.span())
                            .with_message("Timed out while verifying this procedure"),
                    );
                }
                VerifyStatus::Todo => {
                    diagnostics.push(
                        Diagnostic::new(ReportKind::Warning, name.span())
                            .with_message("Skipped this procedure due to timeout"),
                    );
                }
                _ => unreachable!(),
            }
        }

        // Add the collected diagnostics to the server
        for diagnostic in diagnostics {
            self.add_diagnostic(diagnostic)?;
        }

        self.publish_document_statuses()?;
        Ok(())
    }

    fn clear_reported_file_state(&mut self, file_id: FileId) -> Result<(), ServerError> {
        self.file_statuses
            .entry(file_id)
            .and_modify(|status| status.clear());

        self.publish_diagnostics()?;
        self.publish_document_statuses()?;
        Ok(())
    }

    fn lsp_file_id(&self, document: VersionedTextDocumentIdentifier) -> FileId {
        let path = SourceFilePath::Lsp(document);
        self.files
            .lock()
            .unwrap()
            .find(&path)
            .unwrap_or_else(|| panic!("Could not find file id for document {:?}", path))
            .id
    }

    fn reset_verify_state_for_document(
        &mut self,
        document: VersionedTextDocumentIdentifier,
    ) -> Result<FileId, ServerError> {
        self.project_root = Some(document.clone());
        let file_id = self.lsp_file_id(document);
        self.clear_reported_file_state(file_id)?;
        Ok(file_id)
    }

    fn handle_verify_result(
        &mut self,
        id: RequestId,
        file_id: FileId,
        result: Result<(), CaesarError>,
    ) -> Result<Response, CaesarError> {
        // Convert verifier results into LSP-visible state.
        match result {
            Ok(()) => Ok(Response::new_ok(id, Value::Null)),
            Err(CaesarError::LimitError(LimitError::Interrupted)) => Ok(Response::new_err(
                id,
                ErrorCode::RequestCanceled as i32,
                "verification canceled".to_owned(),
            )),
            Err(CaesarError::Diagnostic(diagnostic)) => {
                self.add_diagnostic(diagnostic)?;
                self.set_file_status_type(&file_id, FileStatusType::Invalid)?;
                Ok(Response::new_ok(id, Value::Null))
            }
            Err(CaesarError::LimitError(LimitError::Timeout | LimitError::Oom)) => {
                self.handle_timeout_for_results()
                    .map_err(CaesarError::ServerError)?;
                self.set_file_status_type(&file_id, FileStatusType::Timeout)?;
                Ok(Response::new_ok(id, Value::Null))
            }
            Err(err) => Ok(Response::new_err(id, 0, format!("{err}"))),
        }
    }

    fn make_limits_ref(&self) -> LimitsRef {
        LimitsRef::new(
            Some(Instant::now() + self.request_timeout),
            Some(self.request_mem_limit),
        )
    }
}

impl Server for LspServer {
    fn get_file(&self, file_id: FileId) -> Option<Arc<StoredFile>> {
        self.files.lock().unwrap().get(file_id).cloned()
    }

    fn get_files_internal(&mut self) -> &Mutex<Files> {
        &self.files
    }

    fn add_diagnostic(&mut self, diagnostic: Diagnostic) -> Result<(), CaesarError> {
        self.file_statuses
            .entry(diagnostic.span().file)
            .or_default()
            .diagnostics
            .push(diagnostic);

        self.publish_diagnostics()
            .map_err(CaesarError::ServerError)?;
        Ok(())
    }

    fn add_or_throw_diagnostic(&mut self, diagnostic: Diagnostic) -> Result<(), CaesarError> {
        let diagnostic = unless_fatal_error(self.werr, diagnostic)?;
        self.add_diagnostic(diagnostic)
    }

    fn add_vc_explanation(&mut self, explanation: VcExplanation) -> Result<(), CaesarError> {
        let files = self.files.lock().unwrap();
        for mut explanation in explanation.into_iter() {
            explanation.shrink_to_block(&files);

            self.file_statuses
                .entry(explanation.span.file)
                .or_default()
                .vc_explanations
                .push((
                    explanation.span,
                    explanation.is_block_itself,
                    explanation.to_strings().collect(),
                ));
        }
        drop(files);
        self.publish_explanations()
            .map_err(CaesarError::ServerError)?;
        Ok(())
    }

    fn register_source_unit(
        &mut self,
        source_unit: &mut Item<SourceUnit>,
    ) -> Result<(), CaesarError> {
        let name = source_unit.name().clone();
        let statuses = &mut self
            .file_statuses
            .entry(name.span().file)
            .or_default()
            .verify_statuses;

        // only register source units that are procedures
        if let SourceUnit::Decl(DeclKind::ProcDecl(decl)) = source_unit.enter_mut().deref() {
            // ... and they must have a body, otherwise they trivially verify
            if decl.borrow().body.borrow().is_some() {
                statuses.update_status(&name, VerifyStatus::Todo);
                self.publish_document_statuses()
                    .map_err(CaesarError::ServerError)?;
            }
        }
        Ok(())
    }

    fn set_ongoing_unit(&mut self, name: &SourceUnitName) -> Result<(), CaesarError> {
        let statuses = &mut self
            .file_statuses
            .entry(name.span().file)
            .or_default()
            .verify_statuses;

        statuses.update_status(name, VerifyStatus::Ongoing);
        self.set_file_status_type(&name.span().file, FileStatusType::Ongoing)?;

        self.publish_document_statuses()
            .map_err(CaesarError::ServerError)?;
        Ok(())
    }

    fn set_file_status_type(
        &mut self,
        file_id: &FileId,
        status_type: FileStatusType,
    ) -> Result<(), CaesarError> {
        let doc_status = self.file_statuses.entry(*file_id).or_default();
        doc_status.status_type = status_type;
        self.publish_document_statuses()
            .map_err(CaesarError::ServerError)?;
        Ok(())
    }

    fn handle_vc_check_result<'smt, 'ctx>(
        &mut self,
        name: &SourceUnitName,
        result: &mut SmtVcProveResult<'ctx>,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        proc_soundness: &ProcSoundness,
    ) -> Result<(), ServerError> {
        result.emit_diagnostics(name.span(), self, translate, proc_soundness)?;
        let statuses = &mut self
            .file_statuses
            .entry(name.span().file)
            .or_default()
            .verify_statuses;

        statuses.update_status(
            name,
            VerifyStatus::from_prove_result(&result.prove_result, proc_soundness),
        );

        // If every procedure in the file has been verified, we can set the file status type to Done.
        if statuses
            .results
            .iter()
            .all(|(_, status)| !matches!(status, VerifyStatus::Todo | VerifyStatus::Ongoing))
        {
            if let Some(status) = self.file_statuses.get_mut(&name.span().file) {
                status.status_type = FileStatusType::Done;
            }
        }

        self.publish_document_statuses()?;
        Ok(())
    }
}

struct RunningQueue {
    active_request: Option<(LimitsRef, tokio::task::JoinHandle<Result<(), CaesarError>>)>,
    queued: Vec<lsp_server::Notification>,
}

impl RunningQueue {
    fn is_finished(&self) -> bool {
        self.active_request
            .as_ref()
            .is_some_and(|(_, task)| task.is_finished())
    }

    /// Process the active request, if any, and then handle the queued
    /// notifications. If `cancel` is true, the active request will be cancelled
    /// if it is still running.
    async fn process(
        &mut self,
        server: &Arc<Mutex<LspServer>>,
        cancel: bool,
    ) -> Result<(), CaesarError> {
        if let Some((limits_ref, task)) = self.active_request.take() {
            if cancel && !task.is_finished() {
                limits_ref.cancel();
            }

            match task.await? {
                Ok(()) => {}
                Err(CaesarError::LimitError(LimitError::Interrupted)) if cancel => {}
                Err(err) => return Err(err),
            }
        }
        for notification in mem::take(&mut self.queued) {
            server
                .lock()
                .unwrap()
                .handle_notification(notification)
                .map_err(CaesarError::ServerError)?;
        }
        Ok(())
    }
}

async fn run_verify_request(
    server: Arc<Mutex<LspServer>>,
    options: Arc<VerifyCommand>,
    req: Request,
    limits_ref: LimitsRef,
) -> Result<(), CaesarError> {
    let (id, params) = VerifyRequest::extract(req)?;
    let file_id = server
        .lock()
        .unwrap()
        .reset_verify_state_for_document(params.text_document)
        .map_err(CaesarError::ServerError)?;

    let shared_server: SharedServer = server.clone();
    let result = verify_files_with_limits(&options, &shared_server, vec![file_id], limits_ref)
        .await
        .map(|_| ());
    let response = server
        .lock()
        .unwrap()
        .handle_verify_result(id, file_id, result)?;

    server
        .lock()
        .unwrap()
        .connection
        .sender
        .send(Message::Response(response))
        .map_err(|e| CaesarError::ServerError(e.into()))
}

/// Run the LSP server.
pub async fn run_lsp_server(
    server: Arc<Mutex<LspServer>>,
    options: Arc<VerifyCommand>,
) -> Result<(), CaesarError> {
    let receiver = {
        let server = server.lock().unwrap();
        server.connection.receiver.clone()
    };
    let mut verify_queue = RunningQueue {
        active_request: None,
        queued: Vec::new(),
    };

    while let Ok(msg) = receiver.recv() {
        if verify_queue.is_finished() {
            verify_queue.process(&server, false).await?;
        }

        match msg {
            Message::Request(req) => match req.method.as_str() {
                "custom/verify" => {
                    verify_queue.process(&server, true).await?;
                    let limits_ref = server.lock().unwrap().make_limits_ref();
                    let task = tokio::spawn(run_verify_request(
                        server.clone(),
                        options.clone(),
                        req,
                        limits_ref.clone(),
                    ));
                    verify_queue.active_request = Some((limits_ref, task));
                }
                "shutdown" => {
                    verify_queue.process(&server, true).await?;
                    server
                        .lock()
                        .unwrap()
                        .connection
                        .sender
                        .send(Message::Response(Response::new_ok(
                            req.id.clone(),
                            Value::Null,
                        )))
                        .map_err(|e| CaesarError::ServerError(e.into()))?;
                }
                _ => {}
            },
            Message::Response(_) => todo!(),
            Message::Notification(notification) => {
                if verify_queue.active_request.is_some() {
                    // Apply edits after the running verify finishes.
                    verify_queue.queued.push(notification);
                } else {
                    server
                        .lock()
                        .unwrap()
                        .handle_notification(notification)
                        .map_err(CaesarError::ServerError)?;
                }
            }
        }
    }

    verify_queue.process(&server, true).await
}
