use std::{
    collections::HashMap,
    future::Future,
    ops::Deref,
    pin::Pin,
    sync::{Arc, Mutex},
};

use ariadne::ReportKind;
use crossbeam_channel::Sender;

use itertools::Itertools;
use lsp_server::{Connection, IoThreads, Message, Request, Response};
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
        commands::verify::VerifyCommand,
        error::CaesarError,
        front::SourceUnit,
        item::{Item, SourceUnitName},
        smt_proof::SmtVcProveResult,
    },
    servers::{FileStatus, FileStatusType},
    smt::translate_exprs::TranslateExprs,
    vc::explain::VcExplanation,
    version::caesar_semver_version,
};

use super::{unless_fatal_error, Server, ServerError, VerifyStatus};

#[derive(Debug, Serialize, Deserialize)]
struct VerifyRequest {
    text_document: VersionedTextDocumentIdentifier,
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
                self.clear_file_information(&file_id)?;
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

    fn clear_file_information(&mut self, file_id: &FileId) -> Result<(), ServerError> {
        self.file_statuses
            .entry(*file_id)
            .and_modify(|status| status.clear());

        self.publish_diagnostics()?;
        self.publish_document_statuses()?;
        Ok(())
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
        _is_get_model_task: bool,
    ) -> Result<(), ServerError> {
        result.emit_diagnostics(name.span(), self, translate)?;
        let statuses = &mut self
            .file_statuses
            .entry(name.span().file)
            .or_default()
            .verify_statuses;

        statuses.update_status(name, VerifyStatus::from_prove_result(&result.prove_result));

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

/// A type alias representing an asynchronous closure that returns a `Result<(), CaesarError>`.
///
/// Since async closures are currently unstable in Rust, this type simulates them by using
/// a pinned boxed future that captures the closure and its lifetime.
type VerifyFuture<'a> = Pin<Box<dyn Future<Output = Result<(), CaesarError>> + 'a>>;

/// Run the LSP server with the given verify function which is an async closure that returns a verification result modeled by a `Result<(), CaesarError>` type.
pub async fn run_lsp_server(
    server: Arc<Mutex<LspServer>>,
    mut verify: impl FnMut(&[FileId]) -> VerifyFuture,
) -> Result<(), CaesarError> {
    let (sender, receiver) = {
        let server_guard = server.lock().unwrap();
        let sender = server_guard.connection.sender.clone();
        let receiver = server_guard.connection.receiver.clone();
        (sender, receiver)
    };
    for msg in &receiver {
        match msg {
            Message::Request(req) => match req.method.as_str() {
                "custom/verify" => {
                    handle_verify_request(req, server.clone(), sender.clone(), &mut verify).await?;
                }
                "shutdown" => {
                    sender
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
                server
                    .lock()
                    .unwrap()
                    .handle_notification(notification)
                    .map_err(CaesarError::ServerError)?;
            }
        }
    }
    Ok(())
}

/// Handles the verify request from the client by calling the given verify method and sends the result back.
///
/// The lock on the server must be carefully managed to avoid deadlocks, because the verify function also needs to lock the server.
/// Therefore the server is not locked for the entire duration of the function.
/// Takes a mutable reference to a verify function which is an async closure.
async fn handle_verify_request(
    req: Request,
    server: Arc<Mutex<LspServer>>,
    sender: Sender<Message>,
    verify: &mut impl FnMut(&[FileId]) -> VerifyFuture,
) -> Result<(), CaesarError> {
    let (id, params) = req
        .extract::<VerifyRequest>("custom/verify")
        .map_err(|e| CaesarError::ServerError(e.into()))?;
    let file_id = {
        let mut server_ref = server.lock().unwrap();
        server_ref.project_root = Some(params.text_document.clone());
        let files = server_ref.files.lock().unwrap();
        let file_id = files
            .find(&SourceFilePath::Lsp(params.text_document.clone()))
            .unwrap_or_else(|| {
                panic!(
                    "Could not find file id for document {:?}",
                    params.text_document
                )
            })
            .id;
        drop(files);

        server_ref
            .clear_file_information(&file_id)
            .map_err(CaesarError::ServerError)?;
        file_id
    };

    let result = verify(&[file_id]).await;

    let response = match result {
        Ok(()) => Response::new_ok(id.clone(), Value::Null),
        Err(err) => match err {
            CaesarError::Diagnostic(diagnostic) => {
                let mut server_lock = server.lock().unwrap();
                server_lock.add_diagnostic(diagnostic)?;
                // If the verification failed with a diagnostic, we can assume
                // that the file can not be (soundly) verified due to
                // syntax/type/soundness errors.
                server_lock.set_file_status_type(&file_id, FileStatusType::Invalid)?;
                drop(server_lock);
                Response::new_ok(id.clone(), Value::Null)
            }
            CaesarError::Interrupted | CaesarError::LimitError(_) => {
                let mut server_lock = server.lock().unwrap();

                server_lock
                    .handle_timeout_for_results()
                    .map_err(CaesarError::ServerError)?;

                server_lock.set_file_status_type(&file_id, FileStatusType::Timeout)?;
                drop(server_lock);
                Response::new_ok(id.clone(), Value::Null)
            }
            _ => Response::new_err(id, 0, format!("{err}")),
        },
    };

    sender
        .send(Message::Response(response))
        .map_err(|e| CaesarError::ServerError(e.into()))?;

    Ok(())
}
