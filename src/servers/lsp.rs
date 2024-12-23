use std::{
    collections::HashMap,
    future::Future,
    pin::Pin,
    sync::{Arc, Mutex},
};

use crossbeam_channel::Sender;

use lsp_server::{Connection, IoThreads, Message, Request, Response};
use lsp_types::{
    DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    InitializeParams, ServerCapabilities, TextDocumentItem, TextDocumentSyncCapability,
    TextDocumentSyncKind, VersionedTextDocumentIdentifier,
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

use crate::{
    ast::{Diagnostic, FileId, Files, SourceFilePath, Span, StoredFile},
    driver::{SmtVcCheckResult, SourceUnitName},
    smt::translate_exprs::TranslateExprs,
    vc::explain::VcExplanation,
    version::caesar_semver_version,
    Options, VerifyError,
};

use super::{unless_fatal_error, Server, ServerError, VerifyResult};

#[derive(Debug, Serialize, Deserialize)]
struct VerifyRequest {
    text_document: VersionedTextDocumentIdentifier,
}

#[derive(Debug, Serialize, Deserialize)]
struct VerifyStatusUpdate {
    document: VersionedTextDocumentIdentifier,
    statuses: Vec<(lsp_types::Range, VerifyResult)>,
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
    diagnostics: HashMap<FileId, Vec<Diagnostic>>,
    #[allow(clippy::type_complexity)]
    vc_explanations: HashMap<FileId, Vec<(Span, bool, Vec<(String, String)>)>>,
    statuses: HashMap<Span, VerifyResult>,
}

impl LspServer {
    const HEYVL_LANGUAGE_IDENTIFIER: &'static str = "heyvl";

    /// Create a new client connection on stdin and stdout.
    pub fn connect_stdio(options: &Options) -> (LspServer, IoThreads) {
        let (connection, io_threads) = Connection::stdio();
        let connection = LspServer {
            werr: options.werr,
            project_root: None,
            files: Default::default(),
            connection,
            diagnostics: Default::default(),
            vc_explanations: Default::default(),
            statuses: Default::default(),
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
                let latest = params.content_changes.into_iter().last().unwrap();
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
        let diags_by_document = self.diagnostics.iter().flat_map(|(file_id, diags)| {
            let document_id = files.get(*file_id).unwrap().path.to_lsp_identifier()?;
            Some((document_id, diags))
        });
        for (document_id, diagnostics) in diags_by_document {
            let diagnostics = diagnostics
                .iter()
                .map(|diag| diag.into_lsp_diagnostic(&files).unwrap().1)
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
        let by_document = self
            .vc_explanations
            .iter()
            .flat_map(|(file_id, explanations)| {
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

    fn publish_verify_statuses(&self) -> Result<(), ServerError> {
        let files = self.files.lock().unwrap();
        let statuses_by_document = by_lsp_document(
            &files,
            self.statuses.iter().flat_map(|(span, status)| {
                let (_, range) = span.to_lsp(&files)?;
                Some((span.file, (range, *status)))
            }),
        );
        for (document_id, statuses) in statuses_by_document {
            let params = VerifyStatusUpdate {
                document: document_id,
                statuses,
            };
            let notification =
                lsp_server::Notification::new("custom/verifyStatus".to_string(), params);
            self.connection
                .sender
                .send(lsp_server::Message::Notification(notification))?;
        }
        Ok(())
    }

    fn clear_file_information(&mut self, file_id: &FileId) -> Result<(), ServerError> {
        if let Some(diag) = self.diagnostics.get_mut(file_id) {
            diag.clear();
        }
        if let Some(explanations) = self.vc_explanations.get_mut(file_id) {
            explanations.clear();
        }
        self.statuses.retain(|span, _| span.file != *file_id);
        self.publish_diagnostics()?;
        self.publish_verify_statuses()?;
        Ok(())
    }
}

impl Server for LspServer {
    fn send_server_ready(&self) -> Result<(), ServerError> {
        let start_notification =
            lsp_server::Notification::new("custom/serverReady".to_string(), ());
        self.connection
            .sender
            .send(Message::Notification(start_notification))?;
        Ok(())
    }

    fn get_file(&self, file_id: FileId) -> Option<Arc<StoredFile>> {
        self.files.lock().unwrap().get(file_id).cloned()
    }

    fn get_files_internal(&mut self) -> &Mutex<Files> {
        &self.files
    }

    fn add_diagnostic(&mut self, diagnostic: Diagnostic) -> Result<(), VerifyError> {
        self.diagnostics
            .entry(diagnostic.span().file)
            .or_default()
            .push(diagnostic);
        self.publish_diagnostics()
            .map_err(VerifyError::ServerError)?;
        Ok(())
    }

    fn add_or_throw_diagnostic(&mut self, diagnostic: Diagnostic) -> Result<(), VerifyError> {
        let diagnostic = unless_fatal_error(self.werr, diagnostic)?;
        self.add_diagnostic(diagnostic)
    }

    fn add_vc_explanation(&mut self, explanation: VcExplanation) -> Result<(), VerifyError> {
        let files = self.files.lock().unwrap();
        for mut explanation in explanation.into_iter() {
            explanation.shrink_to_block(&files);
            self.vc_explanations
                .entry(explanation.span.file)
                .or_default()
                .push((
                    explanation.span,
                    explanation.is_block_itself,
                    explanation.to_strings().collect(),
                ));
        }
        drop(files);
        self.publish_explanations()
            .map_err(VerifyError::ServerError)?;
        Ok(())
    }

    fn handle_vc_check_result<'smt, 'ctx>(
        &mut self,
        _name: &SourceUnitName,
        span: Span,
        result: &mut SmtVcCheckResult<'ctx>,
        translate: &mut TranslateExprs<'smt, 'ctx>,
    ) -> Result<(), ServerError> {
        result.emit_diagnostics(span, self, translate)?;
        self.statuses
            .insert(span, VerifyResult::from_prove_result(&result.prove_result));
        self.publish_verify_statuses()?;
        Ok(())
    }

    fn handle_not_checked(&mut self, span: Span) -> Result<(), ServerError> {
        self.statuses.insert(span, VerifyResult::Unknown);
        self.publish_verify_statuses()?;
        Ok(())
    }
}

/// A type alias representing an asynchronous closure that returns a `Result<(), VerifyError>`.
///
/// Since async closures are currently unstable in Rust, this type simulates them by using
/// a pinned boxed future that captures the closure and its lifetime.
type VerifyFuture<'a> = Pin<Box<dyn Future<Output = Result<(), VerifyError>> + 'a>>;

/// Run the LSP server with the given verify function which is an async closure that returns a verification result modeled by a `Result<(), VerifyError>` type.
pub async fn run_lsp_server(
    server: Arc<Mutex<LspServer>>,
    mut verify: impl FnMut(&[FileId]) -> VerifyFuture,
) -> Result<(), VerifyError> {
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
                        .map_err(|e| VerifyError::ServerError(e.into()))?;
                }
                _ => {}
            },
            Message::Response(_) => todo!(),
            Message::Notification(notification) => {
                server
                    .lock()
                    .unwrap()
                    .handle_notification(notification)
                    .map_err(VerifyError::ServerError)?;
            }
        }
    }
    Ok(())
}

fn by_lsp_document<'a, T: 'a>(
    files: &'a Files,
    iter: impl IntoIterator<Item = (FileId, T)>,
) -> impl Iterator<Item = (VersionedTextDocumentIdentifier, Vec<T>)> + 'a {
    let mut by_file: HashMap<FileId, Vec<T>> = HashMap::new();
    for (file_id, val) in iter.into_iter() {
        by_file.entry(file_id).or_default().push(val);
    }
    by_file.into_iter().flat_map(move |(file_id, vals)| {
        let document_id = files.get(file_id).unwrap().path.to_lsp_identifier()?;
        Some((document_id, vals))
    })
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
) -> Result<(), VerifyError> {
    let (id, params) = req
        .extract::<VerifyRequest>("custom/verify")
        .map_err(|e| VerifyError::ServerError(e.into()))?;
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
            .map_err(VerifyError::ServerError)?;
        file_id
    };

    let result = verify(&[file_id]).await;
    let res = match &result {
        Ok(_) => Response::new_ok(id, Value::Null),
        Err(err) => Response::new_err(id, 0, format!("{}", err)),
    };
    sender
        .send(Message::Response(res))
        .map_err(|e| VerifyError::ServerError(e.into()))?;
    match result {
        Ok(()) => {}
        Err(VerifyError::Diagnostic(diagnostic)) => {
            server.lock().unwrap().add_diagnostic(diagnostic)?;
        }
        Err(VerifyError::Interrupted) => {}
        Err(VerifyError::LimitError(_)) => {}
        Err(err) => Err(err)?,
    }
    Ok(())
}
