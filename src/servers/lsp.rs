use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
};

use lsp_server::{Connection, IoThreads, Message, Response};
use lsp_types::{
    DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    InitializeParams, ServerCapabilities, TextDocumentItem, TextDocumentSyncCapability,
    TextDocumentSyncKind, VersionedTextDocumentIdentifier,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{
    ast::{Diagnostic, FileId, Files, SourceFilePath, Span, StoredFile},
    VerifyError,
};

use super::{Server, ServerError};

#[derive(Debug, Serialize, Deserialize)]
struct VerifyStatusRequest {
    text_document: VersionedTextDocumentIdentifier,
}

#[derive(Debug, Serialize, Deserialize)]
struct VerifyStatusUpdate {
    document: VersionedTextDocumentIdentifier,
    statuses: Vec<(lsp_types::Range, bool)>,
}

/// A connection to an LSP client.
pub struct LspServer {
    project_root: Option<VersionedTextDocumentIdentifier>,
    files: Arc<Mutex<Files>>,
    connection: Connection,
    diagnostics: Vec<Diagnostic>,
    statuses: HashMap<Span, bool>,
}

impl LspServer {
    const HEYVL_LANGUAGE_IDENTIFIER: &'static str = "heyvl";

    /// Create a new client connection on stdin and stdout.
    pub fn connect_stdio() -> (LspServer, IoThreads) {
        let (connection, io_threads) = Connection::stdio();
        let connection = LspServer {
            project_root: None,
            files: Default::default(),
            connection,
            diagnostics: Default::default(),
            statuses: Default::default(),
        };
        (connection, io_threads)
    }

    pub fn initialize(&mut self) -> Result<(), ServerError> {
        let server_capabilities = ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
            ..ServerCapabilities::default()
        };
        let res = self
            .connection
            .initialize(serde_json::json!(server_capabilities))?;
        let _init_params: InitializeParams = serde_json::from_value(res)?;

        // TODO: just use the initialization result in the client
        let start_notification =
            lsp_server::Notification::new("custom/serverReady".to_string(), ());
        self.connection
            .sender
            .send(Message::Notification(start_notification))?;

        Ok(())
    }

    pub fn run_server(
        &mut self,
        mut verify: impl FnMut(&mut Self, &[FileId]) -> Result<(), VerifyError>,
    ) -> Result<(), VerifyError> {
        let sender = self.connection.sender.clone();
        let receiver = self.connection.receiver.clone();
        for msg in &receiver {
            match msg {
                Message::Request(req) => {
                    if let "custom/verifyStatus" = req.method.as_str() {
                        let (id, params) = req
                            .extract::<VerifyStatusRequest>("custom/verifyStatus")
                            .map_err(|e| VerifyError::ServerError(e.into()))?;
                        self.project_root = Some(params.text_document.clone());
                        let files = self.files.lock().unwrap();
                        let file_id = files
                            .find(&SourceFilePath::Lsp(params.text_document.clone()))
                            .unwrap()
                            .id;
                        drop(files);
                        self.clear_all();
                        let result = verify(self, &[file_id]);
                        let res = match &result {
                            Ok(_) => Response::new_ok(id, Value::Null),
                            Err(err) => Response::new_err(id, 0, format!("{}", err)),
                        };
                        sender
                            .send(Message::Response(res))
                            .map_err(|e| VerifyError::ServerError(e.into()))?;
                        result?;
                    }
                }
                Message::Response(_) => todo!(),
                Message::Notification(notification) => {
                    self.handle_notification(notification)
                        .map_err(VerifyError::ServerError)?;
                }
            }
        }
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
                let _params: DidCloseTextDocumentParams =
                    notification.extract("textDocument/didClose")?;
                // TODO: remove file?
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
        self.clear_all();
    }

    fn publish_diagnostics(&mut self) -> Result<(), ServerError> {
        let files = self.files.lock().unwrap();
        let diags_by_document = by_lsp_document(
            &files,
            self.diagnostics
                .iter()
                .map(|diagnostic| (diagnostic.span().file, diagnostic)),
        );
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
            dbg!(&notification);
            self.connection
                .sender
                .send(lsp_server::Message::Notification(notification))?;
        }
        Ok(())
    }

    fn clear_all(&mut self) {
        self.diagnostics.clear();
        self.statuses.clear();
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
        // TODO: add --werr support
        self.diagnostics.push(diagnostic);
        self.publish_diagnostics()
            .map_err(VerifyError::ServerError)?;
        Ok(())
    }

    fn set_verify_status(&mut self, span: Span, status: bool) -> Result<(), ServerError> {
        self.statuses.insert(span, status);
        self.publish_verify_statuses()?;
        Ok(())
    }
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
