use lsp_server::{Connection, Message, Request, RequestId, Response};
use lsp_types::{
    lsp_notification, Diagnostic, DiagnosticSeverity, DidSaveTextDocumentParams, TextDocumentItem,
    Url,
};
use lsp_types::{
    notification::Notification, DidChangeTextDocumentParams, DidChangeWorkspaceFoldersParams,
    DidCloseTextDocumentParams, DidOpenTextDocumentParams, ServerCapabilities,
    TextDocumentSyncCapability, TextDocumentSyncKind, WorkspaceFolder,
};
use serde_json::json;
use std::error::Error;
use std::io::{self, BufRead, BufReader, Write};
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::sync::Mutex;

use crate::procs::verify_proc;
use crate::{get_verify_units_from_files, VerifyError};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct VerificationStatusParams {
    text_document: TextDocumentItem,
}

impl lsp_types::request::Request for VerificationStatusParams {
    type Params = VerificationStatusParams;
    type Result = bool;
    const METHOD: &'static str = "custom/verifyStatus";
}

fn main() -> Result<(), Box<dyn Error + Send + Sync>> {
    let (connection, io_threads) = Connection::stdio();
    let server_capabilities = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::NONE)),
        ..ServerCapabilities::default()
    };

    connection.initialize(serde_json::json!(server_capabilities))?;

    let mut documents = Arc::new(Mutex::new(Vec::new()));
    let mut workspace_folders = Arc::new(Mutex::new(Vec::new()));
    // let mut verify_units = Vec::new();

    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                handle_request(req, &connection, &mut documents, &mut workspace_folders)?;
            }
            Message::Notification(not) => {
                handle_notification(not, &connection, &mut documents, &mut workspace_folders)?;
            }
            _ => (),
        }
    }

    Ok(())
}

fn handle_request(
    req: Request,
    connection: &Connection,
    documents: &mut Arc<Mutex<Vec<(String, String)>>>,
    workspace_folders: &mut Arc<Mutex<Vec<WorkspaceFolder>>>,
) -> Result<(), Box<dyn Error + Send + Sync>> {
    match req.method.as_str() {
        // "custom/procStatus" => {
        //     let params = serde_json::from_value(req.params)?;
        //     let text = params.text_document.text;
        // }
        _ => {
            let response = Response::new_err(
                req.id,
                lsp_server::ErrorCode::MethodNotFound as i32,
                "Method not found".to_string(),
            );
            connection.sender.send(Message::Response(response))?;
        }
    }
    Ok(())
}

fn handle_notification(
    not: lsp_server::Notification,
    connection: &Connection,
    documents: &mut Arc<Mutex<Vec<(String, String)>>>,
    workspace_folders: &mut Arc<Mutex<Vec<WorkspaceFolder>>>,
) -> Result<(), Box<dyn Error + Send + Sync>> {
    match not.method.as_str() {
        "textDocument/didOpen" => {
            // let params: DidOpenTextDocumentParams = serde_json::from_value(not.params.clone())?;
            // let uri = params.text_document.uri;
            // let text = params.text_document.text;
            // documents.lock().unwrap().push((uri.to_string(), text));

            // let handle_error = |result: Result<_, VerifyError>| match result {
            //     Ok(value) => Ok(value),
            //     Err(e) => {
            //         // Handle VerifyError
            //         // ...
            //         Err(e)
            //     }
            // };

            // let (mut verify_units, mut tcx) =
            //     get_verify_units_from_files(options, files_mutex, user_files);

            // let mut all_proven: bool = true;
            // for verify_unit in &mut verify_units {
            //     let (name, mut verify_unit) = verify_unit.enter_with_name();

            //     let result = verify_unit.verify(name, &mut tcx, options)?;

            //     all_proven = all_proven && result;
            // }

            // match get_verify_units_from_files(options, files_mutex, user_files) {
            //     Ok((verify_units, tcx)) => {}
            //     Err(e) => match e {
            //         VerifyError::Diagnostic(diagnostic) => {}
            //         VerifyError::IoError(err) => {}
            //         VerifyError::LimitError(_) => {}
            //         VerifyError::Panic(_) => {}
            //     },
            // }
        }
        "textDocument/didSave" => {
            let params: DidSaveTextDocumentParams = serde_json::from_value(not.params.clone())?;
            let uri = params.text_document.uri;
            let text = params.text.unwrap();
            documents.lock().unwrap().push((uri.to_string(), text));
        }
        "textDocument/didChange" => {
            let params: DidChangeTextDocumentParams = serde_json::from_value(not.params.clone())?;
            let uri = params.text_document.uri;
            let content_changes = params.content_changes;
            let mut documents = documents.lock().unwrap();
        }
        "textDocument/didClose" => {
            let params: DidCloseTextDocumentParams = serde_json::from_value(not.params.clone())?;
            let uri = params.text_document.uri;
            documents
                .lock()
                .unwrap()
                .retain(|(doc_uri, _)| !matches!(doc_uri.clone(), uri));
        }
        "workspace/didChangeWorkspaceFolders" => {
            let params: DidChangeWorkspaceFoldersParams =
                serde_json::from_value(not.params.clone())?;
            let event = params.event;
            let mut workspace_folders = workspace_folders.lock().unwrap();
            workspace_folders.extend(event.added.clone());
            workspace_folders.retain(|folder| !event.removed.contains(folder));
        }
        _ => (),
    }
    Ok(())
}

fn verify_and_store() {}
