use lsp_server::{Connection, Message, Request, Response};
use lsp_types::{
    DidChangeTextDocumentParams, DidChangeWorkspaceFoldersParams, DidCloseTextDocumentParams,
    DidOpenTextDocumentParams, ServerCapabilities, TextDocumentSyncCapability,
    TextDocumentSyncKind, WorkspaceFolder,
};
use lsp_types::{DidSaveTextDocumentParams, TextDocumentItem, Url};

use std::collections::HashMap;
use std::error::Error;

use std::sync::Arc;
use std::sync::Mutex;

use crate::ast::decl::DeclKind;
use crate::ast::{Files, Span};
use crate::driver::{SourceUnit, SourceUnitName};
use crate::{
    get_source_units_from_files, load_file, transform_source_to_verify, Options, VerifyError,
};
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

pub fn run_server(options: &Options) -> Result<(), Box<dyn Error + Send + Sync>> {
    let (connection, _) = Connection::stdio();
    let server_capabilities = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::NONE)),

        ..ServerCapabilities::default()
    };

    connection.initialize(serde_json::json!(server_capabilities))?;

    let mut documents = Arc::new(Mutex::new(Vec::new()));
    let mut workspace_folders = Arc::new(Mutex::new(Vec::new()));
    let mut proc_status_map: HashMap<Url, Vec<(lsp_types::Range, bool)>> = HashMap::new();

    let start_notification = lsp_server::Notification::new("custom/serverReady".to_string(), {});
    let _ = connection
        .sender
        .send(Message::Notification(start_notification));

    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                handle_request(
                    req,
                    &connection,
                    options,
                    &mut documents,
                    &mut workspace_folders,
                    &mut proc_status_map,
                )?;
            }
            Message::Notification(not) => {
                handle_notification(
                    not,
                    &connection,
                    options,
                    &mut documents,
                    &mut workspace_folders,
                    &mut proc_status_map,
                )?;
            }
            _ => (),
        }
    }

    Ok(())
}

fn handle_request(
    req: Request,
    connection: &Connection,
    options: &Options,
    _documents: &mut Arc<Mutex<Vec<(String, String)>>>,
    _workspace_folders: &mut Arc<Mutex<Vec<WorkspaceFolder>>>,
    _proc_status_map: &mut HashMap<Url, Vec<(lsp_types::Range, bool)>>,
) -> Result<(), Box<dyn Error + Send + Sync>> {
    let response: Response = match req.method.as_str() {
        "custom/verifyStatus" => {
            let params: VerificationStatusParams = serde_json::from_value(req.params)?;

            let uri = params.text_document.uri;

            // TODO: Implement proper caching later.
            let status_vec = match verify(options, uri.clone(), connection) {
                Ok(vec) => {
                    let _ = clear_diagnostics(connection, uri.clone());
                    vec
                }
                Err(_) => Vec::new(),
            };

            let proc_status_json = serde_json::to_value(status_vec)?;
            Response::new_ok(req.id, proc_status_json)
        }
        _ => Response::new_err(
            req.id,
            lsp_server::ErrorCode::MethodNotFound as i32,
            "Method not found".to_string(),
        ),
    };
    connection.sender.send(Message::Response(response))?;
    Ok(())
}

fn handle_notification(
    not: lsp_server::Notification,
    _connection: &Connection,
    _options: &Options,
    documents: &mut Arc<Mutex<Vec<(String, String)>>>,
    workspace_folders: &mut Arc<Mutex<Vec<WorkspaceFolder>>>,
    proc_status_map: &mut HashMap<Url, Vec<(lsp_types::Range, bool)>>,
) -> Result<(), Box<dyn Error + Send + Sync>> {
    match not.method.as_str() {
        "textDocument/didOpen" => {
            let params: DidOpenTextDocumentParams = serde_json::from_value(not.params.clone())?;
            let uri = params.text_document.uri;
            let text = params.text_document.text;
            documents.lock().unwrap().push((uri.to_string(), text));

            // verify_and_cache(options, uri, connection, proc_status_map);
        }
        "textDocument/didSave" => {
            let params: DidSaveTextDocumentParams = serde_json::from_value(not.params.clone())?;
            let uri = params.text_document.uri;
            let text = params.text.unwrap();
            documents.lock().unwrap().push((uri.to_string(), text));

            // verify_and_cache(uri, connection, proc_status_map);
        }
        "textDocument/didChange" => {
            let params: DidChangeTextDocumentParams = serde_json::from_value(not.params.clone())?;
            let _uri = params.text_document.uri;
            // let _content_changes = params.content_changes;
            // let mut _documents = documents.lock().unwrap();
        }
        "textDocument/didClose" => {
            let params: DidCloseTextDocumentParams = serde_json::from_value(not.params.clone())?;
            let uri = params.text_document.uri;
            documents
                .lock()
                .unwrap()
                .retain(|(doc_uri, _)| !matches!(doc_uri.clone(), _uri));

            proc_status_map.remove(&uri);
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

fn report_diagnostics(
    connection: &Connection,
    uri: Url,
    diagnostics: Vec<lsp_types::Diagnostic>,
) -> Result<(), Box<dyn Error + Send + Sync>> {
    let params = lsp_types::PublishDiagnosticsParams {
        uri,
        diagnostics,
        version: None,
    };
    let notification =
        lsp_server::Notification::new("textDocument/publishDiagnostics".to_string(), params);
    connection
        .sender
        .send(lsp_server::Message::Notification(notification))?;
    Ok(())
}

fn clear_diagnostics(
    connection: &Connection,
    uri: Url,
) -> Result<(), Box<dyn Error + Send + Sync>> {
    let diagnostics = Vec::new();
    let params = lsp_types::PublishDiagnosticsParams {
        uri,
        diagnostics,
        version: None,
    };
    let notification =
        lsp_server::Notification::new("textDocument/publishDiagnostics".to_string(), params);
    connection
        .sender
        .send(lsp_server::Message::Notification(notification))?;
    Ok(())
}

fn verify(
    options: &Options,
    uri: Url,
    connection: &Connection,
) -> Result<Vec<(lsp_types::Range, bool)>, ()> {
    let path = uri
        .to_file_path()
        .expect("Failed to convert URI to file path");

    let mut files = Files::new();
    let file_id = load_file(&mut files, &path);

    let files_mutex = Mutex::new(files);

    let mut proc_span_map: HashMap<SourceUnitName, Span> = HashMap::new();
    let mut local_proc_status: Vec<(lsp_types::Range, bool)> = Vec::new();

    // We use a block to obtain a try-catch structure to catch the VerifyErrors that might be produced by 2 different function calls.
    // The closure is needed to specify the return type of the block so that we can use the '?' operator.
    let result = (|| -> Result<_, VerifyError> {
        let (mut source_units, mut tcx) =
            get_source_units_from_files(options, &files_mutex, &[file_id])?;

        let files = files_mutex.lock().unwrap();

        source_units.iter_mut().for_each(|item| {
            let (name, source_unit) = item.enter_with_name();
            if let SourceUnit::Decl(DeclKind::ProcDecl(ref proc_ref)) = *source_unit {
                proc_span_map.insert(name.clone(), proc_ref.borrow().span);
            }
        });

        let mut verify_units = transform_source_to_verify(options, source_units);
        let mut all_proven: bool = true;
        for verify_unit in &mut verify_units {
            let (name, mut verify_unit) = verify_unit.enter_with_name();
            let result = verify_unit.verify(name, &mut tcx, options)?;

            if let Some(span) = proc_span_map.get(name) {
                // let char_span = files.char_span(*span);
                let range = (*span).to_lsp_range(&files).unwrap();
                local_proc_status.push((range, result));
            }

            all_proven = all_proven && result;
        }
        Ok(())
    })();

    match result {
        Ok(res) => res,
        Err(e) => {
            if let VerifyError::Diagnostic(diagnostic) = e {
                let files = files_mutex.lock().unwrap();
                let diag = diagnostic.into_lsp_diagnostic(&files);
                let _ =
                    report_diagnostics(connection, Url::from_file_path(path).unwrap(), vec![diag]);
                return Err(());
            }
        }
    }

    Ok(local_proc_status)
}
