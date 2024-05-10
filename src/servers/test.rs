use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
};

use crate::ast::{Diagnostic, FileId, Files, Span, StoredFile};

use super::{Server, ServerError};

pub struct TestServer {
    pub files: Arc<Mutex<Files>>,
    pub diagnostics: Vec<Diagnostic>,
    pub statuses: HashMap<Span, bool>,
}

impl TestServer {
    pub fn new() -> Self {
        TestServer {
            files: Default::default(),
            diagnostics: Default::default(),
            statuses: Default::default(),
        }
    }
}

impl Server for TestServer {
    fn send_server_ready(&self) -> Result<(), ServerError> {
        Ok(())
    }

    fn get_file(&self, file_id: FileId) -> Option<Arc<StoredFile>> {
        self.files.lock().unwrap().get(file_id).cloned()
    }

    fn get_files_internal(&mut self) -> &Mutex<Files> {
        &self.files
    }

    fn add_diagnostic(&mut self, diagnostic: Diagnostic) -> Result<(), ServerError> {
        self.diagnostics.push(diagnostic);
        Ok(())
    }

    fn set_verify_status(&mut self, span: Span, status: bool) -> Result<(), ServerError> {
        self.statuses.insert(span, status);
        Ok(())
    }
}
