use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
};

use crate::{
    ast::{Diagnostic, FileId, Files, Span, StoredFile},
    driver::{SmtVcCheckResult, SourceUnitName},
    smt::translate_exprs::TranslateExprs,
    Options, VerifyError,
};

use super::{unless_fatal_error, Server, ServerError, VerifyResult};

pub struct TestServer {
    pub files: Arc<Mutex<Files>>,
    werr: bool,
    pub diagnostics: Vec<Diagnostic>,
    pub statuses: HashMap<Span, VerifyResult>,
}

impl TestServer {
    pub fn new(options: &Options) -> Self {
        TestServer {
            files: Default::default(),
            werr: options.werr,
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

    fn add_diagnostic(&mut self, diagnostic: Diagnostic) -> Result<(), VerifyError> {
        self.diagnostics
            .push(unless_fatal_error(self.werr, diagnostic)?);
        Ok(())
    }

    fn handle_vc_check_result<'smt, 'ctx>(
        &mut self,
        _name: &SourceUnitName,
        span: Span,
        result: &mut SmtVcCheckResult<'ctx>,
        _translate: &mut TranslateExprs<'smt, 'ctx>,
    ) -> Result<(), ServerError> {
        self.statuses
            .insert(span, VerifyResult::from_prove_result(&result.prove_result));
        Ok(())
    }
}
