use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
};

use crate::{
    ast::{Diagnostic, FileId, Files, Span, StoredFile},
    driver::{SmtVcCheckResult, SourceUnitName},
    smt::translate_exprs::TranslateExprs,
    vc::explain::VcExplanation,
    VerifyCommand, VerifyError,
};

use super::{unless_fatal_error, Server, ServerError, VerifyResult};

pub struct TestServer {
    pub files: Arc<Mutex<Files>>,
    werr: bool,
    pub diagnostics: Vec<Diagnostic>,
    pub statuses: HashMap<Span, VerifyResult>,
}

impl TestServer {
    pub fn new(options: &VerifyCommand) -> Self {
        TestServer {
            files: Default::default(),
            werr: options.input_options.werr,
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
        self.diagnostics.push(diagnostic);
        Ok(())
    }

    fn add_or_throw_diagnostic(&mut self, diagnostic: Diagnostic) -> Result<(), VerifyError> {
        let diagnostic = unless_fatal_error(self.werr, diagnostic)?;
        self.add_diagnostic(diagnostic)
    }

    fn add_vc_explanation(&mut self, _explanation: VcExplanation) -> Result<(), VerifyError> {
        // TODO
        Ok(())
    }

    fn register_source_unit(&mut self, _span: Span) -> Result<(), VerifyError> {
        // TODO
        Ok(())
    }

    fn set_ongoing_unit(&mut self, _span: Span) -> Result<(), VerifyError> {
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
