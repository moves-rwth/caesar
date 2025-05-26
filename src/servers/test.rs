use std::{
    ops::Deref,
    sync::{Arc, Mutex},
};

use crate::{
    ast::{DeclKind, Diagnostic, FileId, Files, StoredFile},
    driver::{Item, SmtVcCheckResult, SourceUnit, SourceUnitName},
    smt::translate_exprs::TranslateExprs,
    vc::explain::VcExplanation,
    VerifyCommand, VerifyError,
};

use super::{unless_fatal_error, Server, ServerError, VerifyStatus, VerifyStatusList};

pub struct TestServer {
    pub files: Arc<Mutex<Files>>,
    werr: bool,
    pub diagnostics: Vec<Diagnostic>,
    pub statuses: VerifyStatusList,
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
        Ok(())
    }

    fn register_source_unit(
        &mut self,
        source_unit: &mut Item<SourceUnit>,
    ) -> Result<(), VerifyError> {
        let name = source_unit.name().clone();
        if let SourceUnit::Decl(DeclKind::ProcDecl(_)) = source_unit.enter().deref() {
            self.statuses.update_status(&name, VerifyStatus::Todo);
        }
        Ok(())
    }

    fn set_ongoing_unit(&mut self, name: &SourceUnitName) -> Result<(), VerifyError> {
        self.statuses.update_status(name, VerifyStatus::Ongoing);
        Ok(())
    }

    fn handle_vc_check_result<'smt, 'ctx>(
        &mut self,
        name: &SourceUnitName,
        result: &mut SmtVcCheckResult<'ctx>,
        _translate: &mut TranslateExprs<'smt, 'ctx>,
    ) -> Result<(), ServerError> {
        self.statuses
            .update_status(name, VerifyStatus::from_prove_result(&result.prove_result));
        Ok(())
    }
}
