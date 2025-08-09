use std::{
    collections::HashMap,
    ops::Deref,
    sync::{Arc, Mutex},
};

use crate::{
    ast::{DeclKind, Diagnostic, FileId, Files, StoredFile},
    driver::{Item, SmtVcCheckResult, SourceUnit, SourceUnitName},
    servers::FileStatus,
    smt::translate_exprs::TranslateExprs,
    vc::explain::VcExplanation,
    VerifyCommand, VerifyError,
};

use super::{unless_fatal_error, Server, ServerError, VerifyStatus};

pub struct TestServer {
    pub files: Arc<Mutex<Files>>,
    werr: bool,
    pub diagnostics: Vec<Diagnostic>,
    pub file_statuses: HashMap<FileId, FileStatus>,
}

impl TestServer {
    pub fn new(options: &VerifyCommand) -> Self {
        TestServer {
            files: Default::default(),
            werr: options.input_options.werr,
            diagnostics: Default::default(),
            file_statuses: Default::default(),
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

        let statuses = &mut self
            .file_statuses
            .entry(name.span().file)
            .or_default()
            .verify_statuses;

        if let SourceUnit::Decl(DeclKind::ProcDecl(_)) = source_unit.enter().deref() {
            statuses.update_status(&name, VerifyStatus::Todo);
        }
        Ok(())
    }

    fn set_ongoing_unit(&mut self, name: &SourceUnitName) -> Result<(), VerifyError> {
        let statuses = &mut self
            .file_statuses
            .entry(name.span().file)
            .or_default()
            .verify_statuses;

        statuses.update_status(name, VerifyStatus::Ongoing);
        Ok(())
    }

    fn set_file_status_type(
        &mut self,
        file_id: &FileId,
        status_type: super::FileStatusType,
    ) -> Result<(), VerifyError> {
        let doc_status = self.file_statuses.entry(*file_id).or_default();
        doc_status.status_type = status_type;
        Ok(())
    }

    fn handle_vc_check_result<'smt, 'ctx>(
        &mut self,
        name: &SourceUnitName,
        result: &mut SmtVcCheckResult<'ctx>,
        _translate: &mut TranslateExprs<'smt, 'ctx>,
    ) -> Result<(), ServerError> {
        let statuses = &mut self
            .file_statuses
            .entry(name.span().file)
            .or_default()
            .verify_statuses;

        statuses.update_status(name, VerifyStatus::from_prove_result(&result.prove_result));
        Ok(())
    }
}
