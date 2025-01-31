use std::{
    io::{self, IsTerminal}, path::PathBuf, process::ExitCode, sync::{Arc, Mutex}
};

use ariadne::ReportKind;

use crate::{
    ast::{Diagnostic, FileId, Files, SourceFilePath, Span, StoredFile},
    driver::{SmtVcCheckResult, SourceUnitName},
    smt::translate_exprs::TranslateExprs,
    vc::explain::VcExplanation,
    InputOptions, VerifyError,
};

use super::{unless_fatal_error, Server, ServerError};

pub struct CliServer {
    werr: bool,
    files: Arc<Mutex<Files>>,
    has_emitted_errors: bool,
}

impl CliServer {
    pub fn new(input_options: &InputOptions) -> Self {
        CliServer {
            werr: input_options.werr,
            files: Default::default(),
            has_emitted_errors: false,
        }
    }

    pub fn load_file(&mut self, path: &PathBuf) -> FileId {
        let source = match std::fs::read_to_string(path) {
            Ok(source) => source,
            Err(err) => match err.kind() {
                io::ErrorKind::NotFound => {
                    panic!("Error: Could not find file '{}'", path.to_string_lossy())
                }
                _ => panic!(
                    "Error while loading file '{}': {}",
                    path.to_string_lossy(),
                    err
                ),
            },
        };
        let source_file_path = SourceFilePath::Path(path.clone());
        let mut files = self.files.lock().unwrap();
        let file = files.add(source_file_path, source);
        file.id
    }
}

impl Server for CliServer {
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
        self.has_emitted_errors =
            self.has_emitted_errors || self.werr || diagnostic.kind() == ReportKind::Error;
        let files = self.files.lock().unwrap();
        print_diagnostic(&files, diagnostic)?;
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
        // Not relevant for CLI
        Ok(())
    }

    fn handle_vc_check_result<'smt, 'ctx>(
        &mut self,
        name: &SourceUnitName,
        _span: Span,
        result: &mut SmtVcCheckResult<'ctx>,
        translate: &mut TranslateExprs<'smt, 'ctx>,
    ) -> Result<(), ServerError> {
        result.print_prove_result(self, translate, name);
        Ok(())
    }

    fn handle_not_checked(&mut self, _span: Span) -> Result<(), ServerError> {
        // Not relevant for CLI
        Ok(())
    }

    fn exit_code(&self) -> ExitCode {
        if self.has_emitted_errors {
            ExitCode::FAILURE
        } else {
            ExitCode::SUCCESS
        }
    }
}

fn print_diagnostic(mut files: &Files, diagnostic: Diagnostic) -> io::Result<()> {
    let mut report = diagnostic.into_ariadne(files);
    if !io::stderr().is_terminal() {
        // let's hope there's no config already there
        report = report.with_config(ariadne::Config::default().with_color(false));
    }
    let report = report.finish();
    report.eprint(&mut files)
}
