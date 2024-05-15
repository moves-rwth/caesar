use itertools::Itertools;
use z3::ast::Bool;
use z3rro::model::{InstrumentedModel, SmtEval, SmtEvalError};

use crate::ast::{Diagnostic, Label, Span, Symbol};

use super::{selection::SliceSelection, transform::SliceStmt};

/// Do we have a slice that verifies or that errors?
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SliceMode {
    Verify,
    Error,
}

/// Extraction of models from the slicing solver.
#[derive(Debug)]
pub struct SliceModel {
    mode: SliceMode,
    stmts: Vec<(SliceStmt, Result<bool, SmtEvalError>)>,
}

/// A decision for each statement with optional messages (from annotations).
#[derive(Debug)]
pub enum SliceResult {
    PartOfError(Option<Symbol>),
    NotNecessary(Option<Symbol>),
    Error(SmtEvalError),
}

impl SliceModel {
    pub(super) fn extract_model<'ctx>(
        mode: SliceMode,
        slice_vars: &[(SliceStmt, Bool<'ctx>)],
        selection: SliceSelection,
        model: &InstrumentedModel<'ctx>,
    ) -> SliceModel {
        let stmts = slice_vars
            .iter()
            .map(|(slice_stmt, var)| {
                let status = model.atomically(|| var.eval(model));
                (slice_stmt.clone(), status)
            })
            // first evaluate, then filter to access all slice variables in the
            // model. otherwise we'd get "extra definitions" for the filtered ones
            // in the model output
            .filter(|(stmt, _var)| selection.enables(&stmt.selection))
            .collect_vec();
        SliceModel { mode, stmts }
    }

    /// Iterate over the results in this slice model.
    pub fn iter_results(&self) -> impl Iterator<Item = (Span, SliceResult)> + '_ {
        self.stmts.iter().flat_map(move |(stmt, enabled)| {
            let res = match (self.mode, enabled) {
                (SliceMode::Error, Ok(true)) => SliceResult::PartOfError(stmt.failure_message()),
                (SliceMode::Verify, Ok(false)) => SliceResult::NotNecessary(stmt.success_message()),
                (_, Ok(_)) => return None,
                (_, Err(err)) => SliceResult::Error(err.clone()),
            };
            Some((stmt.statement, res))
        })
    }

    /// Return the slice mode.
    pub fn mode(&self) -> SliceMode {
        self.mode
    }

    /// Whether this model has sliced any statements (true) or whether we have
    /// not sliced any statements (false).
    pub fn count_sliced_stmts(&self) -> usize {
        self.stmts
            .iter()
            .filter(|(_span, result)| matches!(result, Ok(false)))
            .count()
    }

    /// Create diagnostics for this slice model. This is used for the LSP server.
    pub fn to_diagnostics(&self) -> impl Iterator<Item = Diagnostic> + '_ {
        self.iter_results()
            .flat_map(|(span, result)| match result {
                SliceResult::PartOfError(message) => Some(
                    Diagnostic::new(ariadne::ReportKind::Error, span)
                        .with_message(
                            message
                                .unwrap_or(Symbol::intern("This statement is part of the error")),
                        )
                        .with_label(Label::new(span).with_message("here")),
                ),
                SliceResult::NotNecessary(message) => Some(
                    Diagnostic::new(ariadne::ReportKind::Advice, span)
                        .with_message(
                            message.unwrap_or(Symbol::intern("This statement is not necessary")),
                        )
                        .with_label(Label::new(span).with_message("here")),
                ),
                SliceResult::Error(err) => {
                    tracing::error!(err=?err, "error encountered in slice result");
                    None
                }
            })
    }
}
