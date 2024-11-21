use std::{collections::HashSet, iter::FromIterator};

use itertools::Itertools;
use lsp_types::DiagnosticTag;
use z3::ast::Bool;
use z3rro::model::{InstrumentedModel, SmtEval, SmtEvalError};

use crate::ast::{Diagnostic, Ident, Label, Span, Symbol};

use super::{selection::SliceSelection, solver::SmtSliceStmts, transform::SliceStmt};

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
    pub(super) fn from_model<'ctx>(
        mode: SliceMode,
        slice_stmts: &SmtSliceStmts<'ctx>,
        selection: SliceSelection,
        model: &InstrumentedModel<'ctx>,
    ) -> SliceModel {
        let stmts = slice_stmts
            .stmts
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

    pub(super) fn from_enabled<'ctx>(
        mode: SliceMode,
        slice_stmts: &SmtSliceStmts<'ctx>,
        selection: SliceSelection,
        enabled: Vec<Bool<'ctx>>,
    ) -> SliceModel {
        let enabled: HashSet<Bool<'ctx>> = HashSet::from_iter(enabled);
        let stmts = slice_stmts
            .stmts
            .iter()
            .filter(|(stmt, _var)| selection.enables(&stmt.selection))
            .map(|(slice_stmt, var)| {
                let status = Ok(enabled.contains(var));
                (slice_stmt.clone(), status)
            })
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

    /// Return the number of statements in this model.
    pub fn len(&self) -> usize {
        self.stmts.len()
    }

    /// Iterate over all [`Ident`]s for slice variables.
    pub fn iter_variables(&self) -> impl Iterator<Item = Ident> + '_ {
        self.stmts.iter().map(|(stmt, _res)| stmt.ident)
    }

    /// Count the number of statements that were sliced in this model.
    pub fn count_sliced_stmts(&self) -> usize {
        self.stmts
            .iter()
            .filter(|(_span, result)| matches!(result, Ok(false)))
            .count()
    }

    /// Create diagnostics for this slice model. This is used for the LSP server.
    pub fn to_diagnostics(&self) -> impl Iterator<Item = Diagnostic> + '_ {
        self.iter_results().flat_map(|(span, result)| match result {
            SliceResult::PartOfError(message) => Some(
                Diagnostic::new(ariadne::ReportKind::Error, span)
                    .with_message(
                        message.unwrap_or(Symbol::intern("This statement is part of the error")),
                    )
                    .with_label(Label::new(span).with_message("here")),
            ),
            SliceResult::NotNecessary(message) => Some(
                Diagnostic::new(ariadne::ReportKind::Warning, span)
                    .with_message(
                        message.unwrap_or(Symbol::intern("This statement is not necessary")),
                    )
                    .with_label(Label::new(span).with_message("here"))
                    .with_tag(DiagnosticTag::UNNECESSARY),
            ),
            SliceResult::Error(err) => {
                tracing::error!(err=?err, "error encountered in slice result");
                None
            }
        })
    }
}
