//! Pretty-printing an SMT model.

use std::{collections::BTreeMap, fmt::Display, rc::Rc};

use itertools::Itertools;
use z3rro::model::{InstrumentedModel, SmtEval, SmtEvalError};

use crate::{
    ast::{
        decl::{DeclKind, DeclKindName},
        ExprBuilder, Files, Ident, Span, VarKind,
    },
    driver::VcUnit,
    pretty::Doc,
    slicing::{selection::SliceSelection, transform::SliceStmts},
    smt::translate_exprs::TranslateExprs,
};

/// Pretty-print a model.
pub fn pretty_model<'smt, 'ctx>(
    files: &Files,
    slice_stmts: &SliceStmts,
    selection: SliceSelection,
    vc_expr: &VcUnit,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    model: &mut InstrumentedModel<'ctx>,
) -> Doc {
    let mut res: Vec<Doc> = vec![];

    // Print the values of the global variables in the model.
    pretty_globals(translate, model, files, &mut res);

    let slice_lines = pretty_slice(
        files,
        translate,
        slice_stmts,
        selection,
        model,
        PrettySliceMode::Error,
    );

    // Print the unaccessed definitions.
    if let Some(unaccessed) = pretty_unaccessed(model) {
        res.push(unaccessed);
    }

    res.push(print_vc_value(vc_expr, translate, model));

    if let Some(slice_lines) = slice_lines {
        res.push(slice_lines);
    }

    // objects accessed during vc evaluation do not contribute towards the
    // unaccessed list
    model.reset_accessed();

    let doc = Doc::intersperse(res, Doc::line_().append(Doc::line_())).append(Doc::line_());
    doc
}

fn print_vc_value<'smt, 'ctx>(
    vc_expr: &VcUnit,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    model: &InstrumentedModel<'ctx>,
) -> Doc {
    let ast = translate.t_symbolic(&vc_expr.expr);
    let value = ast.eval(model);
    let res = pretty_eval_result(value);
    Doc::text("the pre-quantity evaluated to:").append(Doc::hardline().append(res).nest(4))
}

fn pretty_globals<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    model: &InstrumentedModel<'ctx>,
    files: &Files,
    res: &mut Vec<Doc>,
) {
    // retrieve the global declarations in the smt translator, sorted by their
    // position
    //
    // TODO: these local idents do not include identifiers for limits such as
    // infima and suprema. consequently, those will not be printed in the model.
    // we should include those in the future.
    let global_decls = translate
        .local_idents()
        .sorted_by_key(|ident| ident.span.start)
        .map(|ident| translate.ctx.tcx.get(ident).unwrap())
        .filter(|decl| decl.kind_name() != DeclKindName::Var(VarKind::Slice));

    // now group the declarations by their DeclKindName
    let mut decls_by_kind: BTreeMap<DeclKindName, Vec<Rc<DeclKind>>> = BTreeMap::new();
    for decl in global_decls {
        decls_by_kind
            .entry(decl.kind_name())
            .or_default()
            .push(decl);
    }

    for (kind_name, decls) in decls_by_kind {
        let mut lines: Vec<Doc> = vec![Doc::text(format!("{}s:", kind_name))];

        for decl_kind in decls {
            if let DeclKind::VarDecl(decl_ref) = &*decl_kind {
                let var_decl = decl_ref.borrow();
                let ident = var_decl.name;

                // pretty print the value of this variable
                let value = pretty_var(translate, ident, model);

                // pretty print the span of this variable declaration
                let span = pretty_span(files, ident);

                lines.push(
                    Doc::text(format!("{}: ", var_decl.original_name()))
                        .append(value)
                        .append(span),
                );
            }
        }

        res.push(Doc::intersperse(lines, Doc::hardline()).nest(4));
    }
}

fn pretty_var<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    ident: Ident,
    model: &InstrumentedModel<'ctx>,
) -> Doc {
    let builder = ExprBuilder::new(Span::dummy_span());
    let symbolic = translate.t_symbolic(&builder.var(ident, translate.ctx.tcx));

    // atomically evaluate the value in the model, so that if an error occurs
    // the accessed variables will still show up in the "unaccessed" block later
    // on.
    let res = model.atomically(|| symbolic.eval(model));

    pretty_eval_result(res)
}

fn pretty_eval_result<T>(res: Result<T, SmtEvalError>) -> Doc
where
    T: Display,
{
    match res {
        Ok(value) => Doc::text(format!("{}", value)),
        Err(err) => Doc::text(format!("({})", err)),
    }
}

fn pretty_span(files: &Files, ident: Ident) -> Doc {
    if let Some(text) = files.format_span_start(ident.span) {
        let text = format!("({})", text);
        let note_len = text.chars().count();

        // add padding to align the text to the right
        let padding = Doc::column(move |col| {
            let rest_space = 80_usize
                .saturating_sub(4)
                .saturating_sub(col)
                .saturating_sub(note_len)
                .max(4);
            Doc::text(" ".repeat(rest_space))
        });

        padding.append(Doc::text(text))
    } else {
        Doc::nil()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum PrettySliceMode {
    Verify,
    Error,
}

pub fn pretty_slice<'smt, 'ctx>(
    files: &Files,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    slice_stmts: &SliceStmts,
    selection: SliceSelection,
    model: &InstrumentedModel<'ctx>,
    mode: PrettySliceMode,
) -> Option<Doc> {
    let values = slice_stmts
        .stmts
        .iter()
        .map(|slice_stmt| {
            let builder = ExprBuilder::new(Span::dummy_span());
            let symbolic = translate.t_bool(&builder.var(slice_stmt.ident, translate.ctx.tcx));
            let status = model.atomically(|| symbolic.eval(model));
            (slice_stmt, status)
        })
        // first evaluate, then filter to access all slice variables in the
        // model. otherwise we'd get "extra definitions" for the filtered ones
        // in the model output
        .filter(|(stmt, _status)| selection.enables(&stmt.selection))
        .collect_vec();

    let mut lines: Vec<Doc> = vec![];
    for (stmt, status) in values {
        let ident = stmt.ident;
        if let Some((_file, line_number, _col_number)) = files.get_human_span(ident.span) {
            let line = match status {
                Ok(true) => {
                    if let Some(msg) = stmt.failure_message() {
                        Doc::text("❌ ").append(Doc::text(msg.to_string()))
                    } else if mode == PrettySliceMode::Error
                        && stmt.selection.in_slice_error_annotation
                    {
                        Doc::text("🤷 ").append(Doc::text(format!(
                            "statement in line {} is part of the error",
                            line_number
                        )))
                    } else {
                        continue;
                    }
                }
                Ok(false) => {
                    if let Some(msg) = stmt.success_message() {
                        Doc::text("🤷 ").append(Doc::text(msg.to_string()))
                    } else if mode == PrettySliceMode::Verify
                        && stmt.selection.in_slice_verify_annotation
                    {
                        Doc::text("🤷 ").append(Doc::text(format!(
                            "statement in line {} is not necessary",
                            line_number
                        )))
                    } else {
                        continue;
                    }
                }
                Err(err) => Doc::text(format!("({}):", err)),
            };
            let line = line.append(pretty_span(files, ident));
            lines.push(line);
        }
    }

    if lines.is_empty() {
        return None;
    }

    lines.insert(0, Doc::text("program slice:"));

    Some(Doc::intersperse(lines, Doc::line_()).nest(4))
}

fn pretty_unaccessed(model: &InstrumentedModel<'_>) -> Option<Doc> {
    let unaccessed: Vec<_> = model.iter_unaccessed().collect();
    if unaccessed.is_empty() {
        return None;
    }

    let mut lines: Vec<Doc> = vec![Doc::text("extra definitions:")];
    for decl in unaccessed {
        let line = if decl.arity() == 0 {
            let value = model.eval(&decl.apply(&[]), true).unwrap();
            format!("{}: {}", decl.name(), value)
        } else {
            let interp = model.get_func_interp(&decl).unwrap();
            format!("{}: {}", decl.name(), interp)
        };
        lines.push(Doc::text(line));
    }
    Some(Doc::intersperse(lines, Doc::hardline()).nest(4))
}
