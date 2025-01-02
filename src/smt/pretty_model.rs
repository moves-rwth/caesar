//! Pretty-printing an SMT model.

use std::{
    collections::BTreeMap,
    fmt::Display,
    rc::Rc,
    time::{Duration, Instant},
};

use itertools::Itertools;
use z3rro::model::{InstrumentedModel, SmtEvalError};

use crate::{
    ast::{
        decl::{DeclKind, DeclKindName},
        ExprBuilder, Files, Ident, Span, VarKind,
    },
    driver::QuantVcUnit,
    pretty::Doc,
    resource_limits::LimitsRef,
    slicing::model::{SliceModel, SliceResult},
    smt::translate_exprs::TranslateExprs,
    vc::subst::apply_subst,
};

/// Pretty-print a model.
pub fn pretty_model<'smt, 'ctx>(
    files: &Files,
    slice_model: &SliceModel,
    vc_expr: &QuantVcUnit,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    model: &mut InstrumentedModel<'ctx>,
) -> Doc {
    let mut res: Vec<Doc> = vec![];

    // Print the values of the global variables in the model.
    pretty_globals(translate, model, files, &mut res);

    let slice_lines = pretty_slice(files, slice_model);

    // Print the unaccessed definitions.
    if let Some(unaccessed) = pretty_unaccessed(model) {
        res.push(unaccessed);
    }

    if let Some(slice_lines) = slice_lines {
        res.push(slice_lines);
    }

    res.push(pretty_vc_value(vc_expr, translate, model, slice_model));

    Doc::intersperse(res, Doc::line_().append(Doc::line_())).append(Doc::line_())
}

pub fn pretty_vc_value<'smt, 'ctx>(
    vc_expr: &QuantVcUnit,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    model: &InstrumentedModel<'ctx>,
    slice_model: &SliceModel,
) -> Doc {
    let original_program_vc = if slice_model.count_sliced_stmts() == 0 {
        vc_expr.expr.clone()
    } else {
        // reconstruct the original program's vc by substituting the slice
        // variables by `true`.
        let builder = ExprBuilder::new(Span::dummy_span());
        let expr_true = builder.bool_lit(true);
        let subst_expr = builder.subst_by(
            vc_expr.expr.clone(),
            slice_model.iter_variables(),
            |_ident| expr_true.clone(),
        );
        let mut res = subst_expr;
        let deadline = Instant::now() + Duration::from_millis(1);
        let _ = apply_subst(
            translate.ctx.tcx(),
            &mut res,
            &LimitsRef::new(Some(deadline)),
        );
        res
    };

    let mut lines = vec![];

    let ast = translate.t_symbolic(&original_program_vc);
    let value = ast.eval(model);
    let res = pretty_eval_result(value);
    lines.push(
        Doc::text("the pre-quantity evaluated to:").append(Doc::hardline().append(res).nest(4)),
    );

    let num_sliced_stmts = slice_model.count_sliced_stmts();
    if num_sliced_stmts > 0 {
        let ast = translate.t_symbolic(&vc_expr.expr);
        let value = ast.eval(model);
        let slice_pre = pretty_eval_result(value)
            .append(Doc::line_())
            .append(Doc::text(format!(
                "(slicing removed {}/{} assertions)",
                num_sliced_stmts,
                slice_model.len()
            )));
        lines.push(Doc::nil());
        lines.push(
            Doc::text("in the sliced program, the pre-quantity evaluated to:")
                .append(Doc::hardline().append(slice_pre).nest(4)),
        );
    }

    Doc::intersperse(lines, Doc::line())
}

pub fn pretty_globals<'smt, 'ctx>(
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
                let value = pretty_var_value(translate, ident, model);

                // pretty print the span of this variable declaration
                let span = pretty_span(files, ident.span);

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

pub fn pretty_var_value<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    ident: Ident,
    model: &InstrumentedModel<'ctx>,
) -> String {
    let builder = ExprBuilder::new(Span::dummy_span());
    let symbolic = translate.t_symbolic(&builder.var(ident, translate.ctx.tcx));

    // atomically evaluate the value in the model, so that if an error occurs
    // the accessed variables will still show up in the "unaccessed" block later
    // on.
    let res = model.atomically(|| symbolic.eval(model));

    match res {
        Ok(value) => format!("{}", value),
        Err(err) => format!("({})", err),
    }
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

fn pretty_span(files: &Files, span: Span) -> Doc {
    if let Some(text) = files.format_span_start(span) {
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

pub fn pretty_slice(files: &Files, slice_model: &SliceModel) -> Option<Doc> {
    let mut lines: Vec<Doc> = vec![];
    for (stmt_span, result) in slice_model.iter_results() {
        if let Some((_file, line_number, _col_number)) = files.get_human_span_start(stmt_span) {
            let line = match result {
                SliceResult::PartOfError(msg) => {
                    let msg = msg.map(|msg| msg.to_string()).unwrap_or_else(|| {
                        format!("statement in line {} is part of the error", line_number)
                    });
                    Doc::text("❌ ").append(Doc::text(msg))
                }
                SliceResult::NotNecessary(msg) => {
                    let msg = msg.map(|msg| msg.to_string()).unwrap_or_else(|| {
                        format!("statement in line {} is not necessary", line_number)
                    });
                    Doc::text("🤷 ").append(Doc::text(msg))
                }
                SliceResult::Error(err) => Doc::text(format!("({}):", err)),
            };
            let line = line.append(pretty_span(files, stmt_span));
            lines.push(line);
        }
    }

    if lines.is_empty() {
        return None;
    }

    lines.insert(0, Doc::text("program slice:"));

    Some(Doc::intersperse(lines, Doc::line_()).nest(4))
}

pub fn pretty_unaccessed(model: &InstrumentedModel<'_>) -> Option<Doc> {
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
