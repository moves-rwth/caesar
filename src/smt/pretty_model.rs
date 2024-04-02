//! Pretty-printing an SMT model.

use std::{collections::BTreeMap, rc::Rc};

use itertools::Itertools;
use z3::Model;
use z3rro::model::InstrumentedModel;

use crate::{
    ast::{
        decl::{DeclKind, DeclKindName},
        ExprBuilder, Files, Ident, Span,
    },
    pretty::Doc,
    smt::translate_exprs::TranslateExprs,
};

/// Pretty-print a model.
pub fn pretty_model<'smt, 'ctx>(
    files: &Files,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    model: Model<'ctx>,
) -> Doc {
    let mut res: Vec<Doc> = vec![];

    let mut model = InstrumentedModel::new(model);

    // objects accessed during vc evaluation do not contribute towards the
    // unaccessed list.
    model.reset_accessed();

    // Print the values of the global variables in the model.
    pretty_globals(translate, &model, files, &mut res);

    // Print the unaccessed definitions.
    res.push(pretty_unaccessed(model));

    Doc::intersperse(res, Doc::hardline().append(Doc::hardline()))
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
        .map(|ident| translate.ctx.tcx.get(ident).unwrap());

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
    let value = match symbolic.eval(model) {
        Ok(value) => Doc::text(format!("{}", value)),
        Err(err) => Doc::text(format!("({})", err)),
    };
    value
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

fn pretty_unaccessed(model: InstrumentedModel<'_>) -> Doc {
    let unaccessed: Vec<_> = model.iter_unaccessed().collect();
    if unaccessed.is_empty() {
        return Doc::nil();
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
    Doc::intersperse(lines, Doc::hardline()).nest(4)
}
