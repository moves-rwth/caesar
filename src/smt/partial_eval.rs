use num::{BigInt, BigRational};
use z3rro::{eureal::ConcreteEUReal, filtered_model::FilteredModel, model::SmtEval};

use crate::{
    ast::{self, Expr, ExprBuilder, ExprData, ExprKind, Shared},
    smt::symbolic::Symbolic,
};
use std::collections::HashMap;

/// Instantiate a verification condition (`vc`) with concrete values from the SMT model.
/// Rather than substituting recursively, wrap the VC in nested `Subst` expressions,
/// one for each variable that has a concrete model value.

pub fn instantiate_through_subst<'ctx>(
    model: &FilteredModel<'ctx>,
    vc: &Expr,
    translate: &mut crate::smt::translate_exprs::TranslateExprs<'_, 'ctx>,
) -> (Expr, HashMap<ast::symbol::Ident, Expr>) {
    let span = vc.span;
    let builder = ExprBuilder::new(span);
    let mut substitutions = Vec::new();
    let mut mapping = HashMap::new();

    let idents: Vec<_> = translate.local_idents().collect();

    for ident in idents {
        // Build a variable expression to feed into t_symbolic
        let var_expr = builder.var(ident.clone(), translate.ctx.tcx);
        let symbolic = translate.t_symbolic(&var_expr);

        let lit_opt = match &symbolic {
            Symbolic::Bool(v) => v.eval_filtered(model).ok().map(|b| builder.bool_lit(b)),

            Symbolic::Int(v) => v
                .eval_filtered(model)
                .ok()
                .map(|i: BigInt| builder.frac_lit(BigRational::from_integer(i))),

            Symbolic::UInt(v) => v.eval_filtered(model).ok().map(|i: BigInt| {
                if i >= BigInt::from(0) {
                    match u128::try_from(i.clone()) {
                        Ok(u) => builder.uint(u),
                        Err(_) => builder.frac_lit(BigRational::from_integer(i)),
                    }
                } else {
                    builder.frac_lit(BigRational::from_integer(i))
                }
            }),

            Symbolic::Real(v) => {
                let eval = v.eval_filtered(model);
                eval.ok().map(|r: BigRational| {
                    builder.frac_lit(r)
                })
            }

            Symbolic::UReal(v) => {
                let eval = v.eval_filtered(model);
                eval.ok().map(|r: BigRational| {
                    builder.frac_lit(r)
                })
            }

            Symbolic::EUReal(v) => v.eval_filtered(model).ok().map(|r| match r {
                ConcreteEUReal::Real(rat) => builder.frac_lit(rat),
                ConcreteEUReal::Infinity => builder.infinity_lit(),
            }),

            _ => None,
        };

        if let Some(ref lit) = lit_opt {
            println!("Substituting {ident} with {lit}");
            substitutions.push((ident.clone(), lit.clone()));
            mapping.insert(ident.clone(), lit.clone());
        }
    }

    // Wrap the expression in nested Subst nodes (one per evaluated variable)
    let mut wrapped = vc.clone();
    for (ident, lit) in substitutions {
        wrapped = Shared::new(ExprData {
            kind: ExprKind::Subst(ident, lit, wrapped.clone()),
            ty: wrapped.ty.clone(),
            span,
        });
    }

    (wrapped, mapping)
}
