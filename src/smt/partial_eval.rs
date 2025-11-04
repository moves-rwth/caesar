use num::{bigint::Sign, BigInt, BigRational, BigUint};
use z3rro::{
    eureal::ConcreteEUReal,
    filtered_model::FilteredModel,
    model::{InstrumentedModel, SmtEval},
};

use crate::{
    ast::{Expr, ExprBuilder, ExprData, ExprKind, LitKind, Shared, Span, Spanned},
    smt::{symbolic::Symbolic, translate_exprs::TranslateExprs},
};

/// Instantiate a verification condition (`vc`) with concrete values from the SMT model.
/// Variables that have a value in the model are replaced with typed literals.
pub fn instantiate_vc_with_model<'ctx>(
    model: &FilteredModel<'ctx>,
    vc: &Expr,
    translate: &mut crate::smt::translate_exprs::TranslateExprs<'_, 'ctx>,
) -> Expr
{
    fn recurse<'ctx>(
        e: &Expr,
        model: &FilteredModel<'ctx>,
        translate: &mut crate::smt::translate_exprs::TranslateExprs<'_, 'ctx>,
    ) -> Expr
    {
        let span = e.span;
        let builder = ExprBuilder::new(span);

        match &e.kind {
            // Try to evaluate a symbolic variable under the model
            ExprKind::Var(ident) => {
                let symbolic = translate.t_symbolic(e);
                let lit = match &symbolic {
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
                        v.eval_filtered(model).ok().map(|r: BigRational| builder.frac_lit(r))
                    }
                    Symbolic::UReal(v) => {
                        v.eval_filtered(model).ok().map(|r: BigRational| builder.frac_lit(r))
                    }
                    Symbolic::EUReal(v) => v.eval_filtered(model).ok().map(|r| match r {
                        ConcreteEUReal::Real(rat) => builder.frac_lit(rat),
                        ConcreteEUReal::Infinity => builder.infinity_lit(),
                    }),
                    _ => None,
                };
                lit.unwrap_or_else(|| e.clone())
            }

            // Recurse into calls, conditionals, and operators
            ExprKind::Call(ident, args) => Shared::new(ExprData {
                kind: ExprKind::Call(
                    *ident,
                    args.iter().map(|a| recurse(a, model, translate)).collect(),
                ),
                ty: e.ty.clone(),
                span,
            }),

            ExprKind::Ite(cond, then_br, else_br) => Shared::new(ExprData {
                kind: ExprKind::Ite(
                    recurse(cond, model, translate),
                    recurse(then_br, model, translate),
                    recurse(else_br, model, translate),
                ),
                ty: e.ty.clone(),
                span,
            }),

            ExprKind::Binary(op, lhs, rhs) => Shared::new(ExprData {
                kind: ExprKind::Binary(
                    op.clone(),
                    recurse(lhs, model, translate),
                    recurse(rhs, model, translate),
                ),
                ty: e.ty.clone(),
                span,
            }),

            ExprKind::Unary(op, inner) => Shared::new(ExprData {
                kind: ExprKind::Unary(op.clone(), recurse(inner, model, translate)),
                ty: e.ty.clone(),
                span,
            }),

            ExprKind::Cast(inner) => Shared::new(ExprData {
                kind: ExprKind::Cast(recurse(inner, model, translate)),
                ty: e.ty.clone(),
                span,
            }),

            ExprKind::Quant(op, vars, ann, body) => Shared::new(ExprData {
                kind: ExprKind::Quant(
                    op.clone(),
                    vars.clone(),
                    ann.clone(),
                    recurse(body, model, translate),
                ),
                ty: e.ty.clone(),
                span,
            }),

            ExprKind::Subst(id, subst, inner) => Shared::new(ExprData {
                kind: ExprKind::Subst(
                    *id,
                    recurse(subst, model, translate),
                    recurse(inner, model, translate),
                ),
                ty: e.ty.clone(),
                span,
            }),

            ExprKind::Lit(_) => e.clone(),
        }
    }

    recurse(vc, model, translate)
}
