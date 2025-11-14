use num::{BigInt, BigRational};
use z3rro::{eureal::ConcreteEUReal, model::{InstrumentedModel, SmtEval}};

use crate::{
    ast::{
        self,
        visit::{walk_expr, VisitorMut},
        Expr, ExprBuilder, ExprData, ExprKind, Ident, Shared,
    },
    smt::{symbolic::Symbolic, uninterpreted::FuncEntry},
};
use std::collections::HashMap;


pub struct FunctionInliner<'ctx> {
    pub target: Ident,            // the function ident
    pub entry: &'ctx FuncEntry<'ctx>, // contains params + body
    pub body: &'ctx Expr,           // the function body expression
}

impl<'a> VisitorMut for FunctionInliner<'a> {
    type Err = ();

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        let span = expr.span;

        match &mut expr.kind {
            ExprKind::Call(func_ident, args) if *func_ident == self.target => {
                let parameters: Vec<Ident> = self.entry.inputs.node.iter().map(|p| p.name).collect();

                let mut wrapped = self.body.clone();

                // Apply substitutions
                for (parameter, actual_expr) in parameters.iter().zip(args.iter()) {
                    wrapped = Shared::new(ExprData {
                        kind: ExprKind::Subst(*parameter, actual_expr.clone(), wrapped.clone()),
                        ty: wrapped.ty.clone(),
                        span,
                    });
                }

                *expr = wrapped.clone();

                Ok(())
            }

            _ => walk_expr(self, expr),
        }
    }


}


pub fn create_subst_mapping<'ctx>(
    model: &InstrumentedModel<'ctx>,
    vc: &Expr,
    translate: &mut crate::smt::translate_exprs::TranslateExprs<'_, 'ctx>,
) -> HashMap<ast::symbol::Ident, Expr> {
    let span = vc.span;
    let builder = ExprBuilder::new(span);
    let mut mapping = HashMap::new();

    let idents: Vec<_> = translate.local_idents().collect();


    for ident in idents {
        // Build a variable expression to feed into t_symbolic
        let var_expr = builder.var(ident.clone(), translate.ctx.tcx);
        let symbolic = translate.t_symbolic(&var_expr);

        let lit_opt = match &symbolic {
            Symbolic::Bool(v) => v.eval(model).ok().map(|b| builder.bool_lit(b)),

            Symbolic::Int(v) => v
                .eval(model)
                .ok()
                .map(|i: BigInt| builder.frac_lit(BigRational::from_integer(i))),

            Symbolic::UInt(v) => v.eval(model).ok().map(|i: BigInt| {
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
                let eval = v.eval(model);
                eval.ok().map(|r: BigRational| {
                    builder.frac_lit(r)
                })
            }

            Symbolic::UReal(v) => {
                let eval = v.eval(model);
                eval.ok().map(|r: BigRational| {
                    builder.frac_lit(r)
                })
            }

            Symbolic::EUReal(v) => v.eval(model).ok().map(|r| match r {
                ConcreteEUReal::Real(rat) => builder.frac_lit(rat),
                ConcreteEUReal::Infinity => builder.infinity_lit(),
            }),

            _ => None,
        };

        if let Some(ref lit) = lit_opt {
            mapping.insert(ident.clone(), lit.clone());
        }
    }

    mapping
}

/// Instantiate a verification condition (`vc`) with concrete values from the SMT model.
/// Rather than substituting recursively, wrap the VC in nested `Subst` expressions,
/// one for each variable that has a concrete model value.
pub fn subst_mapping<'ctx>(
    mapping: HashMap<ast::symbol::Ident, Expr>,
    vc: &Expr,
) -> Expr {
    // Wrap the expression in nested Subst nodes (one per evaluated variable)
    let mut wrapped = vc.clone();
    for (ident, expr) in mapping {
        wrapped = Shared::new(ExprData {
            kind: ExprKind::Subst(ident, expr, wrapped.clone()),
            ty: wrapped.ty.clone(),
            span: vc.span,
        });
    }
    wrapped
}
