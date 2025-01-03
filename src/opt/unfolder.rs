//! Unfold an [`Expr`] incrementally by checking whether particular parts of the
//! expression are actually reachable using simple SAT checks. We basically
//! implement a simple form of bounded model checking to unfold the expression.
//!
//! The smart unfolding of expressions is particularly important after
//! verification condition generation ([`crate::vc`]) where expressions with
//! possibly exponential size in the input program are generated. Since the
//! generated verification conditions use shared references to sub-expressions,
//! we can reasily represent gigantic expressions with small memory usage.
//!
//! But for later operations on the verification conditions such as quantifier
//! elimination or the final SAT check using Z3, we need to visit the complete
//! expression. This explodes when the represented expression is very large.
//!
//! This is why we recursively un-share the expression in this module, but keep
//! track of (some of) the conditions to reach parts of the expression. When we
//! can prove that some parts are unreachable, we can avoid expanding a
//! potentially huge sub-expression and replace it with a constant.
//!
//! The reachability checks implemented here are just conservative
//! approximations, so there are many expressions where we do not detect
//! unreachability. However, we must *never* falsely eliminate reachable
//! parts of the expression.

use std::ops::DerefMut;

use z3::SatResult;
use z3rro::prover::Prover;

use crate::{
    ast::{
        util::{is_bot_lit, is_top_lit},
        visit::{walk_expr, VisitorMut},
        BinOpKind, Expr, ExprBuilder, ExprData, ExprKind, Shared, Span, SpanVariant, Spanned,
        TyKind, UnOpKind,
    },
    resource_limits::{LimitError, LimitsRef},
    smt::SmtCtx,
    vc::subst::Subst,
};

use crate::smt::translate_exprs::{TranslateExprs};

pub struct Unfolder<'smt, 'ctx> {
    limits_ref: LimitsRef,

    /// The expressions may contain substitutions. We keep track of those.
    subst: Subst<'smt>,

    /// Context to translate to SMT.
    translate: TranslateExprs<'smt, 'ctx>,

    /// The prover keeps track of the conditions to reach the current
    /// sub-expression. The proof check returns `Proof` if it's unreachable.
    /// Since the conditions are not complete, a result of `Counterexample` does
    /// not prove that a sub-expression is guaranteed to be reachable.
    prover: Prover<'ctx>,
}

impl<'smt, 'ctx> Unfolder<'smt, 'ctx> {
    pub fn new(limits_ref: LimitsRef, ctx: &'smt SmtCtx<'ctx>) -> Self {
        Unfolder {
            limits_ref,
            subst: Subst::new(ctx.tcx()),
            translate: TranslateExprs::new(ctx),
            prover: Prover::new(ctx.ctx()),
        }
    }

    /// Call `f` surrounded by `push()` and `pop()` calls to the prover.
    fn with_prover_scope<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.prover.push();
        let res = f(self);
        self.prover.pop();
        res
    }

    /// Check whether `expr` is currently satisfiable. If `expr` is
    /// unsatisfiable, return `None`. If it is satisfiable, then call `callback`
    /// assuming `expr` is true.
    fn with_sat<T>(&mut self, expr: &Expr, callback: impl FnOnce(&mut Self) -> T) -> Option<T> {
        let expr_z3 = self.translate.t_bool(expr);

        // first add potential new assumptions obtained from `expr`'s
        // translation to the solver.

        // TODO: the local scope is unnecessarily repeatedly added to the
        // solver.
        self.translate
            .local_scope()
            .add_assumptions_to_prover(&mut self.prover);

        self.with_prover_scope(|this| {
            this.prover.add_assumption(&expr_z3);
            tracing::trace!(expr_z3=%expr_z3, "added expr to unfolder solver");
            // here we want to do a SAT check and not a proof search. if the
            // expression is e.g. `false`, then we want to get `Unsat` from the
            // solver and not `Proof`!
            if this.prover.check_sat() == SatResult::Unsat {
                tracing::trace!(solver=%this.prover.solver(), "eliminated zero expr");
                None
            } else {
                Some(callback(this))
            }
        })
    }

    /// With the knowledge that `expr` is not bottom, evaluate `callback`.
    /// However, if `expr` can not be bottom, then return `None` and don't
    /// evaluate the `callback`.
    fn with_nonbot<T>(&mut self, expr: &Expr, callback: impl FnOnce(&mut Self) -> T) -> Option<T> {
        match &expr.kind {
            ExprKind::Unary(un_op, operand) => match un_op.node {
                UnOpKind::Embed | UnOpKind::Iverson => {
                    // If an embed or Iverson expression are nonzero, we know
                    // the Boolean expression must be true.
                    return self.with_sat(operand, callback);
                }
                _ => {}
            },
            _ if is_bot_lit(expr) => return None,
            _ => {}
        }
        Some(callback(self))
    }

    /// With the knowledge that `expr` is not top, evaluate `callback`. However,
    /// if `expr` can not be top, then return `None` and don't evaluate the
    /// `callback`.
    fn with_nontop<T>(&mut self, expr: &Expr, callback: impl FnOnce(&mut Self) -> T) -> Option<T> {
        match &expr.kind {
            ExprKind::Unary(un_op, operand) => {
                if let UnOpKind::Embed = un_op.node {
                    // If an embed expression is not top, then its Boolean
                    // condition must be false.
                    return self.with_sat(&negate_expr(operand.clone()), callback);
                }
            }
            _ if is_top_lit(expr) => return None,
            _ => {}
        }
        Some(callback(self))
    }
}

impl<'smt, 'ctx> VisitorMut for Unfolder<'smt, 'ctx> {
    type Err = LimitError;

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        self.limits_ref.check_limits()?;

        let span = e.span;
        let ty = e.ty.clone().unwrap();
        match &mut e.deref_mut().kind {
            ExprKind::Var(ident) => {
                if let Some(subst) = self.subst.lookup_var(*ident) {
                    *e = subst.clone()
                }
                Ok(())
            }
            ExprKind::Subst(ident, subst, expr) => {
                self.visit_expr(subst)?;
                self.subst.push_subst(*ident, subst.clone());
                self.visit_expr(expr)?;
                self.subst.pop();
                *e = expr.clone(); // TODO: this is an unnecessary clone
                Ok(())
            }
            ExprKind::Ite(cond, lhs, rhs) => {
                self.visit_expr(cond)?;
                let notfalse_res = self.with_sat(cond, |this| this.visit_expr(lhs));
                if let Some(res) = notfalse_res {
                    res?;
                    let neg_cond = negate_expr(cond.clone());
                    let notfalse_res = self.with_sat(&neg_cond, |this| this.visit_expr(rhs));
                    if let Some(res) = notfalse_res {
                        res
                    } else {
                        *e = lhs.clone();
                        Ok(())
                    }
                } else {
                    *e = rhs.clone();
                    self.visit_expr(e)
                }
            }
            ExprKind::Binary(bin_op, lhs, rhs) => match bin_op.node {
                BinOpKind::Mul if matches!(ty, TyKind::Bool | TyKind::UReal | TyKind::EUReal) => {
                    // visit lhs normally first
                    self.visit_expr(lhs)?;
                    // visit the rhs with the knowledge that lhs will be nonzero
                    let nonzero_res = self.with_nonbot(lhs, |this| this.visit_expr(rhs));
                    // evaluate the res or set to constant bottom
                    if let Some(res) = nonzero_res {
                        res
                    } else {
                        let builder = ExprBuilder::new(Span::dummy_span());
                        *e = builder.bot_lit(&ty);
                        Ok(())
                    }
                }
                BinOpKind::Impl | BinOpKind::Compare
                    if matches!(ty, TyKind::Bool | TyKind::EUReal) =>
                {
                    // visit lhs normally first
                    self.visit_expr(lhs)?;
                    // visit the rhs with the knowledge that lhs will be not bottom
                    let nonbot_res = self.with_nonbot(lhs, |this| this.visit_expr(rhs));
                    // evaluate the res or set to constant top
                    if let Some(res) = nonbot_res {
                        res
                    } else {
                        let builder = ExprBuilder::new(Span::dummy_span());
                        *e = builder.top_lit(&ty);
                        Ok(())
                    }
                }
                BinOpKind::CoImpl | BinOpKind::CoCompare
                    if matches!(ty, TyKind::Bool | TyKind::EUReal) =>
                {
                    // visit lhs normally first
                    self.visit_expr(lhs)?;
                    // visit the rhs with the knowledge that lhs will be not top
                    let nontop_res = self.with_nontop(lhs, |this| this.visit_expr(rhs));
                    // evaluate the res or set to constant bot
                    if let Some(res) = nontop_res {
                        res
                    } else {
                        let builder = ExprBuilder::new(Span::dummy_span());
                        *e = builder.bot_lit(&ty);
                        Ok(())
                    }
                }
                _ => walk_expr(self, e),
            },
            ExprKind::Quant(_, quant_vars, _, expr) => {
                self.subst.push_quant(
                    span.variant(SpanVariant::Qelim),
                    quant_vars,
                    self.translate.ctx.tcx(),
                );
                let scope = self.translate.push();

                self.prover.push();
                // we could also add the assumptions before the prover.push()
                // call, but then we're risking re-adding the same assumptions
                // over and over again. The SmtScope structure doesn't
                // deduplicate those yet and I'm not sure Z3 does either.
                scope.add_assumptions_to_prover(&mut self.prover);

                for quant_var in quant_vars {
                    self.translate.fresh(quant_var.name());
                }

                self.visit_expr(expr)?;

                self.translate.pop();
                self.prover.pop();
                self.subst.pop();
                Ok(())
            }
            _ => walk_expr(self, e),
        }
    }
}

fn negate_expr(expr: Expr) -> Expr {
    Shared::new(ExprData {
        kind: ExprKind::Unary(Spanned::with_dummy_span(UnOpKind::Not), expr),
        ty: Some(TyKind::Bool),
        span: Span::dummy_span(),
    })
}

#[cfg(test)]
mod test {
    use super::Unfolder;
    use crate::{
        ast::visit::VisitorMut, fuzz_expr_opt_test, opt::fuzz_test, resource_limits::LimitsRef,
        smt::SmtCtx,
    };

    #[test]
    fn fuzz_unfolder() {
        fuzz_expr_opt_test!(|mut expr| {
            let tcx = fuzz_test::mk_tcx();
            let z3_ctx = z3::Context::new(&z3::Config::default());
            let smt_ctx = SmtCtx::new(&z3_ctx, &tcx);
            let limits_ref = LimitsRef::new(None);
            let mut unfolder = Unfolder::new(limits_ref, &smt_ctx);
            unfolder.visit_expr(&mut expr).unwrap();
            expr
        })
    }
}
