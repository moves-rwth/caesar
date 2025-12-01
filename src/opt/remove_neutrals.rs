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
use z3rro::prover::{IncrementalMode, Prover};

use crate::{
    ast::{
        util::{is_bot_lit, is_one_lit, is_top_lit, is_zero_lit},
        visit::{walk_expr, VisitorMut},
        BinOpKind, Expr, ExprBuilder, ExprData, ExprKind, Shared, Span, SpanVariant, Spanned,
        TyKind, UnOpKind,
    },
    resource_limits::{LimitError, LimitsRef},
    smt::SmtCtx,
    vc::subst::Subst,
};

use crate::smt::translate_exprs::TranslateExprs;

pub struct NeutralsRemover<'smt, 'ctx> {
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

impl<'smt, 'ctx> NeutralsRemover<'smt, 'ctx> {
    pub fn new(limits_ref: LimitsRef, ctx: &'smt SmtCtx<'ctx>) -> Self {
        // it's important that we use the native incremental mode here, because
        // the performance benefit from the neutrals_remover relies on many very fast
        // SAT checks.
        let prover = Prover::new(ctx.ctx(), IncrementalMode::Native);

        NeutralsRemover {
            subst: Subst::new(ctx.tcx(), &limits_ref),
            translate: TranslateExprs::new(ctx),
            prover,
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
            tracing::trace!(expr_z3=%expr_z3, "added expr to neutrals_remover solver");
            // here we want to do a SAT check and not a proof search. if the
            // expression is e.g. `false`, then we want to get `Unsat` from the
            // solver and not `Proof`!
            if this.prover.check_sat() == SatResult::Unsat {
                tracing::trace!(solver=?this.prover, "eliminated zero expr");
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
                UnOpKind::Parens => {
                    return self.with_nonbot(operand, callback);
                }
                _ => {}
            },
            _ if is_bot_lit(expr) => return None,
            _ => {}
        }
        Some(callback(self))
    }

    fn with_nonzero<T>(&mut self, expr: &Expr, callback: impl FnOnce(&mut Self) -> T) -> Option<T> {
        match &expr.kind {
            ExprKind::Unary(un_op, operand) => match un_op.node {
                UnOpKind::Embed | UnOpKind::Iverson => {
                    // If an embed or Iverson expression are nonzero, we know
                    // the Boolean expression must be true.
                    return self.with_sat(operand, callback);
                }
                UnOpKind::Parens => {
                    return self.with_nonzero(operand, callback);
                }
                _ => {}
            },
            _ if is_zero_lit(expr) => return None,
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
impl<'smt, 'ctx> VisitorMut for NeutralsRemover<'smt, 'ctx> {
    type Err = LimitError;

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        self.subst.limits_ref.check_limits()?;
        let ty = e.ty.clone().unwrap();

        match &mut e.deref_mut().kind {
            // ----- variable subst -----
            ExprKind::Var(ident) => {
                if let Some(subst) = self.subst.lookup_var(*ident) {
                    *e = subst.clone();
                }
                Ok(())
            }

            // ----- subst node -----
            ExprKind::Subst(ident, subst, body) => {
                self.visit_expr(subst)?;
                self.subst.push_subst(*ident, subst.clone());
                self.visit_expr(body)?;
                self.subst.pop();
                *e = body.clone();
                Ok(())
            }

            // ----- binary operators -----
            ExprKind::Binary(bin_op, lhs, rhs) => {
                // Always visit children first
                self.visit_expr(lhs)?;
                self.visit_expr(rhs)?;

                use BinOpKind::*;

                match bin_op.node {
                    // --------------------------
                    // MUL: remove 1
                    // --------------------------
                    Mul => {
                        if is_one_lit(lhs) {
                            *e = rhs.clone();
                            return Ok(());
                        }
                        if is_one_lit(rhs) {
                            *e = lhs.clone();
                            return Ok(());
                        }
                        Ok(())
                    }

                    // --------------------------
                    // ADD: remove 0
                    // --------------------------
                    Add => {
                        if is_zero_lit(lhs) {
                            *e = rhs.clone();
                            return Ok(());
                        }
                        if is_zero_lit(rhs) {
                            *e = lhs.clone();
                            return Ok(());
                        }
                        Ok(())
                    }

                    // --------------------------
                    // AND: remove true
                    // --------------------------
                    BinOpKind::And => {
                        // Visit children first
                        self.visit_expr(lhs)?;
                        self.visit_expr(rhs)?;

                        // 1) bottom(lhs) → result is bottom
                        let nonbot:  Option<Result<(), LimitError>> = self.with_nonbot(lhs, |_| Ok(()));
                        if nonbot.is_none() {
                            let b = ExprBuilder::new(e.span);
                            *e = b.bot_lit(&ty);
                            return Ok(());
                        }

                        // 2) lhs == true (top) → result = rhs
                        let nontop:  Option<Result<(), LimitError>> = self.with_nontop(lhs, |_| Ok(()));
                        if nontop.is_none() {
                            *e = rhs.clone();
                            return Ok(());
                        }

                        // 3) NEW: if lhs ⇒ rhs, remove rhs
                        {
                            let builder = ExprBuilder::new(Span::dummy_span());

                            // build (lhs && !rhs)
                            let not_rhs = builder.unary(UnOpKind::Not, Some(ty.clone()), rhs.clone());
                            let lhs_and_not_rhs =
                                builder.binary(BinOpKind::And.into(),  Some(ty),lhs.clone(), not_rhs);

                            // unsat → implied
                            let implied = self.with_sat(&lhs_and_not_rhs, |_| ());
                            if implied.is_none() {
                                *e = lhs.clone(); // keep only lhs
                                return Ok(());
                            }
                        }

                        // 4) keep both sides
                        Ok(())
                    }

                    // --------------------------
                    // OR: remove false
                    // --------------------------
                    Or => {
                        // same bottom/top structure:
                        let nonbot: Option<Result<(), LimitError>> =
                            self.with_nonbot(lhs, |_| Ok(()));
                        if nonbot.is_none() {
                            let b = ExprBuilder::new(e.span);
                            *e = b.bot_lit(&ty);
                            return Ok(());
                        }

                        // remove neutral "false → rhs"
                        if is_bot_lit(lhs) {
                            *e = rhs.clone();
                            return Ok(());
                        }
                        if is_bot_lit(rhs) {
                            *e = lhs.clone();
                            return Ok(());
                        }

                        Ok(())
                    }

                    _ => Ok(()),
                }
            }

            // ----- default recursive walk -----
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
