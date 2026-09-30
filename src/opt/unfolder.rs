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

use std::{ops::DerefMut, time::Duration};

use z3::SatResult;
use z3rro::prover::{IncrementalMode, Prover};

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

use crate::smt::translate_exprs::TranslateExprs;

/// Reachability checks are optional optimizations and should stay cheap.
const REACHABILITY_TIMEOUT: Duration = Duration::from_millis(10);

/// An assumed predicate on an expression's lattice value.
enum Guard<'a> {
    /// The expression equals top.
    Top(&'a Expr),
    /// The expression equals bottom.
    Bot(&'a Expr),
    /// The expression differs from bottom.
    NonBot(&'a Expr),
    /// The expression differs from top.
    NonTop(&'a Expr),
}

#[derive(Debug, PartialEq, Eq)]
enum UnfoldResult {
    /// Traversal completed, including when reachability was inconclusive.
    Done,
    /// The guard was proved impossible, so the expression was not visited.
    Unreachable,
}

impl UnfoldResult {
    fn is_unreachable(&self) -> bool {
        matches!(self, Self::Unreachable)
    }
}

pub struct Unfolder<'smt, 'ctx> {
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
        // it's important that we use the native incremental mode here, because
        // the performance benefit from the unfolder relies on many very fast
        // SAT checks.
        let prover = Prover::new(ctx.ctx(), IncrementalMode::Native);

        Unfolder {
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

    /// Return the local query budget, or `None` when too little time remains for a bounded Z3 call.
    fn reachability_timeout(&self) -> Result<Option<Duration>, LimitError> {
        let limits_ref = &self.subst.limits_ref;
        limits_ref.check_limits()?;
        let timeout = limits_ref
            .time_left()
            .map_or(REACHABILITY_TIMEOUT, |remaining| {
                remaining.min(REACHABILITY_TIMEOUT)
            });

        // Z3 treats a timeout rounded down to zero milliseconds as unlimited.
        if timeout < Duration::from_millis(1) {
            limits_ref.check_limits()?;
            tracing::trace!("skipping unfolder query with less than one millisecond remaining");
            return Ok(None);
        }

        Ok(Some(timeout))
    }

    /// Check satisfiability of the current assumptions within the local time budget.
    /// Propagate global resource-limit errors.
    fn check_sat(&mut self) -> Result<SatResult, LimitError> {
        let Some(timeout) = self.reachability_timeout()? else {
            return Ok(SatResult::Unknown);
        };
        self.prover.set_timeout(timeout);
        let result = self.prover.check_sat();
        self.subst.limits_ref.check_limits()?;
        if result == SatResult::Unknown {
            tracing::trace!(reason = ?self.prover.get_reason_unknown(), "inconclusive unfolder query; retaining branch");
        }
        Ok(result)
    }

    /// Unfold `expr` using cheap facts implied by `guard`.
    /// Return `Unreachable` without visiting `expr` only when the guard is proved impossible.
    fn unfold_under(
        &mut self,
        expr: &mut Expr,
        guard: Guard<'_>,
    ) -> Result<UnfoldResult, LimitError> {
        self.subst.limits_ref.check_limits()?;

        // Extract a cheap Boolean condition, or rule out a contradictory literal guard.
        let condition = match guard {
            Guard::Top(value) => match &value.ty {
                // Boolean top is true, so the value itself is the condition.
                Some(TyKind::Bool) => Some(value.clone()),
                _ => None,
            },
            Guard::Bot(value) => match &value.ty {
                // Boolean bottom is false, so negate the value.
                Some(TyKind::Bool) => Some(negate_expr(value.clone())),
                _ => None,
            },
            Guard::NonBot(value) => {
                if is_bot_lit(value) {
                    return Ok(UnfoldResult::Unreachable);
                }
                match &value.kind {
                    ExprKind::Unary(op, operand) => match op.node {
                        // Both ?(b) and [b] are nonzero exactly when b is true.
                        UnOpKind::Embed | UnOpKind::Iverson => Some(operand.clone()),
                        _ => None,
                    },
                    _ => None,
                }
            }
            Guard::NonTop(value) => {
                if is_top_lit(value) {
                    return Ok(UnfoldResult::Unreachable);
                }
                match &value.kind {
                    ExprKind::Unary(op, operand) => match op.node {
                        // ?(b) is below top exactly when b is false.
                        UnOpKind::Embed => Some(negate_expr(operand.clone())),
                        _ => None,
                    },
                    _ => None,
                }
            }
        };

        let Some(condition) = condition else {
            self.visit_expr(expr)?;
            return Ok(UnfoldResult::Done);
        };
        let condition_z3 = self.translate.t_bool(&condition);

        // Add translation assumptions before the temporary guard scope.
        // TODO: the local scope is unnecessarily repeatedly added to the solver.
        self.translate
            .local_scope()
            .add_assumptions_to_prover(&mut self.prover);

        self.with_prover_scope(|this| {
            this.prover.add_assumption(&condition_z3);
            tracing::trace!(condition = %condition_z3, "added guard to unfolder solver");
            if this.check_sat()? == SatResult::Unsat {
                tracing::trace!(solver = ?this.prover, "skipping unreachable expression");
                Ok(UnfoldResult::Unreachable)
            } else {
                this.visit_expr(expr)?;
                Ok(UnfoldResult::Done)
            }
        })
    }
}

impl<'smt, 'ctx> VisitorMut for Unfolder<'smt, 'ctx> {
    type Err = LimitError;

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        self.subst.limits_ref.check_limits()?;

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
                let result = self.visit_expr(expr);
                self.subst.pop();
                result?;
                *e = expr.clone(); // TODO: this is an unnecessary clone
                Ok(())
            }
            ExprKind::Ite(cond, lhs, rhs) => {
                self.visit_expr(cond)?;
                if self.unfold_under(lhs, Guard::Top(cond))?.is_unreachable() {
                    *e = rhs.clone();
                    return self.visit_expr(e);
                }
                if self.unfold_under(rhs, Guard::Bot(cond))?.is_unreachable() {
                    *e = lhs.clone();
                }
                Ok(())
            }
            ExprKind::Binary(bin_op, lhs, rhs) => match bin_op.node {
                BinOpKind::Mul if matches!(ty, TyKind::Bool | TyKind::UReal | TyKind::EUReal) => {
                    // visit lhs normally first
                    self.visit_expr(lhs)?;
                    // visit the rhs with the knowledge that lhs will be nonzero
                    if self.unfold_under(rhs, Guard::NonBot(lhs))?.is_unreachable() {
                        let builder = ExprBuilder::new(Span::dummy_span());
                        *e = builder.bot_lit(&ty);
                    }
                    Ok(())
                }
                BinOpKind::Impl | BinOpKind::Compare
                    if matches!(ty, TyKind::Bool | TyKind::EUReal) =>
                {
                    // visit lhs normally first
                    self.visit_expr(lhs)?;
                    // visit the rhs with the knowledge that lhs will be not bottom
                    if self.unfold_under(rhs, Guard::NonBot(lhs))?.is_unreachable() {
                        let builder = ExprBuilder::new(Span::dummy_span());
                        *e = builder.top_lit(&ty);
                    }
                    Ok(())
                }
                BinOpKind::CoImpl | BinOpKind::CoCompare
                    if matches!(ty, TyKind::Bool | TyKind::EUReal) =>
                {
                    // visit lhs normally first
                    self.visit_expr(lhs)?;
                    // visit the rhs with the knowledge that lhs will be not top
                    if self.unfold_under(rhs, Guard::NonTop(lhs))?.is_unreachable() {
                        let builder = ExprBuilder::new(Span::dummy_span());
                        *e = builder.bot_lit(&ty);
                    }
                    Ok(())
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

                let result = self.visit_expr(expr);

                self.translate.pop();
                self.prover.pop();
                self.subst.pop();
                result
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
        ast::visit::VisitorMut,
        fuzz_expr_opt_test,
        opt::fuzz_test,
        resource_limits::LimitsRef,
        smt::{
            funcs::{axiomatic::AxiomaticFunctionEncoder, FunctionEncoder},
            DepConfig, SmtCtx,
        },
    };

    #[test]
    fn fuzz_unfolder() {
        fuzz_expr_opt_test!(|mut expr| {
            let tcx = fuzz_test::mk_tcx();
            let z3_ctx = z3::Context::new(&z3::Config::default());
            let smt_ctx = SmtCtx::new(
                &z3_ctx,
                &tcx,
                AxiomaticFunctionEncoder::default().into_boxed(),
                DepConfig::All,
            );
            let limits_ref = LimitsRef::new(None, None);
            let mut unfolder = Unfolder::new(limits_ref, &smt_ctx);
            unfolder.visit_expr(&mut expr).unwrap();
            expr
        })
    }
}
