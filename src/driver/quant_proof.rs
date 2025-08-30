//! Lowering of proofs of quantitative proofs in HeyLo to (many-sorted)
//! classical FO.

use tracing::info_span;
use z3::{Config, Context};

use crate::{
    ast::{
        stats::StatsVisitor, visit::VisitorMut, BinOpKind, Direction, Expr, ExprBuilder, Span,
        TyKind, UnOpKind,
    },
    depgraph::Dependencies,
    driver::{item::SourceUnitName, smt_proof::SmtVcProofTask},
    opt::{
        boolify::Boolify, egraph, qelim::Qelim, relational::Relational, unfolder::Unfolder,
        RemoveParens,
    },
    resource_limits::{LimitError, LimitsRef},
    smt::{
        funcs::{axiomatic::AxiomaticFunctionEncoder, fuel::literals::LiteralExprCollector},
        translate_exprs::TranslateExprs,
        DepConfig, SmtCtx,
    },
    tyctx::TyCtx,
    vc::subst::apply_subst,
    CaesarError, VerifyCommand,
};

/// Quantitative verification conditions that are to be checked.
#[derive(Debug)]
pub struct QuantVcProveTask {
    pub deps: Dependencies,
    pub direction: Direction,
    pub expr: Expr,
}

impl QuantVcProveTask {
    /// Apply unfolding to this verification conditon. If enabled, do lazy
    /// unfolding. Otherwise, eager.
    pub fn unfold(
        &mut self,
        options: &VerifyCommand,
        limits_ref: &LimitsRef,
        tcx: &TyCtx,
    ) -> Result<(), LimitError> {
        let span = info_span!("unfolding");
        let _entered = span.enter();
        if !options.opt_options.strict {
            let ctx = Context::new(&Config::default());
            let dep_config = DepConfig::SpecsOnly;
            let smt_ctx = SmtCtx::new(
                &ctx,
                tcx,
                Box::new(AxiomaticFunctionEncoder::default()),
                dep_config,
            );
            let mut unfolder = Unfolder::new(limits_ref.clone(), &smt_ctx);
            unfolder.visit_expr(&mut self.expr)
        } else {
            apply_subst(tcx, &mut self.expr, limits_ref)?;
            Ok(())
        }
    }

    /// Apply quantitative quantifier elimination.
    pub fn qelim(&mut self, tcx: &mut TyCtx, limits_ref: &LimitsRef) -> Result<(), CaesarError> {
        let mut qelim = Qelim::new(tcx);
        qelim.qelim(self);
        // Apply/eliminate substitutions again
        apply_subst(tcx, &mut self.expr, limits_ref)?;
        Ok(())
    }

    /// Trace some statistics about this vc expression.
    pub fn trace_expr_stats(&mut self) {
        let mut stats = StatsVisitor::default();
        stats.visit_expr(&mut self.expr).unwrap();
        let stats = stats.stats;
        tracing::info!(
            num_exprs = stats.num_exprs,
            num_quants = stats.num_quants,
            depths = %stats.depths_summary(),
            "Verification condition stats"
        );
        if stats.num_quants > 0 {
            tracing::warn!(
                num_quants=stats.num_quants, "Quantifiers are present in the generated verification conditions. It is possible that quantifier elimination failed. If Z3 can't decide the problem, this may be the reason."
            );
        }
    }

    /// Create a verification condition describing that one entails the other.
    ///
    /// This assumes `Self` has [Direction::Up] and the other has
    /// [Direction::Down].
    pub fn entails(self, other: Self) -> Self {
        assert_eq!(self.direction, Direction::Up);
        assert_eq!(other.direction, Direction::Down);
        let builder = ExprBuilder::new(Span::dummy_span());
        let expr = builder.binary(
            BinOpKind::Impl,
            Some(self.expr.ty.clone().unwrap()),
            self.expr,
            other.expr,
        );
        QuantVcProveTask {
            deps: self.deps.union(other.deps),
            direction: Direction::Down,
            expr,
        }
    }

    /// Convert his verification condition into a Boolean query of the form `top
    /// == expr`.
    pub fn into_bool_vc(self) -> BoolVcProveTask {
        let builder = ExprBuilder::new(Span::dummy_span());
        let terminal = builder.top_lit(self.expr.ty.as_ref().unwrap());
        let mut expr = self.expr.clone();

        // Instead of comparing the negated expr to infinity, we should just
        // compare expr to zero for upper bounds. Unfortunately this introduces
        // regressions that I don't know how to debug right now.
        //
        // TODO: figure out what's happening
        if self.direction == Direction::Up {
            expr = builder.unary(UnOpKind::Not, Some(expr.ty.clone().unwrap()), expr);
        }
        let res = builder.binary(BinOpKind::Eq, Some(TyKind::Bool), terminal, expr);
        BoolVcProveTask {
            quant_vc: self,
            vc: res,
        }
    }
}

/// The next step is a Boolean verification condition - it represents that the
/// quantative verification conditions are true/false depending on the direction.
#[derive(Debug)]
pub struct BoolVcProveTask {
    quant_vc: QuantVcProveTask,
    vc: Expr,
}

impl BoolVcProveTask {
    /// E-Graph simplifications. They're not being used at the moment and are
    /// very limited.
    pub fn egraph_simplify(&self) {
        egraph::simplify(&self.vc);
    }

    /// Removing parentheses before optimizations.
    pub fn remove_parens(&mut self) {
        RemoveParens.visit_expr(&mut self.vc).unwrap();
    }

    /// Apply the "boolify" optimization.
    pub fn opt_boolify(&mut self) {
        let span = info_span!("boolify");
        let _entered = span.enter();
        (Boolify {}).visit_expr(&mut self.vc).unwrap();
    }

    /// Apply the "relational" optimization.
    pub fn opt_relational(&mut self) {
        let span = info_span!("relationalize");
        let _entered = span.enter();
        (Relational {}).visit_expr(&mut self.vc).unwrap();
    }

    /// Print the theorem to prove.
    pub fn print_theorem(&self, name: &SourceUnitName) {
        println!("{}: Theorem to prove:\n{}\n", name, &self.vc);
    }

    /// Get the dependencies of this verification condition.
    pub fn get_dependencies(&self) -> &Dependencies {
        &self.quant_vc.deps
    }

    /// Translate to SMT.
    pub fn into_smt_vc<'smt, 'ctx>(
        mut self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
    ) -> SmtVcProofTask<'ctx> {
        let span = info_span!("translation to Z3");
        let _entered = span.enter();

        if translate.ctx.lit_wrap {
            let literal_exprs =
                LiteralExprCollector::new(translate.ctx).collect_literals(&mut self.vc);
            translate.set_literal_exprs(literal_exprs);
        }

        let bool_vc = translate.t_bool(&self.vc);

        if translate.ctx.lit_wrap {
            translate.set_literal_exprs(Default::default());
        }

        SmtVcProofTask {
            quant_vc: self.quant_vc,
            vc: bool_vc,
        }
    }
}
