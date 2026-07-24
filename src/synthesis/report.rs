use crate::ast::{
    util::{remove_casts, strip_nonneg_cast_if_nonneg},
    visit::{walk_expr, VisitorMut},
    BinOpKind, Expr, ExprKind, Ident, Symbol, UnOpKind,
};
use crate::driver::quant_proof::QuantVcProveTask;
use crate::smt::uninterpreted::FuncEntry;
use indexmap::IndexMap;
use std::time::{Duration, Instant};

/// Counts the number of piecewise linear terms (`[guard] * polynomial`) in an expression.
pub struct PiecewiseLinearCounter {
    pub count: usize,
}

impl PiecewiseLinearCounter {
    pub fn new() -> Self {
        Self { count: 0 }
    }
}

impl VisitorMut for PiecewiseLinearCounter {
    type Err = ();

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        if let ExprKind::Binary(bin_op, lhs, _) = &expr.kind {
            if bin_op.node == BinOpKind::Mul {
                if let ExprKind::Unary(un_op, _) = &lhs.kind {
                    if un_op.node == UnOpKind::Iverson {
                        self.count += 1;
                    }
                }
            }
        }

        walk_expr(self, expr)
    }
}

/// Running counters and timings accumulated across the whole synthesis session.
/// Passed by mutable reference through template building and the CEGIS loop so
/// all stats stay together and can be printed in one place.
pub struct SynthStats {
    /// Wall-clock start of the entire synthesis run.
    pub start: Instant,
    /// Total counterexamples produced by the verifier.
    pub cex_count: usize,
    /// SAT checks spent building template expressions.
    pub template_sat_checks: usize,
    /// Time spent in template building.
    pub duration_template_build: Duration,
    /// Outer refinement iterations triggered by the close-CEX heuristic.
    pub close_cex_refinements: usize,
}

impl SynthStats {
    pub fn new() -> Self {
        SynthStats {
            start: Instant::now(),
            cex_count: 0,
            template_sat_checks: 0,
            duration_template_build: Duration::ZERO,
            close_cex_refinements: 0,
        }
    }
}

pub fn print_benchmark_info(
    stats: &SynthStats,
    duration_check: Duration,
    refinement_iter: usize,
    instantiated_tasks: &[(Ident, QuantVcProveTask, usize, usize, bool)],
) {
    println!("\n=== Benchmark info ===");
    println!(
        "Total synthesis:       {:.2}s",
        stats.start.elapsed().as_secs_f64()
    );
    println!(
        "Template building:     {:.2}s",
        stats.duration_template_build.as_secs_f64()
    );
    println!(
        "Verification checks:   {:.2}s",
        duration_check.as_secs_f64()
    );
    println!("Outer iterations:      {refinement_iter}");
    println!("Close CEX refinements: {}", stats.close_cex_refinements);
    println!("Counterexamples:       {}", stats.cex_count);
    println!("SAT checks (template): {}", stats.template_sat_checks);
    for (inv_name, task, guards_before_pruning, guards_after_pruning, loop_mode) in
        instantiated_tasks
    {
        let mut counter = PiecewiseLinearCounter::new();
        counter.visit_expr(&mut task.expr.clone()).unwrap();
        let loop_extra = usize::from(*loop_mode);
        println!(
            "guards_before ({inv_name}):     {}",
            guards_before_pruning + 1 + loop_extra
        );
        println!(
            "guards_after ({inv_name}):      {}",
            guards_after_pruning + 1 + loop_extra
        );
        println!(
            "invariant_size ({inv_name}):    {}",
            counter.count + 1 + loop_extra
        );
    }
    println!("======================\n");
}

pub fn print_synthesized_bodies<'ctx>(
    instantiated_tasks: &[(Ident, QuantVcProveTask, usize, usize, bool)],
    synth_funcs: &IndexMap<Ident, &'ctx FuncEntry<'ctx>>,
    k_induction_calls: &IndexMap<Symbol, String>,
    refinement_iter: usize,
) {
    println!("Synthesized function bodies:");
    for (inv_name, task, _, _, _) in instantiated_tasks {
        let params_str = synth_funcs
            .get(inv_name)
            .map(|entry| {
                entry
                    .inputs
                    .node
                    .iter()
                    .map(|p| format!("{}: {}", p.name.name, p.ty))
                    .collect::<Vec<_>>()
                    .join(", ")
            })
            .unwrap_or_default();
        let ret_ty = task
            .expr
            .ty
            .as_ref()
            .map(|t| t.to_string())
            .unwrap_or_default();
        if let Some(inv_call) = k_induction_calls.get(&inv_name.name) {
            println!("  @k_induction({refinement_iter}, {inv_call})");
        }
        println!(
            "  syn func {}({}) : {} =\n    {}\n",
            inv_name,
            params_str,
            ret_ty,
            strip_nonneg_cast_if_nonneg(&remove_casts(&task.expr))
        );
    }
}
