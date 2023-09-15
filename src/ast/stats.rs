//! Visitor to track statistics about the size of a program/expressions.

use std::fmt;

use hdrhistogram::Histogram;

use crate::ast::{
    visit::{walk_expr, walk_stmt, VisitorMut},
    Expr, ExprKind, Stmt,
};

#[derive(Debug)]
pub struct Stats {
    pub num_stmts: u64,
    pub num_exprs: u64,
    pub num_quants: u64,
    depths: Histogram<u64>,
}

impl Stats {
    pub fn depths_summary(&self) -> HistogramSummary {
        HistogramSummary::new(&self.depths)
    }
}

impl Default for Stats {
    fn default() -> Self {
        Self {
            num_stmts: 0,
            num_exprs: 0,
            num_quants: 0,
            depths: Histogram::new(0).unwrap(),
        }
    }
}

impl fmt::Display for Stats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[num_stmts={num_stmts} num_exprs={num_exprs} num_quants={num_quants} depths={depths}]",
            num_stmts = self.num_stmts,
            num_exprs = self.num_exprs,
            num_quants = self.num_quants,
            depths = self.depths_summary(),
        )
    }
}

/// A very simple visitor to track statistics. Because I am lazy, it only
/// implements VisitorMut, and therefore mutable references to everything, even
/// though that's not needed for statistics collection.
#[derive(Default)]
pub struct StatsVisitor {
    depth: u64,
    pub stats: Stats,
}

impl VisitorMut for StatsVisitor {
    type Err = ();

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        self.stats.num_stmts += 1;
        walk_stmt(self, s)
    }

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        self.depth += 1;
        self.stats.num_exprs += 1;
        match &e.kind {
            ExprKind::Quant(_, _, _) => {
                self.stats.num_quants += 1;
            }
            ExprKind::Var(_) | ExprKind::Lit(_) => {
                self.stats.depths += self.depth;
            }
            _ => {}
        };
        let res = walk_expr(self, e);
        self.depth -= 1;
        res
    }
}

/// Stores some bits of information about the distribution of durations in a histogram.
pub struct HistogramSummary {
    pub len: u64,
    pub mean: f64,
    pub low: u64,
    pub high: u64,
    pub stdev: f64,
    pub p50: u64,
    pub p90: u64,
    pub p99: u64,
}

impl HistogramSummary {
    fn new(h: &Histogram<u64>) -> Self {
        HistogramSummary {
            len: h.len(),
            mean: h.mean(),
            low: h.min(),
            high: h.max(),
            stdev: h.stdev(),
            p50: h.value_at_quantile(0.5),
            p90: h.value_at_quantile(0.90),
            p99: h.value_at_quantile(0.99),
        }
    }
}

impl fmt::Display for HistogramSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[n={len} m={mean:.3} σ={stdev:.3} [{low}, {high}] p50={p50} p90={p90} p99={p99}]",
            len = self.len,
            mean = self.mean,
            low = self.low,
            high = self.high,
            stdev = self.stdev,
            p50 = self.p50,
            p90 = self.p90,
            p99 = self.p99,
        )
    }
}
