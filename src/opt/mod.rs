//! This module groups various optimizations used during verification.
//!
//! The [`unfolder`] uses incremental SAT checks to unfold an expression lazily.
//! This is useful for expressions produced by the [`crate::vc`] module, which
//! contain heavy sharing and where large parts of the expression can be
//! optimized to a constant (e.g. `0`).
//!
//! The quantifier elimination pass ([`qelim`]) removes quantifiers from
//! expressions, producing equi-valid expressions.
//!
//! The module [`relational`] implements a simple visitor that reduces Gödel
//! algebra operators used in comparisons to simpler Boolean expressions.
//!
//! The [`egraph`]-based optimization searches for minimal equivalent
//! expressions by applying a set of rewrite rules repeatedly.

use crate::ast::{
    visit::{walk_expr, VisitorMut},
    Expr, ExprKind, UnOpKind,
};

pub mod boolify;
pub mod egraph;
#[cfg(test)]
mod fuzz_test;
pub mod qelim;
pub mod relational;
pub mod unfolder;

/// This "optimization" removes all parentheses. This makes matching easier in
/// the real optimizations.
pub struct RemoveParens;

impl VisitorMut for RemoveParens {
    type Err = ();

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        match &mut e.kind {
            ExprKind::Unary(un_op, operand) if un_op.node == UnOpKind::Parens => {
                walk_expr(self, operand)?;
                *e = operand.clone();
                Ok(())
            }
            _ => walk_expr(self, e),
        }
    }
}
