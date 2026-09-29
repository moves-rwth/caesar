//! HeyLo quantifier elimination.
//!
//! Algebraic elimination preserves expression values.
//! The subsequent polarity-based elimination preserves validity.

use crate::{
    ast::{BinOpKind, Expr, ExprKind, LitKind, TyKind, UnOpKind},
    driver::quant_proof::QuantVcProveTask,
    tyctx::TyCtx,
};

mod algebraic;
mod polarity;

/// Eliminate quantifiers algebraically while preserving expression values.
/// Then eliminate quantifiers by polarity while preserving validity.
pub fn qelim(tcx: &mut TyCtx, vc_expr: &mut QuantVcProveTask) {
    algebraic::eliminate(&mut vc_expr.expr);
    polarity::eliminate(tcx, vc_expr);
}

/// A sufficient condition for the expression to be finite.
/// May return false for finite expressions.
fn is_finite(expr: &Expr) -> bool {
    if let TyKind::UInt | TyKind::UReal = expr.ty.as_ref().unwrap() {
        return true;
    }
    match &expr.kind {
        ExprKind::Binary(bin_op, lhs, rhs) => match bin_op.node {
            BinOpKind::Add | BinOpKind::Mul | BinOpKind::Sup => is_finite(lhs) && is_finite(rhs),
            BinOpKind::Inf => is_finite(lhs) || is_finite(rhs),
            BinOpKind::Sub => is_finite(lhs),
            _ => false,
        },
        ExprKind::Unary(un_op, inner) => match un_op.node {
            UnOpKind::Iverson => true,
            UnOpKind::Parens => is_finite(inner),
            _ => false,
        },
        ExprKind::Cast(inner) => is_finite(inner),
        ExprKind::Lit(lit) => matches!(&lit.node, LitKind::UInt(_) | LitKind::Frac(_)),
        _ => false,
    }
}
