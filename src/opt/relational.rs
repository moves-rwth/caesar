//! Decomposition of expressions with HeyLo operators like Gödel implication or
//! binary infimum into simpler Boolean formulas.

use std::mem;

use num::Zero;

use crate::ast::{
    util::{is_bot_lit, is_top_lit},
    visit::{walk_expr, VisitorMut},
    BinOpKind, Expr, ExprBuilder, ExprKind, Span, TyKind, UnOpKind,
};

pub struct Relational;

impl VisitorMut for Relational {
    type Err = ();

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        let span = expr.span;
        #[allow(clippy::single_match)]
        match &mut expr.kind {
            ExprKind::Binary(ref mut bin_op, ref mut lhs, ref mut rhs) => match bin_op.node {
                BinOpKind::Le => {
                    self.visit_expr(lhs)?;
                    self.visit_expr(rhs)?;
                    let new_expr = relational_leq(span, lhs, rhs);
                    *expr = new_expr;
                    return Ok(());
                }
                BinOpKind::Ge => {
                    bin_op.node = BinOpKind::Le;
                    mem::swap(lhs, rhs);
                    return self.visit_expr(expr);
                }
                BinOpKind::Eq => {
                    if is_top_lit(lhs) {
                        bin_op.node = BinOpKind::Le;
                        return self.visit_expr(expr);
                    } else if is_bot_lit(lhs) {
                        bin_op.node = BinOpKind::Ge;
                        return self.visit_expr(expr);
                    }
                }
                _ => {}
            },
            _ => {}
        };
        walk_expr(self, expr)
    }
}

fn relational_leq(span: Span, lower: &Expr, upper: &Expr) -> Expr {
    let builder = ExprBuilder::new(span);
    let bool_ty = Some(TyKind::Bool);

    // First match on the upper expression (this is for lower bound proofs/down).
    match &upper.kind {
        _ if is_top_lit(upper) => return builder.bool_lit(true),
        // _ => is_bot_lit(&upper) => {
        //     let zero = builder.frac_lit(Zero::zero());
        //     return builder.binary(BinOpKind::Eq, bool_ty, lower.clone(), zero);
        // }
        ExprKind::Binary(bin_op, lhs, rhs) => match bin_op.node {
            BinOpKind::Inf => {
                let a = relational_leq(upper.span, lower, lhs);
                let b = relational_leq(upper.span, lower, rhs);
                return builder.binary(BinOpKind::And, bool_ty, a, b);
            }
            BinOpKind::Sup => {
                let a = relational_leq(upper.span, lower, lhs);
                let b = relational_leq(upper.span, lower, rhs);
                return builder.binary(BinOpKind::Or, bool_ty, a, b);
            }
            BinOpKind::Impl => {
                let a = relational_leq(upper.span, lower, rhs);
                let b = relational_leq(upper.span, lhs, rhs);
                return builder.binary(BinOpKind::Or, bool_ty, a, b);
            }
            _ => {}
        },
        ExprKind::Unary(un_op, operand) if un_op.node == UnOpKind::Not => match &lower.kind {
            ExprKind::Lit(lit) if lit.node.is_top() => {
                let zero = builder.frac_lit(Zero::zero());
                return relational_leq(upper.span, operand, &zero);
            }
            _ => {}
        },
        /*
        The following transformation is not sound, we must take care of bound variables in `lower`.
        ExprKind::Quant(quant_op, idents, operand) => match quant_op.node {
            QuantOpKind::Inf => {
                return builder.quant(QuantOpKind::Forall, idents, down(span, lower, &operand))
            }
            _ => {}
        },
        */
        _ => {}
    };

    // If we didn't get any matches for `upper`, try to match on `lower`.
    match &lower.kind {
        // ExprKind::Lit(lit) if lit.node.is_top() => {
        //     let infty = builder.infinity_lit();
        //     return builder.binary(BinOpKind::Eq, bool_ty, upper.clone(), infty);
        // },
        _ if is_bot_lit(lower) => return builder.bool_lit(true),
        ExprKind::Binary(bin_op, lhs, rhs) => match bin_op.node {
            BinOpKind::Inf => {
                let a = relational_leq(lower.span, lhs, upper);
                let b = relational_leq(lower.span, rhs, upper);
                return builder.binary(BinOpKind::Or, bool_ty, a, b);
            }
            BinOpKind::Sup => {
                let a = relational_leq(lower.span, lhs, upper);
                let b = relational_leq(lower.span, rhs, upper);
                return builder.binary(BinOpKind::And, bool_ty, a, b);
            }
            BinOpKind::CoImpl => {
                let a = relational_leq(lower.span, rhs, upper);
                let b = relational_leq(lower.span, rhs, lhs);
                return builder.binary(BinOpKind::Or, bool_ty, a, b);
            }
            BinOpKind::CoCompare => {
                let a = relational_leq(lower.span, rhs, lhs);
                let b = relational_leq(span, &builder.infinity_lit(), upper);
                return builder.binary(BinOpKind::Or, bool_ty, a, b);
            }
            _ => {}
        },
        _ => {}
    };

    // The default return value: Just a less-than-or-equal expression.
    builder.binary(BinOpKind::Le, bool_ty, lower.clone(), upper.clone())
}

#[cfg(test)]
mod test {
    use crate::{ast::visit::VisitorMut, fuzz_expr_opt_test};

    use super::Relational;

    #[test]
    fn fuzz_relational() {
        fuzz_expr_opt_test!(|mut expr| {
            Relational.visit_expr(&mut expr).unwrap();
            expr
        });
    }
}
