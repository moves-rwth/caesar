//! HeyLo quantifier elimination.

use tracing::debug;

use crate::{
    ast::{
        BinOpKind, Direction, Expr, ExprBuilder, ExprData, ExprKind, Ident, LitKind, QuantOpKind,
        QuantVar, Span, SpanVariant, TyKind, UnOpKind, VarKind,
    },
    driver::quant_proof::QuantVcProveTask,
    tyctx::TyCtx,
};

pub struct Qelim<'tcx> {
    tcx: &'tcx TyCtx,
}

impl<'tcx> Qelim<'tcx> {
    pub fn new(tcx: &'tcx TyCtx) -> Self {
        Qelim { tcx }
    }

    pub fn qelim(&mut self, vc_expr: &mut QuantVcProveTask) {
        match vc_expr.direction {
            Direction::Down => self.qelim_inf(&mut vc_expr.expr),
            Direction::Up => self.qelim_sup(&mut vc_expr.expr),
        }
    }

    fn qelim_inf(&mut self, expr: &mut Expr) {
        if !matches!(expr.ty.as_ref().unwrap(), TyKind::Bool | TyKind::EUReal) {
            return;
        }
        let expr_data: &mut ExprData = &mut *expr;
        match &mut expr_data.kind {
            ExprKind::Var(_) => {}
            ExprKind::Call(_, _) => {}
            ExprKind::Ite(_, ref mut lhs, ref mut rhs) => {
                self.qelim_inf(lhs);
                self.qelim_inf(rhs);
            }
            ExprKind::Binary(bin_op, ref mut a, ref mut b) => match bin_op.node {
                BinOpKind::Add
                | BinOpKind::And
                | BinOpKind::Or
                | BinOpKind::Inf
                | BinOpKind::Sup => {
                    self.qelim_inf(a);
                    self.qelim_inf(b)
                }
                BinOpKind::Mul if is_finite(a) => self.qelim_inf(b),
                BinOpKind::Mul if is_finite(b) => self.qelim_inf(a),
                BinOpKind::Impl | BinOpKind::Compare => {
                    self.qelim_sup(a);
                    self.qelim_inf(b);
                }
                _ => {}
            },
            ExprKind::Unary(un_op, ref mut operand) => match un_op.node {
                UnOpKind::Not => self.qelim_sup(operand),
                UnOpKind::Parens => self.qelim_inf(operand),
                _ => {}
            },
            ExprKind::Cast(ref mut inner) => self.qelim_inf(inner),
            ExprKind::Quant(quant_op, quant_vars, _, operand) => match quant_op.node {
                QuantOpKind::Inf | QuantOpKind::Forall => {
                    self.qelim_inf(operand);
                    *expr = self.elim_quant(expr_data.span, quant_vars, operand.clone());
                }
                _ => {}
            },
            ExprKind::Subst(_, _, _) => panic!("cannot handle subst"),
            ExprKind::Lit(_) => {}
        }
    }

    fn qelim_sup(&mut self, expr: &mut Expr) {
        if !matches!(expr.ty.as_ref().unwrap(), TyKind::Bool | TyKind::EUReal) {
            return;
        }
        let expr_data: &mut ExprData = &mut *expr;
        match &mut expr_data.kind {
            ExprKind::Var(_) => {}
            ExprKind::Call(_, _) => {}
            ExprKind::Ite(_, ref mut lhs, ref mut rhs) => {
                self.qelim_sup(lhs);
                self.qelim_sup(rhs);
            }
            ExprKind::Binary(bin_op, ref mut a, ref mut b) => match bin_op.node {
                BinOpKind::Add
                | BinOpKind::And
                | BinOpKind::Or
                | BinOpKind::Inf
                | BinOpKind::Sup => {
                    self.qelim_sup(a);
                    self.qelim_sup(b)
                }
                BinOpKind::Mul if is_finite(a) => self.qelim_sup(b),
                BinOpKind::Mul if is_finite(b) => self.qelim_sup(a),
                BinOpKind::CoImpl | BinOpKind::CoCompare => {
                    self.qelim_inf(a);
                    self.qelim_sup(b);
                }
                _ => {}
            },
            ExprKind::Unary(un_op, ref mut operand) => match un_op.node {
                UnOpKind::Non => self.qelim_inf(operand),
                UnOpKind::Parens => self.qelim_sup(operand),
                _ => {}
            },
            ExprKind::Cast(ref mut inner) => self.qelim_sup(inner),
            ExprKind::Quant(quant_op, quant_vars, _, operand) => match quant_op.node {
                QuantOpKind::Sup | QuantOpKind::Exists => {
                    self.qelim_sup(operand);
                    *expr = self.elim_quant(expr_data.span, quant_vars, operand.clone());
                }
                _ => {}
            },
            ExprKind::Subst(_, _, _) => panic!("cannot handle subst"),
            ExprKind::Lit(_) => {}
        }
    }

    fn elim_quant(&mut self, span: Span, quant_vars: &[QuantVar], operand: Expr) -> Expr {
        debug!(span=?span, quant_vars=?quant_vars, "eliminating quantifier");
        let span = span.variant(SpanVariant::Qelim);
        let idents: Vec<Ident> = quant_vars
            .iter()
            .flat_map(|quant_var| match quant_var {
                QuantVar::Shadow(ident) => Some(*ident),
                QuantVar::Fresh(_) => None, // we do not need to eliminate fresh quantified variables, nice!
            })
            .collect();
        let builder = ExprBuilder::new(span);
        builder.subst_by(operand, idents.iter().cloned(), |ident| {
            let clone_var = self.tcx.clone_var(ident, span, VarKind::Quant);
            let fresh_ident = clone_var;
            builder.var(fresh_ident, self.tcx)
        })
    }
}

/// Simple heuristic to check whether an expression is always a finite number
/// (never equal to infty). May return false negatives.
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
