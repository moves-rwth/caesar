//! HeyLo quantifier elimination.

use tracing::debug;

use crate::{
    ast::{
        util::FreeVariableCollector, visit::VisitorMut, BinOpKind, Expr, ExprBuilder, ExprData,
        ExprKind, Ident, QuantOpKind, QuantVar, Span, SpanVariant, TyKind, UnOpKind, VarKind,
    },
    tyctx::TyCtx,
};

pub struct Qelim<'tcx> {
    tcx: &'tcx mut TyCtx,
}

impl<'tcx> Qelim<'tcx> {
    pub fn new(tcx: &'tcx mut TyCtx) -> Self {
        Qelim { tcx }
    }

    pub fn qelim_inf(&mut self, expr: &mut Expr) {
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
                BinOpKind::Mul if is_const(a) => self.qelim_inf(b),
                BinOpKind::Impl | BinOpKind::Compare => {
                    self.qelim_sup(a);
                    self.qelim_inf(b);
                }
                _ => {}
            },
            ExprKind::Unary(un_op, ref mut operand) => {
                if un_op.node == UnOpKind::Not {
                    self.qelim_sup(operand)
                }
            }
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

    pub fn qelim_sup(&mut self, expr: &mut Expr) {
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
                BinOpKind::Mul if is_const(a) => self.qelim_sup(b),
                BinOpKind::CoImpl | BinOpKind::CoCompare => {
                    self.qelim_inf(a);
                    self.qelim_sup(b);
                }
                _ => {}
            },
            ExprKind::Unary(un_op, ref mut operand) => {
                if un_op.node == UnOpKind::Non {
                    self.qelim_sup(operand)
                }
            }
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
        builder.subst_by(operand, &idents, |ident| {
            let clone_var = self.tcx.clone_var(ident, span, VarKind::Quant);
            let fresh_ident = clone_var;
            builder.var(fresh_ident, self.tcx)
        })
    }
}

// check whether an expression is constant by checking that there are no free variables.
fn is_const(expr: &mut Expr) -> bool {
    let mut visitor = FreeVariableCollector::new();
    visitor.visit_expr(expr).unwrap();
    visitor.variables.is_empty()
}
