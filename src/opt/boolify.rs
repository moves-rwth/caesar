//! A standard set of algebraic optimizations that we call "boolification". The
//! optimizations pattern-match outside-in an replace quantitative expressions
//! by Boolean ones. Concretely, we match against expressions `e` in a context
//! of either `\top = e` or `0 = e` and simplify those.
//!
//! In contrast to the [`super::relational`] optimizations, the optimizations
//! here do not increase expression size. There might be some value in unifying
//! both modules in the future.

use crate::ast::{
    visit::{walk_expr, VisitorMut},
    BinOpKind, Expr, ExprBuilder, ExprKind, Span, SpanVariant, TyKind, UnOpKind,
};

pub struct Boolify;

impl VisitorMut for Boolify {
    type Err = ();

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        if !e.ty.as_ref().unwrap().is_complete_lattice() {
            return walk_expr(self, e);
        }

        let span = e.span;

        let res = match &mut e.kind {
            ExprKind::Binary(bin_op, lhs, rhs)
                if lhs.ty.as_ref().unwrap().is_complete_lattice() =>
            {
                match bin_op.node {
                    // match \top = rhs
                    BinOpKind::Eq if is_top_lit(lhs) => Some(self.visit_eq_top(span, rhs)?),
                    // match \bot = rhs
                    BinOpKind::Eq if is_bot_lit(lhs) => Some(self.visit_eq_bot(span, rhs)?),
                    // match lhs = \top
                    BinOpKind::Eq if is_top_lit(rhs) => Some(self.visit_eq_top(span, lhs)?),
                    // match rhs = \bot
                    BinOpKind::Eq if is_bot_lit(rhs) => Some(self.visit_eq_bot(span, lhs)?),
                    // match lhs <= rhs
                    BinOpKind::Le => Some(self.visit_leq(span, lhs, rhs)?),
                    // match lhs >= rhs
                    BinOpKind::Ge => Some(self.visit_leq(span, rhs, lhs)?),
                    // match ?(b) -> rhs, equivalent to ite(b, rhs, \top)
                    BinOpKind::Impl => {
                        self.visit_expr(lhs)?;
                        self.visit_expr(rhs)?;
                        let ty = lhs.ty.clone();
                        match &mut lhs.kind {
                            ExprKind::Unary(un_op, operand) if un_op.node == UnOpKind::Embed => {
                                let builder = ExprBuilder::new(span.variant(SpanVariant::Boolify));
                                Some(builder.ite(
                                    ty,
                                    operand.clone(),
                                    rhs.clone(),
                                    builder.top_lit(lhs.ty.as_ref().unwrap()),
                                ))
                            }
                            _ => None,
                        }
                    }
                    // match ?(b) <- rhs, equivalent to ite(b, \bot, rhs)
                    BinOpKind::CoImpl => {
                        self.visit_expr(lhs)?;
                        self.visit_expr(rhs)?;
                        let ty = lhs.ty.clone();
                        match &mut lhs.kind {
                            ExprKind::Unary(un_op, operand) if un_op.node == UnOpKind::Embed => {
                                let builder = ExprBuilder::new(span.variant(SpanVariant::Boolify));
                                Some(builder.ite(
                                    ty,
                                    operand.clone(),
                                    builder.bot_lit(lhs.ty.as_ref().unwrap()),
                                    rhs.clone(),
                                ))
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        };

        if let Some(res) = res {
            *e = res;
            Ok(())
        } else {
            walk_expr(self, e)
        }
    }
}

impl Boolify {
    fn visit_leq(&mut self, span: Span, lhs: &mut Expr, rhs: &mut Expr) -> Result<Expr, ()> {
        assert!(lhs.ty.as_ref().unwrap().is_complete_lattice());
        assert!(rhs.ty.as_ref().unwrap().is_complete_lattice());

        let builder = ExprBuilder::new(span.variant(SpanVariant::Boolify));

        // match \bot <= rhs, trivially true
        if is_bot_lit(lhs) {
            return Ok(builder.bool_lit(true));
        }
        // match \top <= rhs, equivalent to rhs = \top
        if is_top_lit(lhs) {
            return self.visit_eq_top(span, rhs);
        }
        // match lhs <= \bot, equivalent to lhs = \bot
        if is_bot_lit(rhs) {
            return self.visit_eq_bot(span, lhs);
        }
        // match lhs <= \top, trivially true
        if is_top_lit(rhs) {
            return Ok(builder.bool_lit(true));
        }

        let lhs_span = lhs.span;
        match &mut lhs.kind {
            // match ?(b) <= rhs, equivalent to b -> (rhs = \top)
            ExprKind::Unary(un_op, operand) if un_op.node == UnOpKind::Embed => {
                return Ok(builder.binary(
                    BinOpKind::Impl,
                    Some(TyKind::Bool),
                    operand.clone(),
                    self.visit_eq_top(span, rhs)?,
                ));
            }
            // match (?(a) <- b) <= rhs, equivalent to (a || (b <= rhs))
            ExprKind::Binary(bin_op, a, b) if bin_op.node == BinOpKind::CoImpl => {
                match &mut a.kind {
                    ExprKind::Unary(un_op, a) if un_op.node == UnOpKind::Embed => {
                        return Ok(builder.binary(
                            BinOpKind::Or,
                            Some(TyKind::Bool),
                            a.clone(),
                            self.visit_leq(lhs_span, b, rhs)?,
                        ));
                    }
                    _ => {}
                }
            }
            _ => {}
        }

        let rhs_span = rhs.span;
        match &mut rhs.kind {
            // match lhs <= ?(b), equivalent to !b -> (rhs = \bot), or just b ||
            // (rhs = bot)
            ExprKind::Unary(un_op, operand) if un_op.node == UnOpKind::Embed => {
                return Ok(builder.binary(
                    BinOpKind::Or,
                    Some(TyKind::Bool),
                    operand.clone(),
                    self.visit_eq_bot(span, lhs)?,
                ));
            }
            // match lhs <= (?(a) -> b), equivalent to (a -> (lhs <= b))
            ExprKind::Binary(bin_op, a, b) if bin_op.node == BinOpKind::Impl => match &mut a.kind {
                ExprKind::Unary(un_op, a) if un_op.node == UnOpKind::Embed => {
                    return Ok(builder.binary(
                        BinOpKind::Impl,
                        Some(TyKind::Bool),
                        a.clone(),
                        self.visit_leq(rhs_span, lhs, b)?,
                    ));
                }
                _ => {}
            },
            _ => {}
        }

        // no match
        self.visit_expr(lhs)?;
        self.visit_expr(rhs)?;
        Ok(builder.binary(BinOpKind::Le, Some(TyKind::Bool), lhs.clone(), rhs.clone()))
    }

    fn visit_eq_top(&mut self, span: Span, e: &mut Expr) -> Result<Expr, ()> {
        assert!(e.ty.as_ref().unwrap().is_complete_lattice());

        let inner_span = e.span;
        match &mut e.kind {
            ExprKind::Ite(cond, lhs, rhs) => {
                self.visit_expr(cond)?;
                let lhs = self.visit_eq_top(inner_span, lhs)?;
                let rhs = self.visit_eq_top(inner_span, rhs)?;
                let builder = ExprBuilder::new(inner_span.variant(SpanVariant::Boolify));
                return Ok(builder.ite(Some(TyKind::Bool), cond.clone(), lhs, rhs));
            }
            // match lhs \rightarrow rhs or lhs \searrow rhs, equivalent to lhs
            // <= rhs
            ExprKind::Binary(bin_op, lhs, rhs) => {
                match bin_op.node {
                    BinOpKind::Impl | BinOpKind::Compare => {
                        return self.visit_leq(inner_span, lhs, rhs);
                    }
                    // match lhs \cap rhs and lhs \cup rhs
                    BinOpKind::Inf | BinOpKind::Sup => {
                        let builder = ExprBuilder::new(inner_span.variant(SpanVariant::Boolify));
                        let lhs = self.visit_eq_top(inner_span, lhs)?;
                        let rhs = self.visit_eq_top(inner_span, rhs)?;
                        let operand = if bin_op.node == BinOpKind::Inf {
                            BinOpKind::And
                        } else {
                            BinOpKind::Or
                        };
                        return Ok(builder.binary(operand, lhs.ty.clone(), lhs, rhs));
                    }
                    _ => {}
                }
            }
            // match \not g
            ExprKind::Unary(un_op, ref mut operand) => {
                match un_op.node {
                    UnOpKind::Not => {
                        return self.visit_eq_bot(inner_span, operand);
                    }
                    // \top = ?(b) is equivalent to just b
                    UnOpKind::Embed => {
                        self.visit_expr(operand)?;
                        return Ok(operand.clone());
                    }
                    _ => {}
                }
            }
            _ => {}
        }

        // no match, return \top = e
        self.visit_expr(e)?;

        let builder = ExprBuilder::new(span);
        Ok(builder.binary(
            BinOpKind::Eq,
            Some(TyKind::Bool),
            builder.top_lit(e.ty.as_ref().unwrap()),
            e.clone(),
        ))
    }

    fn visit_eq_bot(&mut self, span: Span, e: &mut Expr) -> Result<Expr, ()> {
        assert!(e.ty.as_ref().unwrap().is_complete_lattice());

        let inner_span = e.span;
        match &mut e.kind {
            ExprKind::Ite(cond, lhs, rhs) => {
                self.visit_expr(cond)?;
                let lhs = self.visit_eq_bot(inner_span, lhs)?;
                let rhs = self.visit_eq_bot(inner_span, rhs)?;
                let builder = ExprBuilder::new(inner_span.variant(SpanVariant::Boolify));
                return Ok(builder.ite(Some(TyKind::Bool), cond.clone(), lhs, rhs));
            }
            ExprKind::Binary(bin_op, lhs, rhs) => {
                match bin_op.node {
                    // match lhs \leftarrow rhs or lhs \nwarrow rhs, equivalent to lhs
                    // >= rhs
                    BinOpKind::CoImpl | BinOpKind::CoCompare => {
                        return self.visit_leq(inner_span, rhs, lhs); // note that this is rhs <= lhs
                    }
                    // match lhs \cap rhs and lhs \cup rhs
                    BinOpKind::Inf | BinOpKind::Sup => {
                        let builder = ExprBuilder::new(inner_span.variant(SpanVariant::Boolify));
                        let lhs = self.visit_eq_bot(inner_span, lhs)?;
                        let rhs = self.visit_eq_bot(inner_span, rhs)?;
                        let operand = if bin_op.node == BinOpKind::Inf {
                            BinOpKind::Or
                        } else {
                            BinOpKind::And
                        };
                        return Ok(builder.binary(operand, lhs.ty.clone(), lhs, rhs));
                    }
                    _ => {}
                }
            }
            ExprKind::Unary(un_op, ref mut operand) => {
                match un_op.node {
                    // match \sim g, equivalent to g = \top
                    UnOpKind::Non => {
                        return self.visit_eq_top(inner_span, operand);
                    }
                    // \bot = ?(b) is equivalent to !b
                    UnOpKind::Embed => {
                        self.visit_expr(operand)?;
                        let builder = ExprBuilder::new(inner_span.variant(SpanVariant::Boolify));
                        return Ok(builder.unary(
                            UnOpKind::Not,
                            Some(TyKind::Bool),
                            operand.clone(),
                        ));
                    }
                    _ => {}
                }
            }
            _ => {}
        }

        // no match, return \bot = e
        self.visit_expr(e)?;

        let builder = ExprBuilder::new(span);
        Ok(builder.binary(
            BinOpKind::Eq,
            Some(TyKind::Bool),
            builder.bot_lit(e.ty.as_ref().unwrap()),
            e.clone(),
        ))
    }
}

fn is_top_lit(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Lit(lit) => lit.node.is_top(),
        _ => false,
    }
}

fn is_bot_lit(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Cast(inner) => is_bot_lit(inner),
        ExprKind::Lit(lit) => lit.node.is_bot(),
        _ => false,
    }
}

#[cfg(test)]
mod test {
    use crate::{ast::visit::VisitorMut, fuzz_expr_opt_test};

    use super::Boolify;

    #[test]
    fn fuzz_boolify() {
        fuzz_expr_opt_test!(|mut expr| {
            Boolify.visit_expr(&mut expr).unwrap();
            expr
        });
    }
}
