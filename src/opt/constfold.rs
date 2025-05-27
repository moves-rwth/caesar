//! Constant folding for expressions. This is not very relevant for the SMT
//! solver backend, but useful to be used the verification condition explanation
//! UI for the user.

use num::{BigRational, FromPrimitive, One, Zero};
use z3rro::eureal::ConcreteEUReal;

use crate::ast::{
    util::{is_bot_lit, is_top_lit},
    visit::{walk_expr, VisitorMut},
    BinOpKind, Expr, ExprBuilder, ExprKind, LitKind, TyKind, UnOpKind,
};

/// Currently very naive constant folding implementation that does bottom-up
/// expression constant folding. It works very well for expressions like `1 + 2`
/// (simplified to `3`). However, expressions like `(x + 1) + 1` are not
/// simplified because the inner `x + 1` expression is not constant and we can
/// therefore not rewrite to `x + 2`.
pub struct ConstFold;

impl VisitorMut for ConstFold {
    type Err = ();

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        walk_expr(self, e)?;

        let builder = ExprBuilder::new(e.span);
        let ty = &e.ty.clone().unwrap();
        match &mut e.kind {
            ExprKind::Binary(op, lhs, rhs) => {
                match op.node {
                    BinOpKind::Add | BinOpKind::Sub => {
                        if is_zero_lit(lhs) {
                            *e = rhs.clone();
                        } else if is_zero_lit(rhs) {
                            *e = lhs.clone();
                        }
                    }
                    BinOpKind::Mul => {
                        if is_zero_lit(lhs) || is_zero_lit(rhs) {
                            if matches!(
                                ty,
                                TyKind::Bool
                                    | TyKind::UInt
                                    | TyKind::UReal
                                    | TyKind::EUReal
                                    | TyKind::Int
                                    | TyKind::Real
                            ) {
                                *e = builder.one_lit(ty);
                            }
                        } else if is_one_lit(lhs) {
                            *e = rhs.clone();
                        } else if is_one_lit(rhs) {
                            *e = lhs.clone();
                        }
                    }
                    BinOpKind::Div => {
                        if is_zero_lit(lhs) {
                            *e = builder.zero_lit(e.ty.as_ref().unwrap());
                        } else if is_one_lit(rhs) {
                            *e = lhs.clone();
                        }
                    }
                    BinOpKind::And | BinOpKind::Inf => {
                        if is_bot_lit(lhs) || is_bot_lit(rhs) {
                            *e = builder.bot_lit(e.ty.as_ref().unwrap());
                        } else if is_top_lit(lhs) {
                            *e = rhs.clone();
                        } else if is_top_lit(rhs) {
                            *e = lhs.clone();
                        }
                    }
                    BinOpKind::Or | BinOpKind::Sup => {
                        if is_top_lit(lhs) || is_top_lit(rhs) {
                            *e = builder.top_lit(e.ty.as_ref().unwrap());
                        } else if is_bot_lit(lhs) {
                            *e = rhs.clone();
                        } else if is_bot_lit(rhs) {
                            *e = lhs.clone();
                        }
                    }
                    _ => {}
                };
            }
            ExprKind::Unary(op, expr) => {
                match op.node {
                    UnOpKind::Not => {
                        if is_zero_lit(expr) {
                            *e = builder.top_lit(ty);
                        }
                        // TODO: handle non-bot literal
                    }
                    UnOpKind::Non => {
                        if is_top_lit(expr) {
                            *e = builder.bot_lit(ty);
                        }
                        // TODO: handle non-top literal
                    }
                    UnOpKind::Embed => {
                        if is_bot_lit(expr) {
                            *e = builder.zero_lit(ty);
                        } else if is_top_lit(expr) {
                            *e = builder.top_lit(ty);
                        }
                    }
                    UnOpKind::Iverson => {
                        if is_zero_lit(expr) {
                            *e = builder.zero_lit(ty);
                        } else if is_one_lit(expr) {
                            *e = builder.one_lit(ty);
                        }
                    }
                    UnOpKind::Parens => {
                        // Parens are just a no-op, so we can remove them.
                        *e = expr.clone();
                    }
                }
            }
            _ => {}
        }

        if let ExprKind::Binary(op, ref lhs, ref rhs) = e.kind {
            if let Some(const_expr) = const_binop(builder, ty, op.node, lhs, rhs) {
                *e = const_expr;
            }
        }

        Ok(())
    }
}

fn is_zero_lit(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Lit(lit) => match &lit.node {
            LitKind::UInt(v) => *v == 0,
            LitKind::Frac(ratio) => Zero::is_zero(ratio),
            _ => false,
        },
        ExprKind::Cast(inner) => is_zero_lit(inner),
        _ => false,
    }
}

fn is_one_lit(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Lit(lit) => match &lit.node {
            LitKind::UInt(v) => *v == 1,
            LitKind::Frac(ratio) => One::is_one(ratio),
            _ => false,
        },
        ExprKind::Cast(inner) => is_one_lit(inner),
        _ => false,
    }
}

fn extract_const_number(e: &Expr) -> Option<ConcreteEUReal> {
    match &e.kind {
        ExprKind::Lit(lit) => match &lit.node {
            LitKind::UInt(v) => Some(ConcreteEUReal::Real(BigRational::from_u128(*v).unwrap())),
            LitKind::Frac(ratio) => Some(ConcreteEUReal::Real(ratio.clone())),
            LitKind::Infinity => Some(ConcreteEUReal::Infinity),
            _ => None,
        },
        ExprKind::Cast(inner) => extract_const_number(inner),
        _ => None,
    }
}

fn const_binop(
    builder: ExprBuilder,
    ty: &TyKind,
    binop: BinOpKind,
    lhs: &Expr,
    rhs: &Expr,
) -> Option<Expr> {
    let a = extract_const_number(lhs)?;
    let b = extract_const_number(rhs)?;

    if !matches!(
        lhs.ty.as_ref(),
        Some(TyKind::EUReal) | Some(TyKind::UReal) | Some(TyKind::UInt),
    ) || !matches!(
        rhs.ty.as_ref(),
        Some(TyKind::EUReal) | Some(TyKind::UReal) | Some(TyKind::UInt),
    ) {
        return None; // Only support operations on concrete numbers
    }

    let res = match binop {
        BinOpKind::Add => a + b,
        BinOpKind::Sub => (a - b)?,
        BinOpKind::Mul => a * b,
        BinOpKind::And | BinOpKind::Inf => a.min(b),
        BinOpKind::Or | BinOpKind::Sup => a.max(b),
        _ => return None, // Unsupported operation
    };

    match ty {
        TyKind::EUReal => match res {
            ConcreteEUReal::Real(ratio) => Some(builder.frac_lit(ratio)),
            ConcreteEUReal::Infinity => Some(builder.infinity_lit()),
        },
        TyKind::UReal => match res {
            ConcreteEUReal::Real(ratio) => {
                let mut e = builder.frac_lit(ratio);
                e.ty = Some(TyKind::UReal);
                Some(e)
            }
            ConcreteEUReal::Infinity => unreachable!(),
        },
        TyKind::UInt => match res {
            ConcreteEUReal::Real(ratio) => {
                let u = ratio.to_integer().try_into().unwrap();
                let mut e = builder.uint(u);
                e.ty = Some(TyKind::UInt);
                Some(e)
            }
            ConcreteEUReal::Infinity => unreachable!(),
        },
        _ => None,
    }
}
