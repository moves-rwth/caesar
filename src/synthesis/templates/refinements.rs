use std::cmp::min;

use num::{BigInt, BigRational};

use crate::ast::{decl, BinOpKind, Expr, ExprBuilder, ExprKind, LitKind, Range, TyKind, UnOpKind};
use crate::tyctx::TyCtx;

/// Splits each range-annotated variable into `split_count` equal-width intervals and returns
/// one Boolean predicate per Cartesian-product cell. Bool vars get two regions: `var` / `!var`.
pub fn get_fix_region_splits(
    ranged_vars: &[(Expr, Range)],
    bool_vars: &[Expr],
    split_count: usize,
    builder: &mut ExprBuilder,
) -> Vec<Expr> {
    if ranged_vars.is_empty() && bool_vars.is_empty() || split_count == 0 {
        return vec![builder.bool_lit(true)];
    }

    let mut all_intervals: Vec<Vec<Expr>> = Vec::new();

    for (var, range) in ranged_vars {
        let (lo, hi) = (range.lower, range.upper);

        // A range of size 0 or 1 cannot be split; emit a single interval [lo, hi].
        if hi <= lo {
            let lo_expr = builder.signed_frac_lit(BigRational::from_integer(BigInt::from(lo)));
            let hi_expr = builder.signed_frac_lit(BigRational::from_integer(BigInt::from(hi)));
            let real_var = builder.cast(TyKind::Real, var.clone());
            let ge = builder.binary(BinOpKind::Ge, Some(TyKind::Bool), real_var.clone(), lo_expr);
            let le = builder.binary(BinOpKind::Le, Some(TyKind::Bool), real_var, hi_expr);
            all_intervals.push(vec![builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                ge,
                le,
            )]);
            continue;
        }

        let num_parts = min(hi - lo, split_count as u64);

        // Ensure the variable is in the Real domain for comparison.
        let real_var = if matches!(var.ty, Some(TyKind::Real)) {
            var.clone()
        } else {
            builder.cast(TyKind::Real, var.clone())
        };

        let mut var_intervals = Vec::new();
        for i in 1..=(num_parts) {
            let (part_lo, part_hi) = if i == 1 {
                (lo, lo + (hi - lo) / num_parts)
            } else if i < num_parts {
                (
                    1 + lo + ((i - 1) * (hi - lo) / num_parts),
                    lo + (i * (hi - lo) / num_parts),
                )
            } else {
                (1 + lo + ((i - 1) * (hi - lo) / num_parts), hi)
            };

            let lo_expr = builder.signed_frac_lit(BigRational::from_integer(BigInt::from(part_lo)));
            let hi_expr = builder.signed_frac_lit(BigRational::from_integer(BigInt::from(part_hi)));

            let ge = builder.binary(BinOpKind::Ge, Some(TyKind::Bool), real_var.clone(), lo_expr);
            let le = builder.binary(BinOpKind::Le, Some(TyKind::Bool), real_var.clone(), hi_expr);
            var_intervals.push(builder.binary(BinOpKind::And, Some(TyKind::Bool), ge, le));
        }

        all_intervals.push(var_intervals);
    }

    for var in bool_vars {
        let neg = builder.unary(UnOpKind::Not, Some(TyKind::Bool), var.clone());
        all_intervals.push(vec![var.clone(), neg]);
    }

    cartesian_and(&all_intervals, builder)
}

/// Like `get_fix_region_splits` but uses fresh synthesized boundary template variables instead of
/// equal-width arithmetic intervals. No range annotations needed. Returns `[true]` if no vars.
pub fn get_variable_region_splits(
    fvars: &[Expr],
    bool_vars: &[Expr],
    split_count: usize,
    builder: &mut ExprBuilder,
    tcx: &TyCtx,
    declare_tvar: &mut dyn FnMut(String) -> decl::VarDecl,
) -> Vec<Expr> {
    if (fvars.is_empty() || split_count <= 1) && bool_vars.is_empty() {
        return vec![builder.bool_lit(true)];
    }

    let mut all_intervals: Vec<Vec<Expr>> = Vec::new();

    for (var_idx, var) in
        fvars
            .iter()
            .enumerate()
            .take(if split_count <= 1 { 0 } else { fvars.len() })
    {
        let real_var = if matches!(var.ty, Some(TyKind::Real)) {
            var.clone()
        } else {
            builder.cast(TyKind::Real, var.clone())
        };

        // Declare split_count - 1 boundary template variables.
        let mut boundaries: Vec<Expr> = Vec::new();
        for bnd_idx in 0..(split_count - 1) {
            let name = format!("tvar_bnd_v{var_idx}_b{bnd_idx}");
            let boundary_decl = declare_tvar(name);
            let boundary = builder.var(boundary_decl.name, tcx);
            let boundary_real = if boundary_decl.ty == TyKind::Real {
                boundary
            } else {
                builder.cast(TyKind::Real, boundary)
            };
            boundaries.push(boundary_real);
        }

        let mut var_intervals = Vec::new();

        // First interval: var < b_0
        var_intervals.push(builder.binary(
            BinOpKind::Lt,
            Some(TyKind::Bool),
            real_var.clone(),
            boundaries[0].clone(),
        ));

        // Middle intervals: b_{i-1} <= var < b_i
        for i in 1..split_count - 1 {
            let ge = builder.binary(
                BinOpKind::Ge,
                Some(TyKind::Bool),
                real_var.clone(),
                boundaries[i - 1].clone(),
            );
            let lt = builder.binary(
                BinOpKind::Lt,
                Some(TyKind::Bool),
                real_var.clone(),
                boundaries[i].clone(),
            );
            var_intervals.push(builder.binary(BinOpKind::And, Some(TyKind::Bool), ge, lt));
        }

        // Last interval: var >= b_{k-2}
        var_intervals.push(builder.binary(
            BinOpKind::Ge,
            Some(TyKind::Bool),
            real_var,
            boundaries[split_count - 2].clone(),
        ));

        all_intervals.push(var_intervals);
    }

    for var in bool_vars {
        let neg = builder.unary(UnOpKind::Not, Some(TyKind::Bool), var.clone());
        all_intervals.push(vec![var.clone(), neg]);
    }

    cartesian_and(&all_intervals, builder)
}

fn is_true_lit(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Lit(s) if matches!(s.node, LitKind::Bool(true)))
}

fn and_simplify(builder: &ExprBuilder, lhs: Expr, rhs: Expr) -> Expr {
    if is_true_lit(&lhs) {
        rhs
    } else if is_true_lit(&rhs) {
        lhs
    } else {
        builder.binary(BinOpKind::And, Some(TyKind::Bool), lhs, rhs)
    }
}

// Returns every combination of one element per inner `Vec`, joined with `And`.
fn cartesian_and(lists: &[Vec<Expr>], builder: &ExprBuilder) -> Vec<Expr> {
    lists
        .iter()
        .fold(vec![builder.bool_lit(true)], |acc, list| {
            acc.iter()
                .flat_map(|prefix| {
                    list.iter()
                        .map(move |item| and_simplify(builder, prefix.clone(), item.clone()))
                })
                .collect()
        })
}
