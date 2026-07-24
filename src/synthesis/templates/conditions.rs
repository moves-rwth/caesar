use indexmap::{IndexMap, IndexSet};
use num::BigUint;
use z3::{Config, Context, SatResult};
use z3rro::prover::Prover;

use crate::{
    ast::{
        util::FreeVariableCollector, BinOpKind, Expr, ExprBuilder, ExprData, ExprKind, Ident,
        LitKind, Shared, Spanned, TyKind, UnOpKind,
    },
    resource_limits::LimitsRef,
    smt::{
        funcs::axiomatic::AxiomaticFunctionEncoder, translate_exprs::TranslateExprs, DepConfig,
        SmtCtx,
    },
    synthesis::cegis::subst_from_mapping,
    tyctx::TyCtx,
};

use super::PVarToFVarMap;

pub(super) fn collect_program_vars(expr: &Expr) -> IndexSet<Ident> {
    let mut collector = FreeVariableCollector::new();
    collector.collect_and_clear(&mut expr.clone())
}

/// Collects all ITE conditions and Iverson operands from `expr`, deduplicated by string representation.
pub fn collect_bool_conditions(expr: &Expr) -> Vec<Expr> {
    let mut out = Vec::new();
    let mut seen: IndexSet<String> = IndexSet::new();
    collect_bool_conditions_rec(expr, &mut out, &mut seen);
    out
}

fn collect_bool_conditions_rec(expr: &Expr, out: &mut Vec<Expr>, seen: &mut IndexSet<String>) {
    match &expr.kind {
        ExprKind::Ite(cond, then_branch, else_branch) => {
            record_if_new(cond, out, seen);
            collect_bool_conditions_rec(cond, out, seen);
            collect_bool_conditions_rec(then_branch, out, seen);
            collect_bool_conditions_rec(else_branch, out, seen);
        }
        ExprKind::Unary(op, operand) if matches!(op.node, UnOpKind::Iverson) => {
            record_if_new(operand, out, seen);
            collect_bool_conditions_rec(operand, out, seen);
        }
        _ => {
            for child in expr.children() {
                collect_bool_conditions_rec(child, out, seen);
            }
        }
    }
}

fn record_if_new(expr: &Expr, out: &mut Vec<Expr>, seen: &mut IndexSet<String>) {
    let key = expr.to_string();
    if seen.insert(key) {
        out.push(expr.clone());
    }
}

/// Collects Boolean conditions from `vc_expr` whose free variables all appear in some
/// call-site substitution map, then rewrites each surviving condition into the synthesis
/// target's formal parameters.
pub fn collect_relevant_bool_conditions(
    vc_expr: &Expr,
    mappings: Vec<PVarToFVarMap>,
    tcx: &TyCtx,
    limits_ref: LimitsRef,
) -> (Vec<Expr>, IndexMap<Ident, Expr>) {
    let ctx = Context::new(&Config::default());
    let smt_ctx = SmtCtx::new(
        &ctx,
        tcx,
        Box::new(AxiomaticFunctionEncoder::default()),
        DepConfig::SpecsOnly,
    );

    let mut pvar_to_fvar_map: IndexMap<Ident, Expr> = IndexMap::new();
    let mut out: Vec<Expr> = Vec::new();
    let mut seen_strs: IndexSet<String> = IndexSet::new();

    for b in collect_bool_conditions(vc_expr) {
        let vars = collect_program_vars(&b);

        for mapping in &mappings {
            if vars.iter().all(|v| mapping.contains_key(v)) {
                let wrapped = subst_from_mapping(mapping, &b, &limits_ref, &smt_ctx).unwrap();

                let key = wrapped.to_string();
                if seen_strs.insert(key) {
                    out.push(wrapped);
                }

                for (pvar, fvar_expr) in mapping {
                    pvar_to_fvar_map.insert(*pvar, fvar_expr.clone());
                }
            }
        }
    }

    // Always populate pvar_to_fvar_map from all call-site mappings, not just those that happened
    // to match a boolean condition. This ensures the guard/post substitution in loop mode works
    // even when no boolean condition references the call argument variables.
    for mapping in &mappings {
        for (pvar, fvar_expr) in mapping {
            pvar_to_fvar_map
                .entry(*pvar)
                .or_insert_with(|| fvar_expr.clone());
        }
    }

    (out, pvar_to_fvar_map)
}

// Normalises `(a - c1) == c2` to `a == (c1 + c2)` for UInt literals, so that
// conditions of the form `(n - 1) == k` from inner-loop invariants are
// deduplicated against the equivalent outer-scope `n == (k+1)` conditions.
pub(super) fn normalize_condition(expr: &Expr) -> Expr {
    let ExprKind::Binary(op, lhs, rhs) = &expr.kind else {
        return expr.clone();
    };
    if !matches!(op.node, BinOpKind::Eq) {
        return expr.clone();
    }
    let ExprKind::Binary(sub_op, inner_lhs, inner_rhs) = &lhs.kind else {
        return expr.clone();
    };
    if !matches!(sub_op.node, BinOpKind::Sub) {
        return expr.clone();
    }
    let ExprKind::Lit(offset_lit) = &inner_rhs.kind else {
        return expr.clone();
    };
    let ExprKind::Lit(val_lit) = &rhs.kind else {
        return expr.clone();
    };
    let LitKind::UInt(offset) = &offset_lit.node else {
        return expr.clone();
    };
    let LitKind::UInt(val) = &val_lit.node else {
        return expr.clone();
    };
    let sum: BigUint = offset + val;
    let new_rhs = Shared::new(ExprData {
        kind: ExprKind::Lit(Spanned::with_dummy_span(LitKind::UInt(sum))),
        ty: rhs.ty.clone(),
        span: rhs.span,
    });
    Shared::new(ExprData {
        kind: ExprKind::Binary(*op, inner_lhs.clone(), new_rhs),
        ty: expr.ty.clone(),
        span: expr.span,
    })
}

// Flattens a (possibly nested) right- or left-associative conjunction into a
// flat list of its conjuncts.
fn flatten_and(expr: &Expr, out: &mut Vec<Expr>) {
    match &expr.kind {
        ExprKind::Binary(op, lhs, rhs) if matches!(op.node, BinOpKind::And) => {
            flatten_and(lhs, out);
            flatten_and(rhs, out);
        }
        _ => out.push(expr.clone()),
    }
}

// Flattens, deduplicates, and drops tautological conjuncts; returns `true` when all are dropped.
pub(super) fn simplify_conjunction(expr: &Expr, builder: &ExprBuilder) -> Expr {
    let mut conjuncts = Vec::new();
    flatten_and(expr, &mut conjuncts);

    let mut seen: IndexSet<String> = IndexSet::new();
    let filtered: Vec<Expr> = conjuncts
        .into_iter()
        .filter(|c| !is_syntactic_tautology(c) && seen.insert(c.to_string()))
        .collect();

    match filtered.len() {
        0 => builder.bool_lit(true),
        _ => filtered
            .into_iter()
            .reduce(|acc, c| builder.binary(BinOpKind::And, Some(TyKind::Bool), acc, c))
            .unwrap(),
    }
}

// Returns `true` for expressions that are syntactically always true and can
// therefore be dropped from the Boolean splitting conditions.
pub(super) fn is_syntactic_tautology(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Lit(lit) => matches!(lit.node, LitKind::Bool(true)),
        ExprKind::Binary(op, lhs, rhs) => {
            // x == x, x <= x, x >= x are reflexively true.
            if matches!(op.node, BinOpKind::Eq | BinOpKind::Le | BinOpKind::Ge)
                && (Shared::as_ptr(lhs) == Shared::as_ptr(rhs)
                    || lhs.to_string() == rhs.to_string())
            {
                return true;
            }
            // 0 <= x is always true when x has type UInt.
            if matches!(op.node, BinOpKind::Le)
                && lhs.to_string() == "0"
                && rhs.ty.as_ref() == Some(&TyKind::UInt)
            {
                return true;
            }
            // A conjunction is a tautology only when both sides are.
            matches!(op.node, BinOpKind::And)
                && is_syntactic_tautology(lhs)
                && is_syntactic_tautology(rhs)
        }
        _ => false,
    }
}

pub(super) fn is_true_lit(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Lit(s) if matches!(s.node, LitKind::Bool(true)))
}

// A group of Boolean conditions to enumerate during template-region exploration.
pub(super) enum ConditionGroup {
    /// A single condition: try both `true` and `false`.
    Independent(Expr),
    /// A set of mutually-exclusive `var == literal` conditions for the same
    /// variable: try each member individually, then the "none of them" case.
    Exclusive(Vec<Expr>),
}

// Extracts a stable string key for the LHS of an equality condition,
// looking through cast wrappers.
fn extract_var_key(expr: &Expr) -> Option<String> {
    match &expr.kind {
        ExprKind::Var(id) => Some(id.name.to_string()),
        ExprKind::Cast(inner) => extract_var_key(inner),
        _ => None,
    }
}

// Groups `var == literal` conditions for the same variable as `Exclusive`; all others stay `Independent`.
pub(super) fn group_exclusive_conditions(exprs: Vec<Expr>) -> Vec<ConditionGroup> {
    let mut eq_groups: IndexMap<String, Vec<Expr>> = IndexMap::new();
    let mut independent: Vec<Expr> = Vec::new();

    for expr in exprs {
        let mut grouped = false;
        if let ExprKind::Binary(op, lhs, rhs) = &expr.kind {
            if matches!(op.node, BinOpKind::Eq) {
                if let Some(key) = extract_var_key(lhs) {
                    if matches!(rhs.kind, ExprKind::Lit(_)) {
                        eq_groups.entry(key).or_default().push(expr.clone());
                        grouped = true;
                    }
                }
            }
        }
        if !grouped {
            independent.push(expr);
        }
    }

    let mut groups: Vec<ConditionGroup> = independent
        .into_iter()
        .map(ConditionGroup::Independent)
        .collect();

    for (_, members) in eq_groups {
        if members.len() > 1 {
            groups.push(ConditionGroup::Exclusive(members));
        } else {
            // Single equality — keep as independent.
            groups.push(ConditionGroup::Independent(
                members.into_iter().next().unwrap(),
            ));
        }
    }

    groups
}

// `lhs && rhs` with identity simplification: drops a literal `true` on either
// side so that template guards don't accumulate leading `true && ...`.
pub(super) fn and_simplify(builder: &ExprBuilder, lhs: Expr, rhs: Expr) -> Expr {
    if is_true_lit(&lhs) {
        rhs
    } else if is_true_lit(&rhs) {
        lhs
    } else {
        builder.binary(BinOpKind::And, Some(TyKind::Bool), lhs, rhs)
    }
}

// Enumerates all satisfiable truth-assignments of `groups` with incremental push/pop SAT
// and collects the resulting case guards (Boolean conjunctions) into `valid_guards`.
pub(super) fn explore_condition_groups<'smt, 'ctx>(
    idx: usize,
    groups: &[ConditionGroup],
    builder: &mut ExprBuilder,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    prover: &mut Prover<'ctx>,
    partial_guard: Expr,
    valid_guards: &mut Vec<Expr>,
) -> usize {
    if idx == groups.len() {
        valid_guards.push(partial_guard);
        return 0;
    }

    let mut num_sat_checks = 0;

    match &groups[idx] {
        ConditionGroup::Independent(b) => {
            let neg = builder.unary(UnOpKind::Not, Some(TyKind::Bool), b.clone());
            // Pairs: (condition to test, its opposite) — try !b first, then b.
            let cases = [(neg.clone(), b.clone()), (b.clone(), neg)];
            for (cond, opposite) in cases {
                let cond_z3 = translate.t_bool(&cond);
                let opposite_z3 = translate.t_bool(&opposite);

                // Tautology check: if the opposite is UNSAT under current assumptions,
                // `cond` is implied — it adds no information to the guard.
                prover.push();
                prover.add_assumption(&opposite_z3);
                num_sat_checks += 1;
                let opposite_is_sat = prover.check_sat() == SatResult::Sat;
                prover.pop();

                // Reachability check: prune the branch if `cond` itself is UNSAT.
                prover.push();
                prover.add_assumption(&cond_z3);
                num_sat_checks += 1;
                if prover.check_sat() == SatResult::Sat {
                    let new_guard = if opposite_is_sat {
                        and_simplify(builder, partial_guard.clone(), cond)
                    } else {
                        tracing::trace!("implied condition at depth {idx}, not added to guard");
                        partial_guard.clone()
                    };
                    num_sat_checks += explore_condition_groups(
                        idx + 1,
                        groups,
                        builder,
                        translate,
                        prover,
                        new_guard,
                        valid_guards,
                    );
                } else {
                    tracing::trace!("pruned UNSAT at depth {idx}");
                }
                prover.pop();
            }
        }

        ConditionGroup::Exclusive(members) => {
            for member in members {
                let cond_z3 = translate.t_bool(member);
                let neg_member = builder.unary(UnOpKind::Not, Some(TyKind::Bool), member.clone());
                let neg_z3 = translate.t_bool(&neg_member);

                // Tautology check: if !member is UNSAT, member is always true — don't add to guard.
                prover.push();
                prover.add_assumption(&neg_z3);
                num_sat_checks += 1;
                let neg_is_sat = prover.check_sat() == SatResult::Sat;
                prover.pop();

                prover.push();
                prover.add_assumption(&cond_z3);
                num_sat_checks += 1;
                if prover.check_sat() == SatResult::Sat {
                    let new_guard = if neg_is_sat {
                        and_simplify(builder, partial_guard.clone(), member.clone())
                    } else {
                        tracing::trace!(
                            "implied exclusive member at depth {idx}, not added to guard"
                        );
                        partial_guard.clone()
                    };
                    num_sat_checks += explore_condition_groups(
                        idx + 1,
                        groups,
                        builder,
                        translate,
                        prover,
                        new_guard,
                        valid_guards,
                    );
                } else {
                    tracing::trace!("pruned UNSAT for exclusive member at depth {idx}");
                }
                prover.pop();
            }

            // Try the "none of them" case (all members false).
            prover.push();
            let mut none_guard = partial_guard.clone();
            for member in members {
                let neg = builder.unary(UnOpKind::Not, Some(TyKind::Bool), member.clone());
                let member_z3 = translate.t_bool(member);
                let neg_z3 = translate.t_bool(&neg);

                // Tautology check: if `member` is UNSAT, then `!member` is implied — don't add to guard.
                prover.push();
                prover.add_assumption(&member_z3);
                num_sat_checks += 1;
                let member_is_sat = prover.check_sat() == SatResult::Sat;
                prover.pop();

                prover.add_assumption(&neg_z3);
                if member_is_sat {
                    none_guard = and_simplify(builder, none_guard, neg);
                }
            }
            num_sat_checks += 1;
            if prover.check_sat() == SatResult::Sat {
                num_sat_checks += explore_condition_groups(
                    idx + 1,
                    groups,
                    builder,
                    translate,
                    prover,
                    none_guard,
                    valid_guards,
                );
            } else {
                tracing::trace!("pruned UNSAT for 'none' case at depth {idx}");
            }
            prover.pop();
        }
    }

    num_sat_checks
}
