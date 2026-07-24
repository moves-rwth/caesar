mod conditions;
mod pipeline;
mod refinements;

pub use pipeline::build_and_inline_templates;

use conditions::{
    and_simplify, collect_program_vars, collect_relevant_bool_conditions, explore_condition_groups,
    group_exclusive_conditions, is_syntactic_tautology, is_true_lit, normalize_condition,
    simplify_conjunction, ConditionGroup,
};
use refinements::{get_fix_region_splits, get_variable_region_splits};

use indexmap::{IndexMap, IndexSet};
use num::{BigInt, BigRational, BigUint};
use z3::SatResult;
use z3rro::prover::{IncrementalMode, Prover};

use crate::{
    ast::{
        decl, BinOpKind, DeclKind, DeclRef, Expr, ExprBuilder, ExprData, ExprKind, Ident, LitKind,
        Range, Shared, Span, Spanned, Symbol, TyKind, UnOpKind, VarDecl, VarKind,
    },
    driver::commands::{options::RefinementMode, verify::VerifyCommand},
    resource_limits::LimitsRef,
    smt::{
        funcs::axiomatic::AxiomaticFunctionEncoder, translate_exprs::TranslateExprs, uninterpreted,
        DepConfig, SmtCtx,
    },
    synthesis::cegis::subst_from_mapping,
    tyctx::TyCtx,
};

/// Refinement state for one outer CEGIS iteration.
pub struct RefinementState {
    pub mode: RefinementMode,
    pub iter: usize,
    pub effective_split_count: usize,
    pub effective_degree: usize,
}

/// Common config for template-building calls.
pub struct TemplateConfig<'a> {
    pub options: &'a VerifyCommand,
    pub limits_ref: &'a LimitsRef,
    pub refinement: &'a RefinementState,
}

/// Polynomial shape shared between the piece builder and the piecewise assembler.
struct PolySpec<'a> {
    synth_name: &'a Ident,
    fvar_decls: &'a [VarDecl],
    signed_output_type: TyKind,
    max_degree: usize,
}

// Maps program variables to the formal-variable expressions they were passed as at a call site.
pub type PVarToFVarMap = IndexMap<Ident, Expr>;

pub struct TemplateResult {
    pub expr: Expr,
    pub template_idents: Vec<(Ident, TyKind)>,
    pub guards_before_pruning: usize,
    pub guards_after_pruning: usize,
    pub num_sat_checks: usize,
    pub loop_mode: bool,
}

pub struct TemplateEntry {
    pub synth_name: Ident,
    pub expr: Expr,
    pub guards_before_pruning: usize,
    pub guards_after_pruning: usize,
    pub loop_mode: bool,
}

/// For each call to `target_ident` in `expr`, returns a map from formal parameter to
/// the program variable passed at that call site (plain-variable arguments only).
pub fn collect_call_var_param_maps(
    expr: &Expr,
    target_ident: &Ident,
    fvars: &[Expr],
) -> Vec<PVarToFVarMap> {
    let mut out = Vec::new();
    collect_call_var_param_maps_rec(expr, target_ident, fvars, &mut out);
    out
}

fn collect_call_var_param_maps_rec(
    expr: &Expr,
    target_ident: &Ident,
    fvars: &[Expr],
    out: &mut Vec<PVarToFVarMap>,
) {
    match &expr.kind {
        ExprKind::Call(func_ident, args) if func_ident.name == target_ident.name => {
            if args.len() == fvars.len() {
                let map: PVarToFVarMap = args
                    .iter()
                    .zip(fvars.iter())
                    .filter_map(|(arg, param)| {
                        if let ExprKind::Var(id) = &arg.kind {
                            Some((*id, param.clone()))
                        } else {
                            None
                        }
                    })
                    .collect();

                if !map.is_empty() {
                    out.push(map);
                }
            }
            // Always recurse into call arguments.
            for arg in args {
                collect_call_var_param_maps_rec(arg, target_ident, fvars, out);
            }
        }
        _ => {
            for child in expr.children() {
                collect_call_var_param_maps_rec(child, target_ident, fvars, out);
            }
        }
    }
}

// Generates all monomials of exactly `degree` from `vars` (combinations with repetition).
fn gen_monomials(
    vars: &[Expr],
    degree: usize,
    start: usize,
    current: &mut Vec<Expr>,
    out: &mut Vec<Vec<Expr>>,
) {
    if current.len() == degree {
        out.push(current.clone());
        return;
    }
    for i in start..vars.len() {
        current.push(vars[i].clone());
        gen_monomials(vars, degree, i, current, out);
        current.pop();
    }
}

// Left-folds a product over `factors`; panics if `factors` is empty.
fn multiply_all(builder: &ExprBuilder, ty: &TyKind, factors: &[Expr]) -> Expr {
    factors[1..].iter().fold(factors[0].clone(), |acc, f| {
        builder.binary(BinOpKind::Mul, Some(ty.clone()), acc, f.clone())
    })
}

// Builds a `c_0 + sum_i c_i * x^i` polynomial with fresh coefficient tvars.
// The result still needs to be wrapped in `nonneg_cast` by the caller.
fn build_polynomial_combination(
    piece_id: String,
    spec: &PolySpec<'_>,
    builder: &ExprBuilder,
    tcx: &TyCtx,
    declare_tvar: &mut dyn FnMut(String) -> decl::VarDecl,
) -> Expr {
    let synth_name = spec.synth_name;
    let fvar_decls = spec.fvar_decls;
    let signed_output_type = spec.signed_output_type.clone();
    let max_degree = spec.max_degree;
    let fvar_exprs: Vec<Expr> = fvar_decls
        .iter()
        .map(|v| {
            let raw = builder.var(v.name, tcx);
            if raw.ty.as_ref() == Some(&signed_output_type) {
                raw
            } else {
                builder.cast(signed_output_type.clone(), raw)
            }
        })
        .collect();

    let mut poly: Option<Expr> = None;
    for degree in 1..=max_degree {
        let mut monomials = Vec::new();
        gen_monomials(&fvar_exprs, degree, 0, &mut Vec::new(), &mut monomials);

        for (idx, mono) in monomials.into_iter().enumerate() {
            let prod = multiply_all(builder, &signed_output_type, &mono);
            let coeff_name = format!("tvar_{synth_name}_{piece_id}_deg{degree}_m{idx}");
            let coeff = builder.var(declare_tvar(coeff_name).name, tcx);
            let term = builder.binary(
                BinOpKind::Mul,
                Some(signed_output_type.clone()),
                coeff,
                prod,
            );
            poly = Some(match poly {
                None => term,
                Some(acc) => {
                    builder.binary(BinOpKind::Add, Some(signed_output_type.clone()), acc, term)
                }
            });
        }
    }

    let constant = builder.var(
        declare_tvar(format!("tvar_{synth_name}_{piece_id}_const")).name,
        tcx,
    );
    match poly {
        None => constant,
        Some(acc) => builder.binary(
            BinOpKind::Add,
            Some(signed_output_type.clone()),
            acc,
            constant,
        ),
    }
}

/// Sums one fresh polynomial per satisfiable (guard, split) pair into a piecewise expression.
/// The result is in `signed_output_type`; the caller wraps it in `nonneg_cast`.
fn assemble_piecewise_expression<'smt, 'ctx>(
    spec: &PolySpec<'_>,
    collected_guards: &[Expr],
    split_conditions: &[Expr],
    builder: &mut ExprBuilder,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    declare_tvar: &mut dyn FnMut(String) -> decl::VarDecl,
) -> (Expr, usize) {
    let ctx = translate.ctx.ctx();
    let tcx = translate.ctx.tcx();
    let signed_output_type = spec.signed_output_type.clone();
    let mut final_expr: Option<Expr> = None;
    let mut num_sat_checks = 0;
    let mut prover = Prover::new(ctx, IncrementalMode::Native);

    for (i_idx, guard) in collected_guards.iter().enumerate() {
        for (s_idx, split) in split_conditions.iter().enumerate() {
            let region = and_simplify(builder, guard.clone(), split.clone());

            let expr_z3 = translate.t_bool(&region);
            prover.push();
            prover.add_assumption(&expr_z3);
            num_sat_checks += 1;
            let sat = prover.check_sat() == SatResult::Sat;
            prover.pop();

            if !sat {
                continue;
            }

            let piece_poly = build_polynomial_combination(
                format!("{}_{}", i_idx, s_idx),
                spec,
                builder,
                tcx,
                declare_tvar,
            );

            let term = if is_true_lit(guard) && is_true_lit(split) {
                piece_poly
            } else {
                let iverson =
                    builder.unary(UnOpKind::Iverson, Some(signed_output_type.clone()), region);
                builder.binary(
                    BinOpKind::Mul,
                    Some(signed_output_type.clone()),
                    iverson,
                    piece_poly,
                )
            };

            final_expr = Some(match final_expr {
                None => term,
                Some(acc) => {
                    builder.binary(BinOpKind::Add, Some(signed_output_type.clone()), acc, term)
                }
            });
        }
    }

    // If every (guard, split) pair was UNSAT, fall back to a single unconstrained
    // polynomial so the synthesis still has coefficients to work with.
    let expr = final_expr.unwrap_or_else(|| {
        build_polynomial_combination(
            "unconstrained".to_string(),
            spec,
            builder,
            tcx,
            declare_tvar,
        )
    });
    (expr, num_sat_checks)
}

// Recursively removes any sub-expression whose top node is a `Quant`.
// Binary nodes with one quant side keep the other; nodes with both sides
// quantified become `false`; a top-level quant becomes `true`.
fn strip_quant_subexprs(expr: &Expr) -> Expr {
    let builder = ExprBuilder::new(expr.span);
    match &expr.kind {
        ExprKind::Quant(..) => builder.bool_lit(true),
        ExprKind::Binary(op, lhs, rhs) => {
            let lhs_q = matches!(lhs.kind, ExprKind::Quant(..));
            let rhs_q = matches!(rhs.kind, ExprKind::Quant(..));
            match (lhs_q, rhs_q) {
                (true, false) => strip_quant_subexprs(rhs),
                (false, true) => strip_quant_subexprs(lhs),
                (true, true) => match expr.ty.as_ref() {
                    Some(ty) if !matches!(ty, TyKind::Bool) => builder.zero_lit(ty),
                    _ => builder.bool_lit(false),
                },
                (false, false) => Shared::new(ExprData {
                    kind: ExprKind::Binary(
                        *op,
                        strip_quant_subexprs(lhs),
                        strip_quant_subexprs(rhs),
                    ),
                    ty: expr.ty.clone(),
                    span: expr.span,
                }),
            }
        }
        ExprKind::Ite(cond, then_expr, else_expr) => Shared::new(ExprData {
            kind: ExprKind::Ite(
                strip_quant_subexprs(cond),
                strip_quant_subexprs(then_expr),
                strip_quant_subexprs(else_expr),
            ),
            ty: expr.ty.clone(),
            span: expr.span,
        }),
        ExprKind::Unary(op, operand) => Shared::new(ExprData {
            kind: ExprKind::Unary(*op, strip_quant_subexprs(operand)),
            ty: expr.ty.clone(),
            span: expr.span,
        }),
        _ => expr.clone(),
    }
}

// Looks for `synth_name(...) <=/= ite(guard, body, post)` in `expr` and extracts
// (guard, post) if found.
fn extract_loop_guard_and_post(expr: &Expr, synth_name: &Ident) -> Option<(Expr, Expr)> {
    if let ExprKind::Binary(bin_op, lhs, rhs) = &expr.kind {
        if matches!(bin_op.node, BinOpKind::CoCompare | BinOpKind::Compare) {
            if matches!(&lhs.kind, ExprKind::Call(f, _) if f.name == synth_name.name) {
                if let ExprKind::Ite(cond, _, else_branch) = &rhs.kind {
                    let post = unwrap_post_sup(&strip_quant_subexprs(else_branch));
                    return Some((cond.clone(), post));
                }
            }
            return extract_loop_guard_and_post(lhs, synth_name)
                .or_else(|| extract_loop_guard_and_post(rhs, synth_name));
        }
    }
    for child in expr.children() {
        if let Some(res) = extract_loop_guard_and_post(child, synth_name) {
            return Some(res);
        }
    }
    None
}

// Peels off leading `Sup` wrappers, keeping the left branch.
fn unwrap_post_sup(expr: &Expr) -> Expr {
    match &expr.kind {
        ExprKind::Binary(op, left, _) if matches!(op.node, BinOpKind::Sup) => unwrap_post_sup(left),
        _ => expr.clone(),
    }
}

// Creates a literal of value `v` in `ty`; falls back to a `Real` fractional literal for non-integer types.
fn make_uint_lit(v: u64, ty: &TyKind, builder: &ExprBuilder) -> Expr {
    match ty {
        TyKind::UInt => Shared::new(ExprData {
            kind: ExprKind::Lit(Spanned::with_dummy_span(LitKind::UInt(BigUint::from(v)))),
            ty: Some(TyKind::UInt),
            span: Span::dummy_span(),
        }),
        TyKind::Int => Shared::new(ExprData {
            kind: ExprKind::Lit(Spanned::with_dummy_span(LitKind::Int(BigInt::from(v)))),
            ty: Some(TyKind::Int),
            span: Span::dummy_span(),
        }),
        _ => builder.signed_frac_lit(BigRational::from_integer(BigInt::from(v))),
    }
}

// Returns `true` if `expr` contains a call to `target`.
fn expr_contains_call(expr: &Expr, target: &Ident) -> bool {
    match &expr.kind {
        ExprKind::Call(f, args) => {
            if f.name == target.name {
                return true;
            }
            args.iter().any(|a| expr_contains_call(a, target))
        }
        _ => expr
            .children()
            .into_iter()
            .any(|c| expr_contains_call(c, target)),
    }
}

/// Builds the piecewise polynomial template for `synth_name` and returns a [`TemplateResult`].
pub fn build_template_expression<'smt, 'ctx>(
    config: &TemplateConfig<'_>,
    synth_name: &Ident,
    synth_val: &uninterpreted::FuncEntry,
    vc_expr: &Expr,
    builder: &mut ExprBuilder,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    vc_expr_unfolded: &Expr,
) -> TemplateResult {
    let options = config.options;
    let limits_ref = config.limits_ref.clone();
    let split_count = config.refinement.effective_split_count;
    let disable_loop_mode = config.options.synth_options.bare_template;
    let max_degree = config.refinement.effective_degree;
    let refinement_mode = config.refinement.mode;
    let ctx = translate.ctx.ctx();
    let tcx = translate.ctx.tcx();
    let loop_parts = extract_loop_guard_and_post(vc_expr_unfolded, synth_name);
    let loop_mode = loop_parts.is_some() && !disable_loop_mode;

    let output_type = if loop_mode {
        TyKind::EUReal
    } else {
        let mut ty = TyKind::EUReal;
        if let Some(DeclKind::FuncDecl(func_ref)) = tcx.get(*synth_name).as_deref() {
            ty = func_ref.borrow().output.clone();
        }
        ty
    };

    let signed_output_type = if options.synth_options.unsigned_coefficients {
        match output_type {
            TyKind::UInt => TyKind::UInt,
            TyKind::EUReal => TyKind::UReal,
            ref t => t.clone(),
        }
    } else {
        match output_type {
            TyKind::UInt => TyKind::Int,
            _ => TyKind::Real,
        }
    };

    let mut template_idents: Vec<(Ident, TyKind)> = Vec::new();
    let mut num_sat_checks = 0;

    let mut fvar_decls = Vec::new();
    let mut fvar_exprs = Vec::new();
    let mut fvar_exprs_for_conds = Vec::new();
    let mut bool_fvar_exprs = Vec::new();

    for param in &synth_val.inputs.node {
        let vardecl = VarDecl::from_param(param, VarKind::Input)
            .try_unwrap()
            .unwrap();
        let raw = builder.var(vardecl.name, tcx);
        fvar_exprs_for_conds.push(raw.clone());
        if vardecl.ty == TyKind::Bool {
            bool_fvar_exprs.push(raw);
        } else {
            fvar_decls.push(vardecl);
            fvar_exprs.push(raw);
        }
    }

    let mappings = collect_call_var_param_maps(vc_expr, synth_name, &fvar_exprs_for_conds);

    let mut declare_tvar = |name: String| -> decl::VarDecl {
        let full_name = format!("{}_sc{}_fn{}", name, split_count + 1, synth_name);
        let ident = Ident::with_dummy_span(Symbol::intern(&full_name));
        let decl = VarDecl {
            name: ident,
            ty: signed_output_type.clone(),
            kind: VarKind::Input,
            init: None,
            span: Span::dummy_span(),
            created_from: None,
            range: None,
        };
        tcx.declare(crate::ast::DeclKind::VarDecl(DeclRef::new(decl.clone())));
        template_idents.push((decl.name, signed_output_type.clone()));
        decl
    };

    let cond_smt_ctx = SmtCtx::new(
        ctx,
        tcx,
        Box::new(AxiomaticFunctionEncoder::default()),
        DepConfig::SpecsOnly,
    );

    let (mut bool_exprs, pvar_to_fvar_map) = if split_count >= 1 {
        collect_relevant_bool_conditions(vc_expr, mappings, tcx, limits_ref.clone())
    } else {
        (Vec::new(), IndexMap::new())
    };

    let subst =
        |e: &Expr| subst_from_mapping(&pvar_to_fvar_map, e, &limits_ref, &cond_smt_ctx).unwrap();

    let loop_info: Option<(Expr, Expr)> = if let Some((guard, post)) = loop_parts {
        if disable_loop_mode {
            let unfolded_mappings =
                collect_call_var_param_maps(vc_expr_unfolded, synth_name, &fvar_exprs_for_conds);
            let ert_guard_map: IndexMap<Ident, Expr> = {
                let mut map = pvar_to_fvar_map.clone();
                for mapping in &unfolded_mappings {
                    for (pvar, fvar_expr) in mapping {
                        map.entry(*pvar).or_insert_with(|| fvar_expr.clone());
                    }
                }
                map
            };
            let guard_subst =
                subst_from_mapping(&ert_guard_map, &guard, &limits_ref, &cond_smt_ctx).unwrap();
            tracing::debug!("loop guard (@ert, adding as bool condition): {guard_subst}");
            let guard_key = guard_subst.to_string();
            if !bool_exprs.iter().any(|e| e.to_string() == guard_key) {
                bool_exprs.push(guard_subst);
            }
            None
        } else {
            let guard_subst = subst(&guard);
            tracing::debug!("loop guard: {guard_subst}");

            // If the guard uses variables that aren't formal parameters of the synth function
            // (e.g. a loop guard on `f` when inv only takes `tc`), the ITE template would
            // leak program-scope variables. Fall back to a plain polynomial.
            let fvar_names: IndexSet<_> = fvar_exprs_for_conds
                .iter()
                .filter_map(|e| {
                    if let ExprKind::Var(id) = &e.kind {
                        Some(id.name)
                    } else {
                        None
                    }
                })
                .collect();
            let guard_fvars = collect_program_vars(&guard_subst);
            if guard_fvars.iter().any(|v| !fvar_names.contains(&v.name)) {
                tracing::debug!(
                    "loop guard uses non-parameter variables ({:?}); disabling loop mode",
                    guard_fvars
                        .iter()
                        .filter(|v| !fvar_names.contains(&v.name))
                        .map(|v| v.name.to_string())
                        .collect::<Vec<_>>()
                );
                None
            } else {
                let guard_str = guard_subst.to_string();
                bool_exprs.retain(|e| e.to_string() != guard_str);

                let post_full = subst(&post);
                Some((guard_subst, post_full))
            }
        }
    } else {
        None
    };

    tracing::debug!("bool conditions (raw, {} total):", bool_exprs.len());
    for b in &bool_exprs {
        tracing::debug!("  {b}");
    }

    // Simplify, normalise, deduplicate, and drop self-referential conditions.
    let mut seen_norm: IndexSet<String> = IndexSet::new();
    let bool_exprs: Vec<Expr> = bool_exprs
        .into_iter()
        .map(|e| simplify_conjunction(&e, builder))
        .map(|e| normalize_condition(&e))
        .filter(|e| !is_syntactic_tautology(e) && seen_norm.insert(e.to_string()))
        .filter(|e| !expr_contains_call(e, synth_name))
        .collect();

    tracing::debug!(
        "bool conditions after simplification ({} total):",
        bool_exprs.len()
    );
    for b in &bool_exprs {
        tracing::debug!("  {b}");
    }

    let ranged_fvars: Vec<(Expr, Range)> = fvar_decls
        .iter()
        .filter_map(|v| Some((builder.var(v.name, tcx), v.range?)))
        .collect();

    let mut prover = Prover::new(ctx, IncrementalMode::Native);
    for (var, range) in &ranged_fvars {
        let var_ty = var.ty.clone().unwrap_or(TyKind::UInt);
        for (typed_var, lo_lit, hi_lit) in [
            (
                var.clone(),
                make_uint_lit(range.lower, &var_ty, builder),
                make_uint_lit(range.upper, &var_ty, builder),
            ),
            (
                {
                    if var_ty == TyKind::Real {
                        var.clone()
                    } else {
                        builder.cast(TyKind::Real, var.clone())
                    }
                },
                builder.signed_frac_lit(BigRational::from_integer(BigInt::from(range.lower))),
                builder.signed_frac_lit(BigRational::from_integer(BigInt::from(range.upper))),
            ),
        ] {
            let ge = builder.binary(BinOpKind::Ge, Some(TyKind::Bool), typed_var.clone(), lo_lit);
            let le = builder.binary(BinOpKind::Le, Some(TyKind::Bool), typed_var, hi_lit);
            let range_constraint = builder.binary(BinOpKind::And, Some(TyKind::Bool), ge, le);
            let range_z3 = translate.t_bool(&range_constraint);
            prover.add_assumption(&range_z3);
        }
    }

    // In loop mode the template lives inside ite(guard, ..., post), so guard is always true
    // there. Add it as an assumption so tautological conditions get pruned correctly.
    if let Some((ref guard, _)) = loop_info {
        let guard_z3 = translate.t_bool(guard);
        prover.add_assumption(&guard_z3);
        tracing::debug!("loop mode: added guard as prover assumption: {guard}");
    }

    // Drop conditions whose negation is UNSAT under the declared ranges (always true).
    let mut filtered_bool_exprs: Vec<Expr> = Vec::new();
    for e in bool_exprs {
        let neg = builder.unary(UnOpKind::Not, Some(TyKind::Bool), e.clone());
        let neg_z3 = translate.t_bool(&neg);
        prover.push();
        prover.add_assumption(&neg_z3);
        num_sat_checks += 1;
        let negation_sat = prover.check_sat() == SatResult::Sat;
        prover.pop();
        if negation_sat {
            filtered_bool_exprs.push(e);
        }
    }
    let bool_exprs = filtered_bool_exprs;

    tracing::debug!(
        "bool conditions after range filtering ({} total):",
        bool_exprs.len()
    );
    for b in &bool_exprs {
        tracing::debug!("  {b}");
    }

    // In variable mode, skip bool params already covered by a VC-derived condition group
    // to avoid redundant cross-products like `(!res1 && !res2) && (!res1 && has_disease)`.
    let bool_exprs_strs: IndexSet<String> = bool_exprs.iter().map(|e| e.to_string()).collect();
    let effective_bool_fvar_exprs: Vec<Expr> = if matches!(
        refinement_mode,
        RefinementMode::Variable | RefinementMode::Degree
    ) {
        bool_fvar_exprs
            .iter()
            .filter(|fvar| !bool_exprs_strs.contains(&fvar.to_string()))
            .cloned()
            .collect()
    } else {
        bool_fvar_exprs.clone()
    };

    // In loop mode the guard is always true in the then-branch, so don't split on it —
    // that would generate redundant [guard] / [!guard] Iverson brackets.
    let effective_bool_fvar_exprs: Vec<Expr> = if let Some((ref guard, _)) = loop_info {
        let guard_str = guard.to_string();
        effective_bool_fvar_exprs
            .into_iter()
            .filter(|fvar| fvar.to_string() != guard_str)
            .collect()
    } else {
        effective_bool_fvar_exprs
    };

    let split_conditions = if matches!(
        refinement_mode,
        RefinementMode::Variable | RefinementMode::Degree
    ) {
        get_variable_region_splits(
            &fvar_exprs,
            &effective_bool_fvar_exprs,
            split_count,
            builder,
            tcx,
            &mut declare_tvar,
        )
    } else {
        get_fix_region_splits(
            &ranged_fvars,
            &effective_bool_fvar_exprs,
            split_count,
            builder,
        )
    };

    let condition_groups = group_exclusive_conditions(bool_exprs);
    tracing::debug!(
        "{} condition groups ({} exclusive, {} independent) × {} split conditions",
        condition_groups.len(),
        condition_groups
            .iter()
            .filter(|g| matches!(g, ConditionGroup::Exclusive(_)))
            .count(),
        condition_groups
            .iter()
            .filter(|g| matches!(g, ConditionGroup::Independent(_)))
            .count(),
        split_conditions.len(),
    );

    let guards_before_pruning: usize = condition_groups.iter().fold(1, |acc, g| match g {
        ConditionGroup::Independent(_) => acc * 2,
        ConditionGroup::Exclusive(members) => acc * (members.len() + 1),
    }) * split_conditions.len();

    // `valid_guards` collects the satisfiable case guards (one Boolean conjunction per region).
    let mut valid_guards: Vec<Expr> = Vec::new();
    num_sat_checks += explore_condition_groups(
        0,
        &condition_groups,
        builder,
        translate,
        &mut prover,
        builder.bool_lit(true),
        &mut valid_guards,
    );
    tracing::debug!("{} satisfiable guard assignments", valid_guards.len());

    let poly_spec = PolySpec {
        synth_name,
        fvar_decls: &fvar_decls,
        signed_output_type: signed_output_type.clone(),
        max_degree,
    };
    let (piecewise, sat_count) = assemble_piecewise_expression(
        &poly_spec,
        &valid_guards,
        &split_conditions,
        builder,
        translate,
        &mut declare_tvar,
    );
    num_sat_checks += sat_count;

    // Apply nonneg_cast to the polynomial piecewise expression.
    let nonneg_cast_name = Ident::with_dummy_span(Symbol::intern("nonneg_cast"));
    let clamped_ty = if matches!(signed_output_type, TyKind::Int | TyKind::UInt) {
        TyKind::UInt
    } else {
        TyKind::UReal
    };
    let clamped = Shared::new(ExprData {
        kind: ExprKind::Call(nonneg_cast_name, vec![piecewise]),
        ty: Some(clamped_ty),
        span: Span::dummy_span(),
    });
    // Cast clamped result up to output_type (e.g. UReal -> EUReal in loop mode).
    let clamped_in_output = if clamped.ty.as_ref() != Some(&output_type) {
        builder.cast(output_type.clone(), clamped)
    } else {
        clamped
    };
    // In loop mode: ITE(guard, clamped_eureal, post_full). post_full stays EUReal —
    // no downcast needed, so infinity is preserved correctly in the else branch.
    let mut final_expr = if let Some((guard, post_full)) = loop_info {
        builder.ite(
            Some(output_type.clone()),
            guard,
            clamped_in_output,
            post_full,
        )
    } else {
        clamped_in_output
    };

    let free_vars = collect_program_vars(&final_expr);
    let subst_iter = free_vars.into_iter().filter_map(|id| {
        fvar_decls
            .iter()
            .position(|d| d.name.name == id.name)
            .map(|idx| (id, fvar_exprs[idx].clone()))
    });
    final_expr = builder.subst(final_expr, subst_iter);

    TemplateResult {
        expr: final_expr,
        template_idents,
        guards_before_pruning,
        guards_after_pruning: valid_guards.len() * split_conditions.len(),
        num_sat_checks,
        loop_mode,
    }
}
