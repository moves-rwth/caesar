use num::{BigInt, BigRational};
use z3::SatResult;
use z3rro::{
    eureal::ConcreteEUReal,
    model::{InstrumentedModel, SmtEval},
    prover::{IncrementalMode, Prover},
};

use crate::{
    ast::{
        self, decl,
        util::FreeVariableCollector,
        visit::{walk_expr, VisitorMut},
        BinOpKind, DeclKind, DeclRef, Expr, ExprBuilder, ExprData, ExprKind, Ident, Range, Shared,
        Span, Symbol, TyKind, UnOpKind, VarDecl, VarKind,
    },
    smt::{
        symbolic::Symbolic,
        translate_exprs::TranslateExprs,
        uninterpreted::{self, FuncEntry, Uninterpreteds},
    },
    tyctx::TyCtx,
};
use std::collections::{HashMap, HashSet};

// Takes a function and substitutes calls to that function with the functions body,
// substituting function parameters with the caller argumentspub struct FunctionInliner<'ctx, T: FuncLookup> {
pub struct FunctionInliner<'smt, 'ctx> {
    pub target: Ident,
    pub entry: &'ctx FuncEntry<'ctx>,
    pub body: &'ctx Expr,
    pub tcx: &'smt TyCtx,

    /// Track which functions are currently being inlined
    inlining_stack: Vec<Ident>, // to avoid infinitely inlining recursive functions
}

impl<'smt, 'ctx> FunctionInliner<'smt, 'ctx> {
    pub fn new(
        target: Ident,
        entry: &'ctx FuncEntry<'ctx>,
        body: &'ctx Expr,
        tcx: &'smt TyCtx,
    ) -> Self {
        Self {
            target,
            entry,
            body,
            tcx,
            inlining_stack: Vec::new(),
        }
    }
}

impl<'smt, 'ctx> VisitorMut for FunctionInliner<'smt, 'ctx> {
    type Err = ();

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        let span = expr.span;

        match &mut expr.kind {
            // Case 1: INLINE THE TARGET FUNCTION (existing)
            ExprKind::Call(func_ident, args) if *func_ident == self.target => {
                let parameters: Vec<Ident> =
                    self.entry.inputs.node.iter().map(|p| p.name).collect();

                let mut wrapped = self.body.clone();

                for (parameter, actual_expr) in parameters.iter().zip(args.iter()) {
                    wrapped = Shared::new(ExprData {
                        kind: ExprKind::Subst(*parameter, actual_expr.clone(), wrapped.clone()),
                        ty: wrapped.ty.clone(),
                        span,
                    });
                }

                *expr = wrapped.clone();
                return Ok(());
            }

            // Case 2: INLINE OTHER FUNCTIONS (with recursion guard)
            ExprKind::Call(func_ident, args) => {
                // RECURSION GUARD: do NOT inline if this function is already being processed
                if self.inlining_stack.contains(func_ident) {
                    // Still recurse through arguments, but do not inline the body
                    return walk_expr(self, expr);
                }

                // Lookup the function definition
                if let Some(DeclKind::FuncDecl(func_ref)) = self.tcx.get(*func_ident).as_deref() {
                    let func = func_ref.borrow();
                    let body_opt = func.body.borrow();
                    let parameters: Vec<Ident> = func.inputs.node.iter().map(|p| p.name).collect();

                    if let Some(body_expr) = body_opt.clone() {
                        // Mark this function as "inlining in progress"
                        self.inlining_stack.push(*func_ident);

                        let mut wrapped = body_expr;

                        // Substitute parameters
                        for (parameter, actual_expr) in parameters.iter().zip(args.iter()) {
                            wrapped = Shared::new(ExprData {
                                kind: ExprKind::Subst(
                                    *parameter,
                                    actual_expr.clone(),
                                    wrapped.clone(),
                                ),
                                ty: wrapped.ty.clone(),
                                span,
                            });
                        }

                        // Recursively inline inside the substituted body
                        let mut wrapped_mut = wrapped.clone();
                        self.visit_expr(&mut wrapped_mut)?;

                        // Done processing this function
                        self.inlining_stack.pop();

                        *expr = wrapped_mut;
                        return Ok(());
                    }

                    return walk_expr(self, expr);
                }

                walk_expr(self, expr)
            }

            _ => walk_expr(self, expr),
        }
    }
}

// Translates a model into a map Ident -> Expression
pub fn create_subst_mapping<'ctx>(
    model: &InstrumentedModel<'ctx>,
    translate: &mut crate::smt::translate_exprs::TranslateExprs<'_, 'ctx>,
) -> HashMap<ast::symbol::Ident, Expr> {
    let builder = ExprBuilder::new(Span::dummy_span());
    let mut mapping = HashMap::new();

    let idents: Vec<_> = translate.local_idents().collect();

    for ident in idents {
        // Build a variable expression to feed into t_symbolic
        let var_expr = builder.var(ident.clone(), translate.ctx.tcx);
        let symbolic = translate.t_symbolic(&var_expr);

        let lit_opt = match &symbolic {
            Symbolic::Bool(v) => v.eval(model).ok().map(|b| builder.bool_lit(b)),

            Symbolic::Int(v) => v
                .eval(model)
                .ok()
                .map(|i: BigInt| builder.frac_lit(BigRational::from_integer(i))),

            Symbolic::UInt(v) => v.eval(model).ok().map(|i: BigInt| {
                if i >= BigInt::from(0) {
                    match u128::try_from(i.clone()) {
                        Ok(u) => builder.uint(u),
                        Err(_) => builder.frac_lit(BigRational::from_integer(i)),
                    }
                } else {
                    builder.frac_lit(BigRational::from_integer(i))
                }
            }),

            Symbolic::Real(v) => {
                let eval = v.eval(model);
                eval.ok().map(|r: BigRational| builder.signed_frac_lit(r))
            }

            Symbolic::UReal(v) => {
                let eval = v.eval(model);
                eval.ok()
                    .map(|r: BigRational| builder.frac_lit_not_extended(r))
            }

            Symbolic::EUReal(v) => {v.eval(model).ok().map(|r| match r {
                ConcreteEUReal::Real(rat) => builder.frac_lit(rat),
                ConcreteEUReal::Infinity => builder.infinity_lit(),
            })},

            _ => None,
        };

        if let Some(ref lit) = lit_opt {
            mapping.insert(ident.clone(), lit.clone());
        }
    }

    mapping
}

/// "Instantiate" an expression with concrete values from a mapping.
/// To do this, wrap the expression in nested `Subst` expressions.
/// Then later tunfolding can take care of the actual substitutions.
pub fn subst_from_mapping<'ctx>(mapping: HashMap<ast::symbol::Ident, Expr>, vc: &Expr) -> Expr {
    let mut wrapped = vc.clone();
    for (ident, expr) in mapping {
        wrapped = Shared::new(ExprData {
            kind: ExprKind::Subst(ident, expr, wrapped.clone()),
            ty: wrapped.ty.clone(),
            span: vc.span,
        });
    }
    wrapped
}

// A helper function to build the templates
// returns (sum_(param_vars)( templ_var * param_var )) + templ_last
fn build_linear_combination(
    name_addon: String,
    synth_name: &Ident,
    builder: &ExprBuilder,
    tcx: &TyCtx,
    declare_template_var: &mut dyn FnMut(String) -> decl::VarDecl,
    program_var_decls: &[VarDecl],
    output_type: TyKind,
) -> Expr {
    let mut lin_comb: Option<Expr> = None;

    for vardecl in program_var_decls {
        let mut variable = builder.var(vardecl.name, tcx);
        variable = builder.cast(TyKind::Real, variable.clone());

        let name = format!("tvar_{synth_name}_{name_addon}_{}", vardecl.name.name);
        let decl = declare_template_var(name);
        let templ = builder.var(decl.name, tcx);
        let templ_paren = builder.unary(UnOpKind::Parens, Some(TyKind::Real), templ);

        let prod = builder.binary(BinOpKind::Mul, Some(TyKind::Real), templ_paren, variable);
        lin_comb = Some(lin_comb.map_or(prod.clone(), |acc| {
            builder.binary(BinOpKind::Add, Some(TyKind::Real), acc, prod)
        }));
    }

    // Add the last summand
    let decl = declare_template_var(format!("tvar_{synth_name}_{name_addon}_last"));
    let last = builder.var(decl.name, tcx);

    let lin_comb_with_last = lin_comb.map_or(last.clone(), |acc| {
        builder.binary(BinOpKind::Add, Some(TyKind::Real), acc, last)
    });

    // if lin_comb_with_last.ty != Some(output_type.clone()) {
    //     lin_comb_with_last = builder.cast(output_type.clone(), lin_comb_with_last);
    // }

    let clamp_with_zero_name = Ident::with_dummy_span(Symbol::intern("clamp_with_zero"));
    let mut final_expr = Shared::new(ExprData {
        kind: ExprKind::Call(clamp_with_zero_name, vec![lin_comb_with_last.clone()]),
        ty: Some(TyKind::UReal),
        span: Span::dummy_span(),
    });

    if final_expr.ty != Some(output_type.clone()) {
        final_expr = builder.cast(output_type, final_expr);
    }

    final_expr
}

pub fn collect_relevant_bool_conditions(
    synth_val: &uninterpreted::FuncEntry,
    vc_expr: &Expr,
) -> Vec<Expr> {
    let mut allowed_vars = HashSet::new();

    for param in &synth_val.inputs.node {
        let vardecl = VarDecl::from_param(param, VarKind::Input)
            .try_unwrap()
            .unwrap();
        allowed_vars.insert(vardecl.name.name);
    }

    vc_expr
        .collect_bool_conditions()
        .into_iter()
        .filter(|b| {
            let vars = collect_program_vars(b);
            vars.iter().all(|id| allowed_vars.contains(&id.name))
        })
        .collect()
}

fn collect_program_vars(expr: &Expr) -> indexmap::IndexSet<Ident> {
    let mut collector = FreeVariableCollector::new();
    let mut cloned = expr.clone();

    let vars = collector.collect_and_clear(&mut cloned);

    vars
}
pub fn get_fix_region_splits<'ctx>(
    ranged_vars: &[(Expr, Range)], // precomputed program variables + ranges
    split_count: usize,
    builder: &mut ExprBuilder,
) -> Vec<Expr> {
    let mut region_conditions = Vec::new();

    if ranged_vars.is_empty() || split_count == 0 {
        region_conditions.push(builder.bool_lit(true));
        return region_conditions;
    }

    let mut per_var_regions: Vec<Vec<Expr>> = Vec::new();

    for (pv, range) in ranged_vars {
        let l = BigRational::from_integer(BigInt::from(range.lower));
        let u = BigRational::from_integer(BigInt::from(range.upper));
        let width = &u - &l;

        let mut regions_for_this_var = Vec::new();

        for i in 1..=(split_count + 1) {
            let pred = if i == 1 {
                let ratio = BigRational::new(i.into(), split_count.into());
                let cut_val = &l + &width * ratio;
                let cut_expr = builder.signed_frac_lit(cut_val);
                builder.binary(
                    BinOpKind::Le,
                    Some(TyKind::Bool),
                    builder.cast(TyKind::Real, pv.clone()),
                    cut_expr,
                )
            } else {
                let ratio = BigRational::new((i - 1).into(), split_count.into());
                let cut_val = &l + &width * ratio;
                let cut_expr = builder.signed_frac_lit(cut_val);
                builder.binary(
                    BinOpKind::Gt,
                    Some(TyKind::Bool),
                    builder.cast(TyKind::Real, pv.clone()),
                    cut_expr,
                )
            };
            regions_for_this_var.push(pred);
        }

        per_var_regions.push(regions_for_this_var);
    }

    cartesian_and(&per_var_regions, builder)
}

fn cartesian_and(lists: &[Vec<Expr>], builder: &ExprBuilder) -> Vec<Expr> {
    // Start with a single empty conjunction
    let mut acc: Vec<Expr> = vec![builder.bool_lit(true)];

    for list in lists {
        let mut next = Vec::new();

        for prefix in &acc {
            for item in list {
                // prefix AND item
                let conj = builder.binary(
                    BinOpKind::And,
                    Some(TyKind::Bool),
                    prefix.clone(),
                    item.clone(),
                );
                next.push(conj);
            }
        }

        acc = next;
    }

    acc
}

pub fn _get_variable_region_splits<'ctx>(
    program_vars: &[Expr], // precomputed builder variables
    split_count: usize,
    builder: &mut ExprBuilder,
    tcx: &TyCtx,
    declare_template_var: &mut dyn FnMut(String) -> decl::VarDecl,
) -> Vec<Expr> {
    let mut threshold_vars = Vec::<Vec<Expr>>::new();
    for (i, _) in program_vars.iter().enumerate() {
        let mut cuts = Vec::new();
        for j in 0..split_count {
            let name = format!("split_threshold_{}_{}", i, j);
            let decl = declare_template_var(name);
            let t = builder.var(decl.name, tcx);
            cuts.push(t);
        }
        threshold_vars.push(cuts);
    }

    if program_vars.is_empty() || split_count == 0 {
        return vec![builder.bool_lit(true)];
    }

    let n = program_vars.len();
    let regions_per_var = split_count + 1;
    let total_regions = regions_per_var.pow(n as u32);

    let mut region_conditions = Vec::new();

    for region_index in 0..total_regions {
        let mut cond = builder.bool_lit(true);
        let mut idx = region_index;

        for var_i in 0..n {
            let reg = idx % regions_per_var;
            idx /= regions_per_var;

            let pv = program_vars[var_i].clone();
            let cuts = &threshold_vars[var_i];

            let pred = match reg {
                0 => builder.binary(
                    BinOpKind::Lt,
                    Some(TyKind::Bool),
                    builder.cast(TyKind::Real, pv.clone()),
                    cuts[0].clone(),
                ),
                r if r == regions_per_var - 1 => builder.binary(
                    BinOpKind::Ge,
                    Some(TyKind::Bool),
                    builder.cast(TyKind::Real, pv.clone()),
                    cuts.last().unwrap().clone(),
                ),
                r => {
                    let ge_prev = builder.binary(
                        BinOpKind::Ge,
                        Some(TyKind::Bool),
                        builder.cast(TyKind::Real, pv.clone()),
                        cuts[r - 1].clone(),
                    );
                    let lt_next = builder.binary(
                        BinOpKind::Lt,
                        Some(TyKind::Bool),
                        builder.cast(TyKind::Real, pv.clone()),
                        cuts[r].clone(),
                    );
                    builder.binary(BinOpKind::And, Some(TyKind::Bool), ge_prev, lt_next)
                }
            };

            cond = builder.binary(BinOpKind::And, Some(TyKind::Bool), cond, pred);
        }

        region_conditions.push(cond);
    }

    region_conditions
}

// Creates the expression (collected_guards x split_conditions) * lc
pub fn assemble_piecewise_expression<'smt, 'ctx>(
    synth_name: &Ident,
    collected_guards: &[Expr],
    split_conditions: &Vec<Expr>,
    builder: &mut ExprBuilder,
    tcx: &TyCtx,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    ctx: &'ctx z3::Context,
    declare_template_var: &mut dyn FnMut(String) -> decl::VarDecl,
    program_var_decls: &[VarDecl],
    output_type: TyKind,
) -> (Expr, usize) {
    let mut final_expr: Option<Expr> = None;

    let mut num_sat_checks = 0;
    for (i_idx, iv_prod) in collected_guards.iter().enumerate() {
        for (s_idx, split) in split_conditions.iter().enumerate() {
            let both = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                iv_prod.clone(),
                split.clone(),
            );

            // Check satisfiability of guard && split_condition, since this is a short formula
            // and if it is not sat we don't have to add the lc
            let expr_z3 = translate.t_bool(&both);
            let mut prover = Prover::new(&ctx, IncrementalMode::Native);
            prover.add_assumption(&expr_z3);

            num_sat_checks = num_sat_checks + 1;
            if prover.check_sat() == SatResult::Sat {
                let iverson_both = builder.unary(UnOpKind::Iverson, Some(output_type.clone()), both);

                // Pass precomputed program_var_decls
                let lc_name = format!("{}_{}", i_idx, s_idx);
                let lc = build_linear_combination(
                    lc_name,
                    synth_name,
                    builder,
                    tcx,
                    declare_template_var,
                    program_var_decls,
                    output_type.clone(),
                );

                let full = builder.binary(BinOpKind::Mul, Some(output_type.clone()), iverson_both, lc);

                final_expr = Some(match final_expr {
                    None => full,
                    Some(acc) => builder.binary(BinOpKind::Add, Some(output_type.clone()), acc, full),
                });
            }
        }
    }

    (final_expr.unwrap(), num_sat_checks)
}

pub fn build_template_expression<'smt, 'ctx>(
    synth_name: &Ident,
    synth_val: &uninterpreted::FuncEntry,
    vc_expr: &Expr,
    builder: &mut ExprBuilder,
    tcx: &TyCtx,
    split_count: usize,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    ctx: &'ctx z3::Context,
) -> (Expr, Vec<Ident>, usize, usize) {
    // Storage for all newly created template parameter identifiers
    let mut template_idents: Vec<Ident> = Vec::new();
    let mut num_sat_checks = 0;

    let mut program_var_decls = Vec::new();
    let mut program_vars = Vec::new();
    let mut program_vars_no_cast = Vec::new();

    for param in &synth_val.inputs.node {
        let vardecl = VarDecl::from_param(param, VarKind::Input)
            .try_unwrap()
            .unwrap();
        if vardecl.ty != TyKind::Bool {
            let raw = builder.var(vardecl.name, tcx);
            let mut casted=raw.clone();
            if vardecl.ty != TyKind::Real{
                casted = builder.cast(TyKind::Real, raw.clone());
            }
            program_var_decls.push(vardecl);
            program_vars.push(casted);
            program_vars_no_cast.push(raw);
        }
    }
    let mut output_type = TyKind::EUReal;
    if let Some(DeclKind::FuncDecl(func_ref)) = tcx.get(*synth_name).as_deref() {
        output_type = func_ref.borrow().output.clone();
    }

    // Template-variable declaration closure
    let mut declare_template_var = |name: String| -> decl::VarDecl {
        let full_name = format!("{}{}", name, split_count+1);
        let ident = Ident::with_dummy_span(Symbol::intern(&full_name));
        let decl = VarDecl {
            name: ident,
            ty: TyKind::Real,
            kind: VarKind::Input,
            init: None,
            span: Span::dummy_span(),
            created_from: None,
            range: None,
        };
        tcx.declare(crate::ast::DeclKind::VarDecl(DeclRef::new(decl.clone())));
        template_idents.push(decl.name);
        decl
    };

    let mut bool_exprs: Vec<Shared<ExprData>> = [].into();
    // Step 1: Collect Boolean conditions relevant to the inputs
    if split_count >= 1 {
        bool_exprs = collect_relevant_bool_conditions(synth_val, vc_expr);
    }

    if bool_exprs.is_empty() {
        bool_exprs.push(builder.bool_lit(true));
    }

    // Step 2: Build all split predicates
    let ranged_vars: Vec<(Expr, Range)> = program_var_decls
        .iter()
        .filter_map(|v| {
            v.range
                .as_ref()
                .map(|r| (builder.var(v.name, tcx), r.clone()))
        })
        .collect();

    let split_conditions = get_fix_region_splits(&ranged_vars, split_count, builder);

    // Step 3: Compute satisfiable guards from Boolean conditions
    let mut valid_iversons = Vec::new();
    num_sat_checks = num_sat_checks
        + explore_boolean_assignments(
            0,
            bool_exprs.as_slice(),
            builder,
            translate,
            ctx,
            &mut Vec::new(),        // partial assignment
            builder.bool_lit(true), // initial Iverson factor
            &mut valid_iversons,    // output
        );

    // Step 4: Combine original guards × split conditions and multiply each with own lin.exp
    let (mut final_expr, temp_sat_checks) = assemble_piecewise_expression(
        synth_name,
        &valid_iversons,
        &split_conditions,
        builder,
        tcx,
        translate,
        ctx,
        &mut declare_template_var,
        &program_var_decls,
        output_type,
    );
    num_sat_checks = num_sat_checks + temp_sat_checks;

    // Step 5: Substitute only program variables in final_expr
    let free_vars = collect_program_vars(&final_expr);

    // Build substitution iterator only for variables that match program_var_decls
    let subst_iter = free_vars.into_iter().filter_map(|id| {
        // Find index of program_var_decl with same name
        program_var_decls
            .iter()
            .position(|decl| decl.name.name == id.name)
            .map(|idx| (id, program_vars_no_cast[idx].clone()))
    });

    // Apply substitution
    final_expr = builder.subst(final_expr, subst_iter);

    (
        final_expr,
        template_idents,
        valid_iversons.len() * split_conditions.len(),
        num_sat_checks,
    )
}

pub fn get_synth_functions<'ctx>(
    un: &'ctx Uninterpreteds<'ctx>,
) -> HashMap<Ident, &'ctx uninterpreted::FuncEntry<'ctx>> {
    un.functions()
        .iter()
        .filter_map(|(id, f)| if f.syn { Some((id.clone(), f)) } else { None })
        .collect()
}

/// Explores all possible Boolean assignments for a given set of Boolean expressions
/// and accumulates the guards for all satisfiable assignments found.
///
/// This function recursively explores each possible Boolean assignment by branching on
/// whether each Boolean variable is assigned `true` or `false`. For each partial
/// assignment, it builds the corresponding conjunction (these are the guards) and checks
/// whether the assignment satisfies the given Boolean expressions using a SAT solver.
///
/// Instead of stopping at the first satisfiable assignment, this version collects
/// guards for all satisfiable assignments found and returns them as a vector.
///
/// The recursion stops at a complete assignment (when all Boolean variables have been
/// assigned) or when an unsatisfiable prefix is encountered. If a satisfiable assignment
/// is found, the guards for that assignment is added to the result list.

fn explore_boolean_assignments<'smt, 'ctx>(
    idx: usize,
    bool_exprs: &[Expr],
    builder: &mut ExprBuilder,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    ctx: &'ctx z3::Context,
    partial_assign: &mut Vec<bool>,
    iverson_prod: Expr,
    valid_iversons: &mut Vec<Expr>, // Accumulate Iverson products here
) -> usize {
    // Base case: a complete assignment
    if idx == bool_exprs.len() {
        valid_iversons.push(iverson_prod); // Add this Iverson product to the list of valid ones
        return 0;
    }

    let mut num_sat_checks = 0;
    // Recursive case: branch on bit = false / true
    for &bit in &[false, true] {
        partial_assign.push(bit);

        // Build conjunction for this prefix
        let mut new_iverson = iverson_prod.clone();
        {
            let b = bool_exprs[idx].clone();
            let cond = if bit {
                b
            } else {
                builder.unary(UnOpKind::Not, Some(TyKind::Bool), b)
            };

            new_iverson = builder.binary(BinOpKind::And, Some(TyKind::Bool), new_iverson, cond);
        }

        // SAT check for the prefix
        let expr_z3 = translate.t_bool(&new_iverson);
        let mut prover = Prover::new(&ctx, IncrementalMode::Native);
        prover.add_assumption(&expr_z3);

        if prover.check_sat() == SatResult::Sat {
            // Prefix is SAT -> explore deeper
            num_sat_checks = 1 + explore_boolean_assignments(
                idx + 1,
                bool_exprs,
                builder,
                translate,
                ctx,
                partial_assign,
                new_iverson,
                valid_iversons, // Accumulate satisfiable Iverson products
            );
        } else {
            tracing::trace!("Pruned UNSAT prefix");
        }

        partial_assign.pop();
    }
    num_sat_checks
}
