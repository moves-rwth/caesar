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
        BinOpKind, DeclRef, Expr, ExprBuilder, ExprData, ExprKind, Ident, Shared, Span, Symbol,
        TyKind, UnOpKind, VarDecl, VarKind,
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
// substituting function parameters with the caller arguments
pub struct FunctionInliner<'ctx> {
    pub target: Ident,                // the function ident
    pub entry: &'ctx FuncEntry<'ctx>, // contains input params
    pub body: &'ctx Expr,             // the function body expression
}

impl<'a> VisitorMut for FunctionInliner<'a> {
    type Err = ();

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        let span = expr.span;

        match &mut expr.kind {
            ExprKind::Call(func_ident, args) if *func_ident == self.target => {
                let parameters: Vec<Ident> =
                    self.entry.inputs.node.iter().map(|p| p.name).collect();

                let mut wrapped = self.body.clone();

                // Substitute arguments with which the function is called into the body
                for (parameter, actual_expr) in parameters.iter().zip(args.iter()) {
                    wrapped = Shared::new(ExprData {
                        kind: ExprKind::Subst(*parameter, actual_expr.clone(), wrapped.clone()),
                        ty: wrapped.ty.clone(),
                        span,
                    });
                }

                // Replace the call with the body wrapped in substitutions
                *expr = wrapped.clone();

                Ok(())
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

            Symbolic::EUReal(v) => v.eval(model).ok().map(|r| match r {
                ConcreteEUReal::Real(rat) => builder.frac_lit(rat),
                ConcreteEUReal::Infinity => builder.infinity_lit(),
            }),

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
    synth_entry: &uninterpreted::FuncEntry,
    synth_name: &Ident,
    builder: &ExprBuilder,
    tcx: &TyCtx,
    declare_template_var: &mut dyn FnMut(String) -> decl::VarDecl,
) -> Expr {
    let mut lin_comb: Option<Expr> = None; // used to accumulate the lin comb
                                           // TODO: currently this assumes that synth has only one entry
    for param in &synth_entry.inputs.node {
        let vardecl = VarDecl::from_param(param, VarKind::Input)
            .try_unwrap()
            .unwrap();

        // Create variable for parameter (and cast to Real)
        let mut variable = builder.var(vardecl.name, tcx);

        if vardecl.ty == TyKind::Bool {
            continue;
            // variable = builder.unary(UnOpKind::Iverson, Some(TyKind::Real), variable.clone());
        }

        variable = builder.cast(TyKind::Real, variable.clone());

        // Create template variable
        // Template var name
        let name = format!("tvar_{synth_name}_{name_addon}_{}", vardecl.name.name);

        let decl = declare_template_var(name);
        let templ = builder.var(decl.name, tcx);

        // Parenthesize template var
        // TODO: this is only needed because fractions get parsed incorrectly:
        // a/b *c gets parsed as a/(b*c)
        let templ_paren = builder.unary(UnOpKind::Parens, Some(TyKind::Real), templ);

        // Multiply: templ * variable
        let prod = builder.binary(BinOpKind::Mul, Some(TyKind::Real), templ_paren, variable);

        // Accumulate sum
        lin_comb = Some(lin_comb.map_or(prod.clone(), |acc| {
            builder.binary(BinOpKind::Add, Some(TyKind::Real), acc, prod)
        }));
    }

    // Add the "last" summand
    let decl = declare_template_var(format!("tvar_{synth_name}_{name_addon}_last",));
    let last = builder.var(decl.name, tcx);

    let lin_comb_with_last = lin_comb.map_or(last.clone(), |acc| {
        builder.binary(BinOpKind::Add, Some(TyKind::Real), acc, last)
    });

    let clamp_with_zero_name = Ident::with_dummy_span(Symbol::intern("clamp_with_zero"));

    lin_comb = Some(Shared::new(ExprData {
        kind: ExprKind::Call(clamp_with_zero_name, vec![lin_comb_with_last.clone()]),
        ty: Some(TyKind::EUReal),

        span: Span::dummy_span(),
    }));
    lin_comb.unwrap()
}

pub fn collect_relevant_bool_conditions(
    synth_val: &uninterpreted::FuncEntry,
    vc_expr: &Expr,
    tcx: &TyCtx,
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
            let mut collector = FreeVariableCollector::new();
            let mut cloned = b.clone();
            let vars = collector.collect_and_clear(&mut cloned);
            for var in &vars{
                tcx.print_var_range(*var);
            }
            vars.iter().all(|id| allowed_vars.contains(&id.name))
        })
        .collect()
}



pub fn get_variable_region_splits<'ctx>(
    synth_name: &Ident,
    synth_val: &uninterpreted::FuncEntry,
    split_count: usize,
    builder: &mut ExprBuilder,
    tcx: &TyCtx,
    declare_template_var: &mut dyn FnMut(String) -> decl::VarDecl,
) -> Vec<Expr> {
    // ---- Collect non-boolean program variables ----
    let mut program_vars = Vec::new();
    for param in &synth_val.inputs.node {
        let vardecl = VarDecl::from_param(param, VarKind::Input)
            .try_unwrap()
            .unwrap();
        if vardecl.ty != TyKind::Bool {
            let raw = builder.var(vardecl.name, tcx);
            let casted = builder.cast(TyKind::Real, raw);
            program_vars.push(casted);
        }
    }


    // ---- Generate threshold variables ----
    let mut threshold_vars = Vec::<Vec<Expr>>::new();
    for (i, _) in program_vars.iter().enumerate() {
        let mut cuts = Vec::new();
        for j in 0..split_count {
            let name = format!("{}_split_threshold_{}_{}", synth_name.name, i, j);
            let decl = declare_template_var(name);
            let t = builder.var(decl.name, tcx);
            cuts.push(t);
        }
        threshold_vars.push(cuts);
    }

    // ---- Build region conditions ----
    let mut region_conditions = Vec::new();
    let total_regions;

    if program_vars.is_empty() || split_count == 0 {
        region_conditions.push(builder.bool_lit(true));
    } else {
        let n = program_vars.len();
        let regions_per_var = split_count + 1;
        total_regions = regions_per_var.pow(n as u32);

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
                        pv.clone(),
                        cuts[0].clone(),
                    ),
                    r if r == regions_per_var - 1 => builder.binary(
                        BinOpKind::Ge,
                        Some(TyKind::Bool),
                        pv.clone(),
                        cuts.last().unwrap().clone(),
                    ),
                    r => {
                        let ge_prev = builder.binary(
                            BinOpKind::Ge,
                            Some(TyKind::Bool),
                            pv.clone(),
                            cuts[r - 1].clone(),
                        );
                        let lt_next = builder.binary(
                            BinOpKind::Lt,
                            Some(TyKind::Bool),
                            pv.clone(),
                            cuts[r].clone(),
                        );
                        builder.binary(BinOpKind::And, Some(TyKind::Bool), ge_prev, lt_next)
                    }
                };

                cond = builder.binary(BinOpKind::And, Some(TyKind::Bool), cond, pred);
            }

            region_conditions.push(cond);
        }
    }

    region_conditions
}

pub fn assemble_piecewise_expression(
    synth_name: &Ident,
    synth_val: &uninterpreted::FuncEntry,
    valid_iversons: &[Expr],
    split_conditions: &Vec<Expr>,
    builder: &mut ExprBuilder,
    tcx: &TyCtx,
    mut declare_template_var: &mut dyn FnMut(String) -> decl::VarDecl,
) -> Expr {
    let mut final_expr: Option<Expr> = None;

    for (i_idx, iv_prod) in valid_iversons.iter().enumerate() {
        let iv_eureal = builder.unary(UnOpKind::Iverson, Some(TyKind::EUReal), iv_prod.clone());

        for (s_idx, split) in split_conditions.iter().enumerate() {
            let split_iv = builder.unary(UnOpKind::Iverson, Some(TyKind::EUReal), split.clone());

            // Create lincomb with unique name
            let lc_name = format!("{}_{}", i_idx, s_idx);
            let lc = build_linear_combination(
                lc_name,
                synth_val,
                synth_name,
                builder,
                tcx,
                &mut declare_template_var,
            );

            let full = builder.binary(
                BinOpKind::Mul,
                Some(TyKind::EUReal),
                builder.binary(
                    BinOpKind::Mul,
                    Some(TyKind::EUReal),
                    iv_eureal.clone(),
                    split_iv,
                ),
                lc,
            );

            final_expr = Some(match final_expr {
                None => full,
                Some(acc) => builder.binary(BinOpKind::Add, Some(TyKind::EUReal), acc, full),
            });
        }
    }

    final_expr.unwrap()
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
) -> (Expr, Vec<Ident>) {
    // -------------------------------------------------------------------------
    // Storage for all newly created template parameter identifiers
    // -------------------------------------------------------------------------
    let mut template_idents: Vec<Ident> = Vec::new();

    // Template-variable declaration closure
    let mut declare_template_var = |name: String| -> decl::VarDecl {
        let full_name = format!("{}{}", name, split_count);
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

    // -------------------------------------------------------------------------
    // Step 1: Collect Boolean conditions relevant to the inputs
    // -------------------------------------------------------------------------
    let bool_exprs = collect_relevant_bool_conditions(synth_val, vc_expr, tcx);

    assert!(
        !bool_exprs.is_empty(),
        "No boolean expressions remain after filtering."
    );

    // -------------------------------------------------------------------------
    // Step 2: Build all split predicates
    // -------------------------------------------------------------------------
    let split_conditions = get_variable_region_splits(
        synth_name,
        synth_val,
        split_count,
        builder,
        tcx,
        &mut declare_template_var,
    );

    // -------------------------------------------------------------------------
    // Step 3: Compute satisfiable guards from Boolean conditions
    // -------------------------------------------------------------------------
    let mut valid_iversons = Vec::new();
    explore_boolean_assignments(
        0,
        bool_exprs.as_slice(),
        builder,
        translate,
        ctx,
        &mut Vec::new(),        // partial assignment
        builder.bool_lit(true), // initial Iverson factor
        &mut valid_iversons,    // output
    );

    println!(
        "Number of expressions for {} is {}",
        synth_name,
        valid_iversons.len() * split_conditions.len()
    );

    // -------------------------------------------------------------------------
    // Step 4: Combine original guars × split conditions and multiply each with own lin.exp
    // -------------------------------------------------------------------------
    let final_expr = assemble_piecewise_expression(
        synth_name,
        synth_val,
        &valid_iversons,
        &split_conditions,
        builder,
        tcx,
        &mut declare_template_var,
    );

    (final_expr, template_idents)
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
) {
    // Base case: a complete assignment
    if idx == bool_exprs.len() {
        valid_iversons.push(iverson_prod); // Add this Iverson product to the list of valid ones
        return;
    }

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
            // Prefix is SAT → explore deeper
            explore_boolean_assignments(
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
}
