use indexmap::{IndexMap, IndexSet};
use num::{BigInt, BigRational, Signed, Zero};
use std::time::{Duration, Instant};

use z3::{Context, Goal};
use z3rro::{
    eureal::ConcreteEUReal,
    model::{InstrumentedModel, SmtEval},
    probes::ProbeSummary,
    prover::{IncrementalMode, ProveResult, Prover},
    util::ReasonUnknown,
};

use crate::{
    ast::{
        self, visit::VisitorMut, Expr, ExprBuilder, ExprData, ExprKind, Ident, LitKind, Shared,
        Span, TyKind,
    },
    driver::{
        commands::verify::VerifyCommand,
        error::CaesarError,
        item::SourceUnitName,
        quant_proof::{BoolVcProveTask, QuantVcProveTask},
        smt_proof::{check_valid, SmtVcProveTask},
    },
    opt::unfolder::Unfolder,
    resource_limits::LimitsRef,
    smt::{
        symbolic::Symbolic,
        translate_exprs::TranslateExprs,
        uninterpreted::{FuncEntry, Uninterpreteds},
        SmtCtx,
    },
    synthesis::{report::SynthStats, templates::TemplateEntry},
};

const MAX_CEGIS_ITERS: usize = 3000;
const CLOSE_CEX_DISTANCE_THRESHOLD: i64 = 3;
const MAX_CLOSE_CEX_COUNT: usize = 100;

pub fn create_subst_mapping<'ctx>(
    idents: &IndexSet<Ident>,
    model: &InstrumentedModel<'ctx>,
    translate: &mut crate::smt::translate_exprs::TranslateExprs<'_, 'ctx>,
) -> IndexMap<ast::symbol::Ident, Expr> {
    let builder = ExprBuilder::new(Span::dummy_span());
    let mut mapping = IndexMap::new();

    for &ident in idents {
        let var_expr = builder.var(ident, translate.ctx.tcx());
        let symbolic = translate.t_symbolic(&var_expr);

        let lit_opt = match &symbolic {
            Symbolic::Bool(v) => {
                let b = v
                    .eval(model)
                    .unwrap_or_else(|e| panic!("SMT eval failed for Bool {ident:?}: {e}"));
                Some(builder.bool_lit(b))
            }

            Symbolic::Int(v) => {
                let i: BigInt = v
                    .eval(model)
                    .unwrap_or_else(|e| panic!("SMT eval failed for Int {ident:?}: {e}"));
                Some(builder.int_lit(i))
            }

            Symbolic::UInt(v) => {
                let i: BigInt = v
                    .eval(model)
                    .unwrap_or_else(|e| panic!("SMT eval failed for UInt {ident:?}: {e}"));

                let lit = if let Some(u) = i.to_biguint() {
                    builder.uint_lit(u)
                } else {
                    // Negative value from model — shouldn't happen for UInt, but fall back gracefully
                    builder.frac_lit(BigRational::from_integer(i))
                };

                Some(lit)
            }

            Symbolic::Real(v) => {
                let r: BigRational = v
                    .eval(model)
                    .unwrap_or_else(|e| panic!("SMT eval failed for Real {ident:?}: {e}"));
                Some(builder.signed_frac_lit(r))
            }

            Symbolic::UReal(v) => {
                let r: BigRational = v
                    .eval(model)
                    .unwrap_or_else(|e| panic!("SMT eval failed for UReal {ident:?}: {e}"));
                Some(builder.frac_lit_not_extended(r))
            }

            Symbolic::EUReal(v) => {
                let r = v
                    .eval(model)
                    .unwrap_or_else(|e| panic!("SMT eval failed for EUReal {ident:?}: {e}"));

                let lit = match r {
                    ConcreteEUReal::Real(rat) => builder.frac_lit(rat),
                    ConcreteEUReal::Infinity => builder.infinity_lit(),
                };

                Some(lit)
            }

            Symbolic::List(_) | Symbolic::Fuel(_) | Symbolic::Uninterpreted(_) => None,
        };

        if let Some(lit) = lit_opt {
            mapping.insert(ident, lit);
        }
    }

    mapping
}

/// Wraps `vc` in nested `Subst` nodes for each entry in `mapping`, then unfolds.
pub fn subst_from_mapping<'ctx>(
    mapping: &IndexMap<ast::symbol::Ident, Expr>,
    vc: &Expr,
    limits_ref: &LimitsRef,
    smt_ctx: &SmtCtx<'ctx>,
) -> Result<Expr, CaesarError> {
    let mut wrapped = vc.clone();
    for (&ident, expr) in mapping {
        let ty = wrapped.ty.clone();
        let inner = wrapped;
        wrapped = Shared::new(ExprData {
            kind: ExprKind::Subst(ident, expr.clone(), inner),
            ty,
            span: vc.span,
        });
    }

    let mut unfolder = Unfolder::new(limits_ref.clone(), smt_ctx);
    unfolder.visit_expr(&mut wrapped)?;
    Ok(wrapped)
}

pub fn get_model_for_constraints<'smt, 'ctx, 'tcx: 'ctx>(
    prover: &mut Prover<'ctx>,
    options: &VerifyCommand,
    constraints: BoolVcProveTask,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    idents: &IndexSet<Ident>,
    ctx: &'ctx Context,
) -> Result<Option<IndexMap<ast::symbol::Ident, Expr>>, CaesarError> {
    let mut smt_task = SmtVcProveTask::translate(constraints, translate);

    if !options.opt_options.no_simplify {
        smt_task.simplify();
    }

    prover.add_assumption(&smt_task.vc);

    if options.debug_options.print_smt {
        println!("Current solver state for constraints:");
        println!("{}", prover.get_smtlib().into_string());
    }

    if options.debug_options.z3_probe {
        let goal = Goal::new(ctx, false, false, false);
        for assertion in prover.get_assertions() {
            goal.assert(&assertion);
        }
        eprintln!(
            "Constraint Probe results: {}",
            ProbeSummary::probe(ctx, &goal)
        );
    }
    let res = prover.check_sat();

    match res {
        z3::SatResult::Unsat | z3::SatResult::Unknown => return Ok(None),
        z3::SatResult::Sat => {}
    }

    if let Some(model) = prover.get_model() {
        let mapping = create_subst_mapping(idents, &model, translate);
        Ok(Some(mapping))
    } else {
        Ok(None)
    }
}

/// Returns a canonical string representation of `map`, used for CEGIS cycle detection.
pub fn canonical_form(map: &IndexMap<Ident, Expr>) -> String {
    let mut items: Vec<_> = map.iter().collect();

    items.sort_by_key(|(ident, _)| ident.name);

    items
        .into_iter()
        .map(|(ident, expr)| format!("{}={}", ident, expr))
        .collect::<Vec<_>>()
        .join(";")
}

/// Returns all synthesised (`syn`) functions from the uninterpreted-function store.
pub fn get_synth_functions<'ctx>(
    uninterps: &'ctx Uninterpreteds<'ctx>,
) -> IndexMap<Ident, &'ctx FuncEntry<'ctx>> {
    uninterps
        .functions()
        .iter()
        .filter_map(|(id, f)| f.syn.then_some((*id, f)))
        .collect()
}

/// Returns the absolute difference between two numeric literal expressions, or zero for non-numeric.
pub fn expr_lit_distance(a: &Expr, b: &Expr) -> BigRational {
    match (expr_to_rational(a), expr_to_rational(b)) {
        (Some(rat_a), Some(rat_b)) => (rat_a - rat_b).abs(),
        _ => BigRational::zero(),
    }
}

// Extracts a rational value from a literal; None for non-numeric literals.
pub fn expr_to_rational(e: &Expr) -> Option<BigRational> {
    match &e.kind {
        ExprKind::Lit(lit) => match &lit.node {
            LitKind::UInt(n) => Some(BigRational::from(BigInt::from(n.clone()))),
            LitKind::Int(n) => Some(BigRational::from(n.clone())),
            LitKind::Frac(f) => Some(f.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// All data for one per-item CEGIS session: templates, program variables,
/// range constraints, and the verification condition.
pub struct CegisData {
    pub templates: Vec<TemplateEntry>,
    pub pvar_idents: IndexSet<Ident>,
    pub tvars: Vec<(Ident, TyKind)>,
    pub range_constraints: Vec<Expr>,
    pub boolean_vc: BoolVcProveTask,
    pub vc_expr: QuantVcProveTask,
}

pub struct VerifyOutcome {
    /// The template-variable assignment used for this check (zeros for unset vars).
    pub zero_extended_mapping: IndexMap<Ident, Expr>,
    pub kind: VerifyOutcomeKind,
}

pub enum VerifyOutcomeKind {
    Proof,
    /// Program-variable counterexample extracted from the model.
    Counterexample(IndexMap<Ident, Expr>),
    Unknown(ReasonUnknown),
    /// Solver returned counterexample but produced no model.
    NoModel,
}

/// Run the verifier side of one CEGIS iteration: instantiate the current
/// template-variable mapping, check the VC, and return the outcome.
pub fn verify_candidate<'smt, 'ctx>(
    data: &CegisData,
    tvar_mapping: &IndexMap<Ident, Expr>,
    limits_ref: &LimitsRef,
    translate: &mut TranslateExprs<'smt, 'ctx>,
) -> Result<VerifyOutcome, CaesarError> {
    let builder = ExprBuilder::new(Span::dummy_span());

    let zero_extended_mapping: IndexMap<Ident, Expr> = data
        .tvars
        .iter()
        .map(|(id, ty)| {
            let val = tvar_mapping
                .get(id)
                .cloned()
                .unwrap_or_else(|| builder.zero_lit(ty));
            (*id, val)
        })
        .collect();

    let bool_vc_inst = subst_from_mapping(
        &zero_extended_mapping,
        &data.boolean_vc.vc,
        limits_ref,
        translate.ctx,
    )?;
    let vc_z3 = translate.t_bool(&bool_vc_inst);
    let (prove_result, model) = check_valid(&vc_z3, limits_ref, translate, &data.range_constraints);

    let kind = match prove_result {
        ProveResult::Proof => VerifyOutcomeKind::Proof,
        ProveResult::Counterexample => match model {
            Some(model) => {
                let cex_mapping = create_subst_mapping(&data.pvar_idents, &model, translate);
                VerifyOutcomeKind::Counterexample(cex_mapping)
            }
            None => VerifyOutcomeKind::NoModel,
        },
        ProveResult::Unknown(reason) => VerifyOutcomeKind::Unknown(reason),
    };

    Ok(VerifyOutcome {
        zero_extended_mapping,
        kind,
    })
}

/// Run the synthesizer side of one CEGIS iteration: add the counterexample
/// constraint to the incremental prover and find new template-variable values.
pub fn synthesize_from_cex<'smt, 'ctx>(
    data: &CegisData,
    prover: &mut Prover<'ctx>,
    prover_initialized: &mut bool,
    options: &VerifyCommand,
    limits_ref: &LimitsRef,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    cex_mapping: &IndexMap<Ident, Expr>,
) -> Result<Option<IndexMap<Ident, Expr>>, CaesarError> {
    if !*prover_initialized {
        translate.ctx.add_lit_axioms_to_prover(prover);
        translate.ctx.uninterpreteds().add_axioms_to_prover(prover);
        // Pre-initialize template vars so their type invariants (e.g. >= 0 for UReal)
        // are in the local scope before add_assumptions_to_prover flushes it.
        for (tvar_id, _) in &data.tvars {
            translate.get_local(*tvar_id);
        }
        translate.local_scope().add_assumptions_to_prover(prover);
        for constraint in &data.range_constraints {
            prover.add_assumption(&translate.t_bool(constraint));
        }
        *prover_initialized = true;
    }

    let bool_vc_inst =
        subst_from_mapping(cex_mapping, &data.boolean_vc.vc, limits_ref, translate.ctx)?;
    let cex_task = BoolVcProveTask {
        quant_vc: data.vc_expr.clone(),
        vc: bool_vc_inst,
    };
    get_model_for_constraints(
        prover,
        options,
        cex_task,
        translate,
        &data.tvars.iter().map(|(id, _)| *id).collect(),
        translate.ctx.ctx(),
    )
}

/// Proof found by the CEGIS loop: the synthesized function bodies and the
/// verification tasks used to confirm them.
pub struct CegisProof {
    pub instantiated_templates: Vec<(Ident, Expr)>,
    pub instantiated_tasks: Vec<(Ident, QuantVcProveTask, usize, usize, bool)>,
    pub duration_check: Duration,
}

/// Run the CEGIS loop: repeatedly verify the current candidate and synthesize
/// a new one from counterexamples until a proof is found or the iteration
/// budget is exhausted. Returns `None` if no proof was found.
pub fn run_cegis_loop<'smt, 'ctx>(
    data: &CegisData,
    ctx: &'ctx Context,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    options: &VerifyCommand,
    limits_ref: &LimitsRef,
    name: &SourceUnitName,
    stats: &mut SynthStats,
) -> Result<Option<CegisProof>, CaesarError> {
    let direction = data.vc_expr.direction;

    let mut tvar_mapping: IndexMap<Ident, Expr> = IndexMap::new();
    let mut seen_tvar_maps: IndexSet<String> = IndexSet::new();
    let mut seen_cex_maps: IndexSet<String> = IndexSet::new();
    let mut prover = Prover::new(ctx, IncrementalMode::Native);
    if let Some(remaining) = limits_ref.time_left() {
        prover.set_timeout(remaining);
    }
    let mut prover_initialized = false;
    let mut close_cex_count: usize = 0;
    let mut prev_cex_mapping: Option<IndexMap<Ident, Expr>> = None;
    let mut duration_check = Duration::ZERO;
    let mut proof: Option<CegisProof> = None;
    let mut iteration: usize = 0;

    loop {
        iteration += 1;
        if options.synth_options.syn_verbose {
            println!("=== CEGIS loop {iteration} ===");
        }

        let check_start = Instant::now();
        let outcome = verify_candidate(data, &tvar_mapping, limits_ref, translate)?;
        duration_check += check_start.elapsed();

        if !seen_tvar_maps.insert(canonical_form(&outcome.zero_extended_mapping)) {
            return Err(CaesarError::UserError(
                "Template-variable mapping appeared twice; CEGIS is cycling.".into(),
            ));
        }

        match outcome.kind {
            VerifyOutcomeKind::Proof => {
                let vc_deps = data.vc_expr.deps.clone();
                let mut instantiated_tasks = Vec::new();
                let mut instantiated_templates = Vec::new();
                for t in data.templates.iter() {
                    let concrete_expr = subst_from_mapping(
                        &outcome.zero_extended_mapping,
                        &t.expr,
                        limits_ref,
                        translate.ctx,
                    )?;
                    instantiated_templates.push((t.synth_name, concrete_expr.clone()));
                    let mut task = QuantVcProveTask {
                        expr: concrete_expr,
                        direction,
                        deps: vc_deps.clone(),
                    };
                    task.remove_neutrals(limits_ref, translate.ctx.tcx())?;
                    instantiated_tasks.push((
                        t.synth_name,
                        task,
                        t.guards_before_pruning,
                        t.guards_after_pruning,
                        t.loop_mode,
                    ));
                }
                proof = Some(CegisProof {
                    instantiated_templates,
                    instantiated_tasks,
                    duration_check,
                });
                break;
            }

            VerifyOutcomeKind::Counterexample(cex_mapping) => {
                stats.cex_count += 1;

                if options.synth_options.syn_verbose {
                    println!("Counterexample:");
                    let mut entries: Vec<_> = cex_mapping.iter().collect();
                    entries.sort_by_key(|(id, _)| &id.name);
                    for (id, val) in &entries {
                        println!("  {} -> {val}", id.name);
                    }
                    println!();
                }

                if !seen_cex_maps.insert(canonical_form(&cex_mapping)) {
                    return Err(CaesarError::UserError(
                        "Counterexample appeared twice; CEGIS is cycling.".into(),
                    ));
                }

                if let Some(ref prev) = prev_cex_mapping {
                    let pvars: Vec<_> = cex_mapping
                        .iter()
                        .filter(|(id, _)| !data.tvars.iter().any(|(tid, _)| tid == *id))
                        .collect();
                    let has_numeric = pvars.iter().any(|(_, val)| expr_to_rational(val).is_some());
                    // Distance is meaningless when all program variables are Boolean:
                    // expr_lit_distance returns 0 for non-numeric pairs, so every CEX
                    // would appear "close" and trigger premature refinement.
                    if has_numeric {
                        let dist: BigRational = pvars
                            .iter()
                            .filter_map(|(id, val)| {
                                prev.get(*id)
                                    .map(|prev_val| expr_lit_distance(val, prev_val))
                            })
                            .sum();
                        if dist <= BigRational::from_integer(CLOSE_CEX_DISTANCE_THRESHOLD.into()) {
                            close_cex_count += 1;
                            if options.synth_options.syn_verbose {
                                println!(
                                    "Close CEX (distance={dist}), total count: {close_cex_count}"
                                );
                            }
                            if close_cex_count >= MAX_CLOSE_CEX_COUNT {
                                if options.synth_options.syn_verbose {
                                    println!(
                                        "Close CEX threshold reached ({close_cex_count} total, \
                                     distance <= {CLOSE_CEX_DISTANCE_THRESHOLD}); \
                                     moving to next template refinement."
                                    );
                                }
                                stats.close_cex_refinements += 1;
                                break;
                            }
                        }
                    } // if has_numeric
                }
                if iteration >= MAX_CEGIS_ITERS {
                    if options.synth_options.syn_verbose {
                        println!("Reached max CEGIS iterations ({iteration}) for `{name}`.");
                    }
                    break;
                }

                match synthesize_from_cex(
                    data,
                    &mut prover,
                    &mut prover_initialized,
                    options,
                    limits_ref,
                    translate,
                    &cex_mapping,
                )? {
                    Some(new_tvar_map) => tvar_mapping = new_tvar_map,
                    None => {
                        if options.synth_options.syn_verbose {
                            println!(
                                "No template model found; stopping CEGIS after iteration {iteration}."
                            );
                        }
                        break;
                    }
                }
                prev_cex_mapping = Some(cex_mapping);
            }

            VerifyOutcomeKind::NoModel => {
                if options.synth_options.syn_verbose {
                    println!("Counterexample had no model; stopping.");
                }
                break;
            }

            VerifyOutcomeKind::Unknown(reason) => {
                if options.synth_options.syn_verbose {
                    println!("Solver returned unknown for `{name}`: {reason}");
                }
                break;
            }
        }
    }

    Ok(proof)
}
