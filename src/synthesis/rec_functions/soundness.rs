use crate::{
    ast::{
        visit::{walk_expr, VisitorMut},
        DeclKind, Expr, ExprKind, Ident,
    },
    depgraph::DepGraph,
    driver::{
        commands::verify::VerifyCommand,
        error::CaesarError,
        item::SourceUnitName,
        quant_proof::{lower_quant_prove_task, QuantVcProveTask},
        smt_proof::{check_valid, mk_function_encoder_override},
    },
    resource_limits::{LimitsRef, MemorySize},
    smt::{translate_exprs::TranslateExprs, DepConfig, SmtCtx},
    tyctx::TyCtx,
};

pub struct SoundnessCheckConfig<'a> {
    pub options: &'a VerifyCommand,
    pub limits_ref: &'a LimitsRef,
    pub depgraph: &'a DepGraph,
    pub name: &'a SourceUnitName,
    pub current_fuel: usize,
}

fn inline_nullary_call_in_domain_bodies(
    func_name: Ident,
    replacement: &Expr,
    all_domain_funcs: &[Ident],
    tcx: &TyCtx,
) {
    struct Replacer {
        func: Ident,
        replacement: Expr,
    }
    impl VisitorMut for Replacer {
        type Err = ();
        fn visit_expr(&mut self, e: &mut Expr) -> Result<(), ()> {
            if let ExprKind::Call(ref f, ref args) = e.kind {
                if *f == self.func && args.is_empty() {
                    *e = self.replacement.clone();
                    return Ok(());
                }
            }
            walk_expr(self, e)
        }
    }

    for &ident in all_domain_funcs {
        if let Some(decl) = tcx.get(ident) {
            if let DeclKind::FuncDecl(func_ref) = decl.as_ref() {
                let body_opt: Option<Expr> = func_ref.borrow().body.borrow().clone();
                if let Some(mut body) = body_opt {
                    let mut replacer = Replacer {
                        func: func_name,
                        replacement: replacement.clone(),
                    };
                    replacer.visit_expr(&mut body).unwrap();
                    *func_ref.borrow().body.borrow_mut() = Some(body);
                }
            }
        }
    }
}
use std::time::{Duration, Instant};
use z3::Context;
use z3rro::prover::ProveResult;

const MAX_FUEL_INCREASES: usize = 5;

/// Result of the soundness check run after a successful CEGIS iteration.
pub enum SoundnessOutcome {
    Proved,
    RetryWithFuel,
    NoConclusion,
}

/// Re-verify the original VC (without assume guards) with the synthesized
/// function bodies plugged in, to check the candidate invariant is actually sound.
pub fn run_soundness_check(
    instantiated_templates: Vec<(Ident, Expr)>,
    range_constraints: &[Expr],
    vc_expr_orig: QuantVcProveTask,
    tcx: &mut TyCtx,
    config: &SoundnessCheckConfig<'_>,
    target_funcs: &[Ident],
) -> Result<SoundnessOutcome, CaesarError> {
    let depgraph = config.depgraph;
    let options = config.options;
    let limits_ref = config.limits_ref;
    let name = config.name;
    let current_fuel = config.current_fuel;
    println!("Checking soundness: verifying invariant holds without assume statements...");

    // Install each instantiated template as the function body so the encoder treats it as defined.
    for (synth_name, concrete_template) in &instantiated_templates {
        if let Some(decl) = tcx.get(*synth_name) {
            if let DeclKind::FuncDecl(func_ref) = decl.as_ref() {
                *func_ref.borrow().body.borrow_mut() = Some(concrete_template.clone());
            }
        }
        inline_nullary_call_in_domain_bodies(*synth_name, concrete_template, target_funcs, tcx);
    }

    let ctx_sound = Context::new(&z3::Config::default());
    let function_encoder_sound =
        mk_function_encoder_override(tcx, depgraph, options, false, Some(current_fuel))?;

    let vc_orig_valid =
        lower_quant_prove_task(options, limits_ref, tcx, name, vc_expr_orig.clone())?;

    let dep_config_sound = DepConfig::Set(vc_orig_valid.get_dependencies());
    let smt_ctx_sound = SmtCtx::new(&ctx_sound, tcx, function_encoder_sound, dep_config_sound);
    let mut translate_sound = TranslateExprs::new(&smt_ctx_sound);

    let soundness_cap = Duration::from_secs(options.synth_options.soundness_timeout);
    let soundness_deadline = {
        let now = Instant::now();
        let cap_deadline = now + soundness_cap;
        match limits_ref.time_left() {
            Some(remaining) => cap_deadline.min(now + remaining),
            None => cap_deadline,
        }
    };
    let soundness_limits_ref = LimitsRef::new(Some(soundness_deadline), None::<MemorySize>);

    let vc_z3 = translate_sound.t_bool(&vc_orig_valid.vc);
    let (prove_result, _) = check_valid(
        &vc_z3,
        &soundness_limits_ref,
        &mut translate_sound,
        range_constraints,
    );

    match prove_result {
        ProveResult::Proof => {
            println!("Soundness check passed: invariant holds without assume statements.");
            Ok(SoundnessOutcome::Proved)
        }
        ProveResult::Counterexample => {
            if current_fuel.saturating_sub(options.opt_options.max_fuel) < MAX_FUEL_INCREASES {
                println!(
                    "Soundness check failed at fuel {current_fuel}; \
                     retrying with fuel {}.",
                    current_fuel + 1
                );
                Ok(SoundnessOutcome::RetryWithFuel)
            } else {
                println!(
                    "Soundness check FAILED after {MAX_FUEL_INCREASES} fuel increases; \
                     invariant does NOT hold without assume statements.",
                );
                Ok(SoundnessOutcome::NoConclusion)
            }
        }
        ProveResult::Unknown(_) => {
            if current_fuel.saturating_sub(options.opt_options.max_fuel) < MAX_FUEL_INCREASES {
                println!(
                    "Soundness check inconclusive at fuel {current_fuel}; \
                     retrying with fuel {}.",
                    current_fuel + 1
                );
                Ok(SoundnessOutcome::RetryWithFuel)
            } else {
                println!(
                    "Soundness check inconclusive after {MAX_FUEL_INCREASES} fuel increases; giving up.",
                );
                Ok(SoundnessOutcome::NoConclusion)
            }
        }
    }
}
