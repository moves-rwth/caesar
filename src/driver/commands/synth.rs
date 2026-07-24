use crate::ast::util::FreeVariableCollector;
use crate::ast::visit::VisitorMut;
use crate::ast::{Expr, Ident, Symbol};
use crate::depgraph::DepGraph;
use crate::driver::commands::options::{FunctionEncodingOption, RefinementMode};
use crate::driver::item::SourceUnitName;
use crate::driver::ranges::{collect_ranges_from_decls, create_range_constraint};
use crate::synthesis::cegis::{get_synth_functions, run_cegis_loop, CegisData, CegisProof};
use crate::synthesis::k_induction::{
    collect_k_induction_calls, read_k_induction_k, set_k_induction_k,
};
use crate::synthesis::rec_functions::InsertAssumeBeforeCalls;
use crate::synthesis::rec_functions::{
    run_soundness_check, SoundnessCheckConfig, SoundnessOutcome,
};
use crate::synthesis::report::{self as synth_report, SynthStats};
use crate::synthesis::templates::{build_and_inline_templates, RefinementState, TemplateConfig};
use crate::tyctx::TyCtx;
use crate::{
    ast::{DeclKind, DomainSpec, FileId},
    driver::{
        commands::{mk_cli_server, print_timings, verify::VerifyCommand},
        core_verify::{lower_core_verify_task, CoreVerifyTask},
        error::{finalize_caesar_result, CaesarError},
        front::{parse_and_tycheck, SourceUnit},
        quant_proof::{lower_quant_prove_task, BoolVcProveTask, QuantVcProveTask},
        smt_proof::{mk_function_encoder_override, set_global_z3_params},
    },
    resource_limits::{await_with_resource_limits, LimitsRef},
    servers::{Server, SharedServer},
    smt::{translate_exprs::TranslateExprs, DepConfig, SmtCtx},
};

#[allow(clippy::collapsible_match)]
fn get_functions_from_source_unit(source_unit: &SourceUnit) -> Vec<Ident> {
    let mut funcs = Vec::new();
    if let SourceUnit::Decl(decl) = source_unit {
        if let DeclKind::DomainDecl(domain_ref) = decl {
            let domain = domain_ref.borrow();
            for spec in &domain.body {
                if let DomainSpec::Function(func_ref) = spec {
                    funcs.push(func_ref.borrow().name);
                }
            }
        }
    }
    funcs
}
use indexmap::{IndexMap, IndexSet};
use std::time::Instant;
use std::{ops::DerefMut, process::ExitCode, sync::Arc};
use z3::Context;

pub async fn run_synth(mut options: VerifyCommand) -> ExitCode {
    let (user_files, server) = match mk_cli_server(&options.input_options) {
        Ok(result) => result,
        Err(code) => return code,
    };
    options.slice_options.no_slice_error = true;
    if options.synth_options.rec_functions
        && options.opt_options.function_encoding == FunctionEncodingOption::FuelParam
    {
        options.opt_options.function_encoding = FunctionEncodingOption::FuelMono;
    }
    let options = Arc::new(options);
    let result = synth_files(&options, &server, user_files).await;

    if options.debug_options.timing {
        print_timings();
    }

    finalize_caesar_result(server, &options.rlimit_options, result)
}

// Synthesize invariants for a list of `user_files`.
pub async fn synth_files(
    options: &Arc<VerifyCommand>,
    server: &SharedServer,
    user_files: Vec<FileId>,
) -> Result<bool, CaesarError> {
    let handle = |limits_ref: LimitsRef| {
        let options = options.clone();
        let server = server.clone();
        tokio::task::spawn_blocking(move || {
            // Use a larger stack (50 MB) since the verifier recurses deeply.
            let stack_size = 50 * 1024 * 1024;
            stacker::maybe_grow(stack_size, stack_size, move || {
                let mut server = server.lock().unwrap();
                synth_main(&options, limits_ref, server.deref_mut(), &user_files)
            })
        })
    };
    let limits_ref = LimitsRef::new(
        Some(Instant::now() + options.rlimit_options.timeout()),
        Some(options.rlimit_options.mem_limit()),
    );
    await_with_resource_limits(limits_ref, handle).await??
}

// Synchronously synthesize invariants for the given files using CEGIS.
fn synth_main(
    options: &VerifyCommand,
    limits_ref: LimitsRef,
    server: &mut dyn Server,
    user_files: &[FileId],
) -> Result<bool, CaesarError> {
    // Parse once upfront to collect item names and (for KInduction) the initial k.
    let (mut module_init, _) = parse_and_tycheck(
        &options.input_options,
        &options.debug_options,
        server,
        user_files,
    )?;
    // Refinement counter: for KInduction this is k, for Degree it's the polynomial degree,
    // for Fixed/Variable it's the number of piecewise intervals.
    let refinement_mode = options.synth_options.refinement_mode;
    let initial_degree = options.synth_options.degree.unwrap_or(1);
    let initial_refinement_iter: usize = match refinement_mode {
        RefinementMode::KInduction => read_k_induction_k(&mut module_init).unwrap_or(1) as usize,
        RefinementMode::Degree => initial_degree,
        _ => 1,
    };
    // Items proven across all outer iterations.
    let mut proven_item_names: IndexSet<String> = IndexSet::new();
    let mut stats = SynthStats::new();
    // Fuel for the guarded encoding; bumped on each soundness-check failure.
    let mut current_fuel: usize = options.opt_options.max_fuel;

    // Collect names upfront; they're stable across re-parses.
    let item_names: Vec<String> = module_init
        .items
        .iter()
        .map(|item| item.name().to_string())
        .collect();

    // Process each item sequentially: complete all refinement iterations for
    // one item before starting the next.
    for target_name in &item_names {
        let mut refinement_iter = initial_refinement_iter;
        let max_refinement_iter = if refinement_mode == RefinementMode::None {
            refinement_iter
        } else {
            refinement_iter + options.synth_options.max_refinements.unwrap_or(300)
        };

        'refinement: while refinement_iter <= max_refinement_iter {
            let effective_split_count = match refinement_mode {
                RefinementMode::Degree | RefinementMode::KInduction => 1,
                _ => refinement_iter,
            };
            let effective_degree = match refinement_mode {
                RefinementMode::Degree => refinement_iter,
                _ => initial_degree,
            };

            if options.synth_options.syn_verbose {
                match refinement_mode {
                    RefinementMode::Degree => println!("Degree {refinement_iter}"),
                    RefinementMode::None => println!("Single CEGIS attempt"),
                    RefinementMode::Variable | RefinementMode::Fixed => {
                        println!("{refinement_iter} interval(s)")
                    }
                    RefinementMode::KInduction => {
                        println!("Iteration {refinement_iter} (k-induction, k={refinement_iter})")
                    }
                }
            }

            // Re-parse on every refinement iteration to get a clean type context.
            let start_parse = Instant::now();
            let (mut module, mut tcx) = parse_and_tycheck(
                &options.input_options,
                &options.debug_options,
                server,
                user_files,
            )?;
            if options.synth_options.syn_benchmarks {
                println!("Parse time = {:.2}s", start_parse.elapsed().as_secs_f64());
            }

            if refinement_mode == RefinementMode::Fixed
                && collect_ranges_from_decls(&tcx.declarations.borrow()).is_empty()
            {
                return Err(CaesarError::UserError(
                    "--refinement-mode fixed requires at least one type range declaration (e.g. `a: UInt [0,3]`)"
                        .into(),
                ));
            }

            // Update k in every @k_induction(k, ...) annotation to the current
            // refinement iteration, so the encoding uses the right unrolling depth.
            if refinement_mode == RefinementMode::KInduction {
                set_k_induction_k(&mut module, refinement_iter as u128);
            }

            // Collect inv_call args from @k_induction before the module is consumed,
            // so we can reprint the updated annotation in the synthesized output.
            let k_induction_calls = if refinement_mode == RefinementMode::KInduction {
                collect_k_induction_calls(&mut module)
            } else {
                Default::default()
            };

            let refinement = RefinementState {
                mode: refinement_mode,
                iter: refinement_iter,
                effective_split_count,
                effective_degree,
            };

            module.register_with_server(server)?;
            module.check_calculus_rules(&mut tcx)?;
            module.apply_encodings(&mut tcx, server)?;

            let mut depgraph = module.generate_depgraph(&options.opt_options.function_encoding)?;

            let domain_funcs: Vec<Ident> = if options.synth_options.rec_functions {
                module
                    .items
                    .iter()
                    .flat_map(|item| get_functions_from_source_unit(item))
                    .collect()
            } else {
                vec![]
            };

            set_global_z3_params(options, &limits_ref);

            for item in module.items {
                if item.name().to_string() != *target_name {
                    continue;
                }

                // Skip non-proc items (e.g. domain declarations) that have no VC to synthesize.
                let Some(mut synth_unit) =
                    item.flat_map(|unit| CoreVerifyTask::from_source_unit(unit, &mut depgraph))
                else {
                    break 'refinement;
                };

                // Clone before applying assumes so the soundness check can use the original VC.
                let mut orig_unit = None;
                if options.synth_options.rec_functions {
                    orig_unit = Some(synth_unit.value().clone());
                    let task = synth_unit.value_mut();
                    let mut visitor = InsertAssumeBeforeCalls {
                        func_idents: &domain_funcs,
                        direction: task.direction,
                        tcx: &tcx,
                        max_fuel: current_fuel,
                    };
                    visitor.visit_block(&mut task.block).unwrap();
                }

                limits_ref.check_limits()?;
                let (name, mut synth_unit) = synth_unit.enter_with_name();
                let name_str = name.to_string();
                server.set_ongoing_unit(name)?;

                if options.debug_options.print_core_procs {
                    println!("Core HeyVL (with assume statements) for `{name}`:");
                    println!("{}", *synth_unit);
                }

                let (vc_expr, _) = lower_core_verify_task(
                    &mut tcx,
                    name,
                    options,
                    &limits_ref,
                    server,
                    &mut synth_unit,
                )?;

                let vc_is_valid =
                    lower_quant_prove_task(options, &limits_ref, &tcx, name, vc_expr.clone())?;

                // Compute the original (no-assume) VC while &mut tcx is still available.
                let vc_expr_orig_opt: Option<QuantVcProveTask> =
                    if options.synth_options.rec_functions {
                        let (vc, _) = lower_core_verify_task(
                            &mut tcx,
                            name,
                            options,
                            &limits_ref,
                            server,
                            &mut orig_unit.unwrap(),
                        )?;
                        Some(vc)
                    } else {
                        None
                    };

                let cegis_config = CegisItemConfig {
                    tcx: &tcx,
                    depgraph: &depgraph,
                    options,
                    limits_ref: &limits_ref,
                    current_fuel,
                    refinement: &refinement,
                };
                let (instantiated_templates, range_constraints) = run_cegis_for_item(
                    &cegis_config,
                    name,
                    vc_expr,
                    vc_is_valid,
                    &mut stats,
                    &k_induction_calls,
                )?;

                // soundness check: verify the found invariant also holds on the original VC (no assumes)
                if options.synth_options.rec_functions {
                    if let Some(instantiated_templates) = instantiated_templates {
                        if let Some(vc_expr_orig) = vc_expr_orig_opt {
                            let soundness_config = SoundnessCheckConfig {
                                options,
                                limits_ref: &limits_ref,
                                depgraph: &depgraph,
                                name,
                                current_fuel,
                            };
                            match run_soundness_check(
                                instantiated_templates,
                                &range_constraints,
                                vc_expr_orig,
                                &mut tcx,
                                &soundness_config,
                                &domain_funcs,
                            )? {
                                SoundnessOutcome::Proved => {
                                    proven_item_names.insert(name_str.clone());
                                    break 'refinement;
                                }
                                SoundnessOutcome::RetryWithFuel => {
                                    current_fuel += 1;
                                    continue 'refinement;
                                }
                                SoundnessOutcome::NoConclusion => {}
                            }
                        }
                    }
                } else if instantiated_templates.is_some() {
                    // Non-recursive: invariant found by CEGIS is immediately valid.
                    proven_item_names.insert(name_str.clone());
                    break 'refinement;
                }
            }

            refinement_iter += 1;
        }
    }

    if proven_item_names.is_empty() {
        println!("No template instantiation found that leads to a verifying function body.");
    }
    Ok(!proven_item_names.is_empty())
}

struct CegisItemConfig<'a> {
    tcx: &'a TyCtx,
    depgraph: &'a DepGraph,
    options: &'a VerifyCommand,
    limits_ref: &'a LimitsRef,
    current_fuel: usize,
    refinement: &'a RefinementState,
}

type CegisItemResult = (Option<Vec<(Ident, Expr)>>, Vec<Expr>);

/// Run the CEGIS loop for one synthesis item and return the instantiated
/// templates (if any) and the range constraints collected from declarations.
fn run_cegis_for_item(
    config: &CegisItemConfig<'_>,
    name: &SourceUnitName,
    vc_expr: QuantVcProveTask,
    vc_is_valid: BoolVcProveTask,
    stats: &mut SynthStats,
    k_induction_calls: &IndexMap<Symbol, String>,
) -> Result<CegisItemResult, CaesarError> {
    let ctx = Context::new(&z3::Config::default());
    let tcx = config.tcx;
    let depgraph = config.depgraph;
    let options = config.options;
    let limits_ref = config.limits_ref;
    let refinement = config.refinement;
    let current_fuel = config.current_fuel;
    let function_encoder = mk_function_encoder_override(
        tcx,
        depgraph,
        options,
        // rec_functions: disable synonym axiom during CEGIS so the solver only
        // sees the guarded approximation; the soundness check re-enables it.
        options.synth_options.rec_functions || options.opt_options.no_synonym_axiom,
        Some(current_fuel),
    )?;
    let smt_ctx = SmtCtx::new(
        &ctx,
        tcx,
        function_encoder,
        DepConfig::Set(vc_is_valid.get_dependencies()),
    );
    let mut translate = TranslateExprs::new(&smt_ctx);

    let mut vc_expr = vc_expr;
    let mut vc_is_valid = vc_is_valid;

    let template_config = TemplateConfig {
        options,
        limits_ref,
        refinement,
    };
    let (templates, tvars) = build_and_inline_templates(
        &mut translate,
        &mut vc_expr,
        &mut vc_is_valid,
        &template_config,
        name,
        stats,
    )?;

    let synth_funcs = get_synth_functions(smt_ctx.uninterpreteds());

    let tvar_ident_set: IndexSet<Ident> = tvars.iter().map(|(id, _)| *id).collect();
    let pvar_idents: IndexSet<Ident> = FreeVariableCollector::new()
        .collect_and_clear(&mut vc_is_valid.vc)
        .difference(&tvar_ident_set)
        .cloned()
        .collect();

    let range_constraints: Vec<Expr> = collect_ranges_from_decls(&tcx.declarations.borrow())
        .iter()
        .map(|(ident, (range, ty))| create_range_constraint(*ident, range, ty.clone()))
        .collect();

    let cegis_data = CegisData {
        templates,
        pvar_idents,
        tvars,
        range_constraints,
        boolean_vc: vc_is_valid,
        vc_expr,
    };

    let cegis_proof = run_cegis_loop(
        &cegis_data,
        &ctx,
        &mut translate,
        options,
        limits_ref,
        name,
        stats,
    )?;

    let instantiated_templates = cegis_proof.map(
        |CegisProof {
             instantiated_templates,
             instantiated_tasks,
             duration_check,
         }| {
            if options.synth_options.syn_benchmarks {
                synth_report::print_benchmark_info(
                    stats,
                    duration_check,
                    refinement.iter,
                    &instantiated_tasks,
                );
            }
            synth_report::print_synthesized_bodies(
                &instantiated_tasks,
                &synth_funcs,
                k_induction_calls,
                refinement.iter,
            );
            instantiated_templates
        },
    );

    Ok((instantiated_templates, cegis_data.range_constraints))
}
