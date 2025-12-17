use std::{collections::HashMap, ops::DerefMut, process::ExitCode, sync::Arc};

use crate::ast::util::remove_casts;
use crate::ast::visit::VisitorMut;
use crate::ast::Ident;
use crate::invariant_synthesis::inv_synth_helpers::{FunctionInliner, create_subst_mapping, get_model_for_constraints, subst_from_mapping};
use crate::invariant_synthesis::template_gen::{build_template_expression, get_synth_functions};
use crate::opt::remove_neutrals::NeutralsRemover;
use crate::opt::unfolder::Unfolder;
use crate::smt::funcs::axiomatic::AxiomaticFunctionEncoder;
use crate::{
    ast::{BinOpKind, Expr, ExprBuilder, FileId, Span, TyKind},
    driver::{
        commands::{mk_cli_server, print_timings, verify::VerifyCommand},
        core_verify::{lower_core_verify_task, CoreVerifyTask},
        error::{finalize_caesar_result, CaesarError},
        front::parse_and_tycheck,
        item::Item,
        quant_proof::{lower_quant_prove_task, BoolVcProveTask, QuantVcProveTask},
        smt_proof::{mk_function_encoder, set_global_z3_params, SmtVcProveTask},
    },
    resource_limits::{await_with_resource_limits, LimitsRef},
    servers::{Server, SharedServer},
    smt::{translate_exprs::TranslateExprs, DepConfig, SmtCtx},
};
use z3::{Config, Context};
use z3rro::prover::ProveResult;
/// The inner loop of the invariant synthesis procedure.
///
/// This loop refines candidate invariants iteratively through several phases:
///
/// Phase 0:Construct the fully uninstantiated verification condition (VC).
///
/// Phase 1: Check whether the current template variables already result in a valid invariant
/// (Check whether VC, evaluated with the template variables, is valid).
///
/// Phase 2:  
/// - If a counterexample is found in Phase 1, use it to (further) constrain the template variables  
///   and search for a new model that satisfies these constraints.  
/// - Otherwise, if no counterexample is found, the current template instantiation
///   is an admissible invariant!
///
/// Phase 3: Instantiate VC with the model found in Phase 2,
/// and return with this to Phase 1.

pub async fn run_synth_inv(options: VerifyCommand) -> ExitCode {
    let (user_files, server) = match mk_cli_server(&options.input_options) {
        Ok(value) => value,
        Err(value) => return value,
    };
    let options = Arc::new(options);
    let result = synth_inv_files(&options, &server, user_files).await;

    if options.debug_options.timing {
        print_timings();
    }

    finalize_caesar_result(server, &options.rlimit_options, result)
}

/// Synthesize invariants for a list of `user_files`. The `options.files` value is ignored here.
pub async fn synth_inv_files(
    options: &Arc<VerifyCommand>,
    server: &SharedServer,
    user_files: Vec<FileId>,
) -> Result<bool, CaesarError> {
    let handle = |limits_ref: LimitsRef| {
        let options = options.clone();
        let server = server.clone();
        tokio::task::spawn_blocking(move || {
            // execute the verifier with a larger stack size of 50MB. the
            // default stack size might be quite small and we need to do quite a
            // lot of recursion.
            let stack_size = 50 * 1024 * 1024;
            stacker::maybe_grow(stack_size, stack_size, move || {
                let mut server = server.lock().unwrap();
                synth_inv_main(&options, limits_ref, server.deref_mut(), &user_files)
            })
        })
    };
    // Unpacking lots of Results with `.await??` :-)
    await_with_resource_limits(
        Some(options.rlimit_options.timeout()),
        Some(options.rlimit_options.mem_limit()),
        handle,
    )
    .await??
}

use std::time::{Duration, Instant};

/// Synchronously synthesize invariants for the given files.
fn synth_inv_main(
    options: &VerifyCommand,
    limits_ref: LimitsRef,
    server: &mut dyn Server,
    user_files: &[FileId],
) -> Result<bool, CaesarError> {
    let start_total = Instant::now();
    let mut split_count = 0;
    let mut num_proven: usize = 0;
    let mut num_failures: usize = 0;
    let mut total_num_cegis_its = 0;
    const MAX_CEGIS_ITERS: usize = 3000;
    const MAX_SPLIT_COUNT: usize = 3;
    let mut template_satchecks = 0;
    let mut duration_template_building = Duration::new(0, 0);

    while split_count <= MAX_SPLIT_COUNT {
        // I have to reset the tcx, how do I do that without parsing new?
        let start_parse = Instant::now();

        let (mut module, mut tcx) = parse_and_tycheck(
            &options.input_options,
            &options.debug_options,
            server,
            user_files,
        )?;
        let duration_parse = start_parse.elapsed(); // Parse time

        println!("Parse time = {:.2}", duration_parse.as_secs_f64());

        // Register all relevant source units with the server
        module.register_with_server(server)?;

        // Visit every source unit and check possible cases of unsoundness
        // based on the provided calculus annotations
        module.check_calculus_rules(&mut tcx)?;

        // Desugar encodings from source units.
        module.apply_encodings(&mut tcx, server)?;

        if options.debug_options.print_core_procs {
            println!("HeyVL invariant synthesis task with generated procs:");
            println!("{module}");
        }

        // generate dependency graph to determine which declarations are needed for
        // the SMT translation later
        let mut depgraph = module.generate_depgraph(&options.opt_options.function_encoding)?;

        let mut synth_inv_units: Vec<Item<CoreVerifyTask>> = module
            .items
            .into_iter()
            .flat_map(|item| {
                item.flat_map(|unit| CoreVerifyTask::from_source_unit(unit, &mut depgraph))
            })
            .collect();

        // set requested global z3 options
        set_global_z3_params(options, &limits_ref);

        for synth_inv_unit in &mut synth_inv_units {
            // --- Phase 0: Create the completely uninstatiated verification condition ---
            limits_ref.check_limits()?;

            let (name, mut synth_inv_unit) = synth_inv_unit.enter_with_name();

            // Set the current unit as ongoing
            server.set_ongoing_unit(name)?;

            // Lowering the core synth_inv_unit task to a quantitative prove task: applying
            // spec call desugaring, preparing slicing, and verification condition
            // generation.
            let (mut vc_expr, slice_vars) = lower_core_verify_task(
                &mut tcx,
                name,
                options,
                &limits_ref,
                server,
                &mut synth_inv_unit,
            )?;

            // The constraints are a conjunction of Expressions, so we start with true

            let direction = vc_expr.direction.clone();
            let vcdeps = vc_expr.deps.clone();

            // Lowering the quantitative task to a Boolean one. This contains (lazy)
            // unfolding, and various optimizations
            // (depending on options).
            // TODO: think about quantifier elimination

            let mut builder = ExprBuilder::new(Span::dummy_span());
            let mut constraints = builder.bool_lit(true);
            let mut vc_is_valid =
                lower_quant_prove_task(options, &limits_ref, &tcx, name, vc_expr.clone())?;
            let ctx = Context::new(&z3::Config::default());
            let function_encoder = mk_function_encoder(&tcx, &depgraph, options)?;
            let dep_config = DepConfig::Set(vc_is_valid.get_dependencies());
            let smt_ctx = SmtCtx::new(&ctx, &tcx, function_encoder, dep_config);
            let mut translate = TranslateExprs::new(&smt_ctx);

            let synth = get_synth_functions(smt_ctx.uninterpreteds());

            let mut templates = Vec::new(); // list of templates (one per synth fn)
            let mut all_template_vars = Vec::new();
            if !synth.is_empty() {
                for (synth_name, synth_val) in synth.iter() {
                    let start_template = Instant::now();

                    // Build template for this particular synthesized function
                    let (temp_template, vars, temp_num_guards, temp_num_sat_checks) =
                        build_template_expression(
                            synth_name,
                            synth_val,
                            &vc_expr.expr,
                            &mut builder,
                            &tcx,
                            split_count,
                            &mut translate,
                            &ctx,
                        );
                    template_satchecks = template_satchecks + temp_num_sat_checks;

                    let duration_template = start_template.elapsed();
                    duration_template_building += duration_template;
                    println!(
                        "Template building for `{}` took: {:.2}",
                        synth_name,
                        duration_template.as_secs_f64()
                    );

                    all_template_vars.extend(vars.clone());

                    // Process the template (unfold, neutral removal, etc.)
                    let ctx = Context::new(&Config::default());
                    let dep_config = DepConfig::SpecsOnly;
                    let smt_ctx_local = SmtCtx::new(
                        &ctx,
                        &tcx,
                        Box::new(AxiomaticFunctionEncoder::default()),
                        dep_config,
                    );

                    let mut tpl = temp_template.clone();

                    let mut unfolder = Unfolder::new(limits_ref.clone(), &smt_ctx_local);
                    unfolder.visit_expr(&mut tpl)?;

                    let mut neutrals_remover =
                        NeutralsRemover::new(limits_ref.clone(), &smt_ctx_local);
                    neutrals_remover.visit_expr(&mut tpl)?;

                    println!("template for `{}`: {}", synth_name, remove_casts(&tpl));

                    // Store the processed template
                    templates.push((synth_name.clone(), tpl, temp_num_guards));
                }

                // Now inline ALL templates into vc_expr
                for (func_ident, template_expr, _num_guards) in templates.iter() {
                    let func_entry = synth
                        .get(func_ident)
                        .expect("synth function disappeared unexpectedly");

                    let mut inliner =
                        FunctionInliner::new(*func_ident, func_entry, template_expr, &tcx);
                    inliner.visit_expr(&mut vc_expr.expr).unwrap();
                }

                // Lower to boolean proof task and unfold
                vc_is_valid =
                    lower_quant_prove_task(options, &limits_ref, &tcx, name, vc_expr.clone())?;
            }

            // This vc_tvars_pvars is the vc where both tvars and pvars are not instantiated.
            // This will be needed later because it will repeatedly get initiated with new tvars,
            // to check if they are IT
            let mut vc_tvars_pvars = SmtVcProveTask::translate(vc_is_valid, &mut translate);

            if !options.opt_options.no_simplify {
                vc_tvars_pvars.simplify();
            }

            if options.debug_options.z3_trace {
                tracing::info!("Z3 tracing output will be written to `z3.log`.");
            }

            let mut iteration = 0;

            // In the first iteration we will use the vc where both tvars and pvars are uninstantiated, but
            // starting from the second loop iteration, the tvars will be instantiated with some value
            let mut vc_pvars;
            let mut tvar_mapping: HashMap<Ident, Expr> = HashMap::new();

            let mut duration_check = Duration::new(0, 0);
            let mut duration_template_inst = Duration::new(0, 0);
            loop {
                total_num_cegis_its += 1;
                let start_check = Instant::now(); // Start the timer for template building

                iteration += 1;
                println!("=== CEGIS loop {iteration} ===");

                // Map all template variables to the value to try out.
                // Template variables with no mapping will be mapped to zero
                let zero_extended_mapping: HashMap<Ident, Expr> = all_template_vars
                    .iter()
                    .cloned()
                    .map(|id| {
                        let value = tvar_mapping
                            .get(&id)
                            .cloned()
                            .unwrap_or_else(|| builder.zero_lit(&TyKind::EUReal));
                        (id.clone(), value)
                    })
                    .collect();

                let instantiated_vc = subst_from_mapping(
                    zero_extended_mapping.clone(),
                    &vc_tvars_pvars.quant_vc.expr,
                );

                println!("mapping used:");
                for (key, val) in &zero_extended_mapping {
                    println!("{key} -> {val}");
                }

                // Rebuild a new Boolean task with the updated formula
                let mut refined_vc = QuantVcProveTask {
                    expr: instantiated_vc,
                    direction: direction,
                    deps: vcdeps.clone(),
                };

                refined_vc.unfold(options, &limits_ref, &tcx)?;
                refined_vc.remove_neutrals(&limits_ref, &tcx)?;

                let refined_vc =
                    lower_quant_prove_task(options, &limits_ref, &tcx, name, refined_vc)?;
                // Translate again to SMT form
                vc_pvars = SmtVcProveTask::translate(refined_vc, &mut translate);

                // println!("finding counterexample for {}", vc_pvars.quant_vc.expr);

                let result = vc_pvars.clone().run_solver(
                    options,
                    &limits_ref,
                    name,
                    &ctx,
                    &mut translate,
                    &slice_vars,
                )?;
                let prove_result = result.prove_result;
                duration_check = start_check.elapsed() + duration_check; // Template instantiation time

                match prove_result {
                    ProveResult::Proof => {
                        num_proven += 1;

                        let mut instantiated_tasks = Vec::new();

                        for (synth_name, template_expr, num_guards) in templates.iter() {
                            let instantiated =
                                subst_from_mapping(zero_extended_mapping.clone(), template_expr);

                            let mut task = QuantVcProveTask {
                                expr: instantiated,
                                direction,
                                deps: vcdeps.clone(),
                            };

                            task.unfold(options, &limits_ref, &tcx)?;
                            task.remove_neutrals(&limits_ref, &tcx)?;

                            instantiated_tasks.push((synth_name.clone(), task));
                            println!(
                                "Number of guard expressions for invariant {synth_name}: {}",
                                num_guards
                            );
                        }

                        let duration_inductivity = start_total.elapsed();

                        println!(
                "After {iteration} CEGIS loop iterations, the following admissible invariants were found:"
            );

                        for (name, task) in instantiated_tasks.iter() {
                            println!("  {} := {}", name, remove_casts(&task.expr));
                        }

                        println!(
                            "Total synthesis took: {:.2}",
                            duration_inductivity.as_secs_f64()
                        );
                        println!(
                            "Template building took: {:.2}",
                            duration_template_building.as_secs_f64()
                        );
                        println!(
                            "Verification checks took: {:.2}",
                            duration_check.as_secs_f64()
                        );
                        println!(
                            "Template instantiation took: {:.2}",
                            duration_template_inst.as_secs_f64()
                        );
                        println!("Number of templates generated: {}", split_count + 1);
                        println!("Number of sat checks/get models done in CEGIS loop to find tvars fullfilling the constraints {total_num_cegis_its}");
                        println!("Number of sat checks in template building {template_satchecks}");
                        split_count = MAX_SPLIT_COUNT + 1;
                        break;
                    }

                    ProveResult::Counterexample => {
                        // println!("Counterexample found, refining template variables...");
                    }
                    ProveResult::Unknown(msg) => {
                        num_failures += 1;
                        println!("Solver returned unknown for {name}: {msg}");
                        break;
                    }
                }

                if iteration >= MAX_CEGIS_ITERS {
                    println!("Reached max num of CEGIS loops ({iteration}) for {name}.");
                    num_failures += 1;
                    break;
                }

                // --- Phase 2: Template-model search ---

                let start_template_instatiate = Instant::now(); // Start the timer for template building

                // Here we add the original vc_tvars_pvars instantiated with the model for the program variables
                // to the constraint we use to find valuations for the template variables.
                if let Some(model) = result.model {
                    let mapping = create_subst_mapping(&model, &mut translate);

                    let filtered_mapping: HashMap<Ident, Expr> = mapping
                        .iter()
                        .filter(|(key, _)| !all_template_vars.contains(key))
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect();

                    let vc_tvars =
                        subst_from_mapping(filtered_mapping, &vc_tvars_pvars.quant_vc.expr);

                    // Create a quantprovetask (so that we get the unfolding)
                    let constraints_on_tvars_task = QuantVcProveTask {
                        expr: vc_tvars,
                        direction: direction,
                        deps: vcdeps.clone(),
                    };

                    let new_constraint = match lower_quant_prove_task(
                        options,
                        &limits_ref,
                        &tcx,
                        name,
                        constraints_on_tvars_task,
                    ) {
                        Ok(c) => c,
                        Err(e) => {
                            return Err(e.into());
                        }
                    };

                    // Add the new constraint to the constraint-set via conjunction
                    constraints = builder.binary(
                        BinOpKind::And,
                        Some(TyKind::Bool),
                        new_constraint.vc,
                        constraints,
                    );

                    // Create a Boolean verification task from the constraints
                    let constraints_on_tvars_bool_task = BoolVcProveTask {
                        quant_vc: new_constraint.quant_vc,
                        vc: constraints.clone(),
                    };

                    // --- Phase 3: Evaluate template variables in original vc ---

                    if let Some(mapping) = get_model_for_constraints(
                        &ctx,
                        options,
                        &limits_ref,
                        constraints_on_tvars_bool_task,
                        &mut translate,
                    )? {
                        // Update template variable mapping; zero-extension happens at top of loop
                        tvar_mapping = mapping;

                        duration_template_inst =
                            start_template_instatiate.elapsed() + duration_template_inst;

                        continue; // restart the loop with the new VC
                    } else {
                        println!(
                "No template model found; stopping CEGIS loop after iteration {iteration}."
            );

                        num_failures += 1;
                        break;
                    }
                }
            }

            split_count = split_count + 1;
        }
    }

    if !options.lsp_options.language_server {
        println!();
        println!("Invariants found for {num_proven}, search failed for {num_failures}.");
    }

    Ok(num_failures == 0)
}
