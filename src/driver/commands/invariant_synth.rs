use std::{collections::HashMap, ops::DerefMut, process::ExitCode, sync::Arc};

use crate::ast::util::remove_casts;
use crate::ast::visit::VisitorMut;
use crate::ast::Ident;
use crate::smt::partial_eval::{create_subst_mapping, subst_mapping};
use crate::{
    ast::{self, BinOpKind, Expr, ExprBuilder, FileId, Span, TyKind},
    driver::{
        commands::{mk_cli_server, print_timings, verify::VerifyCommand},
        core_verify::{lower_core_verify_task, CoreVerifyTask},
        error::{finalize_caesar_result, CaesarError},
        front::parse_and_tycheck,
        item::Item,
        quant_proof::{lower_quant_prove_task, BoolVcProveTask, QuantVcProveTask},
        smt_proof::{
            build_template_expression, get_synth_functions, mk_function_encoder,
            set_global_z3_params, update_vc_with_model, SmtVcProveTask,
        },
    },
    resource_limits::{await_with_resource_limits, LimitsRef},
    servers::{Server, SharedServer},
    smt::{partial_eval::FunctionInliner, translate_exprs::TranslateExprs, DepConfig, SmtCtx},
};
use z3::Context;
use z3rro::prover::ProveResult;
///! Right now, just imagine there is only one syn fun. Later maybe some sort of counting up should happen?
///! How do I actually put the template instance into the function?
///! Okay lets think...
///! For just linear: For each input parameter, create one template variable + one extra one
///! Then put them together in a sum, somehow get that into the function body,
///! Once for each boolean condition and negated (this might be a bit nonsensical, its just for now)
///
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

/// Synchronously synthesize invariants for the given files.
fn synth_inv_main(
    options: &VerifyCommand,
    limits_ref: LimitsRef,
    server: &mut dyn Server,
    user_files: &[FileId],
) -> Result<bool, CaesarError> {
    let (mut module, mut tcx) = parse_and_tycheck(
        &options.input_options,
        &options.debug_options,
        server,
        user_files,
    )?;

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

    let mut num_proven: usize = 0;
    let mut num_failures: usize = 0;

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
        let builder = ExprBuilder::new(Span::dummy_span());
        let mut constraints = builder.bool_lit(true);

        let direction = vc_expr.direction.clone();
        let vcdeps = vc_expr.deps.clone();

        // Lowering the quantitative task to a Boolean one. This contains (lazy)
        // unfolding, quantifier elimination, and various optimizations
        // (depending on options).
        let mut vc_is_valid =
            lower_quant_prove_task(options, &limits_ref, &tcx, name, vc_expr.clone())?;

        let ctx = Context::new(&z3::Config::default());
        let function_encoder = mk_function_encoder(&tcx, &depgraph, options)?;
        let dep_config = DepConfig::Set(vc_is_valid.get_dependencies());
        let smt_ctx = SmtCtx::new(&ctx, &tcx, function_encoder, dep_config);
        let mut translate = TranslateExprs::new(&smt_ctx);

        let synth = get_synth_functions(smt_ctx.uninterpreteds());

        let mut template = builder.bool_lit(true);

        let mut template_vars = Vec::new();
        if !synth.is_empty() {
            let (temp_template, vars) =
                build_template_expression(&synth, &vc_expr.expr, &builder, &tcx);
            template_vars = vars;
            template = temp_template;
            // Create a quantprovetask (so that we get the unfolding)
            let mut template_task = QuantVcProveTask {
                expr: template.clone(),
                direction: direction,
                deps: vcdeps.clone(),
            };

            // Unfolding (applies substitutions)
            template_task.unfold(options, &limits_ref, &tcx)?;

            println!("template: {:}", template_task.expr);

            let (&func_ident, func_entry) = synth
                .iter()
                .next()
                .expect("synth should contain exactly one function");

            let mut inliner = FunctionInliner {
                target: func_ident,
                body: &template,
                entry: func_entry,
            };

            inliner.visit_expr(&mut vc_expr.expr).unwrap();

            vc_is_valid =
                lower_quant_prove_task(options, &limits_ref, &tcx, name, vc_expr.clone())?;
        }

        // Madita, okay, now I just have to get the template into the function. Or replace the function with it?
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
        const MAX_REFINEMENT_ITERS: usize = 10;

        // In the first iteration we will use the vc where both tvars and pvars are uninstantiated, but
        // starting from the second loop iteration, the tvars will be instantiated with some value
        let mut vc_pvars = vc_tvars_pvars.clone();

        let mut tvar_mapping: HashMap<ast::symbol::Ident, Expr> = HashMap::new();

        loop {
            iteration += 1;
            // println!("=== Refinement iteration {iteration} ===");

            // Instantiating the template and doing unfolding just for logging.
            // TODO: This should just be optional
            // let instantiated_template = subst_mapping(tvar_mapping.clone(), &template);

            // let mut template_task = QuantVcProveTask {
            //     expr: instantiated_template,
            //     direction: direction,
            //     deps: vcdeps.clone(),
            // };

            // // Unfolding (applies substitutions)
            // template_task.unfold(options, &limits_ref, &tcx)?;
            // println!("Checking template: {}", template_task.expr);

            // --- Phase 1: Check if tvars are already good (run verification with some eval) ---

            // After the first iteration, vc_pvars shouldn't have any template variables in it
            // Run the solver
            let result = vc_pvars.clone().run_solver(
                options,
                &limits_ref,
                name,
                &ctx,
                &mut translate,
                &slice_vars,
            )?;

            // This result is Proof iff we have already found an admissable template variable evaluation
            // Otherwise it will give us a cex (an evaluation of the program vars) that we will
            // add to the constraints on the template vars
            let prove_result = result.prove_result;

            match prove_result {
                ProveResult::Proof => {
                    num_proven += 1;
                    let instantiated_template = subst_mapping(tvar_mapping, &template);

                    let mut template_task = QuantVcProveTask {
                        expr: instantiated_template,
                        direction: direction,
                        deps: vcdeps.clone(),
                    };

                    // Unfolding (applies substitutions)
                    template_task.unfold(options, &limits_ref, &tcx)?;
                    println!("After {iteration} iterations, the following admissable invariant was found: {}", remove_casts(&template_task.expr));
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

            if iteration >= MAX_REFINEMENT_ITERS {
                println!("Reached max refinement iterations for {name}.");
                num_failures += 1;
                break;
            }

            // --- Phase 2: Template-model search ---

            // Here we add the original vc_tvars_pvars instantiated with the model for the program variables
            // to the constraint we use to find valuations for the template variables.
            if let Some(model) = result.model {
                // vc_tvars: pre <~ code(post)
                // this is 0 iff pre >= code(post) (valid if 0)
                let mapping =
                    create_subst_mapping(&model, &vc_tvars_pvars.quant_vc.expr, &mut translate);

                let filtered_mapping: HashMap<Ident, Expr> = mapping
                    .iter()
                    .filter(|(key, _)| !template_vars.contains(key))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();

                let vc_tvars = subst_mapping(filtered_mapping, &vc_tvars_pvars.quant_vc.expr);

                // Create a quantprovetask (so that we get the unfolding)
                let mut constraints_on_tvars_task = QuantVcProveTask {
                    expr: vc_tvars,
                    direction: direction,
                    deps: vcdeps.clone(),
                };

                // Unfolding (applies substitutions)
                constraints_on_tvars_task.unfold(options, &limits_ref, &tcx)?;

                // For validity later, we will look for a model, s.t. expr = bot
                let bot = builder.bot_lit(constraints_on_tvars_task.expr.ty.as_ref().unwrap());
                let new_constraint = builder.binary(
                    BinOpKind::Eq,
                    Some(TyKind::Bool),
                    constraints_on_tvars_task.expr.clone(),
                    bot,
                );

                // Add the new constraint to the constraint-"set" via conjunction
                constraints = builder.binary(
                    BinOpKind::And,
                    Some(TyKind::Bool),
                    new_constraint,
                    constraints.clone(),
                );

                // Create a Boolean verification task from the constraints
                let constraints_on_tvars_bool_task = BoolVcProveTask {
                    quant_vc: constraints_on_tvars_task,
                    vc: constraints.clone(),
                };

                // --- Phase 3: Evaluate template variables in original vc ---

                if let Some((new_vc_pvars, mapping)) = update_vc_with_model(
                    &ctx,
                    options,
                    &limits_ref,
                    &tcx,
                    &name,
                    constraints_on_tvars_bool_task,
                    &vc_tvars_pvars.quant_vc,
                    &direction,
                    &vcdeps,
                    &mut translate,
                    template_vars.clone(),
                )? {
                    vc_pvars = new_vc_pvars;
                    tvar_mapping = mapping;
                    continue; // restart the loop with the new VC
                } else {
                    println!(
                        "No template model found; stopping refinement after iteration {iteration}."
                    );
                    num_failures += 1;
                    break;
                }
            }
        }
    }

    if !options.lsp_options.language_server {
        println!();
        println!("Invariants found for {num_proven}, search failed for {num_failures}.");
    }

    Ok(num_failures == 0)
}
