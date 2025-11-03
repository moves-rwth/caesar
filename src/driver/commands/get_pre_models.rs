use std::{ops::DerefMut, process::ExitCode, sync::Arc};

use crate::{
    ast::{BinOpKind, Direction, ExprBuilder, FileId, Span, TyKind},
    driver::{
        commands::{mk_cli_server, print_timings, verify::VerifyCommand},
        core_heyvl::{lower_core_heyvl_task, CoreHeyVLTask},
        error::{finalize_caesar_result, CaesarError},
        front::parse_and_tycheck,
        item::Item,
        quant_proof::BoolVcProveTask,
        smt_proof::{run_smt_check_sat, set_global_z3_params},
    },
    resource_limits::{await_with_resource_limits, LimitsRef},
    servers::{Server, SharedServer},
};
use z3::SatResult;

pub async fn run_nontrivial_model_command(options: VerifyCommand) -> ExitCode {
    let (user_files, server) = match mk_cli_server(&options.input_options) {
        Ok(value) => value,
        Err(value) => return value,
    };
    let options = Arc::new(options);
    let nontrivial_models_result = nontrivial_model_files(&options, &server, user_files).await;

    if options.debug_options.timing {
        print_timings();
    }

    finalize_caesar_result(server, &options.rlimit_options, nontrivial_models_result)
}

/// This is just like verify_files()
pub async fn nontrivial_model_files(
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
                nontrivial_model_files_main(&options, limits_ref, server.deref_mut(), &user_files)
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

fn nontrivial_model_files_main(
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

    // explain high-level HeyVL if requested
    if options.lsp_options.explain_vc {
        module.explain_high_level_vc(&tcx, &limits_ref, server)?;
    }

    // Desugar encodings from source units.
    module.apply_encodings(&mut tcx, server)?;

    if options.debug_options.print_core_procs {
        println!("HeyVL get nontrivial model task with generated procs:");
        println!("{module}");
    }

    // generate dependency graph to determine which declarations are needed for
    // the SMT translation later
    let mut depgraph = module.generate_depgraph(&options.opt_options.function_encoding)?;

    // translate program to relevant preexpectation conditions
    let mut verify_units: Vec<Item<CoreHeyVLTask>> = module
        .items
        .into_iter()
        .flat_map(|item| {
            item.flat_map(|unit| CoreHeyVLTask::from_proc_pre_model(unit, &mut depgraph))
        })
        .collect();

    if options.debug_options.z3_trace && verify_units.len() > 1 {
        tracing::warn!("Z3 tracing is enabled with multiple units. Intermediate tracing results will be overwritten.");
    }
    // set requested global z3 options
    set_global_z3_params(options, &limits_ref);

    let mut num_sat: usize = 0;
    let mut num_unsat: usize = 0;

    for verify_unit in &mut verify_units {
        limits_ref.check_limits()?;

        let (name, mut verify_unit) = verify_unit.enter_with_name();

        // Set the current unit as ongoing
        server.set_ongoing_unit(name)?;

        // no slicing
        let mut new_options = VerifyCommand::default();
        new_options.slice_options.no_slice_error = true;

        let (vc_expr, _slice_vars) = lower_core_heyvl_task(
            &mut tcx,
            name,
            &new_options,
            &limits_ref,
            server,
            &mut verify_unit,
        )?;

        // Lowering the quantitative task to a Boolean one.
        let mut quant_task = vc_expr;

        // Unfolding (applies substitutions)
        quant_task.unfold(options, &limits_ref, &tcx)?;

        quant_task.trace_expr_stats();

        // Turn quantitative formula into a Boolean one
        let builder = ExprBuilder::new(Span::dummy_span());
        let top = builder.top_lit(quant_task.expr.ty.as_ref().unwrap());
        let bot = builder.bot_lit(quant_task.expr.ty.as_ref().unwrap());
        let expr = quant_task.expr.clone();

        // Construct the condition based on quantifier direction
        let res = match quant_task.direction {
            Direction::Up => {
                // For coprocs, check if expr < top
                builder.binary(BinOpKind::Lt, Some(TyKind::Bool), expr, top)
            }
            Direction::Down => {
                // For procs, check if expr > bot
                builder.binary(BinOpKind::Gt, Some(TyKind::Bool), expr, bot)
            }
        };

        // Create a Boolean verification task with the comparison
        let mut bool_task = BoolVcProveTask {
            quant_vc: quant_task,
            vc: res,
        };

        // Optimizations
        if !options.opt_options.no_boolify || options.opt_options.opt_rel {
            bool_task.remove_parens();
        }
        if !options.opt_options.no_boolify {
            bool_task.opt_boolify();
        }
        if options.opt_options.opt_rel {
            bool_task.opt_relational();
        }

        if options.debug_options.print_theorem {
            bool_task.print_theorem(name);
        }

        // Running the SMT check sat task: translating to Z3, running the solver.
        // This also handles printing the result
        let sat_result = run_smt_check_sat(
            &options,
            &limits_ref,
            &tcx,
            &depgraph,
            &name,
            bool_task,
            server,
        )?;

        // Handle reasons to stop the verifier.
        match sat_result {
            SatResult::Unknown => return Err(CaesarError::Interrupted),
            _ => {}
        }

        // Increment counters.
        match sat_result {
            SatResult::Sat => num_sat += 1,
            SatResult::Unsat | SatResult::Unknown => num_unsat += 1,
        }
    }

    if !options.lsp_options.language_server {
        println!();
        println!(
            "Found models for {num_sat} (co)procedures, No models for {num_unsat} (co)procedures."
        );
    }

    Ok(num_unsat == 0)
}
