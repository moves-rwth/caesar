use std::{ops::DerefMut, process::ExitCode, sync::Arc};

use z3rro::{prover::ProveResult, util::ReasonUnknown};

use crate::{
    ast::FileId,
    driver::{
        commands::{mk_cli_server, print_timings, verify::VerifyCommand},
        core_verify::{lower_core_verify_task, CoreVerifyTask},
        error::{finalize_caesar_result, CaesarError},
        front::parse_and_tycheck,
        item::Item,
        quant_proof::lower_quant_prove_task,
        smt_proof::set_global_z3_params,
    },
    resource_limits::{await_with_resource_limits, LimitError, LimitsRef},
    servers::{Server, SharedServer},
};

pub async fn run_get_model_command(options: VerifyCommand) -> ExitCode {
    let (user_files, server) = match mk_cli_server(&options.input_options) {
        Ok(value) => value,
        Err(value) => return value,
    };
    let options = Arc::new(options);
    let get_models_result = get_model_files(&options, &server, user_files).await;

    if options.debug_options.timing {
        print_timings();
    }

    finalize_caesar_result(server, &options.rlimit_options, get_models_result)
}

/// This is just like verify_files()
pub async fn get_model_files(
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
                get_model_files_main(&options, limits_ref, server.deref_mut(), &user_files)
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

fn get_model_files_main(
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
        println!("HeyVL get model task with generated procs:");
        println!("{module}");
    }

    // generate dependency graph to determine which declarations are needed for
    // the SMT translation later
    let mut depgraph = module.generate_depgraph(&options.opt_options.function_encoding)?;

    // here the translation from the program to the relevant preexpectation conditions happens
    let mut verify_units: Vec<Item<CoreVerifyTask>> = module
        .items
        .into_iter()
        .flat_map(|item| {
            item.flat_map(|unit| CoreVerifyTask::from_source_unit(unit, &mut depgraph, true))
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

        let (vc_expr, slice_vars) = lower_core_verify_task(
            &mut tcx,
            name,
            &new_options,
            &limits_ref,
            server,
            &mut verify_unit,
        )?;
        // Lowering the quantitative task to a Boolean one. This contains (lazy)
        // unfolding, quantifier elimination, and various optimizations
        // (depending on options).
        let vc_is_valid = lower_quant_prove_task(options, &limits_ref, &mut tcx, name, vc_expr)?;

        // Running the SMT prove task: translating to Z3, running the solver.
        let result = crate::driver::smt_proof::run_smt_prove_task(
            options,
            &limits_ref,
            &tcx,
            &depgraph,
            name,
            server,
            slice_vars,
            vc_is_valid,
            true,
        )?;

        // Handle reasons to stop the verifier.
        match result {
            ProveResult::Unknown(ReasonUnknown::Interrupted) => {
                return Err(CaesarError::Interrupted)
            }
            ProveResult::Unknown(ReasonUnknown::Timeout) => return Err(LimitError::Timeout.into()),
            _ => {}
        }

        // Increment counters.
        match result {
            ProveResult::Counterexample => num_sat += 1,
            ProveResult::Proof | ProveResult::Unknown(_) => num_unsat += 1,
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
