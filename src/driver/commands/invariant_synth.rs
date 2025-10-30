use std::{ops::DerefMut, process::ExitCode, sync::Arc};

use clap::Args;
use tracing::info_span;
use z3::{Context, Goal};
use z3rro::{probes::ProbeSummary, prover::ProveResult, util::ReasonUnknown};

use crate::{
    ast::{ExprBuilder, FileId, Span, Spanned, StmtKind}, driver::{
        commands::{
            mk_cli_server, model_check::run_model_checking, options::SliceVerifyMethod, print_timings, verify::VerifyCommand
        },
        core_verify::{lower_core_verify_task, CoreVerifyTask},
        error::{finalize_caesar_result, CaesarError},
        front::parse_and_tycheck,
        item::Item,
        quant_proof::lower_quant_prove_task,
        smt_proof::{get_smtlib, mk_function_encoder, set_global_z3_params, write_smtlib, SmtVcProveResult, SmtVcProveTask},
    }, resource_limits::{await_with_resource_limits, LimitError, LimitsRef}, servers::{Server, SharedServer}, slicing::solver::{SliceMinimality, SliceSolveOptions, SliceSolver, UnknownHandling}, smt::{translate_exprs::TranslateExprs, DepConfig, SmtCtx}
};

// ? MADITA game plan: 
// Init C: Set of vcs
// 1. Run everything before the proof with the template so that I get 
// the inequality with the template vars uninstantiated. Call this OVC

// 2. Run everything including proof with some tvars valuation (first time choose 0)
// 3a. If cex m, instantiate OVC partially with m|pvars. Add result to C
// 4a. Find a model n that satisfies C (this is a model for the tvars)
// 5a. Go to 2. with this model
// 3b. If not cex, then tvars valuation leads to admissable invariant.


pub async fn run_synth_inv(options: VerifyCommand) -> ExitCode {
    let (user_files, server) = match mk_cli_server(&options.input_options) {
        Ok(value) => value,
        Err(value) => return value,
    };
    let options = Arc::new(options);
    let verify_result = verify_files(&options, &server, user_files).await;

    if options.debug_options.timing {
        print_timings();
    }

    finalize_caesar_result(server, &options.rlimit_options, verify_result)
}

/// Verify a list of `user_files`. The `options.files` value is ignored here.
pub async fn verify_files(
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
                verify_files_main(&options, limits_ref, server.deref_mut(), &user_files)
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

/// Synchronously verify the given source code. This is used for tests. The
/// `--werr` option is enabled by default.
#[cfg(test)]
pub(crate) fn verify_test(source: &str) -> (Result<bool, CaesarError>, crate::servers::TestServer) {
    use crate::ast::SourceFilePath;

    use crate::resource_limits::LimitsRef;

    let mut options = VerifyCommand::default();
    options.input_options.werr = true;

    let mut server = crate::servers::TestServer::new(&options);
    let file_id = server
        .get_files_internal()
        .lock()
        .unwrap()
        .add(SourceFilePath::Builtin, source.to_owned())
        .id;

    let options = Arc::new(options);
    let limits_ref = LimitsRef::new(None, None);
    let res = verify_files_main(&options, limits_ref, &mut server, &[file_id]);
    (res, server)
}

#[cfg(test)]
pub(crate) fn single_desugar_test(source: &str) -> Result<String, CaesarError> {
    use crate::ast::SourceFilePath;

    use crate::driver::front::parse_and_tycheck;

    let mut options = VerifyCommand::default();
    options.input_options.werr = true;

    let mut server = crate::servers::TestServer::new(&options);
    let file_id = server
        .get_files_internal()
        .lock()
        .unwrap()
        .add(SourceFilePath::Builtin, source.to_owned())
        .id;

    let (mut module, mut tcx) = parse_and_tycheck(
        &options.input_options,
        &options.debug_options,
        &mut server,
        &[file_id],
    )?;

    assert_eq!(module.items.len(), 1);

    module.apply_encodings(&mut tcx, &mut server)?;

    Ok(module.to_string())
}

/// Synchronously verify the given files.
fn verify_files_main(
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

    // write to JANI if requested
    run_model_checking(
        &options.model_checking_options,
        &mut module,
        server,
        &limits_ref,
        &tcx,
        false,
    )?;

    // Visit every source unit and check possible cases of unsoundness
    // based on the provided calculus annotations
    module.check_calculus_rules(&mut tcx)?;

    // Desugar encodings from source units.
    module.apply_encodings(&mut tcx, server)?;

    if options.debug_options.print_core_procs {
        println!("HeyVL verification task with generated procs:");
        println!("{module}");
    }

    // If `--no-verify` is set and we don't need to print SMT-LIB or explain the
    // core VC, we can return early.
    if options.debug_options.no_verify
        && !options.lsp_options.explain_core_vc
        && !options.debug_options.z3_probe
        && !options.debug_options.print_smt
        && !options.debug_options.print_core
        && !options.debug_options.print_core_procs
        && options.debug_options.smt_dir.is_none()
    {
        return Ok(true);
    }

    // generate dependency graph to determine which declarations are needed for
    // the SMT translation later
    let mut depgraph = module.generate_depgraph(&options.opt_options.function_encoding)?;

    let mut verify_units: Vec<Item<CoreVerifyTask>> = module
        .items
        .into_iter()
        .flat_map(|item| {
            item.flat_map(|unit| CoreVerifyTask::from_source_unit(unit, &mut depgraph, false))
        })
        .collect();

    if options.debug_options.z3_trace && verify_units.len() > 1 {
        tracing::warn!("Z3 tracing is enabled with multiple verification units. Intermediate tracing results will be overwritten.");
    }

    // set requested global z3 options
    set_global_z3_params(options, &limits_ref);

    let mut num_proven: usize = 0;
    let mut num_failures: usize = 0;

    for verify_unit in &mut verify_units {
        limits_ref.check_limits()?;

        println!("verify unit {verify_unit}");

        let (name, mut verify_unit) = verify_unit.enter_with_name();

        // Set the current unit as ongoing
        server.set_ongoing_unit(name)?;

        // Lowering the core verify task to a quantitative prove task: applying
        // spec call desugaring, preparing slicing, and verification condition
        // generation.
        let (vc_expr, slice_vars) = lower_core_verify_task(
            &mut tcx,
            name,
            options,
            &limits_ref,
            server,
            &mut verify_unit,
        )?;

        // Lowering the quantitative task to a Boolean one. This contains (lazy)
        // unfolding, quantifier elimination, and various optimizations
        // (depending on options).
        let vc_is_valid = lower_quant_prove_task(options, &limits_ref, &mut tcx, name, vc_expr)?;

        let vcv = vc_is_valid.vc.clone();
        println!("vc after lower_quant... {vcv}");

        // run_smt_prove_task
        let ctx = Context::new(&z3::Config::default());
        let function_encoder = mk_function_encoder(&tcx, &depgraph, options)?;
        let dep_config = DepConfig::Set(vc_is_valid.get_dependencies());
        let smt_ctx = SmtCtx::new(&ctx, &tcx, function_encoder, dep_config);
        let mut translate = TranslateExprs::new(&smt_ctx);
        let mut vc_is_valid = SmtVcProveTask::translate(vc_is_valid, &mut translate);

        if !options.opt_options.no_simplify {
            vc_is_valid.simplify();
        }
        let vcv = vc_is_valid.vc.clone();
        println!("vc after translation... {vcv}");

        for ident in translate.local_idents() {
            println!("locals... {:?}", ident);
        }

        if options.debug_options.z3_trace {
            tracing::info!("Z3 tracing output will be written to `z3.log`.");
        }


        let mut result =
            vc_is_valid.run_solver(options, &limits_ref, name, &ctx, &mut translate, &slice_vars)?;

        
        // madita: now i have the quant formula, the model, the original thing
        // I must give it a) the template b) the template variables
        // I want to: in case of cex, take that model
        // and partially instantiate the quant formula with the non-template variables
        // Add the resulting formula to a set of clauses and get 
            
        server
            .handle_vc_check_result(name, &mut result, &mut translate)
            .map_err(CaesarError::ServerError)?;

        let prove_result = result.prove_result;

        // end of run_smt_prove_task

        // Handle reasons to stop the verifier.
        match prove_result {
            ProveResult::Unknown(ReasonUnknown::Interrupted) => {
                return Err(CaesarError::Interrupted)
            }
            ProveResult::Unknown(ReasonUnknown::Timeout) => return Err(LimitError::Timeout.into()),
            _ => {}
        }

        // Increment counters.
        match prove_result {
            ProveResult::Proof => num_proven += 1,
            ProveResult::Counterexample | ProveResult::Unknown(_) => num_failures += 1,
        }
    }

    if !options.lsp_options.language_server {
        println!();
        let ending = if num_failures == 0 {
            " veni, vidi, vici!"
        } else {
            ""
        };
        println!("{num_proven} verified, {num_failures} failed.{ending}");
    }

    Ok(num_failures == 0)
}
