use std::{
    ops::{Deref, DerefMut},
    process::ExitCode,
    sync::Arc,
    time::Instant,
};

use itertools::Itertools;
use tracing::info;
use z3::{Config, Context};
use z3rro::{prover::ProveResult, util::ReasonUnknown};

use crate::{
    ast::{DeclKind, Diagnostic, Direction, ExprBuilder, FileId, Label, Span},
    driver::{core_verify::CoreVerifyTask, front::SourceUnit, item::Item},
    finalize_verify_result, mk_cli_server, mk_function_encoder, parse_and_tycheck, print_timings,
    resource_limits::{LimitError, LimitsRef},
    slicing::transform::SliceStmts,
    smt::{translate_exprs::TranslateExprs, DepConfig, SmtCtx},
    vc::{explain::VcExplanation, vcgen::Vcgen},
    CaesarError, SharedServer, VerifyCommand,
};

pub async fn run_verify_entailment_command(options: VerifyCommand) -> ExitCode {
    let (user_files, server) = match mk_cli_server(&options.input_options) {
        Ok(value) => value,
        Err(value) => return value,
    };
    let options = Arc::new(options);
    let verify_result = verify_entailment(&options, &server, user_files).await;

    if options.debug_options.timing {
        print_timings();
    }

    finalize_verify_result(server, &options.rlimit_options, verify_result)
}

async fn verify_entailment(
    options: &VerifyCommand,
    server: &SharedServer,
    user_files: Vec<FileId>,
) -> Result<bool, CaesarError> {
    // TOOD: run verify_files to start the thread with timeouts and stack size
    let mut server = server.lock().unwrap();
    let server = server.deref_mut();

    let (mut module, mut tcx) = parse_and_tycheck(
        &options.input_options,
        &options.debug_options,
        server,
        &user_files,
    )?;

    // Register all relevant source units with the server
    module.register_with_server(server)?;

    // Desugar encodings from source units. They might generate new source
    // units (for side conditions).
    let new_source_units = module.apply_encodings(&mut tcx, server)?;
    if !new_source_units.is_empty() {
        let first_generated_span = new_source_units[0].enter_mut().diagnostic_span();
        server.add_diagnostic(
            Diagnostic::new(ariadne::ReportKind::Error, first_generated_span).with_label(
                Label::new(first_generated_span).with_message(
                    "When checking entailment, generated extra procs are not supported",
                ),
            ),
        )?;
    }

    // generate dependency graph
    let mut depgraph = module.generate_depgraph(&options.opt_options.function_encoding)?;

    let mut proc_source_units: Vec<Item<SourceUnit>> = vec![];
    let mut other_source_units: Vec<Item<SourceUnit>> = vec![];
    for mut source_unit in module.items {
        let is_entailment_proc = match source_unit.enter_mut().deref() {
            SourceUnit::Decl(DeclKind::ProcDecl(decl_ref)) => {
                decl_ref.borrow().body.borrow().is_some()
            }
            _ => false,
        };
        if is_entailment_proc {
            proc_source_units.push(source_unit);
        } else {
            other_source_units.push(source_unit);
        }
    }

    for mut source_unit_chunk in proc_source_units.into_iter().chunks(2).into_iter() {
        let first = source_unit_chunk.next().unwrap();
        let first_name = first.name().clone();
        let second = source_unit_chunk.next().unwrap();
        assert!(source_unit_chunk.next().is_none());

        let params = if let (SourceUnit::Decl(first_decl), SourceUnit::Decl(second_decl)) =
            (first.deref(), second.deref())
        {
            if let (DeclKind::ProcDecl(first_proc), DeclKind::ProcDecl(second_proc)) =
                (first_decl, second_decl)
            {
                let first_proc = first_proc.borrow();
                let second_proc = second_proc.borrow();

                if first_proc.direction != Direction::Up {
                    server.add_diagnostic(
                        Diagnostic::new(ariadne::ReportKind::Error, first_proc.name.span)
                            .with_label(
                                Label::new(first_proc.name.span)
                                    .with_message("Expected coproc for entailment check"),
                            ),
                    )?;
                }
                if second_proc.direction != Direction::Down {
                    server.add_diagnostic(
                        Diagnostic::new(ariadne::ReportKind::Error, second_proc.name.span)
                            .with_label(
                                Label::new(second_proc.name.span)
                                    .with_message("Expected proc for entailment check"),
                            ),
                    )?;
                }

                // importantly, we need to do substitutions for *both* inputs and outputs!
                let first_params = first_proc
                    .inputs
                    .node
                    .iter()
                    .chain(first_proc.outputs.node.iter())
                    .cloned()
                    .collect_vec();
                let second_params = second_proc
                    .inputs
                    .node
                    .iter()
                    .chain(second_proc.outputs.node.iter())
                    .cloned()
                    .collect_vec();
                (first_params, second_params)
            } else {
                unreachable!();
            }
        } else {
            unreachable!();
        };

        let mut first_verify_unit = first
            .flat_map(|u| CoreVerifyTask::from_source_unit(u, &mut depgraph))
            .unwrap();
        let mut second_verify_unit = second
            .flat_map(|u| CoreVerifyTask::from_source_unit(u, &mut depgraph))
            .unwrap();

        let mut vcs = vec![];
        for verify_unit in [&mut first_verify_unit, &mut second_verify_unit] {
            let (name, mut verify_unit) = verify_unit.enter_with_name();

            // 4. Desugaring: transforming spec calls to procs
            verify_unit.desugar_spec_calls(&mut tcx, name.to_string())?;

            // 5. Prepare slicing
            // TODO: add proper support
            let _slice_vars =
                verify_unit.prepare_slicing(&options.slice_options, &mut tcx, server)?;

            // 6. Generating verification conditions.
            let explanations = options
                .lsp_options
                .explain_core_vc
                .then(|| VcExplanation::new(verify_unit.direction));
            let limits_ref = LimitsRef::new(None, None); // TODO
            let mut vcgen = Vcgen::new(&tcx, &limits_ref, explanations);
            let vc_expr = verify_unit.vcgen(&mut vcgen)?;
            if let Some(explanation) = vcgen.explanation {
                server.add_vc_explanation(explanation)?;
            }
            vcs.push(vc_expr);
        }

        let timeout = Instant::now() + options.rlimit_options.timeout();
        let mem_limit = options.rlimit_options.mem_limit();
        let limits_ref = LimitsRef::new(Some(timeout), Some(mem_limit));

        let first_vc = vcs.remove(0);
        let mut second_vc = vcs.remove(0);
        let builder = ExprBuilder::new(Span::dummy_span());
        second_vc.expr = builder.subst(
            second_vc.expr.clone(),
            params
                .1
                .iter()
                .map(|x| x.name)
                .zip(params.0.iter().map(|y| builder.var(y.name, &tcx))),
        );

        let mut vc_expr = first_vc.entails(second_vc);

        // 7. Unfolding (applies substitutions)
        vc_expr.unfold(options, &limits_ref, &tcx)?;

        // 8. Quantifier elimination
        if !options.opt_options.no_qelim {
            vc_expr.qelim(&mut tcx, &limits_ref)?;
        }

        // In-between, gather some stats about the vc expression
        vc_expr.trace_expr_stats();

        // 9. Create the "vc[S] is valid" expression
        let mut vc_is_valid = vc_expr.into_bool_vc();

        if options.opt_options.egraph {
            vc_is_valid.egraph_simplify();
        }

        // 10. Optimizations
        if !options.opt_options.no_boolify || options.opt_options.opt_rel {
            vc_is_valid.remove_parens();
        }
        if !options.opt_options.no_boolify {
            vc_is_valid.opt_boolify();
        }
        if options.opt_options.opt_rel {
            vc_is_valid.opt_relational();
        }

        // 11. Translate to Z3
        let ctx = Context::new(&Config::default());
        let function_encoder = mk_function_encoder(&tcx, &depgraph, options)?;
        let dep_config = DepConfig::Set(vc_is_valid.get_dependencies());
        let smt_ctx = SmtCtx::new(&ctx, &tcx, function_encoder, dep_config);
        let mut translate = TranslateExprs::new(&smt_ctx);
        let mut vc_is_valid = vc_is_valid.into_smt_vc(&mut translate);

        // 12. Simplify
        if !options.opt_options.no_simplify {
            vc_is_valid.simplify();
        }

        // 13. Create Z3 solver with axioms, solve
        let slice_vars = SliceStmts::default(); // TODO
        let mut result = vc_is_valid.run_solver(
            options,
            &limits_ref,
            &first_name, // TODO
            &ctx,
            &mut translate,
            &slice_vars,
        )?;

        server
            .handle_vc_check_result(&first_name, &mut result, &mut translate)
            .map_err(CaesarError::ServerError)?;

        if options.debug_options.z3_trace {
            info!("Z3 tracing output will be written to `z3.log`.");
        }

        // Handle reasons to stop the verifier.
        match result.prove_result {
            ProveResult::Unknown(ReasonUnknown::Interrupted) => {
                return Err(CaesarError::Interrupted)
            }

            ProveResult::Unknown(ReasonUnknown::Timeout) => return Err(LimitError::Timeout.into()),
            _ => {}
        }
    }

    Ok(true)
}
