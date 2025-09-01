use std::{
    ops::{Deref, DerefMut},
    process::ExitCode,
    sync::Arc,
    time::Instant,
};

use itertools::Itertools;
use z3rro::{prover::ProveResult, util::ReasonUnknown};

use crate::{
    ast::{DeclKind, Diagnostic, Direction, ExprBuilder, FileId, Label, Span},
    driver::{
        commands::{mk_cli_server, print_timings, verify::VerifyCommand},
        core_verify::CoreVerifyTask,
        error::{finalize_caesar_result, CaesarError},
        front::{parse_and_tycheck, SourceUnit},
        item::Item,
        quant_proof::lower_quant_prove_task,
        smt_proof::run_smt_prove_task,
    },
    resource_limits::{LimitError, LimitsRef},
    servers::SharedServer,
    slicing::transform::SliceStmts,
    vc::{explain::VcExplanation, vcgen::Vcgen},
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

    finalize_caesar_result(server, &options.rlimit_options, verify_result)
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

        assert_eq!(vcs.len(), 2);
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

        let vc_expr = first_vc.entails(second_vc);

        // Lowering the quantitative task to a Boolean one. This contains (lazy)
        // unfolding, quantifier elimination, and various optimizations
        // (depending on options).
        let vc_is_valid =
            lower_quant_prove_task(options, &limits_ref, &mut tcx, &first_name, vc_expr)?;

        // Running the SMT prove task: translating to Z3, running the solver.
        let slice_vars = SliceStmts::default(); // TODO
        let result = run_smt_prove_task(
            options,
            &limits_ref,
            &tcx,
            &depgraph,
            &first_name,
            server,
            slice_vars,
            vc_is_valid,
        )?;

        // Handle reasons to stop the verifier.
        match result {
            ProveResult::Unknown(ReasonUnknown::Interrupted) => {
                return Err(CaesarError::Interrupted)
            }
            ProveResult::Unknown(ReasonUnknown::Timeout) => return Err(LimitError::Timeout.into()),
            _ => {}
        }
    }

    Ok(true)
}
