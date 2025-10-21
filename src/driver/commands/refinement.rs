use std::{
    ops::{Deref, DerefMut},
    process::ExitCode,
    sync::Arc,
    time::Instant,
};

use ariadne::ReportKind;
use indexmap::IndexMap;
use itertools::Itertools;
use z3rro::{prover::ProveResult, util::ReasonUnknown};

use crate::{
    ast::{
        BinOpKind, DeclKind, Diagnostic, Direction, ExprBuilder, FileId, Ident, Label, ProcDecl,
        Span, TyKind,
    },
    driver::{
        commands::{mk_cli_server, print_timings, verify::VerifyCommand},
        core_verify::{lower_core_verify_task, CoreVerifyTask},
        error::{finalize_caesar_result, CaesarError},
        front::{parse_and_tycheck, SourceUnit},
        item::Item,
        quant_proof::{lower_quant_prove_task, QuantVcProveTask},
        smt_proof::run_smt_prove_task,
    },
    resource_limits::{LimitError, LimitsRef},
    servers::SharedServer,
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

    let timeout = Instant::now() + options.rlimit_options.timeout();
    let mem_limit = options.rlimit_options.mem_limit();
    let limits_ref = LimitsRef::new(Some(timeout), Some(mem_limit));

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
                EntailmentParameterMapping::new(&first_proc.borrow(), &second_proc.borrow())
                    .map_err(|e| e.diagnostic())?
            } else {
                unreachable!();
            }
        } else {
            unreachable!();
        };

        let mut first_verify_unit = first
            .flat_map(|u| CoreVerifyTask::from_source_unit(u, &mut depgraph, false))
            .unwrap();
        let mut second_verify_unit = second
            .flat_map(|u| CoreVerifyTask::from_source_unit(u, &mut depgraph, false))
            .unwrap();

        let (first_vc, first_slice_stmts) = lower_core_verify_task(
            &mut tcx,
            &first_name,
            options,
            &limits_ref,
            server,
            &mut first_verify_unit.enter_mut(),
        )?;
        let (second_vc, second_slice_stmts) = lower_core_verify_task(
            &mut tcx,
            &first_name,
            options,
            &limits_ref,
            server,
            &mut second_verify_unit.enter_mut(),
        )?;

        let vc_expr = params.entails(first_vc, second_vc);

        // Lowering the quantitative task to a Boolean one. This contains (lazy)
        // unfolding, quantifier elimination, and various optimizations
        // (depending on options).
        let vc_is_valid =
            lower_quant_prove_task(options, &limits_ref, &mut tcx, &first_name, vc_expr)?;

        // Running the SMT prove task: translating to Z3, running the solver.
        let slice_vars = first_slice_stmts.extend(second_slice_stmts);
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

/// A mapping from one coproc's parameters to another proc's parameters.
#[derive(Debug)]
struct EntailmentParameterMapping(IndexMap<Ident, (Ident, Box<TyKind>)>);

impl EntailmentParameterMapping {
    fn new(a: &ProcDecl, b: &ProcDecl) -> Result<Self, ParameterMappingError> {
        if a.direction != Direction::Up {
            return Err(ParameterMappingError::UnexpectedDirection(
                a.name,
                a.direction,
            ));
        }
        if b.direction != Direction::Down {
            return Err(ParameterMappingError::UnexpectedDirection(
                b.name,
                b.direction,
            ));
        }

        if a.params_iter().count() != b.params_iter().count() {
            return Err(ParameterMappingError::CountMismatch(
                a.name,
                a.params_iter().count(),
                b.name,
                b.params_iter().count(),
            ));
        }

        let mut mapping = IndexMap::new();
        for (param_a, param_b) in a.params_iter().zip(b.params_iter()) {
            // important: we only compare the names as strings, not the spans
            if param_a.name.name != param_b.name.name {
                return Err(ParameterMappingError::NameMismatch(
                    param_a.name,
                    param_b.name,
                ));
            }
            if param_a.ty != param_b.ty {
                return Err(ParameterMappingError::TypeMismatch(
                    param_a.name,
                    param_a.ty.clone(),
                    param_b.name,
                    param_b.ty.clone(),
                ));
            }
            mapping.insert(param_a.name, (param_b.name, param_b.ty.clone()));
        }

        Ok(EntailmentParameterMapping(mapping))
    }

    pub fn entails(
        self,
        coproc_task: QuantVcProveTask,
        proc_task: QuantVcProveTask,
    ) -> QuantVcProveTask {
        assert_eq!(coproc_task.direction, Direction::Up);
        assert_eq!(proc_task.direction, Direction::Down);

        let builder = ExprBuilder::new(Span::dummy_span());
        let expr = builder.binary(
            BinOpKind::Impl,
            Some(coproc_task.expr.ty.clone().unwrap()),
            coproc_task.expr,
            builder.subst(
                proc_task.expr,
                self.0
                    .into_iter()
                    .map(|(x, (y, ty))| (y, builder.var_ty(x, *ty))),
            ),
        );
        QuantVcProveTask {
            deps: coproc_task.deps.union(proc_task.deps),
            direction: Direction::Down,
            expr,
        }
    }
}

/// An error during the matching of two procedure declarations for entailment
/// checking. The first's direction must
#[derive(Debug)]
pub enum ParameterMappingError {
    UnexpectedDirection(Ident, Direction),
    CountMismatch(Ident, usize, Ident, usize),
    NameMismatch(Ident, Ident),
    TypeMismatch(Ident, Box<TyKind>, Ident, Box<TyKind>),
}

impl ParameterMappingError {
    pub fn diagnostic(&self) -> Diagnostic {
        match self {
            ParameterMappingError::UnexpectedDirection(name, dir) => {
                Diagnostic::new(ReportKind::Error, name.span)
                    .with_message(format!("Expected {} for entailment check", dir.toggle().prefix("proc")))
                    .with_label(Label::new(name.span).with_message("here"))
            }
            ParameterMappingError::CountMismatch(name1, count1, name2, count2) =>
            Diagnostic::new(ReportKind::Error, name1.span)
            .with_message(format!("Mismatched parameter count: {name1} has {count1} parameters, {name2} has {count2} parameters"))
            .with_label(Label::new(name1.span).with_message("first procedure here"))
            .with_label(Label::new(name2.span).with_message("second procedure here")),
            ParameterMappingError::NameMismatch(name1, name2) => Diagnostic::new(ReportKind::Error, name1.span)
            .with_message(format!("Mismatched parameter names: {name1} vs {name2}"))
            .with_label(Label::new(name1.span).with_message(format!("{name1} declared here")))
            .with_label(Label::new(name2.span).with_message(format!("{name2} declared here"))),
            ParameterMappingError::TypeMismatch(name1, ty1, name2, ty2) => Diagnostic::new(ReportKind::Error, name1.span)
            .with_message(format!("Mismatched parameter types: {name1} ({ty1}) vs {name2} ({ty2})"))
            .with_label(Label::new(name1.span).with_message(format!("{name1} declared here")))
            .with_label(Label::new(name2.span).with_message(format!("{name2} declared here"))),
        }
    }
}
