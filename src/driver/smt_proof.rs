//! SMT-based proofs of formulas.

use std::collections::HashMap;
use std::fs::{create_dir_all, File};
use std::io::Write;

use ariadne::ReportKind;
use itertools::Itertools;
use tracing::info_span;

use z3::{
    ast::{Ast, Bool},
    Context, Goal,
};
use z3rro::params::SmtParams;
use z3rro::quantifiers::QuantifierMeta;
use z3rro::{
    model::InstrumentedModel,
    probes::ProbeSummary,
    prover::{IncrementalMode, ProveResult, Prover},
    smtlib::Smtlib,
    util::{PrefixWriter, ReasonUnknown},
};

use crate::ast::{self, Expr};
use crate::depgraph::DepGraph;
use crate::driver::commands::options::{
    DebugOptions, FunctionEncodingOption, QuantifierInstantiation, SliceVerifyMethod,
};
use crate::driver::commands::verify::VerifyCommand;
use crate::driver::error::CaesarError;
use crate::driver::item::SourceUnitName;
use crate::driver::quant_proof::{BoolVcProveTask, QuantVcProveTask};
use crate::slicing::transform::SliceStmts;
use crate::smt::funcs::axiomatic::{AxiomInstantiation, AxiomaticFunctionEncoder, PartialEncoding};
use crate::smt::funcs::fuel::literals::LiteralExprCollector;
use crate::smt::funcs::fuel::{
    FuelEncodingOptions, FuelMonoFunctionEncoder, FuelParamFunctionEncoder,
};
use crate::smt::funcs::{FunctionEncoder, RecFunFunctionEncoder};
use crate::smt::inv_synth_helpers::create_subst_mapping;
use crate::smt::{DepConfig, SmtCtx};
use crate::tyctx::TyCtx;
use crate::{
    ast::{DeclKind, DeclKindName, Diagnostic, Label, Span, VarKind},
    pretty::Doc,
    resource_limits::LimitsRef,
    servers::Server,
    slicing::{
        model::SliceModel,
        solver::{SliceMinimality, SliceSolveOptions, SliceSolver, UnknownHandling},
    },
    smt::{
        pretty_model::{
            pretty_model, pretty_slice, pretty_unaccessed, pretty_var_value, pretty_vc_value,
        },
        translate_exprs::TranslateExprs,
    },
    version::write_detailed_command_info,
};

/// Initialize global Z3 parameters based on the command's options.
///
/// Uses [`SmtParams`] so that the written options can be read via
/// [`SmtParams::global`].
pub fn set_global_z3_params(command: &VerifyCommand, limits_ref: &LimitsRef) {
    let mut global_params = SmtParams::global().lock().unwrap();

    // see also dafny's options:
    // https://github.com/dafny-lang/dafny/blob/220fdecb25920d2f72ceb4c57af6cb032fdd337d/Source/DafnyCore/DafnyOptions.cs#L1273-L1309

    // we disable order axioms, as this seems to fix all of our performance
    // issues after upgrading from 4.12.1 to 4.15.1.
    //
    // see also this commit in 4.15.2:
    // https://github.com/Z3Prover/z3/commit/bba10c7a8892f1067ee68751fd9989037a3386de.
    // maybe this will solve the problem?
    global_params.set_param("smt.arith.nl.order", "false");

    // enable tracing if requested
    if command.debug_options.z3_trace {
        global_params.set_param("trace", "true");
        global_params.set_param("proof", "true");
        global_params.set_param("trace_file_name", "z3.log");
    }

    // set random seed
    if let Some(seed) = command.debug_options.z3_seed {
        global_params.set_param("smt.random_seed", &seed.to_string());
    }

    // set quantifier instantiation options
    global_params.set_param("smt.qi.eager_threshold", "100");
    global_params.set_param("smt.qi.lazy_threshold", "1000");
    match command.opt_options.quantifier_instantiation {
        QuantifierInstantiation::EMatching => {
            // we *could* fully disable MBQI (and thus also auto-config) like so:
            // ```
            // z3::set_global_param("auto-config", "false");
            // z3::set_global_param("smt.mbqi", "false");
            // ```
            // but this can have some strange side effects (turns out MBQI can
            // be rather useful sometimes).
            //
            // therefore, we set a specific prefix for quantifiers, so that MBQI
            // only acts on quantifiers whose id starts with that prefix.
            global_params.set_param("smt.mbqi.id", QuantifierMeta::MBQI_PREFIX);
        }
        QuantifierInstantiation::Mbqi => {
            global_params.set_param("smt.ematching", "false");
        }
        QuantifierInstantiation::All => {}
    }

    // enable the quantifier instantiation profile if requested
    if command.debug_options.z3_qi_profile {
        global_params.set_param("smt.qi.profile", "true");
        global_params.set_param("smt.qi.profile_freq", "1000");
    }

    // enable MBQI tracing if requested
    if command.debug_options.z3_mbqi_trace {
        global_params.set_param("smt.mbqi.trace", "true");
    }

    // set verbosity level
    if let Some(verbosity) = command.debug_options.z3_verbose {
        global_params.set_param("verbose", &verbosity.to_string());
    }

    if let Some(timeout) = limits_ref.time_left() {
        global_params.set_param("timeout", &timeout.as_millis().to_string());
    }
}

/// Run the SMT prove task: translate to Z3, run the solver, notify the server,
/// and return the result.
#[allow(clippy::too_many_arguments)]
pub fn run_smt_prove_task(
    options: &VerifyCommand,
    limits_ref: &LimitsRef,
    tcx: &TyCtx,
    depgraph: &DepGraph,
    name: &SourceUnitName,
    server: &mut dyn Server,
    slice_vars: SliceStmts,
    vc_is_valid: BoolVcProveTask,
) -> Result<ProveResult, CaesarError> {
    let ctx = Context::new(&z3::Config::default());
    let function_encoder = mk_function_encoder(tcx, depgraph, options)?;
    let dep_config = DepConfig::Set(vc_is_valid.get_dependencies());
    let smt_ctx = SmtCtx::new(&ctx, tcx, function_encoder, dep_config);
    let mut translate = TranslateExprs::new(&smt_ctx);
    let mut vc_is_valid = SmtVcProveTask::translate(vc_is_valid, &mut translate);

    if !options.opt_options.no_simplify {
        vc_is_valid.simplify();
    }

    if options.debug_options.z3_trace {
        tracing::info!("Z3 tracing output will be written to `z3.log`.");
    }

    let mut result =
        vc_is_valid.run_solver(options, limits_ref, name, &ctx, &mut translate, &slice_vars)?;

    server
        .handle_vc_check_result(name, &mut result, &mut translate)
        .map_err(CaesarError::ServerError)?;

    Ok(result.prove_result)
}

/// Get a model for the constraints if it exists and instantiate vc_tvars_pvars with it
pub fn get_model_for_constraints<'smt, 'ctx, 'tcx: 'ctx>(
    ctx: &'ctx z3::Context,
    options: &VerifyCommand,
    limits_ref: &LimitsRef,
    name: &SourceUnitName,
    constraints: BoolVcProveTask,
    translate: &mut TranslateExprs<'smt, 'ctx>,
) -> Result<Option<HashMap<ast::symbol::Ident, Expr>>, CaesarError> {
    let mut constraints_prove_task = SmtVcProveTask::translate(constraints, translate);
    if !options.opt_options.no_simplify {
        constraints_prove_task.simplify();
    }
    let mut prover = Prover::new(&ctx, IncrementalMode::Native);
    if let Some(remaining) = limits_ref.time_left() {
        prover.set_timeout(remaining);
    }
    if let Some(smtlib) = get_smtlib(options, &prover) {
        write_smtlib(&options.debug_options, name, &smtlib, None)?;
    }
    // Add axioms and assumptions
    translate.ctx.add_lit_axioms_to_prover(&mut prover);
    translate
        .ctx
        .uninterpreteds()
        .add_axioms_to_prover(&mut prover);
    translate
        .local_scope()
        .add_assumptions_to_prover(&mut prover);

    // Add the verification condition. This should be checked for satisfiability.
    // Therefore, add_assumption is used (which just adds it as an smtlib assert)
    // vs. add_provable, which would negate it first.
    prover.add_assumption(&constraints_prove_task.vc);

    // Run solver & retrieve model if available
    prover.check_sat();
    let model = prover.get_model();

    // If we find a model for the template constraints, filter it to the template variables and create a mapping from it.
    if let Some(template_model) = model {
        let mapping = create_subst_mapping(&template_model, translate);
        Ok(Some(mapping))
    } else {
        // No template model found;.
        Ok(None)
    }
}

/// Create the function encoder based on the given command's options.
pub fn mk_function_encoder<'ctx>(
    tcx: &TyCtx,
    depgraph: &DepGraph,
    options: &VerifyCommand,
) -> Result<Box<dyn FunctionEncoder<'ctx> + 'ctx>, CaesarError> {
    let fe_opt = options.opt_options.function_encoding;
    let partial_encoding = if options.opt_options.no_partial_strengthening {
        PartialEncoding::Partial
    } else {
        PartialEncoding::StrengthenToTotal
    };
    let function_encoding = match fe_opt {
        FunctionEncodingOption::Axiomatic => {
            AxiomaticFunctionEncoder::new(AxiomInstantiation::Bidirectional, partial_encoding)
                .into_boxed()
        }
        FunctionEncodingOption::Decreasing => {
            AxiomaticFunctionEncoder::new(AxiomInstantiation::Decreasing, partial_encoding)
                .into_boxed()
        }
        FunctionEncodingOption::FuelMono
        | FunctionEncodingOption::FuelParam
        | FunctionEncodingOption::FuelMonoComputation
        | FunctionEncodingOption::FuelParamComputation => {
            let fuel_functions = tcx
                .get_function_decls()
                .into_iter()
                .filter(|f| {
                    let f = f.borrow();
                    f.body.borrow().is_some() && depgraph.is_potentially_recursive(f.name)
                })
                .map(|f| f.borrow().name)
                .collect();
            tracing::debug!("Using fuel encoding for functions: {:?}", fuel_functions);
            let fuel_options = FuelEncodingOptions {
                fuel_functions,
                partial_encoding,
                max_fuel: options.opt_options.max_fuel,
                computation: matches!(
                    fe_opt,
                    FunctionEncodingOption::FuelMonoComputation
                        | FunctionEncodingOption::FuelParamComputation
                ),
                synonym_axiom: !options.opt_options.no_synonym_axiom,
            };
            match fe_opt {
                FunctionEncodingOption::FuelMono | FunctionEncodingOption::FuelMonoComputation => {
                    FuelMonoFunctionEncoder::new(fuel_options).into_boxed()
                }
                FunctionEncodingOption::FuelParam
                | FunctionEncodingOption::FuelParamComputation => {
                    FuelParamFunctionEncoder::new(fuel_options).into_boxed()
                }
                _ => unreachable!(),
            }
        }
        FunctionEncodingOption::DefineFunRec => {
            if partial_encoding == PartialEncoding::StrengthenToTotal {
                return Err(CaesarError::UserError(
                    "--function-encoding define-fun-rec does not support disabling function strengthening.".into(),
                ));
            }
            RecFunFunctionEncoder::new().into_boxed()
        }
    };
    // Warn if using fuel encoding with non-ematching quantifier
    // instantiation. The exception is the [`FuelEncodingOption::FuelMono`]
    // encoding, which does not rely on Z3 not creating new terms for termination.
    if matches!(
        options.opt_options.function_encoding,
        FunctionEncodingOption::FuelParam
            | FunctionEncodingOption::FuelMonoComputation
            | FunctionEncodingOption::FuelParamComputation
    ) && options.opt_options.quantifier_instantiation != QuantifierInstantiation::EMatching
    {
        tracing::warn!(
            "Using fuel function encoding with MBQI still enabled does not guarantee termination. Set the `--quantifier-instantiation e-matching` option to use the fuel encoding without MBQI.",
        );
    }
    Ok(function_encoding)
}

/// The verification condition validitiy formula as a Z3 formula.
#[derive(Clone)]
pub struct SmtVcProveTask<'ctx> {
    pub quant_vc: QuantVcProveTask,
    pub vc: Bool<'ctx>,
}

impl<'ctx> SmtVcProveTask<'ctx> {
    /// Create a new SMT verification condition proof task.
    pub fn translate<'smt>(
        mut task: BoolVcProveTask,
        translate: &mut TranslateExprs<'smt, 'ctx>,
    ) -> SmtVcProveTask<'ctx> {
        let span = info_span!("translation to Z3");
        let _entered = span.enter();

        if translate.ctx.lit_wrap {
            let literal_exprs =
                LiteralExprCollector::new(translate.ctx).collect_literals(&mut task.vc);
            translate.set_literal_exprs(literal_exprs);
        }

        let bool_vc = translate.t_bool(&task.vc);

        if translate.ctx.lit_wrap {
            translate.set_literal_exprs(Default::default());
        }

        SmtVcProveTask {
            quant_vc: task.quant_vc,
            vc: bool_vc,
        }
    }

    /// Simplify the SMT formula using Z3's simplifier.
    pub fn simplify(&mut self) {
        let span = info_span!("simplify query");
        let _entered = span.enter();
        self.vc = self.vc.simplify();
    }

    /// Run the solver(s) on this SMT formula.
    pub fn run_solver<'smt>(
        self,
        options: &VerifyCommand,
        limits_ref: &LimitsRef,
        name: &SourceUnitName,
        ctx: &'ctx Context,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        slice_vars: &SliceStmts,
    ) -> Result<SmtVcProveResult<'ctx>, CaesarError> {
        let span = info_span!("SAT check");
        let _entered = span.enter();

        let prover = mk_valid_query_prover(limits_ref, ctx, translate, &self.vc);

        if options.debug_options.z3_probe {
            let goal = Goal::new(ctx, false, false, false);
            for assertion in prover.get_assertions() {
                goal.assert(&assertion);
            }
            eprintln!(
                "Probe results for {}:\n{}",
                name,
                ProbeSummary::probe(ctx, &goal)
            );
        }

        let smtlib = get_smtlib(options, &prover);
        if let Some(smtlib) = &smtlib {
            write_smtlib(&options.debug_options, name, smtlib, None)?;
        }

        if options.debug_options.no_verify {
            return Ok(SmtVcProveResult {
                prove_result: ProveResult::Unknown(ReasonUnknown::Other(
                    "verification skipped".to_owned(),
                )),
                model: None,
                slice_model: None,
                quant_vc: self.quant_vc,
            });
        }

        let mut slice_solver = SliceSolver::new(slice_vars.clone(), translate, prover);
        let failing_slice_options = SliceSolveOptions {
            minimality: if options.slice_options.slice_error_first {
                SliceMinimality::Any
            } else {
                SliceMinimality::Size
            },
            unknown: if options.slice_options.slice_error_inconsistent {
                UnknownHandling::Accept
            } else {
                UnknownHandling::Stop
            },
        };

        // this is the main call to the SMT solver for the verification task!
        let (result, models) =
            slice_solver.slice_failing_binary_search(&failing_slice_options, limits_ref)?;
        let (model, mut slice_model) = match models {
            Some((model, slice_model)) => (Some(model), Some(slice_model)),
            None => (None, None),
        };

        // if the program was successfully proven, do slicing for verification
        if options.slice_options.slice_verify && matches!(result, ProveResult::Proof) {
            match options.slice_options.slice_verify_via {
                SliceVerifyMethod::UnsatCore => {
                    slice_model = slice_solver.slice_verifying_unsat_core(limits_ref)?;
                }
                SliceVerifyMethod::MinimalUnsatSubset => {
                    let slice_options = SliceSolveOptions {
                        minimality: SliceMinimality::Subset,
                        unknown: UnknownHandling::Continue,
                    };
                    slice_model =
                        slice_solver.slice_verifying_enumerate(&slice_options, limits_ref)?;
                }
                SliceVerifyMethod::SmallestUnsatSubset => {
                    let slice_options = SliceSolveOptions {
                        minimality: SliceMinimality::Size,
                        unknown: UnknownHandling::Continue,
                    };
                    slice_model =
                        slice_solver.slice_verifying_enumerate(&slice_options, limits_ref)?;
                }
                SliceVerifyMethod::ExistsForall => {
                    let slice_options = SliceSolveOptions {
                        minimality: SliceMinimality::Any,
                        unknown: UnknownHandling::Stop,
                    };
                    if translate.ctx.uninterpreteds().is_empty() {
                        slice_model = slice_solver
                            .slice_verifying_exists_forall(&slice_options, limits_ref)?;
                    } else {
                        tracing::warn!("There are uninterpreted sorts, functions, or axioms present. Slicing for correctness is disabled because it does not support them.");
                    }
                }
            }
        }

        if options.debug_options.z3_stats {
            let stats = slice_solver.get_statistics();
            eprintln!("Z3 statistics for {name}: {stats:?}");
        }

        if let Some(smtlib) = &smtlib {
            // only print to the directory again
            let options = DebugOptions {
                print_smt: false,
                smt_dir: options.debug_options.smt_dir.clone(),
                ..options.debug_options
            };
            write_smtlib(&options, name, smtlib, Some(&result))?;
        }

        Ok(SmtVcProveResult {
            prove_result: result,
            model,
            slice_model,
            quant_vc: self.quant_vc,
        })
    }
}

fn mk_valid_query_prover<'smt, 'ctx>(
    limits_ref: &LimitsRef,
    ctx: &'ctx Context,
    smt_translate: &TranslateExprs<'smt, 'ctx>,
    valid_query: &Bool<'ctx>,
) -> Prover<'ctx> {
    // create the prover and set the params
    let mut prover = Prover::new(ctx, IncrementalMode::Native);
    if let Some(remaining) = limits_ref.time_left() {
        prover.set_timeout(remaining);
    }

    // add the definition of all used Lit marker functions
    smt_translate.ctx.add_lit_axioms_to_prover(&mut prover);
    // add assumptions (from axioms and locals) to the prover
    smt_translate
        .ctx
        .uninterpreteds()
        .add_axioms_to_prover(&mut prover);
    smt_translate
        .local_scope()
        .add_assumptions_to_prover(&mut prover);
    // add the provable: is this Boolean true?
    prover.add_provable(valid_query);
    prover
}

fn get_smtlib(options: &VerifyCommand, prover: &Prover) -> Option<Smtlib> {
    if options.debug_options.print_smt || options.debug_options.smt_dir.is_some() {
        let mut smtlib = prover.get_smtlib();
        if !options.debug_options.no_pretty_smtlib {
            let res = smtlib.pretty_raco_read();
            if let Err(err) = res {
                tracing::warn!("error pretty-printing SMT-LIB: {}", err);
            }
        }
        Some(smtlib)
    } else {
        None
    }
}

/// Write the SMT-LIB dump to a file if requested.
fn write_smtlib(
    options: &DebugOptions,
    name: &SourceUnitName,
    smtlib: &Smtlib,
    prove_result: Option<&ProveResult>,
) -> Result<(), CaesarError> {
    if options.print_smt || options.smt_dir.is_some() {
        let mut smtlib = smtlib.clone();
        smtlib.add_check_sat();
        if let Some(prove_result) = prove_result {
            smtlib.add_details_query(prove_result);
        }
        let smtlib = smtlib.into_string();
        if options.print_smt {
            println!("\n; --- Solver SMT-LIB ---\n{smtlib}\n");
        }
        if let Some(smt_dir) = &options.smt_dir {
            let file_path = smt_dir.join(name.to_file_name("smt2"));
            create_dir_all(file_path.parent().unwrap())?;
            let mut file = File::create(&file_path)?;
            let mut comment_writer = PrefixWriter::new("; ".as_bytes(), &mut file);
            write_detailed_command_info(&mut comment_writer)?;
            writeln!(comment_writer, "Source unit: {name}")?;
            if let Some(prove_result) = prove_result {
                writeln!(comment_writer, "Prove result: {}", &prove_result)?;
            }
            file.write_all(smtlib.as_bytes())?;
            tracing::info!(?file_path, "SMT-LIB query written to file");
        }
    }
    Ok(())
}

/// The result of an SMT solver call for a [`SmtVcProveTask`].
pub struct SmtVcProveResult<'ctx> {
    pub prove_result: ProveResult,
    pub(crate) model: Option<InstrumentedModel<'ctx>>,
    slice_model: Option<SliceModel>,
    quant_vc: QuantVcProveTask,
}

impl<'ctx> SmtVcProveResult<'ctx> {
    /// Print the result of the query to stdout.
    pub fn print_prove_result<'smt>(
        &mut self,
        server: &mut dyn Server,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        name: &SourceUnitName,
    ) {
        let files = server.get_files_internal().lock().unwrap();
        match &mut self.prove_result {
            ProveResult::Proof => {
                println!("{name}: Verified.");
                if let Some(slice_model) = &self.slice_model {
                    let mut w = Vec::new();
                    let doc = pretty_slice(&files, slice_model);
                    if let Some(doc) = doc {
                        let doc = doc.nest(4).append(Doc::line_());
                        doc.render(120, &mut w).unwrap();
                        println!("    {}", String::from_utf8(w).unwrap());
                    }
                }
            }
            ProveResult::Counterexample => {
                let model = self.model.as_ref().unwrap();
                println!("{name}: Counter-example to verification found!");
                let mut w = Vec::new();
                let doc = pretty_model(
                    &files,
                    self.slice_model.as_ref().unwrap(),
                    &self.quant_vc,
                    translate,
                    model,
                );
                doc.nest(4).render(120, &mut w).unwrap();
                println!("    {}", String::from_utf8(w).unwrap());
            }
            ProveResult::Unknown(reason) => {
                println!("{name}: Unknown result! (reason: {reason})");
                if let Some(slice_model) = &self.slice_model {
                    let doc = pretty_slice(&files, slice_model);
                    if let Some(doc) = doc {
                        let mut w = Vec::new();
                        doc.nest(4).render(120, &mut w).unwrap();
                        println!("    {}", String::from_utf8(w).unwrap());
                    }
                }
            }
        }
    }

    /// Emit diagnostics for this check result.
    ///
    /// The provided span is for the location to attach the counterexample to.
    pub fn emit_diagnostics<'smt>(
        &mut self,
        span: Span,
        server: &mut dyn Server,
        translate: &mut TranslateExprs<'smt, 'ctx>,
    ) -> Result<(), CaesarError> {
        // TODO: batch all those messages

        if let Some(slice_model) = &self.slice_model {
            for diagnostic in slice_model.to_diagnostics() {
                server.add_diagnostic(diagnostic)?;
            }
        }

        match &mut self.prove_result {
            ProveResult::Proof => {}
            ProveResult::Counterexample => {
                let model = self.model.as_ref().unwrap();
                let mut labels = vec![];
                let files = server.get_files_internal().lock().unwrap();
                // Print the values of the global variables in the model.
                let global_decls = translate
                    .local_idents()
                    .sorted_by_key(|ident| ident.span.start)
                    .map(|ident| translate.ctx.tcx().get(ident).unwrap())
                    .filter(|decl| decl.kind_name() != DeclKindName::Var(VarKind::Slice))
                    .collect_vec();
                for decl_kind in global_decls {
                    if let DeclKind::VarDecl(decl_ref) = &*decl_kind {
                        let var_decl = decl_ref.borrow();
                        let ident = var_decl.name;
                        let value = pretty_var_value(translate, ident, model);
                        labels.push(Label::new(ident.span).with_message(format!(
                            "in the cex, {} variable {} is {}",
                            var_decl.kind,
                            var_decl.original_name(),
                            value
                        )));
                    }
                }
                drop(files);

                let mut res: Vec<Doc> = vec![Doc::text("Counter-example to verification found!")];

                // Print the unaccessed definitions.
                if let Some(unaccessed) = pretty_unaccessed(model) {
                    res.push(unaccessed);
                }

                res.push(pretty_vc_value(
                    &self.quant_vc,
                    translate,
                    model,
                    self.slice_model.as_ref().unwrap(),
                ));

                let mut w = Vec::new();
                Doc::intersperse(res, Doc::line_().append(Doc::line_()))
                    .render(120, &mut w)
                    .unwrap();
                let text = String::from_utf8(w).unwrap();

                let diagnostic = Diagnostic::new(ReportKind::Error, span)
                    .with_message(text)
                    .with_labels(labels);
                server.add_diagnostic(diagnostic)?;
            }
            ProveResult::Unknown(reason) => {
                server.add_diagnostic(
                    Diagnostic::new(ReportKind::Error, span)
                        .with_message(format!("Unknown result: SMT solver returned {reason}"))
                        .with_note(
                            "For many queries, the query to the SMT solver is inherently undecidable. \
                             There are various tricks to help the SMT solver, which can be found in the Caesar documentation:
                             https://www.caesarverifier.org/docs/caesar/debugging"
                        ),
                )?;
            }
        }

        Ok(())
    }
}
