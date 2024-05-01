// clippy (correctly) tells us that we can sometimes elide lifetimes, but many
// of these cases make the declarations way more clear than with implicit
// lifetimes.
#![allow(clippy::needless_lifetimes)]

use std::{
    collections::HashMap,
    fs::{create_dir_all, File},
    io::{self, Write},
    path::PathBuf,
    process::ExitCode,
    sync::{Arc, Mutex},
};

use crate::{
    ast::{stats::StatsVisitor, visit::VisitorMut, TyKind},
    front::{resolve::Resolve, tycheck::Tycheck},
    opt::{egraph, qelim::Qelim, relational::Relational, unfolder::Unfolder},
    smt::{pretty_model, pretty_slice, translate_exprs::TranslateExprs, SmtCtx},
    timing::TimingLayer,
    tyctx::TyCtx,
    vc::{subst::apply_subst, vcgen::Vcgen},
    version::write_detailed_version_info,
};
use ast::{Diagnostic, Expr, FileId, Files, SourceFilePath};
use driver::{Item, SourceUnit, SourceUnitName, VcUnit, VerifyUnit};
use intrinsic::{distributions::init_distributions, list::init_lists};
use opt::{boolify::Boolify, RemoveParens};
use procs::add_default_specs;
use proof_rules::init_encodings;
use resource_limits::{await_with_resource_limits, LimitError, LimitsRef};
use slicing::{
    init_slicing, selection::SliceSelection, solver::SliceSolver, transform::SliceStmts,
};
use smt::PrettySliceMode;
use thiserror::Error;
use timing::DispatchBuilder;
use tokio::task::JoinError;
use tracing::{info, info_span, warn};
use z3::{
    ast::{Ast, Bool},
    Config, Context,
};

use structopt::StructOpt;
use z3rro::{
    model::InstrumentedModel,
    pretty::{get_pretty_solver_smtlib, get_solver_smtlib},
    prover::{ProveResult, Prover},
    util::{PrefixWriter, ReasonUnknown},
};

pub mod ast;
mod driver;
pub mod front;
pub mod intrinsic;
pub mod opt;
pub mod pretty;
mod procs;
mod proof_rules;
mod resource_limits;
mod scope_map;
mod slicing;
mod smt;
mod timing;
pub mod tyctx;
pub mod vc;
mod version;

#[derive(StructOpt, Debug, Default)]
#[structopt(
    name = "caesar",
    about = "A deductive verifier for probabilistic programs."
)]
pub struct Options {
    /// Raw verification of just HeyVL statements without any declarations.
    #[structopt(short, long)]
    pub raw: bool,

    /// The files to verify.
    #[structopt(name = "FILE", parse(from_os_str))]
    pub files: Vec<PathBuf>,

    /// Disable quantifier elimination. You'll never want to do this, except to see why quantifier elimination is important.
    #[structopt(long)]
    pub no_qelim: bool,

    /// Time limit in seconds.
    #[structopt(long, default_value = "300")]
    pub timeout: u64,

    /// Memory usage limit in megabytes.
    #[structopt(long = "mem", default_value = "8192")]
    pub mem_limit: u64,

    /// Emit tracing events as json instead of (ANSI) text.
    #[structopt(long)]
    pub json: bool,

    /// Emit timing information from tracing events. The tracing events need to
    /// be enabled for this to work.
    #[structopt(long)]
    pub timing: bool,

    /// Do e-graph optimization of the generated verification conditions.
    /// The result is not used at the moment.
    #[structopt(long)]
    pub egraph: bool,

    /// Don't do reachability checks during unfolding of verification conditions
    /// to eliminate unreachable branches. Instead, unfold all branches.
    #[structopt(long)]
    pub strict: bool,

    /// Run the "relational view" optimization. Defaults to off.
    #[structopt(long)]
    pub opt_rel: bool,

    /// Don't run the "boolify" optimization pass.
    #[structopt(long)]
    pub no_boolify: bool,

    /// Don't apply Z3's simplification pass. This may help with interpreting
    /// the current solver state.
    #[structopt(long)]
    pub no_simplify: bool,

    /// Print version information to standard output.
    #[structopt(short, long)]
    pub debug: bool,

    /// Treat warnings as errors.
    #[structopt(long)]
    pub werr: bool,

    /// Print the SMT solver state for each verify unit in the SMT-LIB format to
    /// standard output.
    #[structopt(long)]
    pub print_smt: bool,

    /// Print the SMT solver state for each verify unit in the SMT-LIB format to
    /// a file in the given directory.
    #[structopt(long, parse(from_os_str))]
    pub smt_dir: Option<PathBuf>,

    /// Do not pretty-print the output of the `--smt-dir` and `--smt-out` options.
    #[structopt(long)]
    pub no_pretty_smtlib: bool,

    /// Enable Z3 tracing for the final SAT check.
    #[structopt(long)]
    pub z3_trace: bool,

    /// Print the parsed HeyVL code to the command-line.
    #[structopt(long)]
    pub print_parsed: bool,

    /// Print the raw HeyVL program to the command-line after desugaring.
    #[structopt(long)]
    pub print_core: bool,

    /// Print the HeyVL program with generated procs after annotation desugaring
    #[structopt(long)]
    pub print_core_procs: bool,

    /// Print the theorem that is sent to the SMT solver to prove. That is, the
    /// result of preparing vc(S)[⊤] = ⊤. Note that axioms are not included.
    #[structopt(long)]
    pub print_theorem: bool,

    /// Print the verification conditions computed at every label statement to
    /// standard output.
    #[structopt(long)]
    pub print_label_vc: bool,

    /// Do not try to slice after an error occurs. Just return the first
    /// counterexample.
    #[structopt(long)]
    pub no_slice_error: bool,

    /// Slice if the program verifies to return a smaller, verifying program.
    /// This is not enabled by default.
    #[structopt(long)]
    pub slice_verify: bool,
}

#[tokio::main]
async fn main() -> ExitCode {
    // add version to options config
    let version_info = version::self_version_info();
    let clap = Options::clap().version(version_info.as_str());
    // now parse options
    let options = Options::from_clap(&clap.get_matches());

    if options.debug {
        let mut stdout = io::stdout().lock();
        version::write_detailed_version_info(&mut stdout).unwrap();
    }

    // install global collector configured based on RUST_LOG env var.
    setup_tracing(&options);

    let (timeout, mem_limit) = (options.timeout, options.mem_limit);
    if options.files.is_empty() {
        eprintln!("Error: list of files must not be empty.\n");
        return ExitCode::from(1);
    }

    let mut files = Files::new();
    let user_files: Vec<FileId> = options
        .files
        .iter()
        .map(|path| load_file(&mut files, path))
        .collect();

    let options = Arc::new(options);
    let files = Arc::new(Mutex::new(files));
    let verify_result = verify_files(&options, &files, user_files).await;

    if options.timing {
        print_timings();
    }

    match verify_result {
        #[allow(clippy::bool_to_int_with_if)]
        Ok(all_verified) => ExitCode::from(if all_verified { 0 } else { 1 }),
        Err(VerifyError::Diagnostic(diagnostic)) => {
            let files = files.lock().unwrap();
            print_diagnostic(&files, diagnostic).unwrap();
            ExitCode::from(1)
        }
        Err(VerifyError::IoError(err)) => {
            eprintln!("IO Error: {}", err);
            ExitCode::from(1)
        }
        Err(VerifyError::LimitError(LimitError::Timeout)) => {
            tracing::error!("Timed out after {} seconds, exiting.", timeout);
            std::process::exit(2); // exit ASAP
        }
        Err(VerifyError::LimitError(LimitError::Oom)) => {
            tracing::error!("Exhausted {} megabytes of memory, exiting.", mem_limit);
            std::process::exit(3); // exit ASAP
        }
        Err(VerifyError::Panic(join_error)) => panic!("{}", join_error),
        Err(VerifyError::Interrupted) => {
            tracing::error!("Interrupted");
            ExitCode::from(130) // 130 seems to be a standard exit code for CTRL+C
        }
    }
}

/// Errors that can occur in the verifier.
///
/// Note that some unit not verifying (solver yielding unknown or a
/// counter-example) is not actually considered a [`VerifyError`].
#[derive(Debug, Error)]
pub enum VerifyError {
    #[error("{0}")]
    Diagnostic(#[from] Diagnostic),
    #[error("io error")]
    IoError(#[from] io::Error),
    #[error("{0}")]
    LimitError(#[from] LimitError),
    #[error("panic: {0}")]
    Panic(#[from] JoinError),
    #[error("interrupted")]
    Interrupted,
}

/// Verify a list of `user_files`. The `options.files` value is ignored here.
/// This function should be used when Caesar is invoked from Rust and not on the
/// command-line, such as in tests.
pub async fn verify_files(
    options: &Arc<Options>,
    files: &Arc<Mutex<Files>>,
    user_files: Vec<FileId>,
) -> Result<bool, VerifyError> {
    let handle = |limits_ref: LimitsRef| {
        let options = options.clone();
        let files = files.clone();
        tokio::task::spawn_blocking(move || {
            verify_files_main(&options, limits_ref, &files, &user_files)
        })
    };
    // Unpacking lots of Results with `.await??` :-)
    await_with_resource_limits(Some(options.timeout), Some(options.mem_limit), handle).await??
}

/// Synchronously verify the given source code. This is used for tests. The
/// `--werr` option is enabled by default.
#[cfg(test)]
pub(crate) fn verify_test(source: &str) -> (Result<bool, VerifyError>, Files) {
    use std::time::{Duration, Instant};

    let mut files = Files::new();
    let file_id = files.add(SourceFilePath::Builtin, source.to_owned()).id;
    let files_mutex = Mutex::new(files);
    let mut options = Options::default();
    options.werr = true;
    let limits_ref = LimitsRef::new(
        Some(options.timeout).map(|seconds| Instant::now() + Duration::from_secs(seconds)),
    );
    let res = verify_files_main(&options, limits_ref, &files_mutex, &[file_id]);
    (res, files_mutex.into_inner().unwrap())
}

#[cfg(test)]
pub(crate) fn single_desugar_test(source: &str) -> Result<String, VerifyError> {
    let mut files = Files::new();
    let file_id = files.add(SourceFilePath::Builtin, source.to_owned()).id;
    let files_mutex = Mutex::new(files);
    let options = Options::default();

    let mut files = files_mutex.lock().unwrap();
    let file = files.get(file_id).unwrap();
    let mut source_units: Vec<Item<SourceUnit>> =
        SourceUnit::parse(file, options.raw).map_err(|parse_err| parse_err.diagnostic())?;

    let mut source_unit = source_units.remove(0);

    // 2. Resolving (and declaring) idents
    let mut tcx = TyCtx::new(TyKind::EUReal);
    init_encodings(&mut files, &mut tcx);
    init_distributions(&mut files, &mut tcx);
    init_lists(&mut files, &mut tcx);
    init_slicing(&mut tcx);
    drop(files);

    let mut resolve = Resolve::new(&mut tcx);
    // first, do forward declarations
    source_unit
        .enter()
        .forward_declare(&mut resolve)
        .map_err(|resolve_err| resolve_err.diagnostic())?;
    // then, the actual resolving
    source_unit
        .enter()
        .resolve(&mut resolve)
        .map_err(|resolve_err| resolve_err.diagnostic())?;

    // 3. Type checking
    add_default_specs(&mut tcx);

    let mut tycheck = Tycheck::new(&mut tcx);

    {
        // Make a new scope to be able to drop 'entered' afterwards
        let mut entered = source_unit.enter();
        entered
            .tycheck(&mut tycheck)
            .map_err(|ty_err| ty_err.diagnostic())?;
        let monotonicity_res = entered
            .check_monotonicity()
            .map_err(|ty_err| ty_err.diagnostic());
        if let Err(err) = monotonicity_res {
            let files = files_mutex.lock().unwrap();
            print_warning(&options, &files, err)?;
        }
    }
    let mut new_source_units: Vec<Item<SourceUnit>> = vec![];
    // Desugar encodings from source units
    source_unit
        .enter()
        .desugar(&mut tcx, &mut new_source_units)
        .map_err(|ann_err| ann_err.diagnostic())?;

    new_source_units.push(source_unit);

    Ok(new_source_units
        .into_iter()
        .map(|unit: Item<SourceUnit>| unit.to_string())
        .collect::<Vec<String>>()
        .join("\n"))
}

/// Synchronously verify the given files.
fn verify_files_main(
    options: &Options,
    limits_ref: LimitsRef,
    files_mutex: &Mutex<Files>,
    user_files: &[FileId],
) -> Result<bool, VerifyError> {
    // 1. Parsing
    let mut source_units: Vec<Item<SourceUnit>> = Vec::new();
    let mut files = files_mutex.lock().unwrap();
    for file_id in user_files {
        let file = files.get(*file_id).unwrap();
        let new_units =
            SourceUnit::parse(file, options.raw).map_err(|parse_err| parse_err.diagnostic())?;

        // Print the result of parsing if requested
        if options.print_parsed {
            println!("{}: Parsed file:\n", file.path);
            for unit in &new_units {
                println!("{}", unit);
            }
        }

        source_units.extend(new_units);
    }

    // 2. Resolving (and declaring) idents
    let mut tcx = TyCtx::new(TyKind::EUReal);
    init_encodings(&mut files, &mut tcx);
    init_distributions(&mut files, &mut tcx);
    init_lists(&mut files, &mut tcx);
    init_slicing(&mut tcx);
    drop(files);

    let mut resolve = Resolve::new(&mut tcx);
    // first, do forward declarations
    for source_unit in &mut source_units {
        source_unit
            .enter()
            .forward_declare(&mut resolve)
            .map_err(|resolve_err| resolve_err.diagnostic())?;
    }
    // then, the actual resolving
    for source_unit in &mut source_units {
        source_unit
            .enter()
            .resolve(&mut resolve)
            .map_err(|resolve_err| resolve_err.diagnostic())?;
    }

    // 3. Type checking
    add_default_specs(&mut tcx);

    let mut tycheck = Tycheck::new(&mut tcx);
    for source_unit in &mut source_units {
        let mut entered = source_unit.enter();
        entered
            .tycheck(&mut tycheck)
            .map_err(|ty_err| ty_err.diagnostic())?;
        let monotonicity_res = entered
            .check_monotonicity()
            .map_err(|ty_err| ty_err.diagnostic());
        if let Err(err) = monotonicity_res {
            let files = files_mutex.lock().unwrap();
            print_warning(options, &files, err)?;
        }
    }

    let mut source_units_buf = vec![];
    for source_unit in &mut source_units {
        source_unit
            .enter()
            .desugar(&mut tcx, &mut source_units_buf)
            .map_err(|ann_err| ann_err.diagnostic())?;
    }
    source_units.extend(source_units_buf);

    if options.print_core_procs {
        println!("HeyVL query with generated procs:");
        for source_unit in &mut source_units {
            println!("{}", source_unit);
        }
    }

    let mut verify_units: Vec<Item<VerifyUnit>> = source_units
        .into_iter()
        .flat_map(|item| item.flat_map(SourceUnit::into_verify_unit))
        .collect();

    if options.z3_trace && verify_units.len() > 1 {
        warn!("Z3 tracing is enabled with multiple verification units. Intermediate tracing results will be overwritten.");
    }

    let mut all_proven: bool = true;
    for verify_unit in &mut verify_units {
        let (name, mut verify_unit) = verify_unit.enter_with_name();

        // 4. Desugaring: transforming spec calls to procs
        verify_unit.desugar(&mut tcx).unwrap();

        // 5. Prepare slicing
        let slice_vars = verify_unit.prepare_slicing(options, &mut tcx);

        // print HeyVL core after desugaring if requested
        if options.print_core {
            println!("{}: HeyVL core query:\n{}\n", name, *verify_unit);
        }

        // 6. Generating verification conditions
        let vcgen = Vcgen::new(&tcx, options.print_label_vc);
        let mut vc_expr = verify_unit.vcgen(&vcgen).unwrap();

        // 7. Unfolding
        unfold_expr(options, &limits_ref, &tcx, &mut vc_expr)?;

        // 8. Quantifier elimination
        if !options.no_qelim {
            apply_qelim(&mut tcx, &mut vc_expr);
        }

        // In-between, gather some stats about the vc expression
        trace_expr_stats(&mut vc_expr.expr);

        // 9. Create the "vc[S] is valid" expression
        let mut vc_is_valid = vc_expr.to_boolean();

        if options.egraph {
            egraph::simplify(&vc_is_valid);
        }

        // 10. Optimizations
        if !options.no_boolify || options.opt_rel {
            RemoveParens.visit_expr(&mut vc_is_valid).unwrap();
        }
        if !options.no_boolify {
            apply_boolify_opt(&mut vc_is_valid);
        }
        if options.opt_rel {
            apply_relational_opt(&mut vc_is_valid);
        }

        // print theorem to prove if requested
        if options.print_theorem {
            println!("{}: Theorem to prove:\n{}\n", name, &vc_is_valid);
        }

        // 11. Translate to Z3
        let translate_span = info_span!("translation to Z3");
        let translate_entered = translate_span.enter();

        let ctx = mk_z3_ctx(options);
        let smt_ctx = SmtCtx::new(&ctx, &tcx);
        let mut smt_translate = TranslateExprs::new(&smt_ctx);
        let mut valid_query = smt_translate.t_bool(&vc_is_valid);

        drop(translate_entered);
        drop(translate_span);

        if !options.no_simplify {
            info_span!("simplify query").in_scope(|| valid_query = valid_query.simplify());
        }

        // 12. Create Z3 solver with axioms, solve
        let sat_span = info_span!("SAT check");
        let sat_entered = sat_span.enter();

        let prover = mk_valid_query_prover(&limits_ref, &ctx, &smt_translate, &valid_query);
        let smtlib = get_smtlib(options, &prover);

        let mut slice_solver = SliceSolver::new(slice_vars.clone(), &mut smt_translate, prover);
        let mut result = slice_solver.slice_while_failing(&limits_ref)?;
        if matches!(result, ProveResult::Proof) && options.slice_verify {
            let model = slice_solver.slice_while_verified(&limits_ref)?;
            let mut w = Vec::new();
            let files = files_mutex.lock().unwrap();
            let doc = pretty_slice(
                &files,
                &mut smt_translate,
                &slice_vars,
                SliceSelection::VERIFIED_SELECTION,
                &InstrumentedModel::new(model),
                PrettySliceMode::Verify,
            );
            if let Some(doc) = doc {
                doc.nest(4).render(120, &mut w).unwrap();
                println!("    {}", String::from_utf8(w).unwrap());
            }
        }

        drop(sat_entered);
        drop(sat_span);

        // Now let's examine the result.
        print_prove_result(
            files_mutex,
            &slice_vars,
            SliceSelection::FAILURE_SELECTION,
            &vc_expr,
            &mut smt_translate,
            &mut result,
            name,
        );

        write_smtlib(options, smtlib, name, &result).unwrap();

        if options.z3_trace {
            info!("Z3 tracing output will be written to `z3.log`.");
        }

        // Handle reasons to stop the verifier.
        match result {
            ProveResult::Unknown(ReasonUnknown::Interrupted) => {
                return Err(VerifyError::Interrupted)
            }
            ProveResult::Unknown(ReasonUnknown::Timeout) => return Err(LimitError::Timeout.into()),
            _ => {}
        }

        all_proven = all_proven && matches!(result, ProveResult::Proof);
    }

    Ok(all_proven)
}

fn setup_tracing(options: &Options) {
    timing::init_tracing(
        DispatchBuilder::default()
            .json(options.json)
            .timing(options.timing),
    )
}

fn print_timings() {
    let timings = TimingLayer::read_active().unwrap();
    let timings: HashMap<&'static str, String> = timings
        .iter()
        .map(|(key, value)| (*key, format!("{}", value.as_nanos())))
        .collect();
    eprintln!("Timings: {:?}", timings);
}

fn print_warning(
    options: &Options,
    files: &Files,
    diagnostic: Diagnostic,
) -> Result<(), VerifyError> {
    if !options.werr {
        print_diagnostic(files, diagnostic)?;
        Ok(())
    } else {
        Err(diagnostic.into())
    }
}

fn print_diagnostic(mut files: &Files, diagnostic: Diagnostic) -> io::Result<()> {
    let mut report = diagnostic.into_ariadne(files);
    if atty::isnt(atty::Stream::Stderr) {
        // let's hope there's no config already there
        report = report.with_config(ariadne::Config::default().with_color(false));
    }
    let report = report.finish();
    report.eprint(&mut files)
}

fn load_file(files: &mut Files, path: &PathBuf) -> FileId {
    let source = match std::fs::read_to_string(path) {
        Ok(source) => source,
        Err(err) => match err.kind() {
            io::ErrorKind::NotFound => {
                panic!("Error: Could not find file '{}'", path.to_string_lossy())
            }
            _ => panic!(
                "Error while loading file '{}': {}",
                path.to_string_lossy(),
                err
            ),
        },
    };
    let source_file_path = SourceFilePath::Path(path.clone());
    let file = files.add(source_file_path, source);
    file.id
}

fn apply_qelim(tcx: &mut TyCtx, vc_expr: &mut VcUnit) {
    let mut qelim = Qelim::new(tcx);
    qelim.qelim(vc_expr);
    // Apply/eliminate substitutions again
    apply_subst(tcx, &mut vc_expr.expr);
}

fn apply_relational_opt(vc_expr_eq_infinity: &mut Expr) {
    let span = info_span!("relationalize");
    let _entered = span.enter();
    (Relational {}).visit_expr(vc_expr_eq_infinity).unwrap();
}

fn apply_boolify_opt(vc_expr_eq_infinity: &mut Expr) {
    let span = info_span!("boolify");
    let _entered = span.enter();
    (Boolify {}).visit_expr(vc_expr_eq_infinity).unwrap();
}

fn unfold_expr(
    options: &Options,
    limits_ref: &LimitsRef,
    tcx: &TyCtx,
    vc_expr: &mut VcUnit,
) -> Result<(), LimitError> {
    let span = info_span!("unfolding");
    let _entered = span.enter();
    if !options.strict {
        let ctx = Context::new(&Config::default());
        let smt_ctx = SmtCtx::new(&ctx, tcx);
        let mut unfolder = Unfolder::new(limits_ref.clone(), &smt_ctx);
        unfolder.visit_expr(&mut vc_expr.expr)
    } else {
        apply_subst(tcx, &mut vc_expr.expr);
        Ok(())
    }
}

fn mk_z3_ctx(options: &Options) -> Context {
    let mut config = Config::default();
    if options.z3_trace {
        config.set_bool_param_value("trace", true);
        config.set_bool_param_value("proof", true);
    }
    Context::new(&config)
}

fn mk_valid_query_prover<'smt, 'ctx>(
    limits_ref: &LimitsRef,
    ctx: &'ctx Context,
    smt_translate: &TranslateExprs<'smt, 'ctx>,
    valid_query: &Bool<'ctx>,
) -> Prover<'ctx> {
    // create the prover and set the params
    let mut prover = Prover::new(ctx);
    if let Some(remaining) = limits_ref.time_left() {
        prover.set_timeout(remaining);
    }

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

fn trace_expr_stats(vc_expr: &mut Expr) {
    let mut stats = StatsVisitor::default();
    stats.visit_expr(vc_expr).unwrap();
    let stats = stats.stats;
    tracing::info!(
        num_exprs = stats.num_exprs,
        num_quants = stats.num_quants,
        depths = %stats.depths_summary(),
        "Verification condition stats"
    );
    if stats.num_quants > 0 {
        tracing::warn!(
            num_quants=stats.num_quants, "Quantifiers are present in the generated verification conditions. It is possible that quantifier elimination failed. If Z3 can't decide the problem, this may be the reason."
        );
    }
}

fn print_prove_result<'smt, 'ctx>(
    files_mutex: &Mutex<Files>,
    slice_stmts: &SliceStmts,
    selection: SliceSelection,
    vc_expr: &VcUnit,
    smt_translate: &mut TranslateExprs<'smt, 'ctx>,
    result: &mut ProveResult<'ctx>,
    name: &SourceUnitName,
) {
    match result {
        ProveResult::Proof => println!("{}: Verified.", name),
        ProveResult::Counterexample(model) => {
            println!("{}: Counter-example to verification found!", name);
            let mut w = Vec::new();
            let files = files_mutex.lock().unwrap();
            let doc = pretty_model(
                &files,
                slice_stmts,
                selection,
                vc_expr,
                smt_translate,
                model,
            );
            doc.nest(4).render(120, &mut w).unwrap();
            println!("    {}", String::from_utf8(w).unwrap());
        }
        ProveResult::Unknown(reason) => {
            println!("{}: Unknown result! (reason: {})", name, reason)
        }
    }
}

fn get_smtlib(options: &Options, prover: &Prover) -> Option<String> {
    if options.print_smt || options.smt_dir.is_some() {
        let smtlib = if !options.no_pretty_smtlib {
            get_pretty_solver_smtlib(prover.solver())
        } else {
            get_solver_smtlib(prover.solver())
        };
        Some(smtlib)
    } else {
        None
    }
}

fn write_smtlib(
    options: &Options,
    smtlib: Option<String>,
    name: &SourceUnitName,
    result: &ProveResult,
) -> io::Result<()> {
    if options.print_smt || options.smt_dir.is_some() {
        let mut smtlib = smtlib.unwrap();
        match result {
            ProveResult::Proof => {}
            ProveResult::Counterexample(_) => smtlib.push_str("\n(get-model)\n"),
            ProveResult::Unknown(_) => smtlib.push_str("\n(get-info :reason-unknown)\n"),
        }
        if options.print_smt {
            println!("\n; --- Solver SMT-LIB ---\n{}\n", smtlib);
        }
        if let Some(smt_dir) = &options.smt_dir {
            let file_path = smt_dir.join(format!("{}.smt2", name));
            create_dir_all(file_path.parent().unwrap())?;
            let mut file = File::create(&file_path)?;
            let mut comment_writer = PrefixWriter::new("; ".as_bytes(), &mut file);
            write_detailed_version_info(&mut comment_writer)?;
            writeln!(comment_writer, "Source unit: {}", name)?;
            writeln!(comment_writer, "Prove result: {:?}", result)?;
            file.write_all(smtlib.as_bytes())?;
            info!(?file_path, "SMT-LIB query written to file");
        }
    }
    Ok(())
}
