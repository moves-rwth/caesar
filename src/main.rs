// clippy (correctly) tells us that we can sometimes elide lifetimes, but many
// of these cases make the declarations way more clear than with implicit
// lifetimes.
#![allow(clippy::needless_lifetimes)]

use std::{
    collections::HashMap,
    io,
    path::PathBuf,
    process::ExitCode,
    sync::{Arc, Mutex},
};

use crate::{
    ast::TyKind,
    front::{resolve::Resolve, tycheck::Tycheck},
    timing::TimingLayer,
    tyctx::TyCtx,
};
use ast::{Diagnostic, FileId, Files, SourceFilePath};
use driver::{Item, SourceUnit, VerifyUnit};
use intrinsic::{distributions::init_distributions, list::init_lists};

use procs::add_default_specs;
use proof_rules::init_encodings;
use resource_limits::{await_with_resource_limits, LimitError};
use thiserror::Error;
use timing::DispatchBuilder;
use tokio::task::JoinError;
use tracing::warn;

use structopt::StructOpt;

pub mod ast;
mod driver;
pub mod front;
pub mod intrinsic;
mod language_server;
pub mod opt;
pub mod pretty;
mod procs;
mod proof_rules;
mod resource_limits;
mod scope_map;
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
    #[structopt(long)]
    pub timeout: Option<u64>,

    /// Memory usage limit in megabytes.
    #[structopt(long = "mem")]
    pub mem_limit: Option<u64>,

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
            tracing::error!("Timed out after {} seconds, exiting.", timeout.unwrap());
            std::process::exit(2); // exit ASAP
        }
        Err(VerifyError::LimitError(LimitError::Oom)) => {
            tracing::error!(
                "Exhausted {} megabytes of memory, exiting.",
                mem_limit.unwrap()
            );
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
    let handle = {
        let options = options.clone();
        let files = files.clone();
        tokio::task::spawn_blocking(move || verify_files_main(&options, &files, &user_files))
    };
    // Unpacking lots of results with `.await??` :-)
    await_with_resource_limits(options.timeout, options.mem_limit, handle).await??
}

/// Synchronously verify the given source code. This is used for tests. The
/// `--werr` option is enabled by default.
#[cfg(test)]
pub(crate) fn verify_test(source: &str) -> (Result<bool, VerifyError>, Files) {
    let mut files = Files::new();
    let file_id = files.add(SourceFilePath::Builtin, source.to_owned()).id;
    let files_mutex = Mutex::new(files);
    let mut options = Options::default();
    options.werr = true;
    let res = verify_files_main(&options, &files_mutex, &[file_id]);
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
    files_mutex: &Mutex<Files>,
    user_files: &[FileId],
) -> Result<bool, VerifyError> {
    let (source_units, mut tcx) = get_source_units_from_files(options, files_mutex, user_files)?;

    let mut verify_units = transform_source_to_verify(options, source_units);

    let mut all_proven: bool = true;
    for verify_unit in &mut verify_units {
        let (name, mut verify_unit) = verify_unit.enter_with_name();

        let result = verify_unit.verify(name, &mut tcx, options)?;

        all_proven = all_proven && result;
    }

    Ok(all_proven)
}

pub fn get_source_units_from_files(
    options: &Options,
    files_mutex: &Mutex<Files>,
    user_files: &[FileId],
) -> Result<(Vec<Item<SourceUnit>>, TyCtx), VerifyError> {
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

    Ok((source_units, tcx))
}

fn transform_source_to_verify(
    options: &Options,
    source_units: Vec<Item<SourceUnit>>,
) -> Vec<Item<VerifyUnit>> {
    let verify_units: Vec<Item<VerifyUnit>> = source_units
        .into_iter()
        .flat_map(|item| item.flat_map(SourceUnit::into_verify_unit))
        .collect();

    if options.z3_trace && verify_units.len() > 1 {
        warn!("Z3 tracing is enabled with multiple verification units. Intermediate tracing results will be overwritten.");
    }

    verify_units
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
