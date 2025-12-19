use std::{path::PathBuf, time::Duration};

use clap::{Args, ValueEnum};

use crate::{resource_limits::MemorySize, smt::funcs::axiomatic::AxiomInstantiation};

#[derive(Debug, Default, Args)]
#[command(next_help_heading = "Input Options")]
pub struct InputOptions {
    /// The files to verify.
    #[arg(name = "FILE")]
    pub files: Vec<PathBuf>,

    /// Raw verification of just HeyVL statements without any declarations.
    #[arg(short, long)]
    pub raw: bool,

    /// Treat warnings as errors.
    #[arg(long)]
    pub werr: bool,

    /// Only verify/translate (co)procs that match the given filter.
    /// The filter is a regular expression.
    #[arg(short, long)]
    pub filter: Option<String>,
}

#[derive(Debug, Default, Args)]
#[command(next_help_heading = "Resource Limit Options")]
pub struct ResourceLimitOptions {
    /// Time limit in seconds.
    #[arg(long, default_value = "30")]
    pub timeout: u64,

    /// Memory usage limit in megabytes.
    #[arg(long = "mem", default_value = "8192")]
    pub mem_limit: usize,
}

impl ResourceLimitOptions {
    pub fn timeout(&self) -> Duration {
        Duration::from_secs(self.timeout)
    }

    pub fn mem_limit(&self) -> MemorySize {
        MemorySize::megabytes(self.mem_limit)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum RunWhichStorm {
    /// Look for the Storm binary in the PATH.
    Path,
    /// Run Storm using Docker, with the `movesrwth/storm:stable` image.
    DockerStable,
    /// Run Storm using Docker, with the `movesrwth/storm:ci` image.
    DockerCI,
}

#[derive(Debug, Default, Clone, Args)]
#[command(next_help_heading = "Model Checking Options")]
pub struct ModelCheckingOptions {
    /// Export declarations to JANI files in the provided directory.
    #[arg(long)]
    pub jani_dir: Option<PathBuf>,

    /// During extraction of the pre for JANI generation, skip the quantitative
    /// pres (instead of failing with an error).
    #[arg(long)]
    pub jani_skip_quant_pre: bool,

    /// Declare procedure inputs as JANI variables, not constants.
    #[arg(long)]
    pub jani_no_constants: bool,

    /// By default, Caesar assigns arbitrary initial values to output variables.
    /// This means that the model does not reflect the possible effects of
    /// initial values of output variables on the program. Usually, this is not
    /// the case anyway and assigning initial values speeds up the model
    /// checking quite a bit. To disable this behavior, use this flag.
    #[arg(long)]
    pub jani_uninit_outputs: bool,

    /// Run Storm, indicating which version to execute.
    #[arg(long)]
    pub run_storm: Option<RunWhichStorm>,

    /// Pass the `--exact` flag to Storm. Otherwise Storm will use floating
    /// point numbers, which may be arbitrarily imprecise (but are usually good
    /// enough).
    #[arg(long)]
    pub storm_exact: bool,

    /// Pass the `--state-limit [number]` option to Storm. This is useful to
    /// approximate infinite-state models.
    #[arg(long)]
    pub storm_state_limit: Option<usize>,

    /// Pass the `--constants [constants]` option to Storm, containing values
    /// for constants in the model.
    #[arg(long)]
    pub storm_constants: Option<String>,

    /// Timeout in seconds for running Storm.
    ///
    /// Caesar uses the minimum of this value and the remaining time from the
    /// `--timeout` option.
    #[arg(long)]
    pub storm_timeout: Option<u64>,
}

impl ModelCheckingOptions {
    pub fn storm_timeout(&self) -> Option<Duration> {
        self.storm_timeout.map(Duration::from_secs)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, ValueEnum)]
pub enum QuantifierInstantiation {
    /// Use all available quantifier instantiation heuristics, in particular
    /// both e-matching and MBQI are enabled.
    #[default]
    All,
    /// Only use E-matching for quantifier instantiation.
    #[value(alias = "ematching")]
    EMatching,
    /// Only use MBQI for quantifier instantiation.
    Mbqi,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, ValueEnum)]
pub enum FunctionEncodingOption {
    /// The the most direct encoding with FO + uninterpreted functions, allowing
    /// for unbounded computations and arbitrary quantifier instaniations.
    #[default]
    Axiomatic,
    /// Like axiomatic encoding but only allows decreasing instantiations, where
    /// the defining axiom is only instantiated based on occurrences of the
    /// function it defines, not other functions in the definition. These
    /// instantiations are unbounded.
    Decreasing,
    /// Add a version of the function for each fuel value (f_0, f_1, ...) and
    /// recursive calls decrease the fuel value.
    FuelMono,
    /// Add a symbolic fuel parameter to the function.
    FuelParam,
    /// Like `fuel-mono`, additionally allowing unbounded unfolding if the
    /// parameter values are literals.
    FuelMonoComputation,
    /// Like `fuel-param`, additionally allowing unbounded unfolding if the
    /// parameter values are literals.
    FuelParamComputation,
    /// Uses SMT-LIB's `define-fun-rec` to encode functions. Only supports input
    /// parameter types without SMT invariants right now.
    #[value(alias = "recfun")]
    DefineFunRec,
}

impl FunctionEncodingOption {
    pub fn axiom_instantiation(&self) -> AxiomInstantiation {
        if *self == FunctionEncodingOption::Axiomatic {
            AxiomInstantiation::Bidirectional
        } else {
            AxiomInstantiation::Decreasing
        }
    }
}

#[derive(Debug, Default, Args)]
#[command(next_help_heading = "Optimization Options")]
pub struct OptimizationOptions {
    /// Disable quantifier elimination. You'll never want to do this, except to see why quantifier elimination is important.
    #[arg(long)]
    pub no_qelim: bool,

    /// Do e-graph optimization of the generated verification conditions.
    /// The result is not used at the moment.
    #[arg(long)]
    pub egraph: bool,

    /// Don't do SMT-powered reachability checks during unfolding of
    /// verification conditions to eliminate unreachable branches. Instead,
    /// unfold all branches.
    #[arg(long)]
    pub strict: bool,

    /// Run the "relational view" optimization. Defaults to off.
    #[arg(long)]
    pub opt_rel: bool,

    /// Don't run the "boolify" optimization pass.
    #[arg(long)]
    pub no_boolify: bool,

    /// Don't apply Z3's simplification pass. This may help with interpreting
    /// the current solver state.
    #[arg(long)]
    pub no_simplify: bool,

    /// Determine how user-defined functions are encoded.
    /// The fuel encodings require `--quantifier-instantiation e-matching` for
    /// guaranteed termination.
    #[arg(long, alias = "fe", default_value = "fuel-param")]
    pub function_encoding: FunctionEncodingOption,

    /// Whether to disable strengthing of partial function definitions to total
    /// definitions. Essentially, we omit the parameter constraint in the SMT
    /// definition of functions to make macro finding easier for the SMT solver.
    /// This forces a specific definition for invalid inputs, potentially
    /// masking unsound usages of those functions (this should only happen when
    /// Caesar has a bug though).
    ///
    /// This flag disables strengthening, making definitions "obviously correct"
    /// at the expense of impossible macro finding for partial functions.
    ///
    /// The `define-fun-rec` encoding always strengthens definitions, and this
    /// option will result in an error.
    #[arg(long)]
    pub no_partial_strengthening: bool,

    /// The number of times a function declaration can be recursively instantiated/unfolded when
    /// using one of the fuel encodings.
    #[arg(long, default_value = "2")]
    pub max_fuel: usize,

    /// Do not add the "synonym" axiom when translating definitional functions
    /// with the fuel-based encodings. This will allow spurious counter-examples
    /// (unsound!), but sometimes this is acceptable or even desired.
    #[arg(long)]
    pub no_synonym_axiom: bool,

    /// Select which heuristics for quantifier instantiation should be used by the SMT solver.
    #[arg(long, alias = "qi", default_value = "all")]
    pub quantifier_instantiation: QuantifierInstantiation,
}

#[derive(Debug, Default, Args)]
#[command(next_help_heading = "Language Server Options")]
pub struct LanguageServerOptions {
    /// Produce explanations of verification conditions.
    #[arg(long)]
    pub explain_vc: bool,

    /// Produce explanations of verification conditions for the core HeyVL
    /// that's produced after proof rules have been desugared.
    #[arg(long)]
    pub explain_core_vc: bool,

    /// Run the language server.
    #[arg(long)]
    pub language_server: bool,
}

#[derive(Debug, Default, Args)]
#[command(next_help_heading = "Debug Options")]
pub struct DebugOptions {
    /// Emit tracing events as json instead of (ANSI) text.
    #[arg(long)]
    pub json: bool,

    /// Emit timing information from tracing events. The tracing events need to
    /// be enabled for this to work.
    #[arg(long)]
    pub timing: bool,

    /// Print version information to standard error.
    #[arg(short, long)]
    pub debug: bool,

    /// Print the parsed HeyVL code to the command-line.
    #[arg(long)]
    pub print_parsed: bool,

    /// Print the raw HeyVL program to the command-line after desugaring.
    #[arg(long)]
    pub print_core: bool,

    /// Print the HeyVL program with generated procs after annotation desugaring
    #[arg(long)]
    pub print_core_procs: bool,

    /// Print the theorem that is sent to the SMT solver to prove. That is, the
    /// result of preparing `vc(S)[⊤] = ⊤`. Note that axioms are not included.
    #[arg(long)]
    pub print_theorem: bool,

    /// Print the SMT solver state for each verify unit in the SMT-LIB format to
    /// standard output.
    #[arg(long)]
    pub print_smt: bool,

    /// Print the SMT solver state for each verify unit in the SMT-LIB format to
    /// a file in the given directory.
    #[arg(long)]
    pub smt_dir: Option<PathBuf>,

    /// Do not pretty-print the output of the `--smt-dir` and `--smt-out` options.
    #[arg(long)]
    pub no_pretty_smtlib: bool,

    /// Do not run the final SMT check to verify the program. This is useful to
    /// obtain just the SMT-LIB output.
    #[arg(long)]
    pub no_verify: bool,

    /// Enable Z3 tracing for the final SAT check.
    #[arg(long)]
    pub z3_trace: bool,

    /// An explicit seed used by Z3 for the final SAT check.
    #[arg(long)]
    pub z3_seed: Option<u32>,

    /// Enable Z3's quantifier instantiation profiling. Output will be sent
    /// every 1000 instantiations to standard error.
    #[arg(long)]
    pub z3_qi_profile: bool,

    /// Enable Z3's MBQI tracing. Will print a message before every round of MBQI
    #[arg(long)]
    pub z3_mbqi_trace: bool,

    /// Set Z3's verbosity level.
    #[arg(long)]
    pub z3_verbose: Option<u32>,

    /// Print Z3's statistics after the final SAT check.
    #[arg(long, alias = "print-z3-stats")]
    pub z3_stats: bool,

    /// Run a bunch of Z3's probes on the SAT goal.
    #[arg(long, alias = "probe")]
    pub z3_probe: bool,
}

#[derive(Debug, Default, Args)]
#[command(next_help_heading = "Slicing Options")]
pub struct SliceOptions {
    /// Do not try to slice when an error occurs.
    #[arg(long)]
    pub no_slice_error: bool,

    /// Do not try to minimize the error slice and just return the first
    /// counterexample.
    #[arg(long)]
    pub slice_error_first: bool,

    /// If the SMT solver provides a model for an "unknown" result, use that to
    /// obtain an error slice. The slice is not guaranteed to be an actual error
    /// slice, because the model might not be a real counterexample. However, it
    /// is often a helpful indicator of where the SMT solver got stuck.
    #[arg(long)]
    pub slice_error_inconsistent: bool,

    /// Enable slicing tick/reward statements during slicing for errors.
    #[arg(long, alias = "slice-reward")]
    pub slice_ticks: bool,

    /// Enable slicing sampling statements (must also be selected via
    /// annotations).
    #[arg(long)]
    pub slice_sampling: bool,

    /// Slice if the program verifies to return a smaller, verifying program.
    /// This is not enabled by default.
    #[arg(long)]
    pub slice_verify: bool,

    /// If slicing for correctness is enabled, slice via these methods.
    #[arg(long, default_value = "core")]
    pub slice_verify_via: SliceVerifyMethod,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, ValueEnum)]
pub enum SliceVerifyMethod {
    /// Slice for correctness using unsat cores. This approach does not minimize
    /// the result. However, it is applicable all the time and has a very small
    /// overhead. All other methods are much slower or not always applicable.
    #[default]
    #[value(name = "core")]
    UnsatCore,
    /// Slice by doing a search for minimal unsatisfiable subsets. The result
    /// might not be globally optimal - the method returns the first slice from
    /// which nothing can be removed without making the program not verify anymore.
    #[value(name = "mus")]
    MinimalUnsatSubset,
    /// Slice by doing a search for the smallest unsatisfiable subset. This will
    /// enumerate all minimal unsat subsets and return the globally smallest one.
    #[value(name = "sus")]
    SmallestUnsatSubset,
    /// Slice for correctness by encoding a direct exists-forall query into the
    /// SMT solver and then run the minimization algorithm. This approach does
    /// not support using uninterpreted functions. This approach is usually not
    /// good.
    #[value(name = "exists-forall")]
    ExistsForall,
}
