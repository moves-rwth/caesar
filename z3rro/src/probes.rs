//! Convenience functions for some of Z3's probes.

use std::fmt::Display;

use enum_map::{Enum, EnumMap};
use itertools::Itertools;
use z3::{Context, Goal, Probe};

fn run_bool_probe(name: &str, ctx: &Context, goal: &Goal) -> bool {
    let probe = Probe::new(ctx, name);
    probe.apply(goal) != 0.0
}

/// Run the `has-quantifiers` probe: it returns true if the goal contains
/// quantifiers.
pub fn has_quantifiers(ctx: &Context, goal: &Goal) -> bool {
    run_bool_probe("has-quantifiers", ctx, goal)
}

/// Run the `has-patterns` probe: it returns true if the goal contains
/// quantifiers with patterns.
pub fn has_patterns(ctx: &Context, goal: &Goal) -> bool {
    run_bool_probe("has-patterns", ctx, goal)
}

/// Enum representing different SMT-LIB theories that we can probe about. Note
/// that these theories can overlap.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Enum)]
pub enum TheoryProbe {
    /// Linear Integer Arithmetic
    Lia,
    /// Linear Integer and Real Arithmetic
    Lira,
    /// Linear Real Arithmetic
    Lra,
    /// Nonlinear Integer Arithmetic
    Nia,
    /// Nonlinear Integer and Real Arithmetic
    Nira,
    /// Nonlinear Real Arithmetic
    Nra,
}

impl Display for TheoryProbe {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TheoryProbe::Lia => write!(f, "LIA"),
            TheoryProbe::Lira => write!(f, "LIRA"),
            TheoryProbe::Lra => write!(f, "LRA"),
            TheoryProbe::Nia => write!(f, "NIA"),
            TheoryProbe::Nira => write!(f, "NIRA"),
            TheoryProbe::Nra => write!(f, "NRA"),
        }
    }
}

/// Run the appropriate probe based on the given theory.
pub fn is_theory(ctx: &Context, goal: &Goal, theory: TheoryProbe) -> bool {
    let probe_name = match theory {
        TheoryProbe::Lia => "is-lia",
        TheoryProbe::Lira => "is-lira",
        TheoryProbe::Lra => "is-lra",
        TheoryProbe::Nia => "is-nia",
        TheoryProbe::Nira => "is-nira",
        TheoryProbe::Nra => "is-nra",
    };
    run_bool_probe(probe_name, ctx, goal)
}

/// Run the `is-unbounded` probe: it returns true if the goal contains
/// integer/real constants that do not have lower/upper bounds.
pub fn is_unbounded(ctx: &Context, goal: &Goal) -> bool {
    run_bool_probe("is-unbounded", ctx, goal)
}

fn run_int_probe(name: &str, ctx: &Context, goal: &Goal) -> usize {
    let probe = Probe::new(ctx, name);
    let float_res = probe.apply(goal);
    assert!(float_res.fract() == 0.0, "expected integer result");
    float_res as usize
}

/// Run the `num-arith-consts` probe: it returns the number of arithmetic
/// constants in the given goal.
pub fn num_arith_consts(ctx: &Context, goal: &Goal) -> usize {
    run_int_probe("num-arith-consts", ctx, goal)
}

/// Run the `num-bool-consts` probe: it returns the number of Boolean
/// constants in the given goal.
pub fn num_bool_consts(ctx: &Context, goal: &Goal) -> usize {
    run_int_probe("num-bool-consts", ctx, goal)
}

/// Run the `num-bv-consts` probe: it returns the number of bit-vector
/// constants in the given goal.
pub fn num_bv_consts(ctx: &Context, goal: &Goal) -> usize {
    run_int_probe("num-bv-consts", ctx, goal)
}

/// Run the `num-consts` probe: it returns the number of non-Boolean
/// constants in the given goal.
pub fn num_consts(ctx: &Context, goal: &Goal) -> usize {
    run_int_probe("num-consts", ctx, goal)
}

/// Run the `num-exprs` probe: it returns the number of expressions/terms
/// in the given goal.
pub fn num_exprs(ctx: &Context, goal: &Goal) -> usize {
    run_int_probe("num-exprs", ctx, goal)
}

/// Result of running a bunch of selected probes on a goal.
#[derive(Debug)]
pub struct ProbeSummary {
    pub has_quantifiers: bool,
    pub has_patterns: bool,
    pub is_theory: EnumMap<TheoryProbe, bool>,
    pub is_unbounded: bool,
    pub num_arith_consts: usize,
    pub num_bool_consts: usize,
    pub num_bv_consts: usize,
    pub num_consts: usize,
    pub num_exprs: usize,
}

impl ProbeSummary {
    /// Run a bunch of slected probes on the goal.
    pub fn probe(ctx: &Context, goal: &Goal) -> Self {
        Self {
            has_quantifiers: has_quantifiers(ctx, goal),
            has_patterns: has_patterns(ctx, goal),
            is_theory: EnumMap::from_fn(|theory| is_theory(ctx, goal, theory)),
            is_unbounded: is_unbounded(ctx, goal),
            num_arith_consts: num_arith_consts(ctx, goal),
            num_bool_consts: num_bool_consts(ctx, goal),
            num_bv_consts: num_bv_consts(ctx, goal),
            num_consts: num_consts(ctx, goal),
            num_exprs: num_exprs(ctx, goal),
        }
    }

    /// Get an upper bound on the complexity of deciding SAT for the goal.
    pub fn complexity(&self, quantifier_free: bool) -> Complexity {
        self.is_theory
            .iter()
            .filter_map(|(theory, is_theory)| {
                if *is_theory {
                    Some(Complexity::from_theory(
                        theory,
                        self.is_unbounded,
                        quantifier_free,
                    ))
                } else {
                    None
                }
            })
            .min()
            .unwrap_or(Complexity::Unknown)
    }
}

impl Display for ProbeSummary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Has quantifiers: {}", self.has_quantifiers)?;
        if self.has_quantifiers {
            writeln!(f, " - has patterns: {}", self.has_patterns)?;
        }
        let (true_theories, false_theories): (Vec<_>, _) = self
            .is_theory
            .iter()
            .map(|(theory, is_theory)| {
                (
                    theory.to_string(),
                    *is_theory,
                    Complexity::from_theory(theory, self.is_unbounded, self.has_quantifiers),
                )
            })
            .sorted_by_key(|(_, _, complexity)| *complexity)
            .partition(|(_, is_theory, _)| *is_theory);
        let mut true_theories = true_theories.iter().map(|(theory, _, _)| theory).peekable();
        let mut false_theories = false_theories.iter().map(|(theory, _, _)| theory);

        let detected = if true_theories.peek().is_none() {
            "(none)"
        } else {
            &true_theories.join(", ")
        };
        writeln!(f, "Detected theories: {detected}")?;
        if self.has_quantifiers {
            writeln!(
                f,
                " - quantifier-free complexity: {}",
                self.complexity(false)
            )?;
            writeln!(f, " - actual complexity: {}", self.complexity(true))?;
        } else {
            writeln!(f, " - complexity: {}", self.complexity(false))?;
        }
        if !self.is_unbounded {
            writeln!(f, " - all constants are bounded")?;
        }
        writeln!(f, " - rejected theories: {}", false_theories.join(", "))?;
        writeln!(
            f,
            "Number of arithmetic constants: {}",
            self.num_arith_consts
        )?;
        writeln!(f, "Number of Boolean constants: {}", self.num_bool_consts)?;
        writeln!(f, "Number of bit-vector constants: {}", self.num_bv_consts)?;
        writeln!(f, "Number of constants: {}", self.num_consts)?;
        writeln!(f, "Number of expressions: {}", self.num_exprs)
    }
}

/// Complexity of deciding SAT for the different theories ([`TheoryProbe`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Complexity {
    PTime,
    NP,
    PSpace,
    Exptime,
    TwoExptime,
    Decidable,
    Undecidable,
    Unknown,
}

impl Complexity {
    pub fn from_theory(
        theory: TheoryProbe,
        is_unbounded: bool,
        has_quantifiers: bool,
    ) -> Complexity {
        if !has_quantifiers {
            match theory {
                TheoryProbe::Lia if !is_unbounded => Complexity::PTime,
                TheoryProbe::Lia => Complexity::NP,
                TheoryProbe::Lira => Complexity::NP,
                TheoryProbe::Lra => Complexity::PTime,
                TheoryProbe::Nia => Complexity::Undecidable,
                TheoryProbe::Nira => Complexity::Undecidable,
                TheoryProbe::Nra => Complexity::PSpace,
            }
        } else {
            match theory {
                TheoryProbe::Lia => Complexity::TwoExptime,
                TheoryProbe::Lira => Complexity::TwoExptime, // TODO: check this!
                TheoryProbe::Lra => Complexity::PTime,
                TheoryProbe::Nia => Complexity::Undecidable,
                TheoryProbe::Nira => Complexity::Undecidable,
                TheoryProbe::Nra => Complexity::PSpace,
            }
        }
    }
}

impl Display for Complexity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Complexity::PTime => write!(f, "PTIME"),
            Complexity::NP => write!(f, "NP"),
            Complexity::PSpace => write!(f, "PSPACE"),
            Complexity::Exptime => write!(f, "EXPTIME"),
            Complexity::TwoExptime => write!(f, "2-EXPTIME"),
            Complexity::Decidable => write!(f, "Decidable"),
            Complexity::Undecidable => write!(f, "Undecidable"),
            Complexity::Unknown => write!(f, "Unknown"),
        }
    }
}
