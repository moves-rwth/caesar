//! Not a SAT solver, but a prover. There's a difference.
use itertools::Itertools;
use thiserror::Error;

use std::{collections::VecDeque, fmt::Display, io::Write, process::Command, time::Duration};

use tempfile::{Builder, NamedTempFile};

use z3::{
    ast::{forall_const, Ast, Bool, Dynamic},
    Context, SatResult, Solver, Statistics,
};

use crate::{
    model::{InstrumentedModel, ModelConsistency},
    smtlib::Smtlib,
    util::{set_solver_timeout, ReasonUnknown},
};

#[derive(Debug, Error, PartialEq)]
pub enum ProverCommandError {
    #[error("Process execution failed: {0}")]
    ProcessError(String),
    #[error("Parse error")]
    ParseError,
    #[error("Unexpected result from prover: {0}")]
    UnexpectedResultError(String),
}

#[derive(Debug, PartialEq, Clone)]
pub enum SolverType {
    Z3,
    SWINE,
    CVC5,
}

/// The result of a prove query.
#[derive(Debug)]
pub enum ProveResult {
    Proof,
    Counterexample,
    Unknown(ReasonUnknown),
}

/// If z3 is used as the SMT solver, it is not necessary to store
/// a counterexample (for Sat) or reason (for Unknown), since the
/// Z3 solver already retains this information internally.
/// In this case, it is only used to store the SAT result.
///
/// For SwInE, this can be used either to
/// 1) transport the result from SwInE, or
/// 2) store SAT result along with a reason for Unknown.
#[derive(Debug, Clone)]
pub enum SolverResult {
    Unsat,
    Sat(Option<String>),
    Unknown(Option<ReasonUnknown>),
}

impl SolverResult {
    fn to_sat_result(&self) -> SatResult {
        match self {
            SolverResult::Unsat => SatResult::Unsat,
            SolverResult::Sat(_) => SatResult::Sat,
            SolverResult::Unknown(_) => SatResult::Unknown,
        }
    }
}

/// Execute an SMT solver (other than z3)
fn execute_solver(
    prover: &mut Prover<'_>,
    assumptions: &[Bool<'_>],
) -> Result<SolverResult, ProverCommandError> {
    let mut smtlib = prover.get_smtlib();
    if assumptions.is_empty() {
        smtlib.add_check_sat();
    } else {
        smtlib.add_check_sat_assuming(assumptions.iter().map(|a| a.to_string()).collect());
    };
    let smtlib = smtlib.into_string();

    let output = match &prover.smt_solver {
        SolverType::Z3 => {
            unreachable!("The function 'execute_solver' should never be called for z3");
        }
        SolverType::SWINE => {
            let mut smt_file = NamedTempFile::new().unwrap();
            smt_file
                .write_all(transform_input_lines(&smtlib, SolverType::SWINE).as_bytes())
                .unwrap();

            let file_path = smt_file.path();

            Command::new("swine")
                .arg("--no-version")
                .arg(file_path)
                .output()
        }
        SolverType::CVC5 => {
            let mut smt_file = Builder::new().suffix(".smt2").tempfile().unwrap();
            smt_file
                .write_all(transform_input_lines(&smtlib, SolverType::CVC5).as_bytes())
                .unwrap();
            let file_path = smt_file.path();
            Command::new("cvc5")
                .arg("--produce-models")
                .arg(file_path)
                .output()
        }
    };

    match output {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let mut lines_buffer: VecDeque<&str> = stdout.lines().collect();
            let first_line = lines_buffer
                .pop_front()
                .ok_or(ProverCommandError::ParseError)?;
            if first_line.trim().to_lowercase() == "unsat" {
                Ok(SolverResult::Unsat)
            } else if first_line.trim().to_lowercase() == "sat" {
                let cex = lines_buffer.iter().join("");
                Ok(SolverResult::Sat(Some(cex)))
            } else if first_line.trim().to_lowercase() == "unknown" {
                Ok(SolverResult::Unknown(Some(ReasonUnknown::Other(
                    lines_buffer.iter().join("\n"),
                ))))
            } else {
                lines_buffer.push_front(first_line);
                Err(ProverCommandError::UnexpectedResultError(
                    lines_buffer.iter().join("\n"),
                ))
            }
        }
        Err(e) => Err(ProverCommandError::ProcessError(e.to_string())),
    }
}

/// To execute the SMT solver correctly, specific modifications to the input are required:
/// 1) For SwInE, remove lines that contain a `forall` quantifier or the declaration of the exponential function (`exp``).
/// 2) For other solvers, add a line to set logic, and remove incorrect assertions such as `(assert add)`.
/// 3) For solvers that do not support at-most, convert those assertions into equivalent logic.
fn transform_input_lines(input: &str, solver: SolverType) -> String {
    let mut output = match solver {
        SolverType::CVC5 => {
            let mut output = String::new();
            let logic = if input.contains("*") || input.contains("/") {
                "(set-logic QF_NIRA)"
            } else {
                "(set-logic QF_LIRA)"
            };
            output.push_str(logic);
            output
        }
        _ => String::new(),
    };
    let mut tmp_buffer: VecDeque<char> = VecDeque::new();
    let mut input_buffer: VecDeque<char> = input.chars().collect();
    let mut cnt = 0;

    let condition = |tmp: &str| match solver {
        SolverType::SWINE => !tmp.contains("declare-fun exp") && !tmp.contains("forall"),
        _ => !tmp.contains("(assert and)"),
    };

    // Collect characters until all opened parentheses are closed, and
    // keep this block if it does not contain 'declare-fun exp' or 'forall'.
    while let Some(c) = input_buffer.pop_front() {
        tmp_buffer.push_back(c);
        match c {
            '(' => {
                cnt += 1;
            }
            ')' => {
                cnt -= 1;
                if cnt == 0 {
                    let tmp: String = tmp_buffer.iter().collect();
                    if condition(&tmp) {
                        output.push_str(&tmp);
                    }
                    tmp_buffer.clear();
                }
            }
            _ => {}
        }
    }
    output
}

impl Display for ProveResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProveResult::Proof => f.write_str("Proof"),
            ProveResult::Counterexample => f.write_str("Counterexample"),
            ProveResult::Unknown(reason) => {
                f.write_fmt(format_args!("Unknown (reason: {})", reason))
            }
        }
    }
}

/// Because Z3's built-in support for incremental solving often has surprising
/// or simply bad performance for some use cases, we also offer an
/// [`IncrementalMode::Emulated`], with which the [`Prover`] mtaintains its own
/// stack of assumptions and re-initializes a new Z3 solver on every call of
/// [`Prover::pop`].
pub enum IncrementalMode {
    Native,
    Emulated,
}

#[derive(Debug)]
enum StackSolver<'ctx> {
    Native(Solver<'ctx>),
    Emulated(Solver<'ctx>, Vec<Vec<Bool<'ctx>>>),
}

#[derive(Debug)]
struct LastSatSolverResult {
    /// Whether the current model is consistent with the assertions. If the SMT
    /// solver returned [`SatResult::Unknown`], it is
    /// [`ModelConsistency::Unknown`].
    model_consistency: Option<ModelConsistency>,
    /// The last result of a SAT/proof check so we can return a chached result.
    /// It is reset any time the assertions on the solver are modified.
    /// Sometimes Z3 caches on its own, but it is not reliable. Therefore, we do
    /// it here as well to be sure.
    last_result: SolverResult,
}

/// A prover wraps a SAT solver, but it's used to prove validity of formulas.
/// It's a bit of a more explicit API to distinguish between assumptions for a
/// proof ([`Prover::add_assumption`]) and provables ([`Prover::add_provable`]).
///
/// It keeps track of whether there are any assertions added to the solver. If
/// there are none, then [`Prover::check_proof`] will return
/// [`ProveResult::Proof`] (instead of [`SatResult::Sat`], i.e.
/// [`ProveResult::Counterexample`]). Therefore, you shouldn't add assertions
/// via [`Prover::solver`] to not mess that tracking up.
///
/// In contrast to [`z3::Solver`], the [`Prover`] requires exclusive ownership
/// to do any modifications of the solver.
#[derive(Debug)]
pub struct Prover<'ctx> {
    ctx: &'ctx Context,
    timeout: Option<Duration>,
    solver: StackSolver<'ctx>,
    /// Number of times push was called minus number of times pop was called.
    level: usize,
    /// The minimum level where an assertion was added to the solver.
    min_level_with_provables: Option<usize>,
    /// SMT solver type
    smt_solver: SolverType,
    /// Cached information about the last SAT/proof check call.
    last_result: Option<LastSatSolverResult>,
}

impl<'ctx> Prover<'ctx> {
    /// Create a new prover with the given [`Context`] and [`IncrementalMode`].
    pub fn new(ctx: &'ctx Context, mode: IncrementalMode, solver_type: SolverType) -> Self {
        Prover {
            ctx,
            timeout: None,
            solver: match mode {
                IncrementalMode::Native => StackSolver::Native(Solver::new(ctx)),
                IncrementalMode::Emulated => {
                    StackSolver::Emulated(Solver::new(ctx), vec![Vec::new()])
                }
            },
            level: 0,
            min_level_with_provables: None,
            smt_solver: solver_type,
            last_result: None,
        }
    }

    /// Get the Z3 context of this prover.
    pub fn get_context(&self) -> &'ctx Context {
        self.ctx
    }

    fn get_solver(&self) -> &Solver<'ctx> {
        match &self.solver {
            StackSolver::Native(solver) => solver,
            StackSolver::Emulated(solver, _) => solver,
        }
    }

    /// Get all assertions added to the underlying solver.
    pub fn get_assertions(&self) -> Vec<Bool<'ctx>> {
        self.get_solver().get_assertions()
    }

    /// Set a timeout for every `check` call.
    pub fn set_timeout(&mut self, duration: Duration) {
        self.timeout = Some(duration);
        set_solver_timeout(self.get_solver(), duration);
    }

    /// Add an assumption to this prover.
    pub fn add_assumption(&mut self, value: &Bool<'ctx>) {
        match &mut self.solver {
            StackSolver::Native(solver) => {
                solver.assert(value);
            }
            StackSolver::Emulated(solver, stack) => {
                solver.assert(value);
                stack.last_mut().unwrap().push(value.clone());
            }
        }
        self.last_result = None;
    }

    /// Add a proof obligation to this prover. It adds the negated formula to
    /// the underlying SAT solver's assertions. In addition, the prover will
    /// never return a counterexample unless a provable has been added.
    ///
    /// We call it `provable` to avoid confusion between the Z3 solver's
    /// `assert` methods.
    pub fn add_provable(&mut self, value: &Bool<'ctx>) {
        self.add_assumption(&value.not());
        self.min_level_with_provables.get_or_insert(self.level);
    }

    /// `self.check_proof_assuming(&[])`.
    pub fn check_proof(&mut self) -> Result<ProveResult, ProverCommandError> {
        self.check_proof_assuming(&[])
    }

    /// Do the SAT check, but consider a check with no provables to be a
    /// [`ProveResult::Proof`].
    pub fn check_proof_assuming(
        &mut self,
        assumptions: &[Bool<'ctx>],
    ) -> Result<ProveResult, ProverCommandError> {
        if !self.has_provables() {
            return Ok(ProveResult::Proof);
        }

        match self.smt_solver {
            SolverType::Z3 => {
                let res = match &self.last_result {
                    Some(cached_result) if assumptions.is_empty() => {
                        cached_result.last_result.clone()
                    }
                    _ => {
                        let solver = self.get_solver();
                        let res = if assumptions.is_empty() {
                            solver.check()
                        } else {
                            solver.check_assumptions(assumptions)
                        };

                        let solver_result = match res {
                            SatResult::Unsat => SolverResult::Unsat,
                            SatResult::Unknown => SolverResult::Unknown(None),
                            SatResult::Sat => SolverResult::Sat(None),
                        };
                        self.cache_result(solver_result.clone());
                        solver_result
                    }
                };

                match res {
                    SolverResult::Unsat => Ok(ProveResult::Proof),
                    SolverResult::Unknown(_) => {
                        Ok(ProveResult::Unknown(self.get_reason_unknown().unwrap()))
                    }
                    SolverResult::Sat(_) => Ok(ProveResult::Counterexample),
                }
            }
            _ => {
                let res = match &self.last_result {
                    Some(cached_result) if assumptions.is_empty() => {
                        cached_result.last_result.clone()
                    }
                    _ => {
                        let solver_result = execute_solver(self, assumptions)?;

                        if let SolverResult::Sat(Some(cex)) = solver_result.clone() {
                            let solver = self.get_solver();
                            solver.from_string(cex);
                            solver.check();
                        };

                        self.cache_result(solver_result.clone());
                        solver_result
                    }
                };

                match res {
                    SolverResult::Unsat => Ok(ProveResult::Proof),
                    SolverResult::Unknown(r) => {
                        let reason = r.unwrap_or(ReasonUnknown::Other("".to_string()));
                        Ok(ProveResult::Unknown(reason))
                    }
                    SolverResult::Sat(_) => Ok(ProveResult::Counterexample),
                }
            }
        }
    }

    /// Whether this prover has any provables added (excluding assumptions). If
    /// so, then any call to [`Self::check_proof`] or
    /// [`Self::check_proof_assuming`] will return [`ProveResult::Proof`]
    /// immediately.
    pub fn has_provables(&mut self) -> bool {
        self.min_level_with_provables.is_some()
    }

    /// Do the regular SAT check.
    pub fn check_sat(&mut self) -> Result<SatResult, ProverCommandError> {
        if let Some(cached_result) = &self.last_result {
            return Ok(cached_result.last_result.to_sat_result());
        }

        let sat_result = match self.smt_solver {
            SolverType::Z3 => {
                let sat_result = self.get_solver().check();

                let solver_result = match sat_result {
                    SatResult::Unsat => SolverResult::Unsat,
                    SatResult::Unknown => SolverResult::Unknown(None),
                    SatResult::Sat => SolverResult::Sat(None),
                };
                self.cache_result(solver_result);

                sat_result
            }
            _ => {
                let solver_result = execute_solver(self, &[])?;

                if let SolverResult::Sat(Some(cex)) = solver_result.clone() {
                    let solver = self.get_solver();
                    solver.from_string(cex);
                    solver.check();
                };
                self.cache_result(solver_result.clone());

                solver_result.to_sat_result()
            }
        };

        Ok(sat_result)
    }

    /// Save the result of the last SAT/proof check.
    fn cache_result(&mut self, solver_result: SolverResult) {
        let model_consistency = match solver_result {
            SolverResult::Sat(_) => Some(ModelConsistency::Consistent),
            SolverResult::Unknown(_) => Some(ModelConsistency::Unknown),
            SolverResult::Unsat => None,
        };
        self.last_result = Some(LastSatSolverResult {
            model_consistency,
            last_result: solver_result,
        });
    }

    /// Retrieve the model from the solver. If the result of the latest check
    /// was [`ProveResult::Counterexample`] or [`SatResult::Sat`], then the
    /// model is guaranteed to be consistent with the assertions
    /// ([`ModelConsistency::Consistent`]). After a
    /// [`ProveResult::Unknown`]/[`SatResult::Unknown`], the model is
    /// [`ModelConsistency::Inconsistent`].
    pub fn get_model(&self) -> Option<InstrumentedModel<'ctx>> {
        let consistency = self.last_result.as_ref()?.model_consistency?;
        let model = self.get_solver().get_model()?;
        Some(InstrumentedModel::new(consistency, model))
    }

    /// Retrieve the UNSAT core. See [`Solver::get_unsat_core()`].
    pub fn get_unsat_core(&self) -> Vec<Bool<'ctx>> {
        self.get_solver().get_unsat_core()
    }

    /// See [`Solver::get_reason_unknown`].
    pub fn get_reason_unknown(&self) -> Option<ReasonUnknown> {
        self.get_solver()
            .get_reason_unknown()
            .map(|reason| reason.parse().unwrap())
    }

    /// See [`Solver::push`].
    pub fn push(&mut self) {
        self.level += 1;
        match &mut self.solver {
            StackSolver::Native(solver) => solver.push(),
            StackSolver::Emulated(_, stack) => stack.push(Vec::new()),
        }
    }

    /// See [`Solver::pop`].
    pub fn pop(&mut self) {
        self.level = self.level.checked_sub(1).expect("cannot pop level 0");
        if let Some(prev_min_level) = self.min_level_with_provables {
            // if there are no assertions at this level, remove the counter
            if prev_min_level > self.level {
                self.min_level_with_provables.take();
            }
        }

        match &mut self.solver {
            StackSolver::Native(solver) => {
                // we don't know if the pop will change the state, so reset in
                // every case
                self.last_result = None;
                solver.pop(1)
            }
            StackSolver::Emulated(ref mut solver, stack) => {
                let old_top = stack.pop().expect("stack was empty, cannot call pop");
                debug_assert_eq!(stack.len(), self.level + 1);

                // if we didn't change the solver state, we do not need to reset
                if old_top.is_empty() {
                    return;
                }

                self.last_result = None;
                *solver = Solver::new(self.ctx);
                for level in stack.iter().flatten() {
                    solver.assert(level);
                }
            }
        }
    }

    /// Retrieve the current stack level. Useful for debug assertions.
    pub fn level(&self) -> usize {
        if let StackSolver::Emulated(_, stack) = &self.solver {
            debug_assert_eq!(stack.len(), self.level + 1);
        }
        self.level
    }

    /// Return the solver's statistics.
    pub fn get_statistics(&self) -> Statistics {
        self.get_solver().get_statistics()
    }

    /// Turns this prover into a regular [`Solver`].
    pub fn into_solver(self) -> Solver<'ctx> {
        match self.solver {
            StackSolver::Native(solver) => solver,
            StackSolver::Emulated(solver, _) => solver,
        }
    }

    /// Create an exists-forall solver. All constants provided in the iterator
    /// will be universally quantified. The rest will be existentially
    /// quantified.
    ///
    /// The result is a [`Prover`] for convenience (such as using the
    /// [`Self::level()`] function), but it should be used as a [`Solver`] via
    /// [`Self::check_sat()`].
    pub fn to_exists_forall(&self, universal: &[Dynamic<'ctx>]) -> Prover<'ctx> {
        let universal: Vec<&dyn Ast<'ctx>> =
            universal.iter().map(|v| v as &dyn Ast<'ctx>).collect();
        let theorem = forall_const(
            self.ctx,
            &universal,
            &[],
            &Bool::and(self.ctx, &self.get_assertions()).not(),
        );
        let mut res = Prover::new(self.ctx, IncrementalMode::Native, SolverType::Z3); // TODO
        res.add_assumption(&theorem);
        res
    }

    /// Return the SMT-LIB that represents the solver state.
    pub fn get_smtlib(&self) -> Smtlib {
        Smtlib::from_solver(self.get_solver())
    }

    pub fn get_smt_solver(&self) -> SolverType {
        self.smt_solver.clone()
    }
}

#[cfg(test)]
mod test {
    use z3::{ast::Bool, Config, Context, SatResult};

    use crate::prover::{IncrementalMode, SolverType};

    use super::{ProveResult, Prover};

    #[test]
    fn test_prover() {
        for mode in [IncrementalMode::Native, IncrementalMode::Emulated] {
            let ctx = Context::new(&Config::default());
            let mut prover = Prover::new(&ctx, mode, SolverType::Z3);
            assert!(matches!(prover.check_proof(), Ok(ProveResult::Proof)));
            assert_eq!(prover.check_sat(), Ok(SatResult::Sat));

            prover.push();
            prover.add_assumption(&Bool::from_bool(&ctx, true));
            assert!(matches!(prover.check_proof(), Ok(ProveResult::Proof)));
            assert_eq!(prover.check_sat(), Ok(SatResult::Sat));
            prover.pop();

            assert!(matches!(prover.check_proof(), Ok(ProveResult::Proof)));
            assert_eq!(prover.check_sat(), Ok(SatResult::Sat));
        }
    }
}
