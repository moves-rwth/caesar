//! Not a SAT solver, but a prover. There's a difference.
use itertools::Itertools;
use thiserror::Error;

use std::{
    collections::VecDeque,
    env,
    fmt::Display,
    io::{self, Write},
    path::Path,
    process::Command,
    time::Duration,
};

use tempfile::NamedTempFile;

use z3::{
    ast::{forall_const, Ast, Bool, Dynamic},
    Context, SatResult, Solver, Statistics,
};

use crate::{
    model::{InstrumentedModel, ModelConsistency},
    smtlib::Smtlib,
    util::{set_solver_timeout, ReasonUnknown},
};


#[derive(Debug, Error)]
pub enum ProverCommandError {
    #[error("Environment variable error: {0}")]
    EnvVarError(#[from] env::VarError),
    #[error("Process execution failed: {0}")]
    ProcessError(#[from] io::Error),
    #[error("Parse error")]
    ParseError,
}

#[derive(Debug)]
pub enum SolverType {
    Z3,
    SWINE,
}

/// The result of a prove query.
#[derive(Debug)]
pub enum ProveResult {
    Proof,
    Counterexample,
    Unknown(ReasonUnknown),
}

/// Execute swine on the file located at file_path
fn execute_swine(file_path: &Path) -> Result<(SatResult, String), ProverCommandError> {
    let output = Command::new("swine").arg(file_path).output();

    match output {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let mut lines_buffer: VecDeque<&str>= stdout.lines().collect();
            let first_line = lines_buffer.pop_front().ok_or(ProverCommandError::ParseError)?;
            if first_line.trim().to_lowercase() == "unsat" {
                Ok((SatResult::Unsat, "".to_string()))
            } else if first_line.trim().to_lowercase() == "sat" {
                let _last_line = lines_buffer.pop_back().ok_or(ProverCommandError::ParseError)?;
                if _last_line.contains("SHA") {
                    let cex = lines_buffer.iter().join("");
                    Ok((SatResult::Sat, cex))
                } else {
                    Err(ProverCommandError::ParseError)
                }
            } else {
                lines_buffer.push_front(first_line);
                Ok((SatResult::Unknown, lines_buffer.iter().join("\n")))
            }
        }
        Err(e) => Err(ProverCommandError::ProcessError(e)),
    }
}

/// In order to execute the program, it is necessary to remove lines that
/// contain a forall quantifier or the declaration of the exponential function (exp).
fn remove_lines_for_swine(input: &str) -> String {
    let mut output = String::new();
    let mut tmp_buffer: VecDeque<char> = VecDeque::new();
    let mut input_buffer: VecDeque<char> = input.chars().collect();
    let mut cnt = 0;

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
                    if !tmp.contains("declare-fun exp") && !tmp.contains("forall") {
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
struct LastSatResult {
    /// Whether the current model is consistent with the assertions. If the SMT
    /// solver returned [`SatResult::Unknown`], it is
    /// [`ModelConsistency::Unknown`].
    model_consistency: Option<ModelConsistency>,
    /// The last result of a SAT/proof check so we can return a chached result.
    /// It is reset any time the assertions on the solver are modified.
    /// Sometimes Z3 caches on its own, but it is not reliable. Therefore, we do
    /// it here as well to be sure.
    last_result: SatResult,
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
    last_result: Option<LastSatResult>,
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
            SolverType::SWINE => {
                let mut smtlib = self.get_smtlib();
                smtlib.add_check_sat();
                let smtlib = smtlib.into_string();
                let mut smt_file: NamedTempFile = NamedTempFile::new().unwrap();
                smt_file
                    .write_all(remove_lines_for_swine(&smtlib).as_bytes())
                    .unwrap();
                let file_path = smt_file.path();

                let res = execute_swine(file_path);
                match res {
                    Ok((SatResult::Unsat, _)) => Ok(ProveResult::Proof),
                    Ok((SatResult::Unknown, reason)) => {
                        Ok(ProveResult::Unknown(ReasonUnknown::Other(reason)))
                    }
                    Ok((SatResult::Sat, cex)) => {
                        match &self.solver {
                            StackSolver::Native(solver) => {
                                solver.from_string(cex);
                            },
                            StackSolver::Emulated(solver, _) => {
                                solver.from_string(cex);
                            },
                        }
                        
                        Ok(ProveResult::Counterexample)
                    }
                    Err(err) => Err(err),
                }
            }
            SolverType::Z3 => {
                let res = match &self.last_result {
                    Some(cached_result) if assumptions.is_empty() => cached_result.last_result,
                    _ => {
                        let solver = self.get_solver();
                        let res = if assumptions.is_empty() {
                            solver.check()
                        } else {
                            solver.check_assumptions(assumptions)
                        };
                        self.cache_result(res);
                        res
                    }
                };
                match res {
                    SatResult::Unsat => Ok(ProveResult::Proof),
                    SatResult::Unknown => Ok(ProveResult::Unknown(self.get_reason_unknown().unwrap())),
                    SatResult::Sat => Ok(ProveResult::Counterexample),
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
    pub fn check_sat(&mut self) -> SatResult {
        if let Some(cached_result) = &self.last_result {
            return cached_result.last_result;
        }
        let res = self.get_solver().check();
        self.cache_result(res);
        res
    }

    /// Save the result of the last SAT/proof check.
    fn cache_result(&mut self, sat_result: SatResult) {
        let model_consistency = match sat_result {
            SatResult::Sat => Some(ModelConsistency::Consistent),
            SatResult::Unknown => Some(ModelConsistency::Unknown),
            SatResult::Unsat => None,
        };
        self.last_result = Some(LastSatResult {
            model_consistency,
            last_result: sat_result,
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
            assert_eq!(prover.check_sat(), SatResult::Sat);

            prover.push();
            prover.add_assumption(&Bool::from_bool(&ctx, true));
            assert!(matches!(prover.check_proof(), Ok(ProveResult::Proof)));
            assert_eq!(prover.check_sat(), SatResult::Sat);
            prover.pop();

            assert!(matches!(prover.check_proof(), Ok(ProveResult::Proof)));
            assert_eq!(prover.check_sat(), SatResult::Sat);
        }
    }
}
