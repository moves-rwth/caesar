//! Not a SAT solver, but a prover. There's a difference.

use std::{fmt::Display, time::Duration};

use z3::{
    ast::{forall_const, Ast, Bool, Dynamic},
    Context, Model, SatResult, Solver,
};

use crate::{
    model::InstrumentedModel,
    smtlib::Smtlib,
    util::{set_solver_timeout, ReasonUnknown},
};

/// The result of a prove query.
#[derive(Debug)]
pub enum ProveResult<'ctx> {
    Proof,
    Counterexample(InstrumentedModel<'ctx>),
    Unknown(ReasonUnknown),
}

impl Display for ProveResult<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProveResult::Proof => f.write_str("Proof"),
            ProveResult::Counterexample(_) => f.write_str("Counterexample"),
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
}

impl<'ctx> Prover<'ctx> {
    /// Create a new prover with the given [`Context`] and [`IncrementalMode`].
    pub fn new(ctx: &'ctx Context, mode: IncrementalMode) -> Self {
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
    pub fn check_proof(&mut self) -> ProveResult<'ctx> {
        self.check_proof_assuming(&[])
    }

    /// Do the SAT check, but consider a check with no provables to be a
    /// [`ProveResult::Proof`].
    pub fn check_proof_assuming(&mut self, assumptions: &[Bool<'ctx>]) -> ProveResult<'ctx> {
        if self.min_level_with_provables.is_none() {
            return ProveResult::Proof;
        }

        match &mut self.solver {
            StackSolver::Native(solver) => {
                let res = if assumptions.is_empty() {
                    solver.check()
                } else {
                    solver.check_assumptions(assumptions)
                };
                match res {
                    SatResult::Unsat => ProveResult::Proof,
                    SatResult::Unknown => ProveResult::Unknown(self.get_reason_unknown().unwrap()),
                    SatResult::Sat => {
                        let model = self.get_model().unwrap();
                        let model = InstrumentedModel::new(model);
                        ProveResult::Counterexample(model)
                    }
                }
            }
            StackSolver::Emulated(solver, _) => {
                let res = if assumptions.is_empty() {
                    solver.check()
                } else {
                    solver.check_assumptions(assumptions)
                };
                match res {
                    SatResult::Unsat => ProveResult::Proof,
                    SatResult::Unknown => ProveResult::Unknown(self.get_reason_unknown().unwrap()),
                    SatResult::Sat => {
                        let model = self.get_model().unwrap();
                        let model = InstrumentedModel::new(model);
                        ProveResult::Counterexample(model)
                    }
                }
            }
        }
    }

    /// Do the regular SAT check.
    pub fn check_sat(&mut self) -> SatResult {
        self.get_solver().check()
    }

    /// Retrieve the model from the solver.
    pub fn get_model(&self) -> Option<Model<'ctx>> {
        self.get_solver().get_model()
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
            StackSolver::Native(solver) => solver.pop(1),
            StackSolver::Emulated(ref mut solver, stack) => {
                stack.pop();
                debug_assert_eq!(stack.len(), self.level + 1);
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
        let mut res = Prover::new(self.ctx, IncrementalMode::Native); // TODO
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

    use crate::prover::IncrementalMode;

    use super::{ProveResult, Prover};

    #[test]
    fn test_prover() {
        for mode in [IncrementalMode::Native, IncrementalMode::Emulated] {
            let ctx = Context::new(&Config::default());
            let mut prover = Prover::new(&ctx, mode);
            assert!(matches!(prover.check_proof(), ProveResult::Proof));
            assert_eq!(prover.check_sat(), SatResult::Sat);

            prover.push();
            prover.add_assumption(&Bool::from_bool(&ctx, true));
            assert!(matches!(prover.check_proof(), ProveResult::Proof));
            assert_eq!(prover.check_sat(), SatResult::Sat);
            prover.pop();

            assert!(matches!(prover.check_proof(), ProveResult::Proof));
            assert_eq!(prover.check_sat(), SatResult::Sat);
        }
    }
}
