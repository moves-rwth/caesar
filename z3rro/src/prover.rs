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
    Native(Solver<'ctx>, Vec<bool>),
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
}

impl<'ctx> Prover<'ctx> {
    /// Create a new prover with the given [`Context`] and [`IncrementalMode`].
    pub fn new(ctx: &'ctx Context, mode: IncrementalMode) -> Self {
        Prover {
            ctx,
            timeout: None,
            solver: match mode {
                IncrementalMode::Native => StackSolver::Native(Solver::new(ctx), vec![false]),
                IncrementalMode::Emulated => {
                    StackSolver::Emulated(Solver::new(ctx), vec![Vec::new()])
                }
            },
        }
    }

    /// Get the Z3 context of this prover.
    pub fn get_context(&self) -> &'ctx Context {
        self.ctx
    }

    fn get_solver(&self) -> &Solver<'ctx> {
        match &self.solver {
            StackSolver::Native(solver, _) => solver,
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
            StackSolver::Native(solver, stack) => {
                solver.assert(value);
                *stack.last_mut().unwrap() = true;
            }
            StackSolver::Emulated(solver, stack) => {
                solver.assert(value);
                stack.last_mut().unwrap().push(value.clone());
            }
        }
    }

    /// Add a proof obligation to this prover. It adds the negated formula to
    /// the underlying SAT solver's assertions.
    ///
    /// We call it `provable` to avoid confusion between the Z3 solver's
    /// `assert` methods.
    pub fn add_provable(&mut self, value: &Bool<'ctx>) {
        self.add_assumption(&value.not());
    }

    /// `self.check_proof_assuming(&[])`.
    pub fn check_proof(&mut self) -> ProveResult<'ctx> {
        self.check_proof_assuming(&[])
    }

    /// Do the SAT check, but consider a check with no provables to be a
    /// [`ProveResult::Proof`].
    pub fn check_proof_assuming(&mut self, assumptions: &[Bool<'ctx>]) -> ProveResult<'ctx> {
        match &mut self.solver {
            StackSolver::Native(solver, stack) => {
                if stack.iter().all(|v| !*v) {
                    return ProveResult::Proof;
                }

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
            StackSolver::Emulated(solver, stack) => {
                if stack.iter().all(|level| level.is_empty()) {
                    return ProveResult::Proof;
                }

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
        match &mut self.solver {
            StackSolver::Native(solver, stack) => {
                solver.push();
                stack.push(false)
            }
            StackSolver::Emulated(_, stack) => stack.push(Vec::new()),
        }
    }

    /// See [`Solver::pop`].
    pub fn pop(&mut self) {
        match &mut self.solver {
            StackSolver::Native(solver, stack) => {
                solver.pop(1);
                stack.pop();
                assert!(!stack.is_empty())
            }
            StackSolver::Emulated(ref mut solver, stack) => {
                stack.pop();
                assert!(!stack.is_empty());
                *solver = Solver::new(self.ctx);
                for level in stack.iter().flatten() {
                    solver.assert(level);
                }
            }
        }
    }

    /// Retrieve the current stack level. Useful for debug assertions.
    pub fn level(&self) -> usize {
        match &self.solver {
            StackSolver::Native(_, stack) => stack.len() - 1,
            StackSolver::Emulated(_, stack) => stack.len() - 1,
        }
    }

    /// Turns this prover into a regular [`Solver`].
    pub fn into_solver(self) -> Solver<'ctx> {
        match self.solver {
            StackSolver::Native(solver, _) => solver,
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
        let solver = match &self.solver {
            StackSolver::Native(solver, _) => solver,
            StackSolver::Emulated(solver, _stack) => solver,
        };
        Smtlib::from_solver(solver)
    }
}

#[cfg(test)]
mod test {
    use z3::{ast::Bool, Config, Context, SatResult};

    use crate::prover::IncrementalMode;

    use super::{ProveResult, Prover};

    #[test]
    fn test_prover() {
        let ctx = Context::new(&Config::default());
        let mut prover = Prover::new(&ctx, IncrementalMode::Native);
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
