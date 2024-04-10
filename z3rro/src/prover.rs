//! Not a SAT solver, but a prover. There's a difference.

use std::time::Duration;

use z3::{ast::Bool, Context, Model, Params, SatResult, Solver};

use crate::util::{set_solver_timeout, ReasonUnknown};

/// The result of a prove query.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProveResult {
    Proof,
    Counterexample,
    Unknown,
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
pub struct Prover<'ctx> {
    /// The underlying solver.
    solver: Solver<'ctx>,
    /// Number of times push was called minus number of times pop was called.
    level: usize,
    /// The minimum level where an assertion was added to the solver.
    min_level_with_assertions: Option<usize>,
}

impl<'ctx> Prover<'ctx> {
    /// Create a new prover with the given [`Context`].
    pub fn new(ctx: &'ctx Context) -> Self {
        Prover {
            solver: Solver::new(ctx),
            level: 0,
            min_level_with_assertions: None,
        }
    }

    /// Set solver parameters.
    pub fn set_params(&mut self, params: &Params<'ctx>) {
        self.solver.set_params(params);
    }

    /// Set a timeout using [`set_solver_timeout`].
    pub fn set_timeout(&mut self, duration: Duration) {
        set_solver_timeout(&self.solver, duration);
    }

    /// Add an assumption to this prover.
    pub fn add_assumption(&mut self, value: &Bool<'ctx>) {
        self.solver.assert(value);
        self.min_level_with_assertions.get_or_insert(self.level);
    }

    /// Add a proof obligation to this prover. It adds the negated formula to
    /// the underlying SAT solver's assertions.
    ///
    /// We call it `provable` to avoid confusion between the Z3 solver's
    /// `assert` methods.
    pub fn add_provable(&mut self, value: &Bool<'ctx>) {
        self.solver.assert(&value.not());
        self.min_level_with_assertions.get_or_insert(self.level);
    }

    /// Do the SAT check, but consider a check with no assumptions to be a
    /// [`ProveResult::Proof`].
    pub fn check_proof(&mut self) -> ProveResult {
        if self.min_level_with_assertions.is_none() {
            debug_assert_eq!(self.solver.check(), SatResult::Sat);
            return ProveResult::Proof;
        }
        match self.solver.check() {
            SatResult::Unsat => ProveResult::Proof,
            SatResult::Unknown => ProveResult::Unknown,
            SatResult::Sat => ProveResult::Counterexample,
        }
    }

    /// Do the regular SAT check.
    pub fn check_sat(&mut self) -> SatResult {
        self.solver().check()
    }

    /// Retrieve the model from the solver.
    pub fn get_model(&self) -> Option<Model<'ctx>> {
        self.solver.get_model()
    }

    /// See [`Solver::get_reason_unknown`].
    pub fn get_reason_unknown(&self) -> Option<ReasonUnknown> {
        self.solver
            .get_reason_unknown()
            .map(|reason| reason.parse().unwrap())
    }

    /// See [`Solver::push`].
    pub fn push(&mut self) {
        self.solver.push();
        self.level += 1;
    }

    /// See [`Solver::pop`].
    pub fn pop(&mut self) {
        self.solver.pop(1);
        self.level = self.level.checked_sub(1).expect("cannot pop level 0");
        if let Some(prev_min_level) = self.min_level_with_assertions {
            // if there are no assertions at this level, remove the counter
            if prev_min_level > self.level {
                self.min_level_with_assertions.take();
            }
        }
    }

    /// Return a reference to the underlying solver. Please do not modifiy it!
    pub fn solver(&self) -> &Solver<'ctx> {
        &self.solver
    }
}

#[cfg(test)]
mod test {
    use z3::{ast::Bool, Config, Context, SatResult};

    use super::{ProveResult, Prover};

    #[test]
    fn test_prover() {
        let ctx = Context::new(&Config::default());
        let mut prover = Prover::new(&ctx);
        assert_eq!(prover.check_proof(), ProveResult::Proof);
        assert_eq!(prover.check_sat(), SatResult::Sat);

        prover.push();
        prover.add_assumption(&Bool::from_bool(&ctx, true));
        assert_eq!(prover.check_proof(), ProveResult::Counterexample);
        assert_eq!(prover.check_sat(), SatResult::Sat);
        prover.pop();

        assert_eq!(prover.check_proof(), ProveResult::Proof);
        assert_eq!(prover.check_sat(), SatResult::Sat);
    }
}
