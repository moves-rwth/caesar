//! Stateful Z3 solving with scopes, configuration, and query results.

use std::time::Duration;

use z3::{ast::Bool, Context, SatResult, Solver, Statistics};

use crate::{
    model::{InstrumentedModel, ModelConsistency},
    params::SmtParams,
    smtlib::Smtlib,
    util::{set_solver_timeout, ReasonUnknown},
};

/// Whether scopes use Z3's native stack or reconstruct the solver when assertions are popped.
pub enum IncrementalMode {
    Native,
    Emulated,
}

#[derive(Debug)]
enum StackSolver<'ctx> {
    Native(Solver<'ctx>),
    Emulated(Solver<'ctx>, Vec<Vec<Bool<'ctx>>>),
}

/// Remembers the last answer to avoid repeated Z3 calls and guard model/core access.
/// Marks checks with temporary assumptions so their results cannot be reused without them.
#[derive(Debug)]
struct LastCheck {
    has_assumptions: bool,
    result: SatResult,
}

/// A wrapper around [`z3::Solver`] that adds:
///
/// - Caching for repeated checks without temporary assumptions, invalidated when assertions or scopes change.
/// - Emulated push/pop scopes that rebuild the solver instead of using Z3's native stack.
/// - Timeout settings that are reapplied when the solver is rebuilt.
/// - Guarded access to the last check's model, unsat core, and unknown reason.
///
/// Unlike [`z3::Solver`], checking or changing the solver requires `&mut self`.
#[derive(Debug)]
pub struct SolverSession<'ctx> {
    ctx: &'ctx Context,
    timeout: Option<Duration>,
    solver: StackSolver<'ctx>,
    /// Number of times push was called minus number of times pop was called.
    level: usize,
    last_check: Option<LastCheck>,
}

impl<'ctx> SolverSession<'ctx> {
    pub fn new(ctx: &'ctx Context, mode: IncrementalMode) -> Self {
        Self {
            ctx,
            timeout: None,
            solver: match mode {
                IncrementalMode::Native => StackSolver::Native(Self::create_solver(ctx, None)),
                IncrementalMode::Emulated => {
                    StackSolver::Emulated(Self::create_solver(ctx, None), vec![Vec::new()])
                }
            },
            level: 0,
            last_check: None,
        }
    }

    fn create_solver(ctx: &'ctx Context, timeout: Option<Duration>) -> Solver<'ctx> {
        let solver = Solver::new(ctx);
        if let Some(timeout) = timeout {
            set_solver_timeout(&solver, timeout);
        }
        solver
    }

    pub fn get_context(&self) -> &'ctx Context {
        self.ctx
    }

    fn get_solver(&self) -> &Solver<'ctx> {
        match &self.solver {
            StackSolver::Native(solver) => solver,
            StackSolver::Emulated(solver, _) => solver,
        }
    }

    pub(crate) fn clear_last_check(&mut self) {
        self.last_check = None;
    }

    /// Get all assertions added to the underlying solver.
    pub fn get_assertions(&self) -> Vec<Bool<'ctx>> {
        self.get_solver().get_assertions()
    }

    /// Set the timeout for subsequent checks and allow an unknown query to be retried.
    pub fn set_timeout(&mut self, duration: Duration) {
        self.timeout = Some(duration);
        set_solver_timeout(self.get_solver(), duration);
        if self
            .last_check
            .as_ref()
            .is_some_and(|check| check.result == SatResult::Unknown)
        {
            self.last_check = None;
        }
    }

    pub fn assert(&mut self, value: &Bool<'ctx>) {
        match &mut self.solver {
            StackSolver::Native(solver) => {
                solver.assert(value);
            }
            StackSolver::Emulated(solver, stack) => {
                solver.assert(value);
                stack.last_mut().unwrap().push(value.clone());
            }
        }
        self.last_check = None;
    }

    pub fn check(&mut self) -> SatResult {
        self.check_assuming(&[])
    }

    /// Check the current assertions under temporary assumptions.
    /// Only consecutive checks without temporary assumptions may reuse the last result.
    pub fn check_assuming(&mut self, assumptions: &[Bool<'ctx>]) -> SatResult {
        if assumptions.is_empty() {
            if let Some(check) = self
                .last_check
                .as_ref()
                .filter(|check| !check.has_assumptions)
            {
                return check.result;
            }
        }
        let result = if assumptions.is_empty() {
            self.get_solver().check()
        } else {
            self.get_solver().check_assumptions(assumptions)
        };
        self.last_check = Some(LastCheck {
            result,
            has_assumptions: !assumptions.is_empty(),
        });
        result
    }

    /// Retrieve a model of the last check, if available.
    /// A model returned after `Unknown` has no consistency guarantee.
    pub fn get_model(&self) -> Option<InstrumentedModel<'ctx>> {
        let consistency = match self.last_check.as_ref()?.result {
            SatResult::Sat => ModelConsistency::Consistent,
            SatResult::Unknown => ModelConsistency::Unknown,
            SatResult::Unsat => return None,
        };
        let model = self.get_solver().get_model()?;
        Some(InstrumentedModel::new(consistency, model))
    }

    /// Retrieve the core of the current unsatisfiable check.
    /// Panics if no current check returned `Unsat`.
    pub fn get_unsat_core(&self) -> Vec<Bool<'ctx>> {
        assert_eq!(
            self.last_check.as_ref().map(|check| check.result),
            Some(SatResult::Unsat),
            "an unsat core requires a current unsatisfiable check"
        );
        self.get_solver().get_unsat_core()
    }

    /// See [`Solver::get_reason_unknown`].
    pub fn get_reason_unknown(&self) -> Option<ReasonUnknown> {
        if self.last_check.as_ref()?.result != SatResult::Unknown {
            return None;
        }
        self.get_solver()
            .get_reason_unknown()
            .map(|reason| reason.parse().unwrap())
    }

    /// See [`Solver::push`].
    pub fn push(&mut self) {
        self.last_check = None;
        self.level += 1;
        match &mut self.solver {
            StackSolver::Native(solver) => solver.push(),
            StackSolver::Emulated(_, stack) => stack.push(Vec::new()),
        }
    }

    /// See [`Solver::pop`].
    pub fn pop(&mut self) {
        self.level = self.level.checked_sub(1).expect("cannot pop level 0");
        self.last_check = None;

        match &mut self.solver {
            StackSolver::Native(solver) => solver.pop(1),
            StackSolver::Emulated(ref mut solver, stack) => {
                let old_top = stack.pop().expect("stack was empty, cannot call pop");
                debug_assert_eq!(stack.len(), self.level + 1);

                // An empty scope does not require reconstructing the solver.
                if old_top.is_empty() {
                    return;
                }

                *solver = Self::create_solver(self.ctx, self.timeout);
                for level in stack.iter().flatten() {
                    solver.assert(level);
                }
            }
        }
    }

    /// Retrieve the current stack level.
    pub fn level(&self) -> usize {
        if let StackSolver::Emulated(_, stack) = &self.solver {
            debug_assert_eq!(stack.len(), self.level + 1);
        }
        self.level
    }

    /// Return the solver's statistics.
    pub fn get_statistics(&self) -> Statistics<'ctx> {
        self.get_solver().get_statistics()
    }

    /// Return the SMT-LIB that represents the solver state.
    pub fn get_smtlib(&self) -> Smtlib {
        let global_params = SmtParams::global().lock().unwrap().clone();
        Smtlib::from_solver(Some(global_params), self.get_solver())
    }
}

#[cfg(test)]
mod test {
    use std::{panic::AssertUnwindSafe, time::Duration};

    use z3::{ast::Bool, Config, Context, SatResult};

    use super::{IncrementalMode, SolverSession};

    #[test]
    fn temporary_assumptions_do_not_escape_their_check() {
        for mode in [IncrementalMode::Native, IncrementalMode::Emulated] {
            let ctx = Context::new(&Config::default());
            let p = Bool::new_const(&ctx, "p");
            let mut session = SolverSession::new(&ctx, mode);
            session.assert(&p.not());
            assert_eq!(session.check(), SatResult::Sat);
            assert_eq!(
                session.check_assuming(std::slice::from_ref(&p)),
                SatResult::Unsat
            );
            assert_eq!(session.get_unsat_core(), vec![p.clone()]);
            assert!(session.get_model().is_none());
            assert_eq!(session.check_assuming(&[p.not()]), SatResult::Sat);
            assert_eq!(session.check_assuming(&[p]), SatResult::Unsat);
            assert_eq!(session.check(), SatResult::Sat);
            assert_eq!(session.check(), SatResult::Sat);
            assert!(session.get_model().is_some());
        }
    }

    #[test]
    fn scope_changes_invalidate_details_and_restore_assertions() {
        for mode in [IncrementalMode::Native, IncrementalMode::Emulated] {
            let ctx = Context::new(&Config::default());
            let p = Bool::new_const(&ctx, "p");
            let mut session = SolverSession::new(&ctx, mode);
            session.set_timeout(Duration::from_secs(5));
            session.assert(&p);
            assert_eq!(session.check(), SatResult::Sat);
            session.push();
            assert!(session.get_model().is_none());
            session.assert(&p.not());
            assert_eq!(session.check(), SatResult::Unsat);
            session.push();
            assert!(
                std::panic::catch_unwind(AssertUnwindSafe(|| session.get_unsat_core())).is_err()
            );
            assert_eq!(session.check(), SatResult::Unsat);
            session.pop();
            assert!(session.last_check.is_none());
            assert_eq!(session.check(), SatResult::Unsat);
            session.pop();
            assert_eq!(session.level(), 0);
            assert!(session.get_model().is_none());
            assert_eq!(session.get_assertions(), vec![p]);
            assert_eq!(session.check(), SatResult::Sat);
            session.assert(&Bool::from_bool(&ctx, false));
            assert!(session.get_model().is_none());
            assert_eq!(session.check(), SatResult::Unsat);
        }
    }
}
