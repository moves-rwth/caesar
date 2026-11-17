//! Proof obligations over a solver session.

use std::{fmt::Display, time::Duration};

use z3::{ast::Bool, Context, SatResult};

use crate::{
    model::InstrumentedModel,
    smtlib::Smtlib,
    solver::{IncrementalMode, SolverSession},
    util::ReasonUnknown,
};

/// The result of a proof query.
#[derive(Debug)]
pub enum ProveResult {
    Proof,
    Counterexample,
    Unknown(ReasonUnknown),
}

impl Display for ProveResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProveResult::Proof => f.write_str("Proof"),
            ProveResult::Counterexample => f.write_str("Counterexample"),
            ProveResult::Unknown(reason) => f.write_fmt(format_args!("Unknown (reason: {reason})")),
        }
    }
}

/// Adds proof obligations to a solver session and interprets counterexample queries.
/// A query with no proof obligations is proved without consulting the solver.
#[derive(Debug)]
pub struct Prover<'ctx> {
    session: SolverSession<'ctx>,
    min_level_with_provables: Option<usize>,
}

impl<'ctx> Prover<'ctx> {
    pub fn new(ctx: &'ctx Context, mode: IncrementalMode) -> Self {
        Self {
            session: SolverSession::new(ctx, mode),
            min_level_with_provables: None,
        }
    }

    pub fn set_timeout(&mut self, timeout: Duration) {
        self.session.set_timeout(timeout);
    }

    pub fn add_assumption(&mut self, value: &Bool<'ctx>) {
        self.session.assert(value);
    }

    /// Add the negation of a proof obligation to the counterexample query.
    pub fn add_provable(&mut self, value: &Bool<'ctx>) {
        self.session.assert(&value.not());
        self.min_level_with_provables
            .get_or_insert(self.session.level());
    }

    pub fn check_proof(&mut self) -> ProveResult {
        self.check_proof_assuming(&[])
    }

    pub fn check_proof_assuming(&mut self, assumptions: &[Bool<'ctx>]) -> ProveResult {
        if self.min_level_with_provables.is_none() {
            self.session.clear_last_check();
            return ProveResult::Proof;
        }
        match self.session.check_assuming(assumptions) {
            SatResult::Unsat => ProveResult::Proof,
            SatResult::Sat => ProveResult::Counterexample,
            SatResult::Unknown => ProveResult::Unknown(self.session.get_reason_unknown().unwrap()),
        }
    }

    pub fn push(&mut self) {
        self.session.push();
    }

    pub fn pop(&mut self) {
        self.session.pop();
        if self
            .min_level_with_provables
            .is_some_and(|level| level > self.session.level())
        {
            self.min_level_with_provables = None;
        }
    }

    pub fn get_model(&self) -> Option<InstrumentedModel<'ctx>> {
        self.session.get_model()
    }

    pub fn get_assertions(&self) -> Vec<Bool<'ctx>> {
        self.session.get_assertions()
    }

    pub fn get_smtlib(&self) -> Smtlib {
        self.session.get_smtlib()
    }

    /// Consume the prover into a SAT query whose unsatisfiability establishes the proof.
    /// An empty set of obligations has no counterexamples, regardless of the assumptions.
    pub fn into_proof_query(mut self) -> SolverSession<'ctx> {
        if self.min_level_with_provables.is_none() {
            self.session
                .assert(&Bool::from_bool(self.session.get_context(), false));
        }
        self.session
    }
}

#[cfg(test)]
mod test {
    use z3::{ast::Bool, Config, Context, SatResult};

    use super::{ProveResult, Prover};
    use crate::solver::IncrementalMode;

    #[test]
    fn proof_obligations_follow_scopes_and_assumed_checks() {
        for mode in [IncrementalMode::Native, IncrementalMode::Emulated] {
            let ctx = Context::new(&Config::default());
            let p = Bool::new_const(&ctx, "p");
            let mut prover = Prover::new(&ctx, mode);
            assert_eq!(prover.session.check(), SatResult::Sat);
            assert!(prover.get_model().is_some());
            assert!(matches!(prover.check_proof(), ProveResult::Proof));
            assert!(prover.get_model().is_none());
            prover.push();
            prover.add_provable(&p);
            assert!(matches!(
                prover.check_proof_assuming(std::slice::from_ref(&p)),
                ProveResult::Proof
            ));
            assert!(matches!(prover.check_proof(), ProveResult::Counterexample));
            prover.push();
            prover.add_assumption(&p);
            prover.add_provable(&Bool::from_bool(&ctx, true));
            assert!(matches!(prover.check_proof(), ProveResult::Proof));
            prover.pop();
            assert!(matches!(prover.check_proof(), ProveResult::Counterexample));
            prover.pop();
            prover.add_assumption(&p);
            assert!(matches!(prover.check_proof(), ProveResult::Proof));
            assert!(prover.get_model().is_none());
            let mut query = prover.into_proof_query();
            assert_eq!(
                query.get_assertions(),
                vec![p, Bool::from_bool(&ctx, false)]
            );
            assert_eq!(query.check(), SatResult::Unsat);
        }
    }
}
