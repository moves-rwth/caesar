use tracing::{debug, info, info_span, instrument, warn};
use z3::{
    ast::{Bool, Dynamic},
    Model, SatResult,
};
use z3rro::{
    prover::{ProveResult, Prover},
    util::ReasonUnknown,
};

use crate::{
    ast::{ExprBuilder, Span},
    resource_limits::LimitsRef,
    slicing::util::PartialMinimizeResult,
    smt::translate_exprs::TranslateExprs,
    VerifyError,
};

use super::{
    selection::SliceSelection,
    transform::{SliceStmt, SliceStmts},
    util::PartialMinimizer,
};

/// A structure that wraps the other SMT structures to do SMT-based program
/// slicing by doing a binary search of upper bounds on the number of statements
/// we're keeping in the program.
pub struct SliceSolver<'ctx> {
    prover: Prover<'ctx>,
    slice_stmts: Vec<(SliceStmt, Bool<'ctx>)>,
    universally_bound: Vec<Dynamic<'ctx>>,
}

impl<'ctx> SliceSolver<'ctx> {
    pub fn new<'smt>(
        slice_vars: SliceStmts,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        mut prover: Prover<'ctx>,
    ) -> Self {
        let builder = ExprBuilder::new(Span::dummy_span());
        let toggle_values: Vec<(SliceStmt, Bool<'_>)> = slice_vars
            .stmts
            .into_iter()
            .map(|stmt| {
                let z3_var = translate.t_bool(&builder.var(stmt.ident, translate.ctx.tcx()));
                (stmt, z3_var)
            })
            .collect();

        let universally_bound = translate
            .local_scope()
            .get_bounds()
            .filter(|bound| {
                if let Some(bound) = bound.as_bool() {
                    toggle_values.iter().all(|(_, b)| b != &bound)
                } else {
                    true
                }
            })
            .cloned()
            .collect();

        // add the constraints to the solver
        for slice_constraint in &slice_vars.constraints {
            prover.add_assumption(&translate.t_bool(slice_constraint));
        }

        prover.push();
        prover.push();

        SliceSolver {
            prover,
            slice_stmts: toggle_values,
            universally_bound,
        }
    }

    fn translate_selection(&self, selection: SliceSelection) -> (Bool<'ctx>, Vec<Bool<'ctx>>) {
        // collect Bool values for those variables we want to optimize
        let active_toggle_values: Vec<_> = self
            .slice_stmts
            .iter()
            .filter(|(stmt, _)| selection.enables(&stmt.selection))
            .map(|(_, value)| value.clone())
            .collect();

        // collect Bool values for those variables we do not want to optimize, which must be set to true.
        let inactive_toggle_values: Vec<_> = self
            .slice_stmts
            .iter()
            .filter(|(stmt, _)| !selection.enables(&stmt.selection))
            .map(|(_, value)| value)
            .collect();
        let inactive_formula = Bool::and(
            self.prover().solver().get_context(),
            &inactive_toggle_values,
        );

        (inactive_formula, active_toggle_values)
    }

    pub fn prover(&self) -> &Prover<'ctx> {
        &self.prover
    }

    /// Run [`check_original_proof`] on the original query, without slicing anything.
    /*     pub fn check_original_proof(&mut self) -> ProveResult<'ctx> {
        self.prover.pop();
        self.prover.push();
        let active_toggle_values: Vec<_> = self
            .slice_stmts
            .iter()
            .map(|(_, value)| value.clone())
            .collect();
        self.prover.add_assumption(&Bool::and(
            self.prover.solver().get_context(),
            &active_toggle_values,
        ));
        self.prover.check_proof()
    } */

    /// Minimize the number of statements while the program still verifies.
    #[instrument(level = "info", skip_all)]
    pub fn slice_while_verified(
        &mut self,
        limits_ref: &LimitsRef,
    ) -> Result<Option<Model<'ctx>>, VerifyError> {
        assert_eq!(self.prover.level(), 2);
        self.prover.pop();
        self.prover.pop();
        self.prover.push();

        let (inactive_formula, active_toggle_values) =
            self.translate_selection(SliceSelection::VERIFIED_SELECTION);

        let (prover, universally_bound) = (&mut self.prover, &self.universally_bound);

        // TODO: this is unsound if there are uninterpreted functions!
        warn!("The --slice-verify option is unsound if uninterpreted functions are used. This is not checked at the moment. Be careful!");

        let mut exists_forall_solver = prover.to_exists_forall(universally_bound);
        exists_forall_solver.add_assumption(&inactive_formula);
        exists_forall_solver.push();
        exists_forall_solver.push();
        slice(
            &mut exists_forall_solver,
            &active_toggle_values,
            false,
            true,
            limits_ref,
        )?;
        if prover.check_sat() == SatResult::Sat {
            Ok(exists_forall_solver.get_model())
        } else {
            Ok(None)
        }
    }

    /// Minimize the number of statements while the program is rejected with a counterexample.
    #[instrument(level = "info", skip_all)]
    pub fn slice_while_failing(
        &mut self,
        limits_ref: &LimitsRef,
    ) -> Result<ProveResult<'ctx>, VerifyError> {
        assert_eq!(self.prover.level(), 2);
        self.prover.pop();
        self.prover.pop();
        self.prover.push();

        let (inactive_formula, active_toggle_values) =
            self.translate_selection(SliceSelection::FAILURE_SELECTION);

        self.prover.add_assumption(&inactive_formula);
        self.prover.push();

        slice(
            &mut self.prover,
            &active_toggle_values,
            true,
            false,
            limits_ref,
        )?;
        Ok(self.prover.check_proof())
    }
}

fn slice<'ctx>(
    prover: &mut Prover<'ctx>,
    active_slice_vars: &[Bool<'ctx>],
    at_least_one: bool,
    continue_on_unknown: bool,
    limits_ref: &LimitsRef,
) -> Result<(), VerifyError> {
    assert_eq!(prover.level(), 2);

    let slice_vars: Vec<(&Bool<'ctx>, i32)> =
        active_slice_vars.iter().map(|value| (value, 1)).collect();

    let set_at_most_true = |prover: &mut Prover<'ctx>, at_most_n: usize| {
        prover.pop();
        prover.push();

        let ctx = prover.solver().get_context();
        let at_most_n_true = Bool::pb_le(ctx, &slice_vars, at_most_n as i32);
        prover.add_assumption(&at_most_n_true);
    };

    let min_least_bound = if at_least_one { 1 } else { 0 };
    let mut minimize = PartialMinimizer::new(min_least_bound..=slice_vars.len());

    let mut first_acceptance = None;

    let mut cur_solver_n: Option<usize> = None;
    while let Some(mid) = minimize.next_trial() {
        cur_solver_n = Some(mid);
        limits_ref.check_limits()?;

        let entered = info_span!(
            "at most n statements",
            n = mid,
            max_reject = minimize.max_reject(),
            min_accept = minimize.min_accept(),
            res = tracing::field::Empty,
        )
        .entered();

        set_at_most_true(prover, mid);
        if let Some(timeout) = limits_ref.time_left() {
            prover.set_timeout(timeout);
        }
        let res = prover.check_sat();

        entered.record("res", tracing::field::debug(res));

        match res {
            SatResult::Sat => {
                let model = prover.get_model().unwrap();
                // how many variables are actually true in the model? we can use
                // this as a tighter upper bound instead of just `mid`.
                let num_actually_true = slice_vars
                    .iter()
                    .filter(|var| model.eval(var.0, true).unwrap().as_bool().unwrap())
                    .count();
                assert!(num_actually_true <= mid);
                if num_actually_true != mid {
                    debug!(
                        actually_true = num_actually_true,
                        distance = mid - num_actually_true,
                        "obtained a better upper bound from model"
                    );
                }
                minimize.add_result(num_actually_true, PartialMinimizeResult::AcceptUpwards);
                if first_acceptance.is_none() {
                    first_acceptance = Some(num_actually_true);
                }
            }
            SatResult::Unknown => {
                if prover.get_reason_unknown() == Some(ReasonUnknown::Interrupted) {
                    return Err(VerifyError::Interrupted);
                }
                let res = if continue_on_unknown {
                    PartialMinimizeResult::Unknown
                } else {
                    PartialMinimizeResult::RejectDownwards
                };
                minimize.add_result(mid, res)
            }
            SatResult::Unsat => minimize.add_result(mid, PartialMinimizeResult::RejectDownwards),
        }
    }

    let enabled = minimize
        .min_accept()
        .or(minimize.max_reject())
        .unwrap_or(minimize.total_max());

    info!(
        enabled = enabled,
        removed_statements = slice_vars.len() - enabled,
        from_first_model = first_acceptance.map(|x| x - enabled),
        "slicing complete"
    );

    // after we're done searching, reset the solver to the last known
    // working number of statements.
    if let Some(cur_solver_n) = cur_solver_n {
        if cur_solver_n != enabled {
            set_at_most_true(prover, enabled);
            if let Some(timeout) = limits_ref.time_left() {
                prover.set_timeout(timeout);
            }
            let res = prover.check_sat();
            if minimize.min_accept().is_some() {
                assert_eq!(res, SatResult::Sat);
            } else if minimize.max_reject().is_some() {
                assert_eq!(res, SatResult::Unsat);
            } else if !active_slice_vars.is_empty() {
                assert_eq!(res, SatResult::Unknown);
            }
        }
    }

    assert_eq!(prover.level(), 2);
    Ok(())
}
