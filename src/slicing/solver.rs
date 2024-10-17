use std::{collections::HashSet, time::Duration};

use tracing::{debug, info, info_span, instrument, warn};
use z3::{
    ast::{Bool, Dynamic},
    SatResult,
};
use z3rro::{
    model::InstrumentedModel,
    prover::{ProveResult, Prover},
    util::ReasonUnknown,
};

use crate::{
    ast::{ExprBuilder, Span},
    resource_limits::{LimitError, LimitsRef},
    slicing::{
        model::{SliceMode, SliceModel},
        util::{PartialMinimizeResult, SubsetExploration},
    },
    smt::translate_exprs::TranslateExprs,
    VerifyError,
};

use super::{
    selection::SliceSelection,
    transform::{SliceStmt, SliceStmts},
    util::PartialMinimizer,
};

#[derive(Debug)]
pub struct SliceSolveOptions {
    pub globally_optimal: bool,
    pub continue_on_unknown: bool,
}

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

    fn translate_selection(&self, selection: &SliceSelection) -> (Bool<'ctx>, Vec<Bool<'ctx>>) {
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

    /*
    /// Run [`check_original_proof`] on the original query, without slicing anything.
    pub fn check_original_proof(&mut self) -> ProveResult<'ctx> {
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

    /// Minimize the number of statements while the program still verifies using
    /// an exists-forall encoding.
    #[instrument(level = "info", skip_all)]
    pub fn exists_verified_slice(
        &mut self,
        options: &SliceSolveOptions,
        limits_ref: &LimitsRef,
    ) -> Result<Option<SliceModel>, VerifyError> {
        assert_eq!(self.prover.level(), 2);
        self.prover.pop();
        self.prover.pop();
        self.prover.push();

        let selection = SliceSelection::VERIFIED_SELECTION;
        let (inactive_formula, active_toggle_values) = self.translate_selection(&selection);

        let (prover, universally_bound) = (&mut self.prover, &self.universally_bound);

        tracing::warn!("The --slice-verify option is unsound if uninterpreted functions are used.");

        let mut exists_forall_solver = prover.to_exists_forall(universally_bound);
        exists_forall_solver.add_assumption(&inactive_formula);
        exists_forall_solver.push();
        exists_forall_solver.push();
        slice_sat_binary_search(
            &mut exists_forall_solver,
            &active_toggle_values,
            options,
            limits_ref,
        )?;
        if exists_forall_solver.check_sat() == SatResult::Sat {
            let model = InstrumentedModel::new(exists_forall_solver.get_model().unwrap());
            let slice_model =
                SliceModel::extract_model(SliceMode::Verify, &self.slice_stmts, selection, &model);
            Ok(Some(slice_model))
        } else {
            Ok(None)
        }
    }

    /// Get a "slice while verified" from the SMT solver's unsat core.
    #[instrument(level = "info", skip_all)]
    pub fn verified_slice_unsat_core(
        &mut self,
        limits_ref: &LimitsRef,
    ) -> Result<Option<SliceModel>, VerifyError> {
        assert_eq!(self.prover.level(), 2);
        self.prover.pop();
        self.prover.pop();
        self.prover.push();

        let selection = SliceSelection::VERIFIED_SELECTION;
        let (inactive_formula, active_toggle_values) = self.translate_selection(&selection);

        if let Some(timeout) = limits_ref.time_left() {
            self.prover.set_timeout(timeout);
        }

        self.prover.add_assumption(&inactive_formula);
        let res = self.prover.check_proof_assuming(&active_toggle_values);

        if let ProveResult::Proof = res {
            let slice_model = SliceModel::extract_enabled(
                SliceMode::Verify,
                &self.slice_stmts,
                selection,
                self.prover.get_unsat_core(),
            );
            Ok(Some(slice_model))
        } else {
            Ok(None)
        }
    }

    /// Get a "slice while verified" from a minimal unsatisfiable subset
    /// algorithm operating on the SMT solver.
    ///
    /// Set `options.globally_optimal` to `true` to enumerate all minimal unsat
    /// subsets to find the globally smallest one.
    #[instrument(level = "info", skip_all)]
    pub fn verified_slice_mus(
        &mut self,
        options: &SliceSolveOptions,
        limits_ref: &LimitsRef,
    ) -> Result<Option<SliceModel>, VerifyError> {
        assert_eq!(self.prover.level(), 2);
        self.prover.pop();
        self.prover.pop();
        self.prover.push();

        let selection = SliceSelection::VERIFIED_SELECTION;
        let (inactive_formula, active_toggle_values) = self.translate_selection(&selection);

        self.prover.add_assumption(&inactive_formula);

        // TODO: re-use the unsat core from the proof instead of starting fresh
        let mut optimum_so_far: Option<SliceModel> = None;
        let mut subset_explorer =
            SubsetExploration::new(self.prover.solver().get_context(), active_toggle_values);
        while let Some(extremal_set) =
            slice_next_extremal_set(&mut subset_explorer, &mut self.prover, options, limits_ref)?
        {
            if let ExtremalSet::MinimalUnsat(minimal_unsat) = extremal_set {
                debug!(enabled = minimal_unsat.len(), "found minimal unsat subset");

                let minimal_unsat: Vec<_> = minimal_unsat.into_iter().collect();
                let slice_model = SliceModel::extract_enabled(
                    SliceMode::Verify,
                    &self.slice_stmts,
                    selection.clone(),
                    minimal_unsat,
                );
                if !options.globally_optimal {
                    return Ok(Some(slice_model));
                }
                if let Some(ref mut inner_optimum_so_far) = &mut optimum_so_far {
                    if inner_optimum_so_far.count_sliced_stmts() > slice_model.count_sliced_stmts()
                    {
                        *inner_optimum_so_far = slice_model;
                    }
                } else {
                    optimum_so_far = Some(slice_model);
                }
            } else {
                // continue
            }
        }
        Ok(optimum_so_far)
    }

    /// Minimize the number of statements while the program is rejected with a counterexample.
    ///
    /// Usually, we set `options.continue_on_unknown` to `false` for this as we
    /// consider "unknown" a failure.
    #[instrument(level = "info", skip_all)]
    pub fn slice_while_failing(
        &mut self,
        options: &SliceSolveOptions,
        limits_ref: &LimitsRef,
    ) -> Result<(ProveResult<'ctx>, Option<SliceModel>), VerifyError> {
        assert_eq!(self.prover.level(), 2);
        self.prover.pop();
        self.prover.pop();
        self.prover.push();

        let selection = SliceSelection::FAILURE_SELECTION;
        let (inactive_formula, active_toggle_values) = self.translate_selection(&selection);

        self.prover.add_assumption(&inactive_formula);
        self.prover.push();

        slice_sat_binary_search(&mut self.prover, &active_toggle_values, options, limits_ref)?;
        let res = self.prover.check_proof();
        let slice_model = if let ProveResult::Counterexample(model) = &res {
            Some(SliceModel::extract_model(
                SliceMode::Error,
                &self.slice_stmts,
                selection,
                model,
            ))
        } else {
            None
        };
        Ok((res, slice_model))
    }
}

/// Slice on the provided prover with the given slice variables while the solver
/// returns SAT. We do a kind of binary search on the number of enabled slice
/// variables using Z3's `pb_le` constraint (at most n true).
fn slice_sat_binary_search<'ctx>(
    prover: &mut Prover<'ctx>,
    active_slice_vars: &[Bool<'ctx>],
    options: &SliceSolveOptions,
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

    // TODO: we could have min_least_bound set to 1 if we could conclude for
    // sure that the program must verify (assuming the axioms are correct) when
    // all sliceable statements are removed. however, this is sometimes not the
    // case:
    // - tick statements are not sliced by default (because slicing them by
    //   default has adverse performance effects on some benchmarks :( )
    // - if otherwise the program is partially sliced (this is currently not
    //   supported anyways, but we'd like to have this in the future)
    //
    // the fix would be to track explicitly whether we can make that assumption
    // that min_least_bound is 1.
    let min_least_bound = 0;
    let mut minimize = PartialMinimizer::new(min_least_bound..=slice_vars.len());

    let mut first_acceptance = None;

    let mut cur_solver_n: Option<usize> = None;
    while let Some(n) = minimize.next_trial() {
        cur_solver_n = Some(n);
        limits_ref.check_limits()?;

        let entered = info_span!(
            "at most n statements",
            n = n,
            max_reject = minimize.max_reject(),
            min_accept = minimize.min_accept(),
            res = tracing::field::Empty,
        )
        .entered();

        set_at_most_true(prover, n);
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
                    .filter(|var| {
                        // evaluate a value in the model without model completion
                        let symbolic: Bool<'ctx> = model.eval(var.0, false).unwrap();
                        // if it is a concrete value in the model, use it.
                        // otherwise it is irrelevant and we set it to false.
                        symbolic.as_bool().unwrap_or(false)
                    })
                    .count();
                assert!(num_actually_true <= n);
                if num_actually_true != n {
                    debug!(
                        actually_true = num_actually_true,
                        distance = n - num_actually_true,
                        "obtained a better upper bound from model"
                    );
                }
                minimize.add_result(num_actually_true, PartialMinimizeResult::AcceptUpwards);
                if first_acceptance.is_none() {
                    first_acceptance = Some(num_actually_true);
                }

                // stop at the first nontrivial result if requested
                if !options.globally_optimal && n < slice_vars.len() {
                    break;
                }
            }
            SatResult::Unknown => {
                if prover.get_reason_unknown() == Some(ReasonUnknown::Interrupted) {
                    return Err(VerifyError::Interrupted);
                }
                let res = if options.continue_on_unknown {
                    PartialMinimizeResult::Unknown
                } else {
                    PartialMinimizeResult::RejectDownwards
                };
                minimize.add_result(n, res)
            }
            SatResult::Unsat => minimize.add_result(n, PartialMinimizeResult::RejectDownwards),
        }
    }

    if let Some(min_accept) = minimize.min_accept() {
        info!(
            enabled = min_accept,
            removed_statements = slice_vars.len() - min_accept,
            from_first_model = first_acceptance.map(|x| x - min_accept),
            "sat slicing successful"
        );
    } else {
        info!("no sat slice");
    }

    let enabled = minimize
        .min_accept()
        .or(minimize.max_reject())
        .unwrap_or(minimize.total_max());

    // after we're done searching, reset the solver to the last known
    // working number of statements.
    if let Some(cur_solver_n) = cur_solver_n {
        // only reset if the solver isn't already in the correct state
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

enum ExtremalSet<'ctx> {
    MinimalUnsat(HashSet<Bool<'ctx>>),
    #[allow(unused)]
    MaximalSat(HashSet<Bool<'ctx>>),
}

/// Find the next extremal set of assumptions in this prover.
#[instrument(level = "trace", skip_all)]
pub fn slice_next_extremal_set<'ctx>(
    exploration: &mut SubsetExploration<'ctx>,
    prover: &mut Prover<'ctx>,
    options: &SliceSolveOptions,
    limits_ref: &LimitsRef,
) -> Result<Option<ExtremalSet<'ctx>>, LimitError> {
    let all_variables = exploration.variables().clone();

    while let Some(seed) = exploration.next_set() {
        limits_ref.check_limits()?;

        match check_proof_seed(prover, limits_ref, &seed) {
            ProveResult::Proof => {
                let seed = unsat_core_to_seed(prover, &all_variables);

                // now start the shrinking, then block up
                let res = exploration.shrink_block_up(seed, |seed| {
                    match check_proof_seed(prover, limits_ref, seed) {
                        ProveResult::Proof => Some(unsat_core_to_seed(prover, &all_variables)),
                        ProveResult::Counterexample(_) | ProveResult::Unknown(_) => None,
                    }
                });
                return Ok(Some(ExtremalSet::MinimalUnsat(res)));
            }
            ProveResult::Counterexample(_) => {
                // grow the counterexample and then block down
                let res = exploration.grow_block_down(seed, |seed| {
                    match check_proof_seed(prover, limits_ref, seed) {
                        ProveResult::Counterexample(_) => true,
                        ProveResult::Proof | ProveResult::Unknown(_) => false,
                    }
                });
                return Ok(Some(ExtremalSet::MaximalSat(res)));
            }
            ProveResult::Unknown(_) => {
                if options.continue_on_unknown {
                    // for seeds that result in unknown, just block them to
                    // ensure progress.
                    exploration.block_this(&seed);
                } else {
                    return Ok(None);
                }
            }
        }
    }
    Ok(None)
}

#[instrument(level = "trace", skip_all, ret)]
fn check_proof_seed<'ctx>(
    prover: &mut Prover<'ctx>,
    limits_ref: &LimitsRef,
    seed: &HashSet<Bool<'ctx>>,
) -> ProveResult<'ctx> {
    let mut timeout = Duration::from_millis(100);
    if let Some(time_left) = limits_ref.time_left() {
        timeout = timeout.min(time_left);
    }
    prover.set_timeout(timeout);

    let seed: Vec<_> = seed.iter().cloned().collect();
    prover.check_proof_assuming(&seed)
}

fn unsat_core_to_seed<'ctx>(
    prover: &mut Prover<'ctx>,
    all_variables: &HashSet<Bool<'ctx>>,
) -> HashSet<Bool<'ctx>> {
    let unsat_core = &prover.get_unsat_core().into_iter().collect();
    all_variables.intersection(unsat_core).cloned().collect()
}
