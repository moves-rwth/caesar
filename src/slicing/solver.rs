use std::{collections::HashSet, time::Duration};

use tracing::{debug, info, info_span, instrument, warn};
use z3::{
    ast::{Bool, Dynamic},
    Model, SatResult,
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

/// Configuration for the slice solver.
#[derive(Debug)]
pub struct SliceSolveOptions {
    /// Should we search for the globally optimal slice?
    pub globally_optimal: bool,
    /// Should we continue on "unknown" results from the solver or stop with an
    /// error?
    pub continue_on_unknown: bool,
}

/// Extended version of [`SliceStmts`] with SMT variables attached.
pub struct SmtSliceStmts<'ctx> {
    pub(super) stmts: Vec<(SliceStmt, Bool<'ctx>)>,
    constraints: Bool<'ctx>,
}

impl<'ctx> SmtSliceStmts<'ctx> {
    fn new<'smt>(slice_stmts: SliceStmts, translate: &mut TranslateExprs<'smt, 'ctx>) -> Self {
        let builder = ExprBuilder::new(Span::dummy_span());

        // retrieve the Bool SMT variable from the translator for each
        // statement. they were already created when we translated the VC.
        let stmts: Vec<(SliceStmt, Bool<'_>)> = slice_stmts
            .stmts
            .into_iter()
            .map(|stmt| {
                let z3_var = translate.t_bool(&builder.var(stmt.ident, translate.ctx.tcx()));
                (stmt, z3_var)
            })
            .collect();

        // translate the constraints to SMT
        let constraints = Bool::and(
            translate.ctx.ctx(),
            &slice_stmts
                .constraints
                .iter()
                .map(|constraint| translate.t_bool(constraint))
                .collect::<Vec<_>>(),
        );

        SmtSliceStmts { stmts, constraints }
    }

    // collect all top-level variables, excluding those for slicing. they
    // will be universally quantified for the exists-forall translation.
    fn universally_bound<'smt>(
        &self,
        translate: &TranslateExprs<'smt, 'ctx>,
    ) -> Vec<Dynamic<'ctx>> {
        translate
            .local_scope()
            .get_bounds()
            .filter(|bound| {
                if let Some(bound) = bound.as_bool() {
                    self.stmts.iter().all(|(_, b)| b != &bound)
                } else {
                    true
                }
            })
            .cloned()
            .collect()
    }

    fn split_by_selection(&self, selection: &SliceSelection) -> (Vec<Bool<'ctx>>, Vec<Bool<'ctx>>) {
        let mut active = vec![];
        let mut inactive = vec![];
        for (stmt, var) in &self.stmts {
            if selection.enables(&stmt.selection) {
                active.push(var.clone());
            } else {
                inactive.push(var.clone());
            }
        }
        (active, inactive)
    }
}

/// A structure that wraps the other SMT structures to do SMT-based program
/// slicing by doing a binary search of upper bounds on the number of statements
/// we're keeping in the program.
pub struct SliceSolver<'ctx> {
    prover: Prover<'ctx>,
    slice_stmts: SmtSliceStmts<'ctx>,
    universally_bound: Vec<Dynamic<'ctx>>,
}

impl<'ctx> SliceSolver<'ctx> {
    pub fn new<'smt>(
        slice_stmts: SliceStmts,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        prover: Prover<'ctx>,
    ) -> Self {
        let slice_stmts = SmtSliceStmts::new(slice_stmts, translate);
        let universally_bound = slice_stmts.universally_bound(translate);

        SliceSolver {
            prover,
            slice_stmts,
            universally_bound,
        }
    }

    fn translate_selection(&self, selection: &SliceSelection) -> (Vec<Bool<'ctx>>, Bool<'ctx>) {
        let (active, inactive) = self.slice_stmts.split_by_selection(selection);

        // inactive statements must be enabled in the slice
        let inactive_formula = Bool::and(self.prover.solver().get_context(), &inactive);

        debug!(
            active = active.len(),
            inactive = inactive.len(),
            "translated slice selection"
        );

        (active, inactive_formula)
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
        &self,
        options: &SliceSolveOptions,
        limits_ref: &LimitsRef,
    ) -> Result<Option<SliceModel>, VerifyError> {
        assert_eq!(self.prover.level(), 0);
        let mut prover = self.prover.clone();

        let selection = SliceSelection::VERIFIED_SELECTION;
        let (active_toggle_values, inactive_formula) = self.translate_selection(&selection);

        let (prover, universally_bound) = (&mut prover, &self.universally_bound);

        tracing::warn!("The --slice-verify option is unsound if uninterpreted functions are used."); // TODO

        prover.add_assumption(&self.slice_stmts.constraints);
        let mut exists_forall_solver = prover.to_exists_forall(universally_bound);
        exists_forall_solver.add_assumption(&inactive_formula);
        exists_forall_solver.push();
        exists_forall_solver.push();
        exists_forall_solver = slice_sat_binary_search(
            exists_forall_solver,
            &active_toggle_values,
            options,
            limits_ref,
        )?;
        if exists_forall_solver.check_sat() == SatResult::Sat {
            let model = InstrumentedModel::new(exists_forall_solver.get_model().unwrap());
            let slice_model =
                SliceModel::from_model(SliceMode::Verify, &self.slice_stmts, selection, &model);
            Ok(Some(slice_model))
        } else {
            Ok(None)
        }
    }

    /// Get a "slice while verified" from the SMT solver's unsat core.
    #[instrument(level = "info", skip_all)]
    pub fn verified_slice_unsat_core(
        &self,
        limits_ref: &LimitsRef,
    ) -> Result<Option<SliceModel>, VerifyError> {
        assert_eq!(self.prover.level(), 0);
        let mut prover = self.prover.clone();

        let selection = SliceSelection::VERIFIED_SELECTION;
        let (active_toggle_values, inactive_formula) = self.translate_selection(&selection);

        if let Some(timeout) = limits_ref.time_left() {
            prover.set_timeout(timeout);
        }

        prover.add_assumption(&self.slice_stmts.constraints);
        prover.add_assumption(&inactive_formula);
        let res = prover.check_proof_assuming(&active_toggle_values);

        let mut slice_searcher = SliceModelSearch::new(active_toggle_values.clone());
        if let ProveResult::Proof = res {
            slice_searcher.found_active(prover.get_unsat_core());
        }

        Ok(slice_searcher.finish().map(|minimal_unsat| {
            SliceModel::from_enabled(
                SliceMode::Verify,
                &self.slice_stmts,
                selection.clone(),
                minimal_unsat,
            )
        }))
    }

    /// Get a "slice while verified" from a minimal unsatisfiable subset
    /// algorithm operating on the SMT solver.
    ///
    /// Set `options.globally_optimal` to `true` to enumerate all minimal unsat
    /// subsets to find the globally smallest one.
    #[instrument(level = "info", skip_all)]
    pub fn verified_slice_mus(
        &self,
        options: &SliceSolveOptions,
        limits_ref: &LimitsRef,
    ) -> Result<Option<SliceModel>, VerifyError> {
        assert_eq!(self.prover.level(), 0);
        let mut prover = self.prover.clone();

        let selection = SliceSelection::VERIFIED_SELECTION;
        let (active_toggle_values, inactive_formula) = self.translate_selection(&selection);

        prover.add_assumption(&self.slice_stmts.constraints);
        prover.add_assumption(&inactive_formula);

        // TODO: re-use the unsat core from the proof instead of starting fresh
        let mut slice_searcher = SliceModelSearch::new(active_toggle_values.clone());
        let mut subset_explorer =
            SubsetExploration::new(self.prover.solver().get_context(), active_toggle_values);
        while let Some(extremal_set) =
            slice_next_extremal_set(&mut subset_explorer, &mut prover, options, limits_ref)?
        {
            if let ExtremalSet::MinimalUnsat(minimal_unsat) = extremal_set {
                let minimal_unsat: Vec<_> = minimal_unsat.into_iter().collect();
                slice_searcher.found_active(minimal_unsat);

                // stop at the first nontrivial result if requested
                if !options.globally_optimal {
                    break;
                }
            } else {
                // continue
            }
        }

        Ok(slice_searcher.finish().map(|minimal_unsat| {
            SliceModel::from_enabled(
                SliceMode::Verify,
                &self.slice_stmts,
                selection.clone(),
                minimal_unsat,
            )
        }))
    }

    /// Minimize the number of statements while the program is rejected with a counterexample.
    ///
    /// Usually, we set `options.continue_on_unknown` to `false` for this as we
    /// consider "unknown" a failure.
    #[instrument(level = "info", skip_all)]
    pub fn slice_while_failing(
        &self,
        options: &SliceSolveOptions,
        limits_ref: &LimitsRef,
    ) -> Result<(ProveResult<'ctx>, Option<SliceModel>), VerifyError> {
        assert_eq!(self.prover.level(), 0);
        let mut prover = self.prover.clone();

        let selection = SliceSelection::FAILURE_SELECTION;
        let (active_toggle_values, inactive_formula) = self.translate_selection(&selection);

        prover.add_assumption(&self.slice_stmts.constraints);
        prover.add_assumption(&inactive_formula);
        let mut prover = prover.clone();

        prover = slice_sat_binary_search(prover, &active_toggle_values, options, limits_ref)?;
        let res = prover.check_proof();
        let slice_model = if let ProveResult::Counterexample(model) = &res {
            let slice_model =
                SliceModel::from_model(SliceMode::Error, &self.slice_stmts, selection, model);
            Some(slice_model)
        } else {
            None
        };
        Ok((res, slice_model))
    }
}

/// A structure to keep track of some information during the slice search.
struct SliceModelSearch<'ctx> {
    active_slice_vars: Vec<Bool<'ctx>>,
    first_accepted: Option<usize>,
    num_slices_accepted: usize,
    optimum_so_far: Option<Vec<Bool<'ctx>>>,
}

impl<'ctx> SliceModelSearch<'ctx> {
    fn new(active_slice_vars: Vec<Bool<'ctx>>) -> Self {
        SliceModelSearch {
            active_slice_vars,
            first_accepted: None,
            num_slices_accepted: 0,
            optimum_so_far: None,
        }
    }

    fn found_model(&mut self, model: Model<'ctx>) -> usize {
        let slice_vars: Vec<_> = self
            .active_slice_vars
            .iter()
            .filter(move |var| {
                // evaluate a value in the model without model completion
                let symbolic: Bool<'ctx> = model.eval(*var, false).unwrap();
                // if it is a concrete value in the model, use it.
                // otherwise it is irrelevant and we set it to false.
                symbolic.as_bool().unwrap_or(false)
            })
            .cloned()
            .collect();
        self.found_active(slice_vars)
    }

    fn found_active(&mut self, slice_vars: Vec<Bool<'ctx>>) -> usize {
        let slice_vars_len = slice_vars.len();

        debug!(
            slice_size = slice_vars_len,
            removed_statements = self.active_slice_vars.len() - slice_vars_len,
            "found a slice"
        );

        self.num_slices_accepted += 1;

        if self.first_accepted.is_none() {
            self.first_accepted = Some(slice_vars_len);
        }

        if let Some(ref mut optimum_so_far) = &mut self.optimum_so_far {
            if optimum_so_far.len() > slice_vars_len {
                *optimum_so_far = slice_vars;
            }
        } else {
            self.optimum_so_far = Some(slice_vars);
        }

        slice_vars_len
    }

    fn finish(self) -> Option<Vec<Bool<'ctx>>> {
        if let Some(slice_model) = self.optimum_so_far {
            info!(
                slice_size = slice_model.len(),
                removed_statements = self.active_slice_vars.len() - slice_model.len(),
                from_first_model = self.first_accepted.map(|x| x - slice_model.len()),
                found_slices = self.num_slices_accepted,
                "slicing successful"
            );
            Some(slice_model)
        } else {
            info!("no slice accepted");
            None
        }
    }
}

/// Slice on the provided prover with the given slice variables while the solver
/// returns SAT. We do a kind of binary search on the number of enabled slice
/// variables using Z3's `pb_le` constraint (at most n true).
fn slice_sat_binary_search<'ctx>(
    base_prover: Prover<'ctx>,
    active_slice_vars: &[Bool<'ctx>],
    options: &SliceSolveOptions,
    limits_ref: &LimitsRef,
) -> Result<Prover<'ctx>, VerifyError> {
    assert_eq!(base_prover.level(), 0);

    let slice_vars: Vec<(&Bool<'ctx>, i32)> =
        active_slice_vars.iter().map(|value| (value, 1)).collect();

    let set_at_most_true = |prover: &mut Prover<'ctx>, at_most_n: usize| {
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

    struct IterationInfo<'ctx> {
        n: usize,
        prover: Prover<'ctx>,
    }
    let mut cur_info = None;
    let mut slice_searcher = SliceModelSearch::new(active_slice_vars.to_vec());
    while let Some(n) = minimize.next_trial() {
        cur_info = Some(IterationInfo {
            n,
            prover: base_prover.clone(),
        });
        let current_prover = &mut cur_info.as_mut().unwrap().prover;
        limits_ref.check_limits()?;

        let entered = info_span!(
            "at most n statements",
            n = n,
            max_reject = minimize.max_reject(),
            min_accept = minimize.min_accept(),
            res = tracing::field::Empty,
        )
        .entered();

        set_at_most_true(current_prover, n);
        if let Some(timeout) = limits_ref.time_left() {
            current_prover.set_timeout(timeout);
        }
        let res = current_prover.check_sat();

        entered.record("res", tracing::field::debug(res));

        match res {
            SatResult::Sat => {
                let model = current_prover.get_model().unwrap();
                let num_actually_true = slice_searcher.found_model(model);

                assert!(num_actually_true <= n);
                if num_actually_true != n {
                    debug!(
                        actually_true = num_actually_true,
                        distance = n - num_actually_true,
                        "obtained a better upper bound from model"
                    );
                }

                minimize.add_result(num_actually_true, PartialMinimizeResult::AcceptUpwards);

                // stop at the first nontrivial result if requested
                if !options.globally_optimal && n < slice_vars.len() {
                    break;
                }
            }
            SatResult::Unknown => {
                if current_prover.get_reason_unknown() == Some(ReasonUnknown::Interrupted) {
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

    // emit tracing info
    slice_searcher.finish();

    let enabled = minimize
        .min_accept()
        .or(minimize.max_reject())
        .unwrap_or(minimize.total_max());

    // after we're done searching, reset the solver to the last known
    // working number of statements.
    if let Some(IterationInfo {
        n,
        prover: last_prover,
    }) = cur_info
    {
        if n == enabled {
            Ok(last_prover)
        } else {
            let mut prover = base_prover.clone();
            // only reset if the solver isn't already in the correct state
            set_at_most_true(&mut prover, enabled);
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
            Ok(prover)
        }
    } else {
        Ok(base_prover)
    }
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
