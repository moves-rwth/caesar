use std::time::Duration;

use indexmap::IndexSet;
use itertools::Itertools;
use tracing::{debug, info, info_span, instrument, warn};
use z3::{
    ast::{Bool, Dynamic},
    SatResult, Statistics,
};
use z3rro::{
    model::{InstrumentedModel, ModelConsistency},
    prover::{ProveResult, Prover},
    util::ReasonUnknown,
};

use crate::{
    ast::{ExprBuilder, Span},
    driver::error::CaesarError,
    resource_limits::{LimitError, LimitsRef},
    slicing::{
        model::{SliceMode, SliceModel},
        util::{PartialMinimizeResult, SubsetExploration},
    },
    smt::translate_exprs::TranslateExprs,
};

use super::{
    selection::SliceSelection,
    transform::{SliceStmt, SliceStmts},
    util::PartialMinimizer,
};

/// Whether and if so, with respect to which metric to minimize slices.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SliceMinimality {
    /// Any slice is acceptable, do not minimize.
    Any,
    /// Find a minimal slice with respect to subset inclusion.
    Subset,
    /// Find the smallest slice with respect to number of statements included.
    Size,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnknownHandling {
    /// Skip unknown results (but continue the search).
    Continue,
    /// Stop the search on unknown results and return the best slice found
    /// before that, if any.
    Stop,
    /// Accept a slice if the solver returned unknown. The resulting
    /// [`SliceModel`] will have [`ModelConsistency::Unknown`], i.e. there are
    /// *no guarantees* whether the result is actually a valid slice!
    Accept,
}

/// Configuration for the slice solver.
#[derive(Debug)]
pub struct SliceSolveOptions {
    pub minimality: SliceMinimality,
    pub unknown: UnknownHandling,
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
        mut prover: Prover<'ctx>,
    ) -> Self {
        let slice_stmts = SmtSliceStmts::new(slice_stmts, translate);
        let universally_bound = slice_stmts.universally_bound(translate);

        prover.push();
        prover.push();

        SliceSolver {
            prover,
            slice_stmts,
            universally_bound,
        }
    }

    fn translate_selection(&self, selection: &SliceSelection) -> (Vec<Bool<'ctx>>, Bool<'ctx>) {
        let (active, inactive) = self.slice_stmts.split_by_selection(selection);

        // inactive statements must be enabled in the slice
        let inactive_formula = Bool::and(self.prover.get_context(), &inactive);

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
    pub fn slice_verifying_exists_forall(
        &mut self,
        options: &SliceSolveOptions,
        limits_ref: &LimitsRef,
    ) -> Result<Option<SliceModel>, CaesarError> {
        assert_eq!(self.prover.level(), 2);
        self.prover.pop();
        self.prover.pop();
        self.prover.push();

        let selection = SliceSelection::VERIFIED_SELECTION;
        let (active_toggle_values, inactive_formula) = self.translate_selection(&selection);

        let (prover, universally_bound) = (&mut self.prover, &self.universally_bound);

        prover.add_assumption(&self.slice_stmts.constraints);
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
            let model = exists_forall_solver.get_model().unwrap();
            let slice_model =
                SliceModel::from_model(SliceMode::Verify, &self.slice_stmts, selection, &model);
            Ok(Some(slice_model))
        } else {
            Ok(None)
        }
    }

    /// Get a "slice while verified" from the SMT solver's unsat core.
    #[instrument(level = "info", skip_all)]
    pub fn slice_verifying_unsat_core(
        &mut self,
        limits_ref: &LimitsRef,
    ) -> Result<Option<SliceModel>, CaesarError> {
        assert_eq!(self.prover.level(), 2);
        self.prover.pop();
        self.prover.pop();
        self.prover.push();

        let selection = SliceSelection::VERIFIED_SELECTION;
        let (active_toggle_values, inactive_formula) = self.translate_selection(&selection);

        if let Some(timeout) = limits_ref.time_left() {
            self.prover.set_timeout(timeout);
        }

        self.prover.add_assumption(&self.slice_stmts.constraints);
        self.prover.add_assumption(&inactive_formula);
        let res = self.prover.check_proof_assuming(&active_toggle_values);

        let mut slice_searcher = SliceModelSearch::new(active_toggle_values.clone());
        if let ProveResult::Proof = res {
            slice_searcher.found_active(self.prover.get_unsat_core());
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

    /// Get a "slice while verified" from an unsatisfiable subset enumeration
    /// algorithm.
    #[instrument(level = "info", skip_all)]
    pub fn slice_verifying_enumerate(
        &mut self,
        options: &SliceSolveOptions,
        limits_ref: &LimitsRef,
    ) -> Result<Option<SliceModel>, CaesarError> {
        assert_eq!(self.prover.level(), 2);
        self.prover.pop();
        self.prover.pop();
        self.prover.push();

        let selection = SliceSelection::VERIFIED_SELECTION;
        let (active_toggle_values, inactive_formula) = self.translate_selection(&selection);

        self.prover.add_assumption(&self.slice_stmts.constraints);
        self.prover.add_assumption(&inactive_formula);

        // TODO: re-use the unsat core from the proof instead of starting fresh
        let context = self.prover.get_context();
        let mut subset_explorer = {
            let active_toggle_values = active_toggle_values.iter().cloned().collect();
            let extensive: IndexSet<Bool<'_>> = self
                .slice_stmts
                .stmts
                .iter()
                .flat_map(|(slice_stmt, var)| {
                    if slice_stmt.selection.concordant {
                        Some(var.clone())
                    } else {
                        None
                    }
                })
                .collect();
            let reductive: IndexSet<Bool<'_>> = self
                .slice_stmts
                .stmts
                .iter()
                .flat_map(|(slice_stmt, var)| {
                    if slice_stmt.selection.discordant {
                        Some(var.clone())
                    } else {
                        None
                    }
                })
                .collect();
            SubsetExploration::new(context, active_toggle_values, extensive, reductive)
        };

        let res = slice_unsat_search(&mut subset_explorer, &mut self.prover, options, limits_ref)?;

        Ok(res.map(|minimal_unsat| {
            SliceModel::from_enabled(
                SliceMode::Verify,
                &self.slice_stmts,
                selection.clone(),
                minimal_unsat,
            )
        }))
    }

    /// Minimize the number of statements while the program is rejected with a counterexample.
    #[instrument(level = "info", skip_all)]
    pub fn slice_failing_binary_search(
        &mut self,
        options: &SliceSolveOptions,
        limits_ref: &LimitsRef,
    ) -> Result<(ProveResult, Option<(InstrumentedModel<'ctx>, SliceModel)>), CaesarError> {
        if !self.prover.has_provables() {
            return Ok((ProveResult::Proof, None));
        }

        assert_eq!(self.prover.level(), 2);
        self.prover.pop();
        self.prover.pop();
        self.prover.push();

        let selection = SliceSelection::FAILURE_SELECTION;
        let (active_toggle_values, inactive_formula) = self.translate_selection(&selection);

        self.prover.add_assumption(&self.slice_stmts.constraints);
        self.prover.add_assumption(&inactive_formula);
        self.prover.push();

        println!("smtlib: {:}", self.prover.get_smtlib().into_string());

        slice_sat_binary_search(&mut self.prover, &active_toggle_values, options, limits_ref)?;
        let res = self.prover.check_proof();
        let model = if let Some(model) = self.prover.get_model() {
            assert!(matches!(
                res,
                ProveResult::Counterexample | ProveResult::Unknown(_)
            ));
            let slice_model =
                SliceModel::from_model(SliceMode::Error, &self.slice_stmts, selection, &model);
            Some((model, slice_model))
        } else {
            None
        };
        Ok((res, model))
    }

    /// Retrieve the underlying prover's statistics.
    pub fn get_statistics(&self) -> Statistics<'ctx> {
        self.prover.get_statistics()
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

    fn found_model(&mut self, model: InstrumentedModel<'ctx>) -> usize {
        let model = model.into_model(); // we don't need the accessed tracking
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
    prover: &mut Prover<'ctx>,
    active_slice_vars: &[Bool<'ctx>],
    options: &SliceSolveOptions,
    limits_ref: &LimitsRef,
) -> Result<(), CaesarError> {
    assert_eq!(prover.level(), 2);

    let slice_vars: Vec<(&Bool<'ctx>, i32)> =
        active_slice_vars.iter().map(|value| (value, 1)).collect();

    let set_at_most_true = |prover: &mut Prover<'ctx>, at_most_n: usize| {
        prover.pop();
        prover.push();

        let ctx = prover.get_context();
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

    
    let mut cur_solver_n = None;
    let mut slice_searcher = SliceModelSearch::new(active_slice_vars.to_vec());
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

        if prover.get_reason_unknown() == Some(ReasonUnknown::Interrupted) {
            return Err(CaesarError::Interrupted);
        }


        let mut done = false;
        if let Some(model) = prover.get_model() {
            if model.consistency() == ModelConsistency::Consistent
                || options.unknown == UnknownHandling::Accept
            {
                let num_actually_true = slice_searcher.found_model(model);
                assert!(num_actually_true <= n);
                if num_actually_true != n {
                    debug!(
                        actually_true = num_actually_true,
                        distance = n - num_actually_true,
                        "obtained a better upper bound from model"
                    );
                }

                cur_solver_n = Some(num_actually_true);
                minimize.add_result(num_actually_true, PartialMinimizeResult::AcceptUpwards);

                done = true;

                // TODO: for subset inclusion we also want to add
                // constraints on the next model so that we only find a subset
                match options.minimality {
                    SliceMinimality::Any => break,
                    SliceMinimality::Subset | SliceMinimality::Size => {}
                }
            }
        }

        let choice = match res {
            SatResult::Unsat => PartialMinimizeResult::RejectDownwards,
            SatResult::Unknown if options.unknown == UnknownHandling::Stop => {
                PartialMinimizeResult::RejectDownwards
            }
            _ if !done => PartialMinimizeResult::Unknown,
            _ => continue,
        };
        minimize.add_result(n, choice);
    }

    // emit tracing info
    slice_searcher.finish();

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
                assert!(res == SatResult::Sat || res == SatResult::Unknown);
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

/// Find a (minimal) slice that verifies.
#[instrument(level = "trace", skip_all)]
pub fn slice_unsat_search<'ctx>(
    exploration: &mut SubsetExploration<'ctx>,
    prover: &mut Prover<'ctx>,
    options: &SliceSolveOptions,
    limits_ref: &LimitsRef,
) -> Result<Option<Vec<Bool<'ctx>>>, LimitError> {
    let mut slice_searcher =
        SliceModelSearch::new(exploration.variables().iter().cloned().collect_vec());
    let all_variables = exploration.variables().clone();

    while let Some(seed) = exploration.next_set() {
        limits_ref.check_limits()?;

        match check_proof_seed(&all_variables, prover, limits_ref, &seed) {
            ProveResult::Proof => {
                // now start the shrinking, then block up
                let res = exploration.shrink_block_unsat(seed, |seed| {
                    match check_proof_seed(&all_variables, prover, limits_ref, seed) {
                        ProveResult::Proof => Some(unsat_core_to_seed(prover, &all_variables)),
                        ProveResult::Counterexample | ProveResult::Unknown(_) => None,
                    }
                });

                let res_vec: Vec<_> = res.iter().cloned().collect();
                slice_searcher.found_active(res_vec);

                match options.minimality {
                    SliceMinimality::Any => break,
                    SliceMinimality::Subset => exploration.block_non_subset(&res),
                    SliceMinimality::Size => exploration.block_at_least(res.len()),
                }
            }
            ProveResult::Counterexample => {
                // grow the counterexample and then block down
                exploration.grow_block_sat(seed, |seed| {
                    match check_proof_seed(&all_variables, prover, limits_ref, seed) {
                        ProveResult::Counterexample => true,
                        ProveResult::Proof | ProveResult::Unknown(_) => false,
                    }
                });
            }
            ProveResult::Unknown(_) => {
                exploration.block_this(&seed);

                match options.unknown {
                    UnknownHandling::Continue => {}
                    UnknownHandling::Stop => {
                        tracing::trace!("stopping search because of unknown result");
                        break;
                    }
                    UnknownHandling::Accept => {
                        panic!("UnknownHandling::Accept is not sensible to find verifying slices")
                    }
                }
            }
        }
    }

    Ok(slice_searcher.finish())
}

#[instrument(level = "trace", skip_all, ret)]
fn check_proof_seed<'ctx>(
    all_variables: &IndexSet<Bool<'ctx>>,
    prover: &mut Prover<'ctx>,
    limits_ref: &LimitsRef,
    seed: &IndexSet<Bool<'ctx>>,
) -> ProveResult {
    let mut timeout = Duration::from_millis(100);
    if let Some(time_left) = limits_ref.time_left() {
        timeout = timeout.min(time_left);
    }

    prover.set_timeout(timeout);

    let (all_on, all_off): (IndexSet<_>, IndexSet<_>) = all_variables
        .iter()
        .cloned()
        .partition(|var| seed.contains(var));
    let all_on_assumptions = all_on.iter().cloned();
    let all_off_assumptions = all_off.iter().map(Bool::not);
    let all_assumptions = all_on_assumptions.chain(all_off_assumptions).collect_vec();

    // prover.push();
    prover.check_proof_assuming(&all_assumptions)
    // prover.pop();
}

fn unsat_core_to_seed<'ctx>(
    prover: &mut Prover<'ctx>,
    all_variables: &IndexSet<Bool<'ctx>>,
) -> IndexSet<Bool<'ctx>> {
    let unsat_core: IndexSet<Bool<'ctx>> = prover.get_unsat_core().into_iter().collect();
    all_variables.intersection(&unsat_core).cloned().collect()
}
