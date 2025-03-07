use std::{
    collections::HashSet,
    iter::FromIterator,
    ops::{RangeFrom, RangeInclusive, RangeToInclusive},
};

use itertools::Itertools;
use tracing::{instrument, trace};
use z3::{ast::Bool, Context, SatResult, Solver};

/// A result of a test during the partial minimization. Either we accept all
/// values from this value upwards, we reject all values from this value
/// downwards, or we do not know anything about this value ([`Self::Unknown`]).
pub enum PartialMinimizeResult {
    AcceptUpwards,
    RejectDownwards,
    Unknown,
}

/// Helper to minimize an integer based on conditions given by an acceptance
/// function, but where sometimes the result might be "unknown".
///
/// The PartialMinimizer tracks a range in which to search, and the maximum
/// value that was rejected and the minimum value that was accepted so far. It
/// also maintains a list of "unknown" results that we got already.
///
/// The algorithm is basically a binary search with some modifications:
///  * In the beginning, we try the maximum value (to quickly reject all values
///    downwards so we can quit early).
///  * If the result is [`PartialMinimizeResult::Unknown`], then put the value
///    into an "unknown" list and try a nearby value next.
pub struct PartialMinimizer {
    initial_range: RangeInclusive<usize>,
    max_reject: Option<usize>,
    min_accept: Option<usize>,
    unknowns: Vec<usize>,
}

impl PartialMinimizer {
    /// Create a new minimizer with an initial range in which to search.
    pub fn new(initial_range: RangeInclusive<usize>) -> Self {
        PartialMinimizer {
            initial_range,
            max_reject: None,
            min_accept: None,
            unknowns: vec![],
        }
    }

    /// Add a new result to this minimizer to inform the choice of the next
    /// trial.
    pub fn add_result(&mut self, n: usize, result: PartialMinimizeResult) {
        assert!(self.initial_range.contains(&n));
        match result {
            PartialMinimizeResult::RejectDownwards => {
                // Adjust the maximum rejected value
                let max_reject = self.max_reject.map(|other| other.max(n)).unwrap_or(n);
                if let Some(min_accept) = self.min_accept {
                    assert!(max_reject < min_accept);
                }
                self.max_reject = Some(max_reject);
            }
            PartialMinimizeResult::AcceptUpwards => {
                // Adjust the minimum accepted value
                let min_accept = self.min_accept.map(|other| other.min(n)).unwrap_or(n);
                if let Some(max_reject) = self.max_reject {
                    assert!(max_reject < min_accept);
                }
                self.min_accept = Some(min_accept);
            }
            PartialMinimizeResult::Unknown => {
                // Add a new unknown value
                debug_assert!(!self.unknowns.contains(&n));
                self.unknowns.push(n);
            }
        }
    }

    /// Return the next value to try. You must call [`Self::add_result()`]
    /// afterwards for this method to return a new value.
    pub fn next_trial(&self) -> Option<usize> {
        let mut range = self.initial_range.clone();

        if let Some(i) = self.max_reject {
            range = range_exclude_to(range, ..=i);
        };
        if let Some(i) = self.min_accept {
            range = range_exclude_from(range, i..);
        };

        // for the first trial, set the upper bound as high as possible
        if range.contains(self.initial_range.end())
            && !self.unknowns.contains(self.initial_range.end())
        {
            return Some(*self.initial_range.end());
        }

        iter_range_from_mid(range).find(|index| !self.unknowns.contains(index))
    }

    /// Return the maximum value from the initial range in which to search.
    pub fn total_max(&self) -> usize {
        *self.initial_range.end()
    }

    /// Return the current maximum rejected value.
    pub fn max_reject(&self) -> Option<usize> {
        self.max_reject
    }

    /// Return the current minimal accepted value.
    pub fn min_accept(&self) -> Option<usize> {
        self.min_accept
    }
}

fn range_exclude_to(
    range: RangeInclusive<usize>,
    value: RangeToInclusive<usize>,
) -> RangeInclusive<usize> {
    let start = (*range.start()).max(value.end + 1);
    start..=*range.end()
}

fn range_exclude_from(
    range: RangeInclusive<usize>,
    value: RangeFrom<usize>,
) -> RangeInclusive<usize> {
    if value.start == 0 {
        // this is an empty range on purpose
        #[allow(clippy::reversed_empty_ranges)]
        return 1..=0;
    }
    let end = (*range.end()).min(value.start - 1);
    *range.start()..=end
}

fn iter_range_from_mid(range: RangeInclusive<usize>) -> Box<dyn Iterator<Item = usize>> {
    let (start, end) = (*range.start(), *range.end());
    if end.saturating_sub(start) <= 1 {
        Box::new(range)
    } else {
        let mid = (start + end) / 2;
        Box::new((mid..=end).chain(start..end))
    }
}

/// Tracks a set of subsets that were not yet explored. This is used for the
/// minimal unsatisfiable subset slicing method.
pub struct SubsetExploration<'ctx> {
    solver: Solver<'ctx>,
    variables: HashSet<Bool<'ctx>>,
    extensive: HashSet<Bool<'ctx>>,
    reductive: HashSet<Bool<'ctx>>,
}

impl<'ctx> SubsetExploration<'ctx> {
    pub fn new(
        ctx: &'ctx Context,
        variables: HashSet<Bool<'ctx>>,
        extensive: HashSet<Bool<'ctx>>,
        reductive: HashSet<Bool<'ctx>>,
    ) -> Self {
        SubsetExploration {
            solver: Solver::new(ctx),
            variables,
            extensive,
            reductive,
        }
    }

    /// Return the set of variables that we're exploring subsets of.
    pub fn variables(&self) -> &HashSet<Bool<'ctx>> {
        &self.variables
    }

    /// Return the next unexplored set. Returns `None` if there is no unexplored
    /// set left.
    pub fn next_set(&mut self) -> Option<HashSet<Bool<'ctx>>> {
        match self.solver.check() {
            SatResult::Unsat => None,
            SatResult::Unknown => panic!("solver returned unknown"),
            SatResult::Sat => {
                let model = self.solver.get_model().unwrap();
                Some(HashSet::from_iter(
                    self.variables
                        .iter()
                        .filter(|variable| match model.eval(*variable, false) {
                            // if variable is not set, default to true
                            Some(value) => value.as_bool().unwrap_or(true),
                            None => true,
                        })
                        .cloned(),
                ))
            }
        }
    }

    /// Block all models which have size at least `size`.
    pub fn block_at_least(&mut self, size: usize) {
        let variables = self.variables.iter().map(|v| (v, 1)).collect_vec();
        self.solver
            .assert(&Bool::pb_ge(self.solver.get_context(), &variables, size as i32).not())
    }

    /// Block all models which are not subsets of the given set.
    pub fn block_non_subset(&mut self, set: &HashSet<Bool<'ctx>>) {
        let ctx = self.solver.get_context();
        let constraint = Bool::and(
            ctx,
            &self.variables.difference(set).map(Bool::not).collect_vec(),
        );
        self.solver.assert(&constraint);
    }

    /// Block a set of models where all variables `all_off` are set to `false`
    /// and all variables `all_on` are set to `true`.
    fn block(&mut self, all_on: &HashSet<Bool<'ctx>>, all_off: &HashSet<Bool<'ctx>>) {
        let ctx = self.solver.get_context();
        let all_on_constraint = Bool::and(ctx, &all_on.iter().collect_vec());
        let all_off_constraint = Bool::and(ctx, &all_off.iter().map(Bool::not).collect_vec());
        let both_constraints = Bool::and(ctx, &[all_on_constraint, all_off_constraint]);
        let constraint = both_constraints.not();
        tracing::trace!(constraint = ?constraint, "Adding blocking constraint");
        self.solver.assert(&constraint);
    }

    /// Block an exact variable assignment, we do not want to see it again, where
    /// all variables in `set` are set to `true` and all other variables are set
    /// to `false`.
    pub fn block_this(&mut self, set: &HashSet<Bool<'ctx>>) {
        tracing::trace!(set = ?set, "Blocking exact set");

        let (all_on, all_off): (HashSet<_>, HashSet<_>) = self
            .variables
            .iter()
            .cloned()
            .partition(|var| set.contains(var));
        self.block(&all_on, &all_off);
    }

    /// Block a set of models knowing that the following model is unsat:
    /// `all_true` variables are set to true and all others are set to false.
    ///
    /// Then, we block all models of those where the enabled extensive
    /// variables are a *superset* of those currently enabled and where the
    /// enabled reductive variables are a *subset* of those currently enabled.
    ///
    /// Phrased differently: a new model must have a currently disabled
    /// `reductive` variable set to true *or* a currently enabled `extensive`
    /// variable set to false.
    fn block_unsat(&mut self, all_true: &HashSet<Bool<'ctx>>) {
        tracing::trace!(all_true = ?all_true, "Blocking unsat");

        let all_false: HashSet<Bool<'ctx>> = self
            .variables
            .clone()
            .difference(all_true)
            .cloned()
            .collect();

        // turning off a reductive variable (assertion) will still result in UNSAT.
        let all_on: HashSet<Bool<'ctx>> = all_true.difference(&self.reductive).cloned().collect();

        // turning on an extensive variable (assumption) will still result in UNSAT.
        let all_off: HashSet<Bool<'ctx>> = all_false.difference(&self.extensive).cloned().collect();

        self.block(&all_on, &all_off);
    }

    /// Block a set of models knowing that the following model is sat:
    /// `all_true` variables are set to true and all others are set to false.
    ///
    /// Then, we block all models of those where the enabled extensive
    /// variables are a *subset* of those currently enabled and where the
    /// enabled reductive variables are a *superset* of those currently enabled.
    ///
    /// Phrased differently: a new model must have a currently disabled
    /// `extensive` variable set to true *or* a currently enabled `reductive`
    /// variable set to false.
    #[instrument(level = "trace", skip_all, fields(all_true.len = all_true.len()))]
    fn block_sat(&mut self, all_true: &HashSet<Bool<'ctx>>) {
        trace!(all_true = ?all_true, "Blocking sat");

        let all_false: HashSet<Bool<'ctx>> = self
            .variables
            .clone()
            .difference(all_true)
            .cloned()
            .collect();

        // turning off an extensive variable (assumption) will still result in SAT.
        let all_on: HashSet<Bool<'ctx>> = all_true.difference(&self.extensive).cloned().collect();

        // turning on a reductive variable (assertion) will still result in SAT.
        let all_off: HashSet<Bool<'ctx>> = all_false.difference(&self.reductive).cloned().collect();

        self.block(&all_on, &all_off);
    }

    /// *Shrink and block* a set of models knowing that the following model is
    /// unsat: `all_true` variables are set to true and all others are set to
    /// false.
    ///
    /// For *blocking*, we use [`Self::block_unsat()`]. *Shrinking* tries to
    /// remove extensive variables from the set of enabled ones. It uses the
    /// `get_shrunk_core` function to check whether the shrunk set is still
    /// unsatisfiable. If so, the `get_shrunk_core` function returns the
    /// unsatisfiable core. If not, it returns `None`.
    ///
    /// We use a heuristic for shrinking: simply try to remove one extensive
    /// variable after another so that the runtime is linear. We do *not* try
    /// all combinations of removals.
    ///
    /// We could also try to *add* reductive variables here, but we do not to
    /// keep it simple.
    #[instrument(level = "trace", skip_all, fields(all_true.len = all_true.len(), ret.len))]
    pub fn shrink_block_unsat(
        &mut self,
        all_true: HashSet<Bool<'ctx>>,
        mut get_shrunk_core: impl FnMut(&HashSet<Bool<'ctx>>) -> Option<HashSet<Bool<'ctx>>>,
    ) -> HashSet<Bool<'ctx>> {
        let mut current = all_true.clone();

        if let Some(shrunk_set) = get_shrunk_core(&current) {
            debug_assert!(shrunk_set.is_subset(&current));

            // check if we removed an extensive statement, then we don't use
            // the unsat core.
            if current
                .difference(&shrunk_set)
                .cloned()
                .collect::<HashSet<_>>()
                .difference(&self.extensive)
                .next()
                .is_some()
            {
                // the result was unsat (good), but we cannot use the unsat
                // core because we removed stuff that's not extensive.
            } else {
                current = shrunk_set;
            }
        }

        for var in all_true.intersection(&self.extensive) {
            if !current.remove(var) {
                continue;
            }
            if let Some(shrunk_set) = get_shrunk_core(&current) {
                debug_assert!(shrunk_set.is_subset(&current));

                // check if we removed an extensive statement, then we don't use
                // the unsat core.
                if current
                    .difference(&shrunk_set)
                    .cloned()
                    .collect::<HashSet<_>>()
                    .difference(&self.extensive)
                    .next()
                    .is_some()
                {
                    // the result was unsat (good), but we cannot use the unsat
                    // core because we removed stuff that's not extensive.
                } else {
                    current = shrunk_set;
                }
            } else {
                // undo removal
                current.insert(var.clone());
            }
        }
        self.block_unsat(&current);
        tracing::Span::current().record("ret.len", current.len());
        current
    }

    /// *Grow and block* a set of models knowing that the following model is
    /// sat: `all_true` variables are set to true and all others are set to
    /// false.
    ///
    /// For *blocking*, we use [`Self::block_sat()`]. *Growing* tries to add
    /// extensive variables from the set of enabled ones. It uses the
    /// `check_grow` function to check whether the grown set is still
    /// satisfiable. If so, the `check_grow` function returns `true` and
    /// `false` otherwise.
    ///
    /// We use a heuristic for growing: simply try to add one extensive variable
    /// after another so that the runtime is linear. We do *not* try all
    /// combinations of additions.
    ///
    /// We could also try to *remove* reductive variables here, but we do not to
    /// keep it simple.
    #[instrument(level = "trace", skip_all, fields(all_true.len = all_true.len(), ret.len))]
    pub fn grow_block_sat(
        &mut self,
        all_true: HashSet<Bool<'ctx>>,
        mut check_grow: impl FnMut(&HashSet<Bool<'ctx>>) -> bool,
    ) -> HashSet<Bool<'ctx>> {
        let mut current = all_true.clone();
        for var in self.extensive.difference(&all_true) {
            current.insert(var.clone());
            if !check_grow(&current) {
                // undo addition on unsat
                current.remove(var);
            }
        }
        self.block_sat(&current);
        tracing::Span::current().record("ret.len", current.len());
        current
    }
}
