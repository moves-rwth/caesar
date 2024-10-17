use std::{
    collections::HashSet,
    iter::FromIterator,
    ops::{RangeFrom, RangeInclusive, RangeToInclusive},
};

use tracing::instrument;
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
}

impl<'ctx> SubsetExploration<'ctx> {
    pub fn new(ctx: &'ctx Context, variables: impl IntoIterator<Item = Bool<'ctx>>) -> Self {
        SubsetExploration {
            solver: Solver::new(ctx),
            variables: HashSet::from_iter(variables),
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
            SatResult::Unknown => None,
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

    /// Block this set, we do not want to see it again.
    pub fn block_this(&mut self, set: &HashSet<Bool<'ctx>>) {
        let assignments: Vec<_> = self
            .variables
            .iter()
            .map(|var| {
                if set.contains(var) {
                    var.clone()
                } else {
                    var.not()
                }
            })
            .collect();
        let constraint = Bool::and(self.solver.get_context(), &assignments);
        self.solver.assert(&constraint.not());
    }

    /// "Block down" - all values at this point or lower are considered not unsat.
    fn block_down(&mut self, from_point: &HashSet<Bool<'ctx>>) {
        // we add a constraint that says the next set must have any variable set
        // to true not in the given `from_point`.
        let complement: Vec<_> = self.variables.difference(from_point).collect();
        let constraint = Bool::or(self.solver.get_context(), &complement);
        self.solver.assert(&constraint);
    }

    /// "Block up" - the next sets must not contain at least one of the given values.
    fn block_up(&mut self, from_point: &HashSet<Bool<'ctx>>) {
        // we add a constraint that says the next set must have any variable set
        // to true not in the given `from_point`.
        let negated: Vec<_> = from_point.iter().map(|var| var.not()).collect();
        let constraint = Bool::or(self.solver.get_context(), &negated);
        self.solver.assert(&constraint);
    }

    /// Shrink this set with the given shrinking function. If the shrinking
    /// function returns `Some`, we will shrink to this set. Then, we'll block
    /// upwards.
    #[instrument(level = "trace", skip_all, fields(seed.len = seed.len(), ret.len))]
    pub fn shrink_block_up(
        &mut self,
        seed: HashSet<Bool<'ctx>>,
        mut get_shrunk_core: impl FnMut(&HashSet<Bool<'ctx>>) -> Option<HashSet<Bool<'ctx>>>,
    ) -> HashSet<Bool<'ctx>> {
        let mut current = seed.clone();
        for var in seed {
            if !current.remove(&var) {
                continue;
            }
            if let Some(shrunk_set) = get_shrunk_core(&current) {
                debug_assert!(shrunk_set.is_subset(&current));
                current = shrunk_set;
            } else {
                current.insert(var);
            }
        }
        self.block_up(&current);
        tracing::Span::current().record("ret.len", current.len());
        current
    }

    /// Grow this set with the given function that checks the set. Then, we
    /// block downwards from this grown set.
    #[instrument(level = "trace", skip_all, fields(seed.len = seed.len(), ret.len))]
    pub fn grow_block_down(
        &mut self,
        seed: HashSet<Bool<'ctx>>,
        mut check_grow: impl FnMut(&HashSet<Bool<'ctx>>) -> bool,
    ) -> HashSet<Bool<'ctx>> {
        let mut current = seed.clone();
        for var in self.variables.difference(&seed) {
            if check_grow(&current) {
                current.insert(var.clone());
            }
        }
        self.block_down(&current);
        tracing::Span::current().record("ret.len", current.len());
        current
    }
}
