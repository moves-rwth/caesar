use std::ops::{RangeFrom, RangeInclusive, RangeToInclusive};

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
