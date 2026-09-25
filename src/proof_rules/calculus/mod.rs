//! Calculi, fixed-point semantics, and their soundness checks.

mod calculus_checker;
pub use calculus_checker::*;
mod recursion_checker;
pub use recursion_checker::*;
mod soundness_checker;
pub use soundness_checker::*;

#[cfg(test)]
mod tests;

use crate::ast::{Expr, ExprBuilder, TyKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CalculusType {
    Wp,
    Wlp,
    Uwlp,
    Ert,
}

impl std::fmt::Display for CalculusType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Wp => write!(f, "wp"),
            Self::Wlp => write!(f, "wlp"),
            Self::Uwlp => write!(f, "uwlp"),
            Self::Ert => write!(f, "ert"),
        }
    }
}

impl CalculusType {
    pub fn fixpoint_kind(self) -> FixpointKind {
        match self {
            Self::Wp | Self::Ert => FixpointKind::Least,
            Self::Wlp => FixpointKind::Greatest { one_bounded: true },
            Self::Uwlp => FixpointKind::Greatest { one_bounded: false },
        }
    }
}

/// Fixed-point semantics of an expectation transformer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FixpointKind {
    Least,
    Greatest {
        /// Whether expectations are bounded by one.
        one_bounded: bool,
    },
}

impl std::fmt::Display for FixpointKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Least => "least",
            Self::Greatest { one_bounded: true } => "greatest (one-bounded)",
            Self::Greatest { one_bounded: false } => "greatest (unbounded)",
        })
    }
}

impl FixpointKind {
    /// The starting expectation in Kleene's fixed-point iteration.
    ///
    /// For an ω-continuous transformer F on a complete lattice, `lfp(F) = sup_{n∈ℕ} Fⁿ(⊥)`.
    /// Dually, if F preserves infima of decreasing ω-chains, `gfp(F) = inf_{n∈ℕ} Fⁿ(⊤)`.
    ///
    /// Here `⊥ = 0`, and `⊤ = 1` for one-bounded expectations or `∞` otherwise.
    /// The result is an `EUReal` expression.
    ///
    /// Loop unrolling uses this expectation as the terminator to obtain finite Kleene iterates.
    /// Omega invariants use it in their base case to bound these iterates from below (least fixed points) or above (greatest fixed points).
    /// Kleene's theorem identifies the supremum or infimum of the iterates with the fixed point.
    /// The one-sided bounds themselves require only monotonicity.
    pub fn terminator(self, builder: ExprBuilder) -> Expr {
        match self {
            Self::Least => builder.bot_lit(&TyKind::EUReal),
            Self::Greatest { one_bounded: true } => builder.one_lit(&TyKind::EUReal),
            Self::Greatest { one_bounded: false } => builder.infinity_lit(),
        }
    }
}
