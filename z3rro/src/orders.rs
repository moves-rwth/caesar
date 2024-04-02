//! This module defines some structures from order theory as traits. We have
//! partial orders on SMT types via [`SmtPartialOrd`], bounded lattices via
//! [`SmtLattice`] and complete lattices via [`SmtCompleteLattice`]. For Gödel
//! algebras, there is a corresponding [`SmtGodel`] trait.
//!
//! All these structures have order-theoretic duals. The [`Opp`] newtype wrapper
//! implements the order-theoretic dual versions of the underlying type for
//! free. Most traits have some default implementations of functions using
//! [`Opp`].

use ref_cast::RefCast;
use z3::{
    ast::{Ast, Bool, Int, Real},
    Pattern,
};

use crate::{scope::SmtAlloc, Factory, SmtFactory, SmtInvariant};

use super::{
    scope::{SmtFresh, SmtScope},
    SmtBranch,
};

/// The different ordering relations. It's like [`std::cmp::Ordering`], but with
/// more options to allow for more specialization.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum SmtOrdering {
    Less,
    LessOrEqual,
    Equal,
    GreaterOrEqual,
    Greater,
}

impl SmtOrdering {
    /// Return the dual ordering relation.
    pub fn reverse(self) -> Self {
        match self {
            SmtOrdering::Less => SmtOrdering::Greater,
            SmtOrdering::LessOrEqual => SmtOrdering::GreaterOrEqual,
            SmtOrdering::Equal => SmtOrdering::Equal,
            SmtOrdering::GreaterOrEqual => SmtOrdering::LessOrEqual,
            SmtOrdering::Greater => SmtOrdering::Less,
        }
    }
}

/// Partially ordered SMT values.
pub trait SmtPartialOrd<'ctx>: Sized {
    /// Encode the given relation between `self` and `other`.
    fn smt_cmp(&self, other: &Self, ordering: SmtOrdering) -> Bool<'ctx>;

    /// Shortcut for `self.smt_cmp(other, SmtOrdering::LessOrEqual)`.
    fn smt_le(&self, other: &Self) -> Bool<'ctx> {
        self.smt_cmp(other, SmtOrdering::LessOrEqual)
    }
}

impl<'ctx> SmtPartialOrd<'ctx> for Int<'ctx> {
    fn smt_cmp(&self, other: &Self, ordering: SmtOrdering) -> Bool<'ctx> {
        match ordering {
            SmtOrdering::Less => self.lt(other),
            SmtOrdering::LessOrEqual => self.le(other),
            SmtOrdering::Equal => self._eq(other),
            SmtOrdering::GreaterOrEqual => self.ge(other),
            SmtOrdering::Greater => self.gt(other),
        }
    }
}

impl<'ctx> SmtPartialOrd<'ctx> for Real<'ctx> {
    fn smt_cmp(&self, other: &Self, ordering: SmtOrdering) -> Bool<'ctx> {
        match ordering {
            SmtOrdering::Less => self.lt(other),
            SmtOrdering::LessOrEqual => self.le(other),
            SmtOrdering::Equal => self._eq(other),
            SmtOrdering::GreaterOrEqual => self.ge(other),
            SmtOrdering::Greater => self.gt(other),
        }
    }
}

/// Return the minimum between two SMT values by encoding a conditional branch
/// on whether `a` is less than or equal to `b`.
pub fn smt_min<'ctx, T>(a: &T, b: &T) -> T
where
    T: SmtBranch<'ctx> + SmtPartialOrd<'ctx>,
{
    T::branch(&a.smt_cmp(b, SmtOrdering::LessOrEqual), a, b)
}

/// Return the maximum between two SMT values by encoding a conditional branch
/// on whether `a` is greater than or equal to `b`.
pub fn smt_max<'ctx, T>(a: &T, b: &T) -> T
where
    T: SmtBranch<'ctx> + SmtPartialOrd<'ctx>,
{
    T::branch(&a.smt_cmp(b, SmtOrdering::GreaterOrEqual), a, b)
}

impl<'ctx> SmtPartialOrd<'ctx> for Bool<'ctx> {
    fn smt_cmp(&self, other: &Self, ordering: SmtOrdering) -> Bool<'ctx> {
        match ordering {
            SmtOrdering::Less => Bool::and(self.get_ctx(), &[&self.not(), &other]),
            SmtOrdering::LessOrEqual => self.implies(other),
            SmtOrdering::Equal => self._eq(other),
            SmtOrdering::GreaterOrEqual => other.implies(self),
            SmtOrdering::Greater => z3_and!(self, &other.not()),
        }
    }
}

/// A bounded lattice with top and bottom elements and binary infimum and
/// supremum.
pub trait SmtLattice<'ctx>: SmtFactory<'ctx> + SmtPartialOrd<'ctx> {
    fn bot(factory: &Factory<'ctx, Self>) -> Self;

    fn top(factory: &Factory<'ctx, Self>) -> Self;

    fn inf(&self, other: &Self) -> Self;

    fn sup(&self, other: &Self) -> Self;
}

/// _Embed_ the Boolean formula in a lattice. If `cond` evaluates to `true`,
/// `smt_bool_embed(factory, cond)` evaluates to the top element of the lattice.
/// Otherwise, it evaluates to the bottom element.
pub fn smt_bool_embed<'ctx, T>(factory: &Factory<'ctx, T>, cond: &Bool<'ctx>) -> T
where
    T: SmtBranch<'ctx> + SmtLattice<'ctx>,
{
    T::branch(cond, &T::top(factory), &T::bot(factory))
}

impl<'ctx> SmtLattice<'ctx> for Bool<'ctx> {
    fn bot(factory: &Factory<'ctx, Self>) -> Self {
        Bool::from_bool(factory, false)
    }

    fn top(factory: &Factory<'ctx, Self>) -> Self {
        Bool::from_bool(factory, true)
    }

    fn inf(&self, other: &Self) -> Self {
        z3_and!(self, other)
    }

    fn sup(&self, other: &Self) -> Self {
        z3_or!(self, other)
    }
}

/// A bi-Heyting algebra with Gödel implications (bi-Gödel algebra).
///
/// Because the Gödel algebra is uniquely determined by the underlying lattice,
/// all functions of this trait have default implementations based on the
/// underlying lattice.
pub trait SmtGodel<'ctx>: SmtLattice<'ctx> + SmtBranch<'ctx> {
    /// The Gödel implication.
    fn implication(&self, other: &Self) -> Self {
        let factory = self.factory();
        let top = Self::top(&factory);
        Self::branch(&self.smt_le(other), &top, other)
    }

    /// The dual of the Gödel implication.
    fn coimplication(&self, other: &Self) -> Self {
        Opp::with_opp2(self, other, |a, b| a.implication(b))
    }

    /// The _hard implication_ `a ↘ b`.
    fn compare(&self, other: &Self) -> Self {
        let factory = self.factory();
        let top = Self::top(&factory);
        let bot = Self::bot(&factory);
        Self::branch(&self.smt_le(other), &top, &bot)
    }

    /// The _hard co-implication_ `a ↖ b`.
    fn cocompare(&self, other: &Self) -> Self {
        Opp::with_opp2(self, other, |a, b| a.compare(b))
    }

    /// Negation in the Gödel algebra.
    fn negate(&self) -> Self {
        let factory = self.factory();
        let top = Self::top(&factory);
        let bot = Self::bot(&factory);
        Self::branch(&self.smt_le(&bot), &top, &bot)
    }

    /// Dual of the Gödel algebra negation.
    fn conegate(&self) -> Self {
        Opp::with_opp(self, |a| a.negate())
    }
}

/// SMT encoding for a complete lattice.
///
/// Although all functions have a default implementation, it is an unchecked
/// invariant that all subsets of this type have an infimum and supremum. If
/// that's not the case, any generated implementation will be unsound.
pub trait SmtCompleteLattice<'ctx>: SmtFresh<'ctx> + SmtLattice<'ctx> {
    /// Return an expression representing the infimum of `self`, quantifying
    /// over the variables specified in `bounds`. Additional variables to
    /// specify the infimum may be added to the outer scope `ctx`.
    fn infimum(
        &self,
        inf_vars: SmtScope<'ctx>,
        patterns: &[&Pattern<'ctx>],
        ctx: &mut SmtScope<'ctx>,
    ) -> Self {
        let factory = self.factory();

        // the resulting infimum is created in the outer context
        let inf = Self::fresh(&factory, ctx, "extremum");

        // infimum is a lower bound to all self
        let inf_is_lower_bound = &inf_vars.forall(patterns, &inf.smt_le(self));
        ctx.add_constraint(inf_is_lower_bound);

        // `other_lb` is another lower bound to self...
        let mut inf_vars_and_other = inf_vars.clone();
        let other_lb = Self::fresh(&factory, &mut inf_vars_and_other, "bound");
        let other_is_lb = inf_vars.forall(patterns, &other_lb.smt_le(self));
        // infimum is the greatest lower bound, i.e. `other_lb <= inf`
        let inf_glb = other_is_lb.implies(&other_lb.smt_le(&inf));
        ctx.add_constraint(&inf_vars_and_other.forall(&[], &inf_glb));

        inf
    }

    /// Dual of [`SmtCompleteLattice::infimum`].
    fn supremum(
        &self,
        sup_vars: SmtScope<'ctx>,
        patterns: &[&Pattern<'ctx>],
        ctx: &mut SmtScope<'ctx>,
    ) -> Self {
        Opp::with_opp(self, |a| a.infimum(sup_vars, patterns, ctx))
    }
}

impl<'ctx> SmtCompleteLattice<'ctx> for Bool<'ctx> {}

/// The opposite lattice. Duals of the traits of [`crate::orders`] are
/// automatically implemented if the underlying type implements them.
#[repr(transparent)]
#[derive(Clone, Copy, RefCast)]
pub struct Opp<L>(pub L);

impl<L> Opp<L> {
    /// Do a unary operation in the opposite lattice and convert the result
    /// back.
    pub fn with_opp(a: &L, f: impl FnOnce(&Opp<L>) -> Opp<L>) -> L {
        f(Opp::ref_cast(a)).0
    }

    /// Do a binary operation in the opposite lattice and convert the result
    /// back.
    pub fn with_opp2(a: &L, b: &L, f: impl FnOnce(&Opp<L>, &Opp<L>) -> Opp<L>) -> L {
        f(Opp::ref_cast(a), Opp::ref_cast(b)).0
    }
}

impl<'ctx, L: SmtFactory<'ctx>> SmtFactory<'ctx> for Opp<L> {
    type FactoryType = L::FactoryType;

    fn factory(&self) -> Factory<'ctx, Self> {
        self.0.factory()
    }
}

impl<'ctx, L: SmtInvariant<'ctx>> SmtInvariant<'ctx> for Opp<L> {
    fn smt_invariant(&self) -> Option<Bool<'ctx>> {
        self.0.smt_invariant()
    }
}

impl<'ctx, L: SmtFresh<'ctx>> SmtFresh<'ctx> for Opp<L> {
    fn allocate<'a>(
        factory: &Factory<'ctx, Self>,
        alloc: &mut SmtAlloc<'ctx, 'a>,
        prefix: &str,
    ) -> Self {
        Opp(L::allocate(factory, alloc, prefix))
    }
}

impl<'ctx, L: SmtBranch<'ctx>> SmtBranch<'ctx> for Opp<L> {
    fn branch(cond: &Bool<'ctx>, a: &Self, b: &Self) -> Self {
        Opp(L::branch(cond, &a.0, &b.0))
    }
}

impl<'ctx, L: SmtPartialOrd<'ctx>> SmtPartialOrd<'ctx> for Opp<L> {
    fn smt_cmp(&self, other: &Self, ordering: SmtOrdering) -> Bool<'ctx> {
        self.0.smt_cmp(&other.0, ordering.reverse())
    }
}

impl<'ctx, L: SmtLattice<'ctx>> SmtLattice<'ctx> for Opp<L> {
    fn bot(factory: &Factory<'ctx, Self>) -> Self {
        Opp(L::top(factory))
    }

    fn top(factory: &Factory<'ctx, Self>) -> Self {
        Opp(L::bot(factory))
    }

    fn inf(&self, other: &Self) -> Self {
        Opp(self.0.sup(&other.0))
    }

    fn sup(&self, other: &Self) -> Self {
        Opp(self.0.inf(&other.0))
    }
}

impl<'ctx, L: SmtGodel<'ctx>> SmtGodel<'ctx> for Opp<L> {}

impl<'ctx, L: SmtCompleteLattice<'ctx>> SmtCompleteLattice<'ctx> for Opp<L> {}

#[cfg(test)]
mod test {
    use z3::ast::{Ast, Int};

    use crate::{scope::SmtFresh, test::test_prove};

    use super::SmtCompleteLattice;

    /// This is a smoke test to check that the infimum over Bools actually
    /// computes the least value for the quantified expression.
    ///
    /// There was a bug where this wasn't the case, so that's why this test is here.
    #[test]
    fn test_inf() {
        test_prove(|ctx, scope| {
            let x = Int::fresh(&ctx, scope, "x");
            let x_is_5 = x._eq(&Int::from_u64(ctx, 5));
            let inf = x_is_5.infimum(scope.clone(), &[], scope);
            inf.not()
        });
    }
}
