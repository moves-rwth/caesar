//! This module defines some structures from order theory as traits. We have
//! partial orders on SMT types via [`SmtPartialOrd`], bounded lattices via
//! [`SmtLattice`] and complete lattices via [`SmtCompleteLattice`]. For Gödel
//! algebras, there is a corresponding [`SmtGodel`] trait.
//!
//! All these structures have order-theoretic duals. The [`Opp`] newtype wrapper
//! implements the order-theoretic dual versions of the underlying type for
//! free. Most traits have some default implementations of functions using
//! [`Opp`].

use std::borrow::Cow;

use ref_cast::RefCast;
use z3::ast::{Ast, Bool, Int, Real};

use super::{
    scope::{SmtFresh, SmtScope, SmtSkolem},
    SmtBranch,
};
use crate::{quantifiers::QuantifierMeta, Factory, SmtFactory, SmtInvariant};

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
            SmtOrdering::Less => Bool::and(self.get_ctx(), &[&self.not(), other]),
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

/// The variables relevant while encoding one extremum.
///
/// `quantified` are the variables introduced by the extremum itself.
/// `skolem_args` are the already-bound outer variables that the extremum
/// witness may depend on.
#[derive(Clone)]
pub struct SmtExtremumVars<'ctx> {
    pub quantified: SmtScope<'ctx>,
    pub skolem_args: SmtScope<'ctx>,
}

/// SMT encoding for a complete lattice.
///
/// Although all functions have a default implementation, it is an unchecked
/// invariant that all subsets of this type have an infimum and supremum. If
/// that's not the case, any generated implementation will be unsound.
pub trait SmtCompleteLattice<'ctx>: SmtSkolem<'ctx> + SmtLattice<'ctx> {
    /// Encode `inf q. self(args, q)` using:
    /// - `forall args, q. extremum(args) <= self(args, q)`
    /// - `forall args, candidate. (forall q. candidate <= self(args, q)) -> candidate <= extremum(args)`
    fn infimum(
        &self,
        vars: SmtExtremumVars<'ctx>,
        meta: QuantifierMeta<'ctx>,
        constraints: &mut SmtScope<'ctx>,
    ) -> Self {
        let factory = self.factory();
        let SmtExtremumVars {
            quantified: q_scope,
            skolem_args: args_scope,
        } = vars;
        let mut pointwise_glb_scope = args_scope.clone();

        // `extremum(args)`
        let extremum = Self::fresh_skolem(&factory, &args_scope, "extremum");
        if let Some(invariant) = extremum.smt_invariant() {
            // `forall args. inv(extremum(args))`
            constraints.add_constraint(&extremum_invariant_axiom(&args_scope, &meta, &invariant));
        }

        // `forall args, q. extremum(args) <= self(args, q)`
        constraints.add_constraint(&extremum_lower_bound_axiom(
            &args_scope,
            &q_scope,
            &meta,
            &extremum,
            self,
        ));

        // Pointwise lower-bound candidate.
        let pointwise_candidate = Self::fresh(&factory, &mut pointwise_glb_scope, "bound");
        // `forall args, candidate. (forall q. candidate <= self(args, q)) -> candidate <= extremum(args)`
        constraints.add_constraint(&extremum_glb_axiom(
            &pointwise_glb_scope,
            &q_scope,
            &meta,
            &pointwise_candidate,
            self,
            &extremum,
        ));

        extremum
    }

    /// Return a term representing `sup q. self(args, q)`.
    ///
    /// This is encoded by dualizing [`SmtCompleteLattice::infimum`]:
    /// - `forall args, q. self(args, q) <= sup(args)`
    /// - `forall args, other. (forall q. self(args, q) <= other) -> sup(args) <= other`
    fn supremum(
        &self,
        vars: SmtExtremumVars<'ctx>,
        meta: QuantifierMeta<'ctx>,
        constraints: &mut SmtScope<'ctx>,
    ) -> Self {
        Opp::with_opp(self, |a| a.infimum(vars, meta, constraints))
    }
}

/// `forall args. inv(extremum(args))`.
fn extremum_invariant_axiom<'ctx>(
    args_scope: &SmtScope<'ctx>,
    meta: &QuantifierMeta<'ctx>,
    invariant: &Bool<'ctx>,
) -> Bool<'ctx> {
    args_scope.forall(
        &meta.variant(Cow::Borrowed("extremum_invariant")),
        invariant,
    )
}

/// `forall args, q. extremum(args) <= body(args, q)`.
fn extremum_lower_bound_axiom<'ctx, T: SmtPartialOrd<'ctx>>(
    args_scope: &SmtScope<'ctx>,
    q_scope: &SmtScope<'ctx>,
    meta: &QuantifierMeta<'ctx>,
    extremum: &T,
    body: &T,
) -> Bool<'ctx> {
    let for_all_q = q_scope.forall(
        &meta.variant(Cow::Borrowed("extremum_lower_bound_inner")),
        &extremum.smt_le(body),
    );
    args_scope.forall(
        &meta.variant(Cow::Borrowed("extremum_lower_bound_outer")),
        &for_all_q,
    )
}

/// `forall args, candidate. (forall q. candidate <= body(args, q)) -> candidate <= extremum(args)`.
fn extremum_glb_axiom<'ctx, T: SmtPartialOrd<'ctx>>(
    pointwise_glb_scope: &SmtScope<'ctx>,
    q_scope: &SmtScope<'ctx>,
    meta: &QuantifierMeta<'ctx>,
    pointwise_candidate: &T,
    body: &T,
    extremum: &T,
) -> Bool<'ctx> {
    let candidate_is_lower_bound = q_scope.forall(
        &meta.variant(Cow::Borrowed("extremum_glb_inner")),
        &pointwise_candidate.smt_le(body),
    );
    pointwise_glb_scope.forall(
        &meta.variant(Cow::Borrowed("extremum_glb_outer")),
        &candidate_is_lower_bound.implies(&pointwise_candidate.smt_le(extremum)),
    )
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
    fn allocate(factory: &Factory<'ctx, Self>, scope: &mut SmtScope<'ctx>, prefix: &str) -> Self {
        Opp(L::allocate(factory, scope, prefix))
    }
}

impl<'ctx, L: SmtSkolem<'ctx>> SmtSkolem<'ctx> for Opp<L> {
    fn allocate_skolem(factory: &Factory<'ctx, Self>, args: &SmtScope<'ctx>, prefix: &str) -> Self {
        Opp(L::allocate_skolem(factory, args, prefix))
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
    use z3::ast::{Ast, Bool, Int};

    use crate::{
        quantifiers::QuantifierMeta,
        scope::{SmtFresh, SmtScope},
        test::test_prove,
    };

    use super::{SmtCompleteLattice, SmtExtremumVars};

    fn inf<'ctx>(
        expr: &Bool<'ctx>,
        quantified: SmtScope<'ctx>,
        skolem_args: SmtScope<'ctx>,
        qid: &'static str,
        scope: &mut SmtScope<'ctx>,
    ) -> Bool<'ctx> {
        expr.infimum(
            SmtExtremumVars {
                quantified,
                skolem_args,
            },
            QuantifierMeta::new(qid),
            scope,
        )
    }

    /// This is a smoke test to check that the infimum over Bools actually
    /// computes the least value for the quantified expression.
    ///
    /// There was a bug where this wasn't the case, so that's why this test is here.
    #[test]
    fn test_inf() {
        test_prove(|ctx, scope| {
            let x = Int::fresh(&ctx, scope, "x");
            let x_is_5 = x._eq(&Int::from_u64(ctx, 5));
            let meta = QuantifierMeta::new("test_inf");
            let inf = x_is_5.infimum(
                SmtExtremumVars {
                    quantified: scope.clone(),
                    skolem_args: SmtScope::new(),
                },
                meta,
                scope,
            );
            inf.not()
        });
    }

    #[test]
    fn test_nested_extremum_depends_on_outer_quantifier() {
        test_prove(|ctx, scope| {
            let z = Bool::fresh(&ctx, scope, "z");

            let mut xs = SmtScope::new();
            let x = Bool::fresh(&ctx, &mut xs, "x");

            let mut ys = SmtScope::new();
            let y = Bool::fresh(&ctx, &mut ys, "y");

            let body = z.implies(&x._eq(&z).implies(&y.not().implies(&x)));

            // inf x. inf y. (z -> (x = z -> (!y -> x)))
            let nested = inf(
                &inf(&body, ys.clone(), xs.clone(), "inner", scope),
                xs.clone(),
                SmtScope::new(),
                "outer",
                scope,
            );

            let mut xys = xs;
            xys.append(&ys);
            // inf x, y. (z -> (x = z -> (!y -> x)))
            let joint = inf(&body, xys, SmtScope::new(), "joint", scope);

            nested.iff(&joint)
        });
    }
}
