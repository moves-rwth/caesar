//! The [`SmtScope`] tracks variables and associated constraints to create
//! quantifiers. Types that implement [`SmtFresh::fresh`] support the creation
//! of fresh instances in a surrounding scope.

use z3::{
    ast::{exists_const, forall_const, Ast, Bool, Datatype, Dynamic, Int, Real},
    Context, Pattern,
};

use crate::{prover::Prover, Factory, SmtFactory, SmtInvariant};

/// An SmtScope can be used to construct a quantifier like `forall` or `exists`.
/// The scope has a list of bound expressions (usually just variables) and a
/// list of [`Bool`] constraints.
///
/// During translation to SMT, we keep an SmtScope for each variable. When a
/// quantifier is encoded, the SmtScopes of the quantified variables are
/// combined to an SmtScope for all variables. This is then used to create the
/// `forall` or `exists` quantifier. There is also a global SmtScope whose
/// constraints are added to the solver before SAT checking (using
/// [`SmtScope::add_assumptions_to_prover`]).
///
/// Since the SmtScopes are used to create quantifiers with the corresponding
/// constraints of the quantified variables, it is important that all variables
/// used in quantifiers along with their constraints are added to the SmtScopes.
/// The [`SmtFresh::fresh`] function of types that implement the [`SmtFresh`]
/// trait can be used to create new variables and add them to an SmtScope.
///
/// When a type implements [`super::orders::SmtCompleteLattice`], the
/// [`super::orders::SmtCompleteLattice::infimum`] and
/// [`super::orders::SmtCompleteLattice::supremum`] functions can be used to
/// create infimums and suprema, quantifying over variables in an SmtScope.
#[derive(Clone, Default)]
pub struct SmtScope<'ctx> {
    bounds: Vec<Dynamic<'ctx>>,
    constraints: Vec<Bool<'ctx>>,
}

impl<'ctx> SmtScope<'ctx> {
    /// Create a new SmtScope.
    pub fn new() -> Self {
        Default::default()
    }

    /// Add a new expression to the list of bounds. This is usually just a
    /// variable.
    pub fn add_bound(&mut self, bound: &dyn Ast<'ctx>) {
        self.bounds.push(Dynamic::from_ast(bound));
    }

    /// Add a constraint to the list of constraints in this scope.
    pub fn add_constraint(&mut self, constraint: &Bool<'ctx>) {
        self.constraints.push(constraint.clone());
    }

    /// Directly add this scope to the global scope of the given prover.
    pub fn add_assumptions_to_prover(&self, prover: &mut Prover<'ctx>) {
        // We only need to add the constraints to the prover, any unquantified
        // variables occuring in the bound list are automatically existentially
        // quantified by Z3.
        for constraint in &self.constraints {
            prover.add_assumption(constraint);
        }
    }

    /// Create a new existential quantifier around `body`, quantifying over all
    /// bound expressions in this solver.
    pub fn exists(&self, patterns: &[&Pattern<'ctx>], body: &Bool<'ctx>) -> Bool<'ctx> {
        let ctx = body.get_ctx();
        exists_const(
            ctx,
            &self.bounds_dyn(),
            patterns,
            &Bool::and(ctx, &[&self.all_constraints(ctx), &body]),
        )
    }

    /// Create a new universal quantifier around `body`, quantifying over all
    /// bound expressions in this solver.
    pub fn forall(&self, patterns: &[&Pattern<'ctx>], body: &Bool<'ctx>) -> Bool<'ctx> {
        let ctx = body.get_ctx();
        forall_const(
            ctx,
            &self.bounds_dyn(),
            patterns,
            &self.all_constraints(ctx).implies(body),
        )
    }

    pub fn get_bounds(&self) -> impl Iterator<Item = &Dynamic<'ctx>> {
        self.bounds.iter()
    }

    /// The Z3 Rust API needs the bounds as a vector of `&dyn Ast<'ctx>` and
    /// does not accept a vector of [`Dynamic`] references, so we convert that
    /// here.
    fn bounds_dyn(&self) -> Vec<&dyn Ast<'ctx>> {
        self.bounds
            .iter()
            .map(|bound| {
                let b: &dyn Ast<'ctx> = bound;
                b
            })
            .collect()
    }

    /// Create a conjunction of all constraints in this scope.
    fn all_constraints(&self, ctx: &'ctx Context) -> Bool<'ctx> {
        let constraints_ref: Vec<&Bool<'_>> = self.constraints.iter().collect();
        Bool::and(ctx, &constraints_ref)
    }

    /// Append another scope's bounds and constraints to this scope.
    pub fn append(&mut self, other: &SmtScope<'ctx>) {
        self.bounds.extend(other.bounds.iter().cloned());
        self.constraints.extend(other.constraints.iter().cloned());
    }

    /// [`SmtScope::append`] all scopes from the iterator to this scope.
    pub fn extend<'a>(&mut self, others: impl IntoIterator<Item = &'a Self>)
    where
        'ctx: 'a,
    {
        for other in others.into_iter() {
            self.append(other);
        }
    }

    /// Does this scope not contain any bounds or constraints?
    pub fn is_empty(&self) -> bool {
        self.bounds.is_empty() && self.constraints.is_empty()
    }
}

/// Restricted interface to [`SmtScope`] provided to [`SmtFresh::allocate`].
pub struct SmtAlloc<'ctx, 'a>(&'a mut SmtScope<'ctx>);

impl<'ctx, 'a> SmtAlloc<'ctx, 'a> {
    /// Register a new variable in this allocator.
    pub fn register_var(&mut self, bound: &impl Ast<'ctx>) {
        self.0.add_bound(bound);
    }
}

/// This is the central trait to create new variables in our framework. The
/// [`SmtFresh::fresh`] function creates a new instance of this type and adds
/// the required Z3 variables and constraints to the given [`SmtScope`].
///
/// Implementors of this trait should only implement [`SmtFresh::allocate`] and
/// users should only use [`SmtFresh::fresh`].
pub trait SmtFresh<'ctx>: Sized + SmtFactory<'ctx> + SmtInvariant<'ctx> {
    /// Create a new instance of this type and prefix the created Z3 variable(s)
    /// with `prefix`. All created Z3 variables must be registered with the
    /// allocator so that quantification works correctly.
    fn allocate<'a>(
        factory: &Factory<'ctx, Self>,
        alloc: &mut SmtAlloc<'ctx, 'a>,
        prefix: &str,
    ) -> Self;

    /// Creates a new instance of this type with variables prefixed with
    /// `prefix`. Variables and the types' invariant (see [`SmtInvariant`]) are
    /// added to the [`SmtScope`].
    fn fresh(factory: &Factory<'ctx, Self>, scope: &mut SmtScope<'ctx>, prefix: &str) -> Self {
        let value = Self::allocate(factory, &mut SmtAlloc(scope), prefix);
        if let Some(invariant) = value.smt_invariant() {
            scope.add_constraint(&invariant);
        }
        value
    }
}

macro_rules! z3_simple_fresh {
    ($ty:ident) => {
        impl<'ctx> SmtFresh<'ctx> for $ty<'ctx> {
            fn allocate<'a>(
                factory: &Factory<'ctx, Self>,
                alloc: &mut SmtAlloc<'ctx, 'a>,
                prefix: &str,
            ) -> Self {
                let res = $ty::fresh_const(factory, prefix);
                alloc.register_var(&res);
                res
            }
        }
    };
}

z3_simple_fresh!(Bool);
z3_simple_fresh!(Int);
z3_simple_fresh!(Real);

impl<'ctx> SmtFresh<'ctx> for Dynamic<'ctx> {
    fn allocate<'a>(
        factory: &Factory<'ctx, Self>,
        alloc: &mut SmtAlloc<'ctx, 'a>,
        prefix: &str,
    ) -> Self {
        let res = Dynamic::fresh_const(factory.0, prefix, &factory.1);
        alloc.register_var(&res);
        res
    }
}

impl<'ctx> SmtFresh<'ctx> for Datatype<'ctx> {
    fn allocate<'a>(
        factory: &Factory<'ctx, Self>,
        alloc: &mut SmtAlloc<'ctx, 'a>,
        prefix: &str,
    ) -> Self {
        let res = Datatype::fresh_const(factory.0, prefix, &factory.1);
        alloc.register_var(&res);
        res
    }
}
