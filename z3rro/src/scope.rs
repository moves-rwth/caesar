//! The [`SmtScope`] tracks variables and associated constraints to create
//! quantifiers. Types that implement [`SmtFresh::fresh`] support the creation
//! of fresh instances in a surrounding scope.

use std::{
    borrow::Cow,
    sync::atomic::{AtomicUsize, Ordering},
};

use z3::{
    ast::{Ast, Bool, Datatype, Dynamic, Int, Real},
    Context, FuncDecl, Sort, Symbol,
};

use crate::{
    prover::Prover,
    quantifiers::{mk_quantifier, QuantifierMeta, QuantifierType},
    Factory, SmtFactory, SmtInvariant,
};

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
    pub fn exists(&self, meta: &QuantifierMeta<'ctx>, body: &Bool<'ctx>) -> Bool<'ctx> {
        let ctx = body.get_ctx();
        let body = if self.constraints.is_empty() {
            Cow::Borrowed(body)
        } else {
            Cow::Owned(Bool::and(ctx, &[&self.all_constraints(ctx), body]))
        };
        if self.bounds.is_empty() {
            body.into_owned()
        } else {
            mk_quantifier(meta, QuantifierType::Exists, &self.bounds_dyn(), &body)
        }
    }

    /// Create a new universal quantifier around `body`, quantifying over all
    /// bound expressions in this solver.
    pub fn forall(&self, meta: &QuantifierMeta<'ctx>, body: &Bool<'ctx>) -> Bool<'ctx> {
        let ctx = body.get_ctx();
        let body = if self.constraints.is_empty() {
            Cow::Borrowed(body)
        } else {
            Cow::Owned(self.all_constraints(ctx).implies(body))
        };
        if self.bounds.is_empty() {
            body.into_owned()
        } else {
            mk_quantifier(meta, QuantifierType::Forall, &self.bounds_dyn(), &body)
        }
    }

    pub fn get_bounds(&self) -> impl Iterator<Item = &Dynamic<'ctx>> {
        self.bounds.iter()
    }

    /// Remove all constraints from this scope. You'll have to know what you are doing!
    pub fn clear_constraints(&mut self) {
        self.constraints.clear();
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

/// This is the central trait to create new variables in our framework. The
/// [`SmtFresh::fresh`] function creates a new instance of this type and adds
/// the required Z3 variables and constraints to the given [`SmtScope`].
pub trait SmtFresh<'ctx>: Sized + SmtFactory<'ctx> + SmtInvariant<'ctx> {
    /// Create a new instance of this type and prefix the created Z3 variable(s)
    /// with `prefix` and register any quantified variables in `scope`.
    fn allocate(factory: &Factory<'ctx, Self>, scope: &mut SmtScope<'ctx>, prefix: &str) -> Self;

    /// Creates a new instance of this type with variables prefixed with
    /// `prefix`. Variables and the types' invariant (see [`SmtInvariant`]) are
    /// added to the [`SmtScope`].
    fn fresh(factory: &Factory<'ctx, Self>, scope: &mut SmtScope<'ctx>, prefix: &str) -> Self {
        let value = Self::allocate(factory, scope, prefix);
        if let Some(invariant) = value.smt_invariant() {
            scope.add_constraint(&invariant);
        }
        value
    }
}

/// Types that support Skolemized values over already-bound outer variables.
pub trait SmtSkolem<'ctx>: SmtFresh<'ctx> {
    /// Create a fresh value which may depend on `args`.
    fn allocate_skolem(factory: &Factory<'ctx, Self>, args: &SmtScope<'ctx>, prefix: &str) -> Self;

    /// Create a fresh value which may depend on `args`.
    fn fresh_skolem(factory: &Factory<'ctx, Self>, args: &SmtScope<'ctx>, prefix: &str) -> Self {
        Self::allocate_skolem(factory, args, prefix)
    }
}

fn fresh_symbol(prefix: &str) -> Symbol {
    static NEXT_FRESH_SYMBOL: AtomicUsize = AtomicUsize::new(0);
    let id = NEXT_FRESH_SYMBOL.fetch_add(1, Ordering::Relaxed);
    Symbol::String(format!("{prefix}!{id}"))
}

/// Build a fresh value for the given range, using a Skolem function when the
/// value is allowed to depend on already-bound variables.
fn fresh_skolem_application<'ctx>(
    ctx: &'ctx Context,
    args: &SmtScope<'ctx>,
    range: &Sort<'ctx>,
    prefix: &str,
) -> Dynamic<'ctx> {
    let bounds: Vec<_> = args.get_bounds().cloned().collect();
    if bounds.is_empty() {
        return Dynamic::fresh_const(ctx, prefix, range);
    }

    let domain: Vec<_> = bounds.iter().map(Dynamic::get_sort).collect();
    let domain_refs: Vec<_> = domain.iter().collect();
    let args: Vec<_> = bounds.iter().map(|bound| bound as &dyn Ast<'ctx>).collect();
    let decl = FuncDecl::new(ctx, fresh_symbol(prefix), &domain_refs, range);
    decl.apply(&args)
}

macro_rules! z3_simple_fresh {
    ($ty:ident, $sort:expr, $cast:ident) => {
        impl<'ctx> SmtFresh<'ctx> for $ty<'ctx> {
            fn allocate(
                factory: &Factory<'ctx, Self>,
                scope: &mut SmtScope<'ctx>,
                prefix: &str,
            ) -> Self {
                let value = $ty::fresh_const(factory, prefix);
                scope.add_bound(&value);
                value
            }
        }

        impl<'ctx> SmtSkolem<'ctx> for $ty<'ctx> {
            fn allocate_skolem(
                factory: &Factory<'ctx, Self>,
                args: &SmtScope<'ctx>,
                prefix: &str,
            ) -> Self {
                fresh_skolem_application(factory, args, &$sort(factory), prefix)
                    .$cast()
                    .unwrap()
            }
        }
    };
}

z3_simple_fresh!(Bool, Sort::bool, as_bool);
z3_simple_fresh!(Int, Sort::int, as_int);
z3_simple_fresh!(Real, Sort::real, as_real);

impl<'ctx> SmtFresh<'ctx> for Dynamic<'ctx> {
    fn allocate(factory: &Factory<'ctx, Self>, scope: &mut SmtScope<'ctx>, prefix: &str) -> Self {
        let value = Dynamic::fresh_const(factory.0, prefix, &factory.1);
        scope.add_bound(&value);
        value
    }
}

impl<'ctx> SmtSkolem<'ctx> for Dynamic<'ctx> {
    fn allocate_skolem(factory: &Factory<'ctx, Self>, args: &SmtScope<'ctx>, prefix: &str) -> Self {
        fresh_skolem_application(factory.0, args, &factory.1, prefix)
    }
}

impl<'ctx> SmtFresh<'ctx> for Datatype<'ctx> {
    fn allocate(factory: &Factory<'ctx, Self>, scope: &mut SmtScope<'ctx>, prefix: &str) -> Self {
        let value = Datatype::fresh_const(factory.0, prefix, &factory.1);
        scope.add_bound(&value);
        value
    }
}

impl<'ctx> SmtSkolem<'ctx> for Datatype<'ctx> {
    fn allocate_skolem(factory: &Factory<'ctx, Self>, args: &SmtScope<'ctx>, prefix: &str) -> Self {
        fresh_skolem_application(factory.0, args, &factory.1, prefix)
            .as_datatype()
            .unwrap()
    }
}
