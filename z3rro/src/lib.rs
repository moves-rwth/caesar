//! We implement some of our own types and wrappers for SMT like [`EUReal`]
//! and [`UInt`]. For the creation of fresh variables of our new SMT types (as
//! well as Z3's built-in ones), we use the [`scope::SmtScope`] structure which
//! tracks "free" variables and associated constraints in a scope.
//! [`scope::SmtScope`] can be used to create existential and universal
//! quantifiers with constraints for variables. The [`scope::SmtFresh`] defines
//! an API to create new instances of SMT types in a scope. The constraints
//! for the "free" variables are required to encode types like non-negative
//! numbers in Z3.
//!
//! The [`orders`] module defines structures from order theory for our SMT
//! types. This module defines the interfaces to create SMT expressions for e.g.
//! partial orders ([`orders::SmtPartialOrd`]) or bi-Gödel algebras
//! ([`orders::SmtGodel`]).

#[macro_use]
pub mod util;
pub mod interpreted;
pub mod orders;
pub mod scope;

pub mod model;
pub mod pretty;
pub mod prover;
mod uint;
pub use uint::UInt;
mod ureal;
pub use ureal::UReal;
pub mod eureal;
pub use eureal::EUReal;
mod list;
pub use list::{List, ListFactory};

#[cfg(test)]
mod test;

use z3::{
    ast::{Array, Ast, Bool, Datatype, Dynamic, Float, Int, Real, Set, BV},
    Context, Sort,
};

/// SMT values who have an associated factory to create new values of its type.
pub trait SmtFactory<'ctx> {
    /// The value of the factory type. You'll probably use [`Factory`] most of the time.
    type FactoryType;

    /// Get a reference to the factory for this type.
    fn factory(&self) -> Factory<'ctx, Self>;
}

/// Type alias for a reference to the the factory type of an [`SmtAst`] type.
pub type Factory<'ctx, T> = <T as SmtFactory<'ctx>>::FactoryType;

// Many built-in Z3 AST object trivially implement [`SmtAst`].
macro_rules! z3_smt_ast {
    ($ty:ident) => {
        impl<'ctx> SmtFactory<'ctx> for $ty<'ctx> {
            type FactoryType = &'ctx Context;

            fn factory(&self) -> &'ctx Context {
                self.get_ctx()
            }
        }
    };
}

z3_smt_ast!(BV);
z3_smt_ast!(Bool);
z3_smt_ast!(Int);
z3_smt_ast!(Real);

#[derive(Debug, Clone)]
pub struct ArrayFactory<'ctx> {
    pub domain: Sort<'ctx>,
    pub range: Sort<'ctx>,
}

impl<'ctx> SmtFactory<'ctx> for Array<'ctx> {
    type FactoryType = ArrayFactory<'ctx>;

    fn factory(&self) -> Factory<'ctx, Self> {
        let sort = self.get_sort();
        ArrayFactory {
            domain: sort.array_domain().unwrap(),
            range: sort.array_range().unwrap(),
        }
    }
}

impl<'ctx> SmtFactory<'ctx> for Dynamic<'ctx> {
    type FactoryType = (&'ctx Context, Sort<'ctx>);

    fn factory(&self) -> Factory<'ctx, Self> {
        (self.get_ctx(), self.get_sort())
    }
}

impl<'ctx> SmtFactory<'ctx> for Datatype<'ctx> {
    type FactoryType = (&'ctx Context, Sort<'ctx>);

    fn factory(&self) -> Factory<'ctx, Self> {
        (self.get_ctx(), self.get_sort())
    }
}

/// SMT values whose equality can be tested.
pub trait SmtEq<'ctx>: Sized {
    /// Encode the given relation between `self` and `other`.
    fn smt_eq(&self, other: &Self) -> Bool<'ctx>;
}

/// Any built-in Z3 AST object trivially implements [`SmtEq`].
impl<'ctx, T: Ast<'ctx>> SmtEq<'ctx> for T {
    fn smt_eq(&self, other: &Self) -> Bool<'ctx> {
        self._eq(other)
    }
}

/// More general version of Z3's [`Bool::ite`]. Our [`SmtBranch::branch`] is not
/// restricted to types that implement [`z3::ast::Ast`].
pub trait SmtBranch<'ctx>: Sized {
    /// If `cond` evaluates to `true`, return `a`. Otherwise, return `b`.
    fn branch(cond: &Bool<'ctx>, a: &Self, b: &Self) -> Self;
}

/// All types that implement [`z3::ast::Ast`] can just use Z3's [`Bool::ite`].
impl<'ctx, T: Ast<'ctx>> SmtBranch<'ctx> for T {
    fn branch(cond: &Bool<'ctx>, a: &Self, b: &Self) -> Self {
        Bool::ite(cond, a, b)
    }
}

/// Many SMT types have associated _invariants_. These are Boolean constraints
/// that always hold for values.
///
/// For example, our type for non-negative real numbers ([`crate::UInt`]) uses a
/// representation based on Z3's [`z3::ast::Int`]. All values of that type
/// always satisfy that they are non-negative. This is the invariant provided by
/// this trait's function.
pub trait SmtInvariant<'ctx> {
    /// Return a Boolean expression that specifies whether a value of this type
    /// is valid. May be `None` if there is no invariant.
    fn smt_invariant(&self) -> Option<Bool<'ctx>>;
}

macro_rules! z3_smt_invariant {
    ($ty:tt) => {
        impl<'ctx> SmtInvariant<'ctx> for $ty<'ctx> {
            fn smt_invariant(&self) -> Option<Bool<'ctx>> {
                None
            }
        }
    };
}

z3_smt_invariant!(Array);
z3_smt_invariant!(BV);
z3_smt_invariant!(Bool);
z3_smt_invariant!(Datatype);
z3_smt_invariant!(Dynamic);
z3_smt_invariant!(Float);
z3_smt_invariant!(Int);
z3_smt_invariant!(Real);
z3_smt_invariant!(Set);
