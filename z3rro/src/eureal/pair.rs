//! Encoding of the EUReal type as a pair of two values: a Boolean value
//! indicating whether the value is infinite and a real number with the value.
//! This encoding does not use datatype declarations or custom sorts.

use std::ops::{Add, Mul, Sub};

use z3::{ast::Bool, Context};

use crate::model::{InstrumentedModel, SmtEval, SmtEvalError};
use crate::{forward_binary_op, scope::SmtAlloc, Factory, SmtEq, SmtFactory, SmtInvariant, UReal};

use crate::{
    orders::{
        smt_max, smt_min, SmtCompleteLattice, SmtGodel, SmtLattice, SmtOrdering, SmtPartialOrd,
    },
    scope::SmtFresh,
    uint::UInt,
    SmtBranch,
};

use super::ConcreteEUReal;

#[derive(Debug, Clone)]
pub struct EURealFactory<'ctx> {
    ctx: &'ctx Context,
}

impl<'ctx> EURealFactory<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        EURealFactory { ctx }
    }
}

/// A EUReal value represented by a Boolean value indicating whether the value
/// is infinite and a non-negative real number with the value.
#[derive(Debug, Clone)]
pub struct EUReal<'ctx> {
    factory: EURealFactory<'ctx>,
    is_infinite: Bool<'ctx>,
    number: UReal<'ctx>,
}

impl<'ctx> EUReal<'ctx> {
    pub fn infinity(factory: &Factory<'ctx, Self>) -> Self {
        EUReal {
            factory: factory.clone(),
            is_infinite: Bool::from_bool(factory.ctx, true),
            number: UReal::one(&factory.ctx),
        }
    }

    pub fn is_infinity(&self) -> &Bool<'ctx> {
        &self.is_infinite
    }

    pub fn zero(factory: &Factory<'ctx, Self>) -> Self {
        Self::from_ureal(factory, &UReal::zero(&factory.ctx))
    }

    pub fn from_ureal(factory: &Factory<'ctx, Self>, value: &UReal<'ctx>) -> Self {
        EUReal {
            factory: factory.clone(),
            is_infinite: Bool::from_bool(factory.ctx, false),
            number: value.clone(),
        }
    }

    pub fn iverson(factory: &Factory<'ctx, Self>, cond: &Bool<'ctx>) -> Self {
        EUReal::branch(
            cond,
            &EUReal::from_ureal(factory, &UReal::one(&factory.ctx)),
            &EUReal::zero(factory),
        )
    }

    pub fn from_uint(factory: &Factory<'ctx, Self>, value: &UInt<'ctx>) -> Self {
        EUReal::from_ureal(factory, &UReal::from_uint(value))
    }

    pub fn get_ureal(&self) -> &UReal<'ctx> {
        &self.number
    }
}

impl<'ctx> SmtFactory<'ctx> for EUReal<'ctx> {
    type FactoryType = EURealFactory<'ctx>;

    fn factory(&self) -> Factory<'ctx, Self> {
        self.factory.clone()
    }
}

impl<'ctx> SmtInvariant<'ctx> for EUReal<'ctx> {
    fn smt_invariant(&self) -> Option<Bool<'ctx>> {
        let number_inv = self.number.smt_invariant().unwrap();
        let one = UReal::one(&self.factory.ctx);
        let if_inf_then_val_one = self.is_infinite.implies(&self.number.smt_eq(&one));
        Some(z3_and!(number_inv, if_inf_then_val_one))
    }
}

impl<'ctx> SmtFresh<'ctx> for EUReal<'ctx> {
    fn allocate<'a>(
        factory: &Factory<'ctx, Self>,
        alloc: &mut SmtAlloc<'ctx, 'a>,
        prefix: &str,
    ) -> Self {
        let is_infinite = Bool::fresh_const(factory.ctx, prefix);
        alloc.register_var(&is_infinite);
        let number = UReal::allocate(&factory.ctx, alloc, prefix);
        EUReal {
            factory: factory.clone(),
            is_infinite,
            number,
        }
    }
}

impl<'ctx> SmtBranch<'ctx> for EUReal<'ctx> {
    fn branch(cond: &Bool<'ctx>, a: &Self, b: &Self) -> Self {
        EUReal {
            factory: a.factory.clone(),
            is_infinite: Bool::ite(cond, &a.is_infinite, &b.is_infinite),
            number: SmtBranch::branch(cond, &a.number, &b.number),
        }
    }
}

impl<'ctx> SmtEval<'ctx> for EUReal<'ctx> {
    type Value = ConcreteEUReal;

    fn eval(&self, model: &InstrumentedModel<'ctx>) -> Result<Self::Value, SmtEvalError> {
        let is_infinite = self.is_infinite.eval(model)?;
        // we evaluate the number even if the value is infinite. this is so the
        // instrumented model tracks the access and we don't have a (logically
        // falsely) unaccessed value left over in the model.
        let real = self.number.eval(model)?;
        if is_infinite {
            Ok(ConcreteEUReal::Infinity)
        } else {
            Ok(ConcreteEUReal::Real(real))
        }
    }
}

impl<'a, 'ctx> Add<&'a EUReal<'ctx>> for &'a EUReal<'ctx> {
    type Output = EUReal<'ctx>;

    fn add(self, rhs: &'a EUReal<'ctx>) -> Self::Output {
        EUReal {
            factory: self.factory.clone(),
            is_infinite: z3_or!(&self.is_infinite, &rhs.is_infinite),
            number: &self.number + &rhs.number,
        }
    }
}

forward_binary_op!(EUReal<'ctx>, EUReal<'ctx>, EUReal<'ctx>, Add, add, add);

impl<'a, 'ctx> Sub<&'a EUReal<'ctx>> for &'a EUReal<'ctx> {
    type Output = EUReal<'ctx>;

    fn sub(self, rhs: &'a EUReal<'ctx>) -> Self::Output {
        EUReal {
            factory: self.factory.clone(),
            is_infinite: z3_and!(&self.is_infinite, &rhs.is_infinite.not()),
            number: &self.number - &rhs.number,
        }
    }
}

forward_binary_op!(EUReal<'ctx>, EUReal<'ctx>, EUReal<'ctx>, Sub, sub, sub);

impl<'a, 'ctx> Mul<&'a EUReal<'ctx>> for &'a EUReal<'ctx> {
    type Output = EUReal<'ctx>;

    fn mul(self, rhs: &'a EUReal<'ctx>) -> Self::Output {
        let zero = UReal::zero(&self.factory.ctx);
        let a_nonzero = z3_or!(&self.is_infinite, &self.number.smt_eq(&zero).not());
        let b_nonzero = z3_or!(&rhs.is_infinite, &rhs.number.smt_eq(&zero).not());
        EUReal {
            factory: self.factory.clone(),
            is_infinite: z3_or!(
                z3_and!(&self.is_infinite, &b_nonzero),
                z3_and!(&rhs.is_infinite, &a_nonzero)
            ),
            number: &self.number * &rhs.number,
        }
    }
}

forward_binary_op!(EUReal<'ctx>, EUReal<'ctx>, EUReal<'ctx>, Mul, mul, mul);

impl<'ctx> SmtEq<'ctx> for EUReal<'ctx> {
    fn smt_eq(&self, other: &Self) -> Bool<'ctx> {
        z3_and!(
            self.is_infinite._eq(&other.is_infinite),
            z3_or!(self.is_infinite.not(), other.is_infinite.not())
                .implies(&self.number.smt_eq(&other.number))
        )
    }
}

impl<'ctx> SmtPartialOrd<'ctx> for EUReal<'ctx> {
    fn smt_cmp(&self, other: &Self, ordering: SmtOrdering) -> Bool<'ctx> {
        fn eureal_le<'ctx>(a: &EUReal<'ctx>, b: &EUReal<'ctx>) -> Bool<'ctx> {
            z3_or!(
                &b.is_infinite,
                &z3_and!(&a.is_infinite.not(), &a.number.smt_le(&b.number))
            )
        }

        match ordering {
            SmtOrdering::Less => eureal_le(other, self).not(),
            SmtOrdering::LessOrEqual => eureal_le(self, other),
            SmtOrdering::Equal => self.smt_eq(other),
            SmtOrdering::GreaterOrEqual => eureal_le(other, self),
            SmtOrdering::Greater => eureal_le(self, other).not(),
        }
    }
}

impl<'ctx> SmtLattice<'ctx> for EUReal<'ctx> {
    fn bot(factory: &Factory<'ctx, Self>) -> Self {
        Self::from_ureal(factory, &UReal::zero(&factory.ctx))
    }

    fn top(factory: &Factory<'ctx, Self>) -> Self {
        Self::infinity(factory)
    }

    fn inf(&self, other: &Self) -> Self {
        smt_min(self, other)
    }

    fn sup(&self, other: &Self) -> Self {
        smt_max(self, other)
    }
}

impl<'ctx> SmtGodel<'ctx> for EUReal<'ctx> {}

impl<'ctx> SmtCompleteLattice<'ctx> for EUReal<'ctx> {}

#[cfg(test)]
mod test {
    use super::{EUReal, EURealFactory};

    use crate::{generate_smt_branch_tests, generate_smt_partial_ord_tests};

    generate_smt_branch_tests!(|ctx| EURealFactory::new(ctx), EUReal);

    generate_smt_partial_ord_tests!(|ctx| EURealFactory::new(ctx), EUReal);
}
