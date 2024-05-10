use std::ops::{Add, Div, Mul, Sub};

use num::BigRational;
use z3::{
    ast::{Ast, Bool, Real},
    Context,
};

use crate::{
    forward_binary_op,
    model::{InstrumentedModel, SmtEval, SmtEvalError},
    scope::SmtAlloc,
    Factory, SmtFactory, SmtInvariant, UInt,
};

use super::{
    orders::{SmtOrdering, SmtPartialOrd},
    scope::SmtFresh,
    SmtBranch, SmtEq,
};

/// Z3's [`Real`] type, but restricted to non-negative numbers.
#[derive(Debug, Clone)]
pub struct UReal<'ctx>(Real<'ctx>);

impl<'ctx> UReal<'ctx> {
    pub fn unchecked_from_real(value: Real<'ctx>) -> Self {
        UReal(value)
    }

    pub fn from_uint(value: &UInt<'ctx>) -> Self {
        UReal(Real::from_int(value.as_int()))
    }

    pub fn zero(factory: &Factory<'ctx, Self>) -> Self {
        UReal(Real::from_real(factory, 0, 1))
    }

    pub fn one(factory: &Factory<'ctx, Self>) -> Self {
        UReal(Real::from_real(factory, 1, 1))
    }

    pub fn as_real(&self) -> &Real<'ctx> {
        &self.0
    }

    pub fn into_real(self) -> Real<'ctx> {
        self.0
    }
}

impl<'ctx> SmtFactory<'ctx> for UReal<'ctx> {
    type FactoryType = &'ctx Context;

    fn factory(&self) -> Factory<'ctx, Self> {
        self.0.get_ctx()
    }
}

impl<'ctx> SmtInvariant<'ctx> for UReal<'ctx> {
    fn smt_invariant(&self) -> Option<Bool<'ctx>> {
        let zero = Real::from_real(self.0.get_ctx(), 0, 1);
        Some(self.0.ge(&zero))
    }
}

impl<'ctx> SmtFresh<'ctx> for UReal<'ctx> {
    fn allocate<'a>(
        factory: &Factory<'ctx, Self>,
        alloc: &mut SmtAlloc<'ctx, 'a>,
        prefix: &str,
    ) -> Self {
        let int = Real::fresh_const(factory, prefix);
        alloc.register_var(&int);
        UReal(int)
    }
}

impl<'ctx> SmtEq<'ctx> for UReal<'ctx> {
    fn smt_eq(&self, other: &Self) -> Bool<'ctx> {
        self.0._eq(&other.0)
    }
}

impl<'ctx> SmtBranch<'ctx> for UReal<'ctx> {
    fn branch(cond: &Bool<'ctx>, a: &Self, b: &Self) -> Self {
        UReal(Real::branch(cond, &a.0, &b.0))
    }
}

impl<'ctx> SmtPartialOrd<'ctx> for UReal<'ctx> {
    fn smt_cmp(&self, other: &Self, ordering: SmtOrdering) -> Bool<'ctx> {
        self.0.smt_cmp(&other.0, ordering)
    }
}

impl<'ctx> SmtEval<'ctx> for UReal<'ctx> {
    type Value = BigRational;

    fn eval(&self, model: &InstrumentedModel<'ctx>) -> Result<Self::Value, SmtEvalError> {
        self.0.eval(model)
    }
}

impl<'a, 'ctx> Add<&'a UReal<'ctx>> for &'a UReal<'ctx> {
    type Output = UReal<'ctx>;

    fn add(self, rhs: &'a UReal<'ctx>) -> Self::Output {
        UReal(&self.0 + &rhs.0)
    }
}

forward_binary_op!(UReal<'ctx>, UReal<'ctx>, UReal<'ctx>, Add, add, add);

impl<'a, 'ctx> Sub<&'a UReal<'ctx>> for &'a UReal<'ctx> {
    type Output = UReal<'ctx>;

    fn sub(self, rhs: &'a UReal<'ctx>) -> Self::Output {
        UReal(int_monus(&self.0, &rhs.0))
    }
}

forward_binary_op!(UReal<'ctx>, UReal<'ctx>, UReal<'ctx>, Sub, sub, sub);

impl<'a, 'ctx> Mul<&'a UReal<'ctx>> for &'a UReal<'ctx> {
    type Output = UReal<'ctx>;

    fn mul(self, rhs: &'a UReal<'ctx>) -> Self::Output {
        UReal(&self.0 * &rhs.0)
    }
}

forward_binary_op!(UReal<'ctx>, UReal<'ctx>, UReal<'ctx>, Mul, mul, mul);

impl<'a, 'ctx> Div<&'a UReal<'ctx>> for &'a UReal<'ctx> {
    type Output = UReal<'ctx>;

    fn div(self, rhs: &'a UReal<'ctx>) -> Self::Output {
        UReal(&self.0 / &rhs.0)
    }
}

forward_binary_op!(UReal<'ctx>, UReal<'ctx>, UReal<'ctx>, Div, div, div);

fn int_monus<'ctx>(lhs: &Real<'ctx>, rhs: &Real<'ctx>) -> Real<'ctx> {
    let zero = Real::from_real(lhs.get_ctx(), 0, 1);
    Bool::ite(&lhs.ge(rhs), &(lhs - rhs), &zero)
}

#[cfg(test)]
mod test {
    use super::UReal;

    use crate::{generate_smt_branch_tests, generate_smt_partial_ord_tests};

    generate_smt_branch_tests!(|ctx| ctx, UReal);

    generate_smt_partial_ord_tests!(|ctx| ctx, UReal);
}
