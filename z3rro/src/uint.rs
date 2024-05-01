use std::ops::{Add, Mul, Sub};

use num::BigInt;
use z3::{
    ast::{Ast, Bool, Int},
    Context,
};

use crate::{
    forward_binary_op,
    model::{InstrumentedModel, SmtEval, SmtEvalError},
    scope::SmtAlloc,
    Factory, SmtFactory, SmtInvariant,
};

use super::{
    orders::{SmtOrdering, SmtPartialOrd},
    scope::SmtFresh,
    SmtBranch, SmtEq,
};

/// Z3's [`Int`] type, but restricted to non-negative numbers.
#[derive(Debug, Clone)]
pub struct UInt<'ctx>(Int<'ctx>);

impl<'ctx> UInt<'ctx> {
    pub fn from_u64(ctx: &'ctx Context, value: u64) -> Self {
        UInt(Int::from_u64(ctx, value))
    }

    pub fn unchecked_from_int(value: Int<'ctx>) -> Self {
        UInt(value)
    }

    pub fn as_int(&self) -> &Int<'ctx> {
        &self.0
    }

    pub fn into_int(self) -> Int<'ctx> {
        self.0
    }

    pub fn modulo(&self, other: &Self) -> Self {
        UInt(self.0.modulo(&other.0))
    }
}

impl<'ctx> SmtFactory<'ctx> for UInt<'ctx> {
    type FactoryType = &'ctx Context;

    fn factory(&self) -> Factory<'ctx, Self> {
        self.0.get_ctx()
    }
}

impl<'ctx> SmtInvariant<'ctx> for UInt<'ctx> {
    fn smt_invariant(&self) -> Option<Bool<'ctx>> {
        let zero = Int::from_u64(self.0.get_ctx(), 0);
        Some(self.0.ge(&zero))
    }
}

impl<'ctx> SmtFresh<'ctx> for UInt<'ctx> {
    fn allocate<'a>(
        factory: &Factory<'ctx, Self>,
        alloc: &mut SmtAlloc<'ctx, 'a>,
        prefix: &str,
    ) -> Self {
        let int = Int::fresh_const(factory, prefix);
        alloc.register_var(&int);
        UInt(int)
    }
}

impl<'ctx> SmtEq<'ctx> for UInt<'ctx> {
    fn smt_eq(&self, other: &Self) -> Bool<'ctx> {
        self.0._eq(&other.0)
    }
}

impl<'ctx> SmtBranch<'ctx> for UInt<'ctx> {
    fn branch(cond: &Bool<'ctx>, a: &Self, b: &Self) -> Self {
        UInt(Int::branch(cond, &a.0, &b.0))
    }
}

impl<'ctx> SmtPartialOrd<'ctx> for UInt<'ctx> {
    fn smt_cmp(&self, other: &Self, ordering: SmtOrdering) -> Bool<'ctx> {
        self.0.smt_cmp(&other.0, ordering)
    }
}

impl<'ctx> SmtEval<'ctx> for UInt<'ctx> {
    type Value = BigInt;

    fn eval(&self, model: &InstrumentedModel<'ctx>) -> Result<BigInt, SmtEvalError> {
        self.0.eval(model)
    }
}

impl<'a, 'ctx> Add<&'a UInt<'ctx>> for &'a UInt<'ctx> {
    type Output = UInt<'ctx>;

    fn add(self, rhs: &'a UInt<'ctx>) -> Self::Output {
        UInt(&self.0 + &rhs.0)
    }
}

forward_binary_op!(UInt<'ctx>, UInt<'ctx>, UInt<'ctx>, Add, add, add);

impl<'a, 'ctx> Sub<&'a UInt<'ctx>> for &'a UInt<'ctx> {
    type Output = UInt<'ctx>;

    fn sub(self, rhs: &'a UInt<'ctx>) -> Self::Output {
        UInt(int_monus(&self.0, &rhs.0))
    }
}

forward_binary_op!(UInt<'ctx>, UInt<'ctx>, UInt<'ctx>, Sub, sub, sub);

impl<'a, 'ctx> Mul<&'a UInt<'ctx>> for &'a UInt<'ctx> {
    type Output = UInt<'ctx>;

    fn mul(self, rhs: &'a UInt<'ctx>) -> Self::Output {
        UInt(&self.0 * &rhs.0)
    }
}

forward_binary_op!(UInt<'ctx>, UInt<'ctx>, UInt<'ctx>, Mul, mul, mul);

fn int_monus<'ctx>(lhs: &Int<'ctx>, rhs: &Int<'ctx>) -> Int<'ctx> {
    Bool::ite(&lhs.ge(rhs), &(lhs - rhs), &Int::from_u64(lhs.get_ctx(), 0))
}

#[cfg(test)]
mod test {
    use super::UInt;

    use crate::{
        generate_smt_branch_tests, generate_smt_partial_ord_tests,
        scope::{SmtFresh, SmtScope},
        test::test_prove,
        SmtEq,
    };

    generate_smt_branch_tests!(|ctx| ctx, UInt);

    generate_smt_partial_ord_tests!(|ctx| ctx, UInt);

    #[test]
    fn test_exclude_negatives() {
        // prove that there is no `x` such that x + 1 == 0.
        test_prove(|ctx, _scope| {
            let mut inner_scope = SmtScope::new();
            let zero = UInt::from_u64(ctx, 0);
            let one = UInt::from_u64(ctx, 1);
            let x = UInt::fresh(&ctx, &mut inner_scope, "x");
            inner_scope.exists(&[], &(x + one).smt_eq(&zero)).not()
        });
    }
}
