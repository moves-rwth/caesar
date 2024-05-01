//! Encoding of the EUReal type using SMT-LIB's user-defined datatypes.
#![allow(unused)]

use std::{
    ops::{Add, Mul, Sub},
    rc::Rc,
};

use once_cell::unsync;
use z3::{
    ast::{Ast, Bool, Datatype, Dynamic},
    Context, DatatypeAccessor, DatatypeBuilder, FuncDecl, Model, RecFuncDecl, Sort,
};

use crate::{
    eureal::ConcreteEUReal,
    forward_binary_op,
    interpreted::FuncDef,
    model::{InstrumentedModel, SmtEval, SmtEvalError},
    orders::{
        smt_max, smt_min, SmtCompleteLattice, SmtGodel, SmtLattice, SmtOrdering, SmtPartialOrd,
    },
    scope::{SmtAlloc, SmtFresh},
    uint::UInt,
    Factory, SmtBranch, SmtEq, SmtFactory, SmtInvariant, UReal,
};

/// This structure saves the necessary Z3 objects to construct and work with
/// values of our SMT-LIB datatype for EUReal.
#[derive(Debug)]
pub struct EURealFactory<'ctx> {
    ctx: &'ctx Context,
    sort: Sort<'ctx>,
    rplus_mk_inf: FuncDecl<'ctx>,
    rplus_is_inf: FuncDecl<'ctx>,
    rplus_mk_real: FuncDecl<'ctx>,
    rplus_is_real: FuncDecl<'ctx>,
    rplus_get_real: FuncDecl<'ctx>,
    late: unsync::OnceCell<EURealLateDefs<'ctx>>,
}

impl<'ctx> EURealFactory<'ctx> {
    /// Declare a new `EUReal` datatype in this context and return the
    /// datatype object.
    pub fn new(ctx: &'ctx Context) -> Rc<Self> {
        let datatype = DatatypeBuilder::new(ctx, "EUReal")
            .variant("Rplus_inf", vec![])
            .variant(
                "Rplus_real",
                vec![("rplus_real", DatatypeAccessor::Sort(Sort::real(ctx)))],
            )
            .finish();

        let mut variants = datatype.variants;
        let mut real_variant = variants.pop().unwrap();
        let inf_variant = variants.pop().unwrap();
        let factory = EURealFactory {
            ctx,
            sort: datatype.sort,
            rplus_mk_inf: inf_variant.constructor,
            rplus_is_inf: inf_variant.tester,
            rplus_mk_real: real_variant.constructor,
            rplus_is_real: real_variant.tester,
            rplus_get_real: real_variant.accessors.pop().unwrap(),
            late: unsync::OnceCell::new(),
        };
        let factory = Rc::new(factory);
        factory.late.set(EURealLateDefs::new(&factory)).unwrap();
        factory
    }

    pub fn sort(&self) -> &Sort<'ctx> {
        &self.sort
    }

    #[cfg(feature = "datatype-eureal-funcs")]
    fn late(&self) -> &EURealLateDefs<'ctx> {
        self.late
            .get()
            .expect("late definitions are not yet initialized")
    }
}

/// This representation of EUReal values uses values of a custom datatype.
/// Values are either infinite or a (non-negative) real number.
#[derive(Debug, Clone)]
pub struct EUReal<'ctx> {
    factory: Rc<EURealFactory<'ctx>>,
    /// The actual value is just a single Z3 AST object.
    value: Datatype<'ctx>,
}

impl<'ctx> EUReal<'ctx> {
    fn fresh_unconstrained(factory: &Factory<'ctx, Self>, prefix: &str) -> Self {
        let value = Datatype::fresh_const(factory.ctx, prefix, &factory.sort);
        EUReal {
            factory: factory.clone(),
            value,
        }
    }

    pub fn infinity(factory: &Factory<'ctx, Self>) -> Self {
        let value = factory.rplus_mk_inf.apply(&[]).as_datatype().unwrap();
        EUReal {
            factory: factory.clone(),
            value,
        }
    }

    pub fn is_infinity(&self) -> Bool<'ctx> {
        self.factory
            .rplus_is_inf
            .apply(&[&self.value])
            .as_bool()
            .unwrap()
    }

    pub fn zero(factory: &Factory<'ctx, Self>) -> Self {
        Self::from_ureal(factory, &UReal::zero(&factory.ctx))
    }

    pub fn from_ureal(factory: &Factory<'ctx, Self>, ast: &UReal<'ctx>) -> Self {
        let value = factory
            .rplus_mk_real
            .apply(&[ast.as_real()])
            .as_datatype()
            .unwrap();
        EUReal {
            factory: factory.clone(),
            value,
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

    pub fn is_real(&self) -> Bool<'ctx> {
        self.factory
            .rplus_is_real
            .apply(&[&self.value])
            .as_bool()
            .unwrap()
    }

    pub fn get_ureal(&self) -> UReal<'ctx> {
        let real = self
            .factory
            .rplus_get_real
            .apply(&[&self.value])
            .as_real()
            .unwrap();
        UReal::unchecked_from_real(real)
    }

    pub fn from_dynamic(factory: &Factory<'ctx, Self>, val: &Dynamic<'ctx>) -> Self {
        EUReal {
            factory: factory.clone(),
            value: val.as_datatype().unwrap(),
        }
    }

    pub fn as_dynamic(&self) -> Dynamic<'ctx> {
        Dynamic::from(self.value.clone())
    }
}

impl<'ctx> SmtFactory<'ctx> for EUReal<'ctx> {
    type FactoryType = Rc<EURealFactory<'ctx>>;

    fn factory(&self) -> Factory<'ctx, Self> {
        self.factory.clone()
    }
}

impl<'ctx> SmtInvariant<'ctx> for EUReal<'ctx> {
    fn smt_invariant(&self) -> Option<Bool<'ctx>> {
        self.get_ureal().smt_invariant()
    }
}

impl<'ctx> SmtFresh<'ctx> for EUReal<'ctx> {
    fn allocate<'a>(
        factory: &Factory<'ctx, Self>,
        alloc: &mut SmtAlloc<'ctx, 'a>,
        prefix: &str,
    ) -> Self {
        let value = Datatype::fresh_const(factory.ctx, prefix, &factory.sort);
        alloc.register_var(&value);
        EUReal {
            factory: factory.clone(),
            value,
        }
    }
}

impl<'ctx> SmtEq<'ctx> for EUReal<'ctx> {
    fn smt_eq(&self, other: &Self) -> Bool<'ctx> {
        self.value._eq(&other.value)
    }
}

impl<'ctx> SmtBranch<'ctx> for EUReal<'ctx> {
    fn branch(cond: &Bool<'ctx>, a: &Self, b: &Self) -> Self {
        EUReal {
            factory: a.factory.clone(),
            value: Bool::ite(cond, &a.value, &b.value),
        }
    }
}

impl<'ctx> SmtEval<'ctx> for EUReal<'ctx> {
    type Value = ConcreteEUReal;

    fn eval(&self, model: &InstrumentedModel<'ctx>) -> Result<Self::Value, SmtEvalError> {
        let is_infinite = self.is_infinity().eval(model)?;
        if is_infinite {
            Ok(ConcreteEUReal::Infinity)
        } else {
            let real = self.get_ureal().eval(model)?;
            Ok(ConcreteEUReal::Real(real))
        }
    }
}

#[derive(Debug)]
struct EURealLateDefs<'ctx> {
    rplus_le: FuncDef<'ctx>,
    rplus_add: FuncDef<'ctx>,
    rplus_sub: FuncDef<'ctx>,
    rplus_mul: FuncDef<'ctx>,
}

impl<'ctx> EURealLateDefs<'ctx> {
    fn new(factory: &Factory<'ctx, EUReal<'ctx>>) -> Self {
        Self {
            rplus_le: eureal_rel_def(factory, "rplus_le", eureal_le),
            rplus_add: eureal_binop_def(factory, "rplus_add", eureal_add),
            rplus_sub: eureal_binop_def(factory, "rplus_sub", eureal_sub),
            rplus_mul: eureal_binop_def(factory, "rplus_mul", eureal_mul),
        }
    }
}

fn eureal_rel_def<'ctx>(
    factory: &Factory<'ctx, EUReal<'ctx>>,
    name: &str,
    bin_op: impl FnOnce(&EUReal<'ctx>, &EUReal<'ctx>) -> Bool<'ctx>,
) -> FuncDef<'ctx> {
    let a = EUReal::fresh_unconstrained(factory, "a");
    let b = EUReal::fresh_unconstrained(factory, "b");
    FuncDef::new(
        name,
        &[&Dynamic::from_ast(&a.value), &Dynamic::from_ast(&b.value)],
        &Dynamic::from_ast(&bin_op(&a, &b)),
    )
}

#[cfg(feature = "datatype-eureal-funcs")]
fn eureal_rel_apply<'ctx>(func: &FuncDef<'ctx>, a: &EUReal<'ctx>, b: &EUReal<'ctx>) -> Bool<'ctx> {
    func.apply_call(&[&Dynamic::from_ast(&a.value), &Dynamic::from_ast(&b.value)])
        .as_bool()
        .unwrap()
}

fn eureal_binop_def<'ctx>(
    factory: &Factory<'ctx, EUReal<'ctx>>,
    name: &str,
    bin_op: impl FnOnce(&EUReal<'ctx>, &EUReal<'ctx>) -> EUReal<'ctx>,
) -> FuncDef<'ctx> {
    let a = EUReal::fresh_unconstrained(factory, "a");
    let b = EUReal::fresh_unconstrained(factory, "b");
    FuncDef::new(
        name,
        &[&Dynamic::from_ast(&a.value), &Dynamic::from_ast(&b.value)],
        &Dynamic::from_ast(&bin_op(&a, &b).value),
    )
}

#[cfg(feature = "datatype-eureal-funcs")]
fn eureal_binop_apply<'ctx>(
    func: &FuncDef<'ctx>,
    a: &EUReal<'ctx>,
    b: &EUReal<'ctx>,
) -> EUReal<'ctx> {
    let value = func
        .apply_call(&[&Dynamic::from_ast(&a.value), &Dynamic::from_ast(&b.value)])
        .as_datatype()
        .unwrap();
    EUReal {
        factory: a.factory.clone(),
        value,
    }
}

fn eureal_le<'ctx>(a: &EUReal<'ctx>, b: &EUReal<'ctx>) -> Bool<'ctx> {
    z3_or!(
        b.is_infinity(),
        z3_and!(a.is_real(), a.get_ureal().smt_le(&b.get_ureal()))
    )
}

fn eureal_add<'ctx>(a: &EUReal<'ctx>, b: &EUReal<'ctx>) -> EUReal<'ctx> {
    let either_infinite = Bool::or(a.factory.ctx, &[&a.is_infinity(), &b.is_infinity()]);
    let infinity = EUReal::infinity(&a.factory);
    let values_added = EUReal::from_ureal(&a.factory, &(a.get_ureal() + b.get_ureal()));
    EUReal::branch(&either_infinite, &infinity, &values_added)
}

fn eureal_sub<'ctx>(a: &EUReal<'ctx>, b: &EUReal<'ctx>) -> EUReal<'ctx> {
    let zero = EUReal::zero(&a.factory);
    let infinity = EUReal::infinity(&a.factory);
    // TODO: this doesn't ensure the resulting value is >= 0
    let values_subtracted = EUReal::from_ureal(&a.factory, &(a.get_ureal() - b.get_ureal()));
    EUReal::branch(
        &b.is_infinity(),
        &zero,
        &EUReal::branch(&a.is_infinity(), &infinity, &values_subtracted),
    )
}

fn eureal_mul<'ctx>(a: &EUReal<'ctx>, b: &EUReal<'ctx>) -> EUReal<'ctx> {
    let is_both_finite = Bool::and(a.factory.ctx, &[&a.is_real(), &b.is_real()]);
    let values_mul = EUReal::from_ureal(&a.factory, &(a.get_ureal() * b.get_ureal()));
    let zero = EUReal::zero(&a.factory);
    let is_result_zero = z3_or!(
        z3_and!(a.is_infinity(), b.value._eq(&zero.value)),
        z3_and!(b.is_infinity(), a.value._eq(&zero.value)),
    );
    let infinity = EUReal::infinity(&a.factory);
    EUReal::branch(
        &is_both_finite,
        &values_mul,
        &EUReal::branch(&is_result_zero, &zero, &infinity),
    )
}

impl<'a, 'ctx> Add<&'a EUReal<'ctx>> for &'a EUReal<'ctx> {
    type Output = EUReal<'ctx>;

    fn add(self, rhs: &'a EUReal<'ctx>) -> Self::Output {
        cfg_if::cfg_if! {
            if #[cfg(feature = "datatype-eureal-funcs")] {
                eureal_binop_apply(&self.factory.late().rplus_add, self, rhs)
            } else {
                eureal_add(self, rhs)
            }
        }
    }
}

forward_binary_op!(EUReal<'ctx>, EUReal<'ctx>, EUReal<'ctx>, Add, add, add);

impl<'a, 'ctx> Sub<&'a EUReal<'ctx>> for &'a EUReal<'ctx> {
    type Output = EUReal<'ctx>;

    fn sub(self, rhs: &'a EUReal<'ctx>) -> Self::Output {
        cfg_if::cfg_if! {
            if #[cfg(feature = "datatype-eureal-funcs")] {
                eureal_binop_apply(&self.factory.late().rplus_sub, self, rhs)
            } else {
                eureal_sub(self, rhs)
            }
        }
    }
}

forward_binary_op!(EUReal<'ctx>, EUReal<'ctx>, EUReal<'ctx>, Sub, sub, sub);

impl<'a, 'ctx> Mul<&'a EUReal<'ctx>> for &'a EUReal<'ctx> {
    type Output = EUReal<'ctx>;

    fn mul(self, rhs: &'a EUReal<'ctx>) -> Self::Output {
        cfg_if::cfg_if! {
            if #[cfg(feature = "datatype-eureal-funcs")] {
                eureal_binop_apply(&self.factory.late().rplus_mul, self, rhs)
            } else {
                eureal_mul(self, rhs)
            }
        }
    }
}

forward_binary_op!(EUReal<'ctx>, EUReal<'ctx>, EUReal<'ctx>, Mul, mul, mul);

impl<'ctx> SmtPartialOrd<'ctx> for EUReal<'ctx> {
    fn smt_cmp(&self, other: &Self, ordering: SmtOrdering) -> Bool<'ctx> {
        cfg_if::cfg_if! {
            if #[cfg(feature = "datatype-eureal-funcs")] {
                let le = eureal_rel_apply(&self.factory.late().rplus_le, self, other);
            } else {
                let le = eureal_le(self, other);
            }
        }
        let eq = self.value._eq(&other.value);
        match ordering {
            SmtOrdering::Less => z3_and!(le, eq.not()),
            SmtOrdering::LessOrEqual => le,
            SmtOrdering::Equal => eq,
            SmtOrdering::GreaterOrEqual => z3_or!(le.not(), eq),
            SmtOrdering::Greater => le.not(),
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
