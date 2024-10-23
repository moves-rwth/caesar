use crate::scope::{SmtAlloc, SmtFresh};
use crate::{Factory, SmtFactory, SmtInvariant};
use std::rc::Rc;
use z3::ast::{Ast, Bool, Datatype, Dynamic};
use z3::{Context, DatatypeAccessor, DatatypeBuilder, FuncDecl, Sort, Symbol};

#[derive(Debug)]
pub struct FuelFactory<'ctx> {
    ctx: &'ctx Context,
    sort: Sort<'ctx>,
    zero: FuncDecl<'ctx>,
    succ: FuncDecl<'ctx>,
}

impl<'ctx> FuelFactory<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Rc<Self> {
        // TODO: How do we avoid clashes with user defined code?
        let datatype = DatatypeBuilder::new(ctx, "Fuel")
            .variant("Zero", vec![])
            .variant(
                "Succ",
                vec![("f", DatatypeAccessor::Datatype(Symbol::from("Fuel")))],
            )
            .finish();

        let mut variants = datatype.variants;
        let succ_variant = variants.pop().unwrap();
        let zero_variant = variants.pop().unwrap();

        let factory = Self {
            ctx,
            sort: datatype.sort,
            zero: zero_variant.constructor,
            succ: succ_variant.constructor,
        };
        Rc::new(factory)
    }

    pub fn sort(&self) -> &Sort<'ctx> {
        &self.sort
    }
}

/// Datatype representing peano numbers. Used to control how often quantifiers are instantiated.
/// Equivalent to the rust type:
/// ```
/// enum Fuel {
///      Zero,
///      Succ(Fuel)
/// }
/// ```
#[derive(Debug, Clone)]
pub struct Fuel<'ctx> {
    factory: Rc<FuelFactory<'ctx>>,
    value: Datatype<'ctx>,
}

impl<'ctx> Fuel<'ctx> {
    pub fn new(factory: Factory<'ctx, Self>, n: u32) -> Self {
        let mut fuel = Self::zero(factory);
        for _ in 0..n {
            fuel = Self::succ(fuel);
        }
        fuel
    }

    pub fn zero(factory: Factory<'ctx, Self>) -> Self {
        let value = factory.zero.apply(&[]).as_datatype().unwrap();

        Self { factory, value }
    }

    pub fn succ(fuel: Self) -> Self {
        let factory = fuel.factory;
        let value = factory
            .succ
            .apply(&[&fuel.value as &dyn Ast<'ctx>])
            .as_datatype()
            .unwrap();

        Self { factory, value }
    }

    pub fn as_dynamic(&self) -> Dynamic<'ctx> {
        Dynamic::from_ast(&self.value)
    }
}

impl<'ctx> SmtFactory<'ctx> for Fuel<'ctx> {
    type FactoryType = Rc<FuelFactory<'ctx>>;

    fn factory(&self) -> Factory<'ctx, Self> {
        self.factory.clone()
    }
}

impl<'ctx> SmtInvariant<'ctx> for Fuel<'ctx> {
    fn smt_invariant(&self) -> Option<Bool<'ctx>> {
        None
    }
}

impl<'ctx> SmtFresh<'ctx> for Fuel<'ctx> {
    fn allocate<'a>(
        factory: &Factory<'ctx, Self>,
        alloc: &mut SmtAlloc<'ctx, 'a>,
        prefix: &str,
    ) -> Self {
        let datatype_factory = (factory.ctx, factory.sort.clone());
        Fuel {
            factory: factory.clone(),
            value: Datatype::allocate(&datatype_factory, alloc, prefix),
        }
    }
}
