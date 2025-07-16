use crate::scope::{SmtAlloc, SmtFresh};
use crate::{Factory, SmtFactory, SmtInvariant};
use std::rc::Rc;
use z3::ast::{Ast, Bool, Dynamic};
use z3::{Context, FuncDecl, Sort, Symbol};

#[derive(Debug)]
pub struct FuelFactory<'ctx> {
    ctx: &'ctx Context,
    sort: Sort<'ctx>,
    zero: FuncDecl<'ctx>,
    succ: FuncDecl<'ctx>,
}

impl<'ctx> FuelFactory<'ctx> {
    #[cfg(feature = "datatype-fuel")]
    pub fn new(ctx: &'ctx Context) -> Rc<Self> {
        use z3::{DatatypeAccessor, DatatypeBuilder};

        // Clashes with user defined code are avoided by `$` in names
        let datatype = DatatypeBuilder::new(ctx, "$Fuel")
            .variant("$FZ", vec![])
            .variant(
                "$FS",
                vec![("f", DatatypeAccessor::Datatype(Symbol::from("$Fuel")))],
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

    #[cfg(not(feature = "datatype-fuel"))]
    pub fn new(ctx: &'ctx Context) -> Rc<Self> {
        // Clashes with user defined code are avoided by `$` in names
        let fuel_sort = Sort::uninterpreted(ctx, Symbol::from("$Fuel"));
        let zero = FuncDecl::new(ctx, "$Z", &[], &fuel_sort);
        let succ = FuncDecl::new(ctx, "$S", &[&fuel_sort], &fuel_sort);

        let factory = Self {
            ctx,
            sort: fuel_sort,
            zero,
            succ,
        };
        Rc::new(factory)
    }

    pub fn sort(&self) -> &Sort<'ctx> {
        &self.sort
    }
}

/// Datatype representing Peano numbers. Used to control how often quantifiers are instantiated.
/// Equivalent to the rust type:
/// ```
/// enum Fuel {
///      Zero,
///      Succ(Box<Fuel>)
/// }
/// ```
#[derive(Debug, Clone)]
pub struct Fuel<'ctx> {
    factory: Rc<FuelFactory<'ctx>>,
    value: Dynamic<'ctx>,
}

impl<'ctx> Fuel<'ctx> {
    /// Create a new fuel value from constant `n`.
    pub fn from_constant(factory: &Factory<'ctx, Self>, n: usize) -> Self {
        let mut fuel = Self::zero(factory);
        for _ in 0..n {
            fuel = Self::succ(fuel);
        }
        fuel
    }

    /// Zero fuel.
    pub fn zero(factory: &Factory<'ctx, Self>) -> Self {
        let value = factory.zero.apply(&[]);
        Self {
            factory: factory.clone(),
            value,
        }
    }

    /// Increment the fuel value by one.
    pub fn succ(fuel: Self) -> Self {
        let factory = fuel.factory;
        let value = factory.succ.apply(&[&fuel.value as &dyn Ast<'ctx>]);
        Self { factory, value }
    }

    /// If the fuel variable is not a literal, extract the free variable inside
    /// this fuel expression. If it is a literal, return `None`.
    pub fn extract_var(&self) -> Option<Fuel<'ctx>> {
        let mut ast = self.value.clone();
        while !ast.is_const() {
            assert_eq!(ast.num_children(), 1);
            debug_assert_eq!(ast.decl().name(), self.factory.succ.name());
            ast = ast.nth_child(0).unwrap();
        }
        if ast.decl().name() == self.factory.zero.name() {
            None
        } else {
            Some(Fuel {
                factory: self.factory.clone(),
                value: ast,
            })
        }
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
            value: Dynamic::allocate(&datatype_factory, alloc, prefix),
        }
    }
}
