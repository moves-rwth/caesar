//! Symbolic lists based on Z3's arrays.

use std::rc::Rc;

use z3::{
    ast::{Array, Ast, Bool, Datatype, Dynamic},
    Context, DatatypeAccessor, DatatypeBuilder, FuncDecl, Sort,
};

use crate::{
    orders::SmtPartialOrd,
    scope::{SmtAlloc, SmtFresh, SmtScope},
    Factory, SmtBranch, SmtEq, SmtFactory, SmtInvariant, UInt,
};

#[derive(Debug)]
pub struct ListFactory<'ctx> {
    ctx: &'ctx Context,
    element_sort: Sort<'ctx>,
    sort: Sort<'ctx>,
    list_mk: FuncDecl<'ctx>,
    list_len: FuncDecl<'ctx>,
    list_elements: FuncDecl<'ctx>,
}

impl<'ctx> ListFactory<'ctx> {
    pub fn new(ctx: &'ctx Context, element_sort: &Sort<'ctx>) -> Rc<Self> {
        let list_ty_name = format!("List[{}]", &element_sort);
        let datatype = DatatypeBuilder::new(ctx, &*list_ty_name)
            .variant(
                &format!("{}_list", &list_ty_name),
                vec![
                    (
                        &format!("{}_len", &list_ty_name),
                        DatatypeAccessor::Sort(Sort::int(ctx)),
                    ),
                    (
                        &format!("{}_elements", &list_ty_name),
                        DatatypeAccessor::Sort(Sort::array(ctx, &Sort::int(ctx), element_sort)),
                    ),
                ],
            )
            .finish();
        let mut variants = datatype.variants;
        let mut variant = variants.pop().unwrap();
        let list_elements = variant.accessors.pop().unwrap();
        let list_len = variant.accessors.pop().unwrap();
        let factory = ListFactory {
            ctx,
            element_sort: element_sort.clone(),
            sort: datatype.sort,
            list_mk: variant.constructor,
            list_len,
            list_elements,
        };
        Rc::new(factory)
    }

    pub fn element_sort(&self) -> &Sort<'ctx> {
        &self.element_sort
    }

    pub fn sort(&self) -> &Sort<'ctx> {
        &self.sort
    }
}

/// A symbolic list based on Z3 arrays, but with a length.
#[derive(Debug, Clone)]
pub struct List<'ctx> {
    factory: Rc<ListFactory<'ctx>>,
    value: Datatype<'ctx>,
}

impl<'ctx> List<'ctx> {
    pub fn new(factory: Factory<'ctx, Self>, len: &UInt<'ctx>, elements: Array<'ctx>) -> Self {
        let value = factory
            .list_mk
            .apply(&[len.as_int() as &dyn Ast<'ctx>, &elements as &dyn Ast<'ctx>])
            .as_datatype()
            .unwrap();
        List { factory, value }
    }

    pub fn from_dynamic(factory: Factory<'ctx, Self>, value: &Dynamic<'ctx>) -> Self {
        List {
            factory,
            value: value.as_datatype().unwrap(),
        }
    }

    pub fn len(&self) -> UInt<'ctx> {
        let len_dynamic = self.factory.list_len.apply(&[&self.value]);
        UInt::unchecked_from_int(len_dynamic.as_int().unwrap())
    }

    /// Get an element at a certain index.
    ///
    /// It's not checked whether the index is actually in the list bounds!
    pub fn get(&self, index: &UInt<'ctx>) -> Dynamic<'ctx> {
        let elements = self
            .factory
            .list_elements
            .apply(&[&self.value])
            .as_array()
            .unwrap();
        elements.select(index.as_int())
    }

    /// Set an element at a certain index.
    ///
    /// It's not checked whether the index is actually in the list bounds!
    pub fn set(&self, index: &UInt<'ctx>, value: &Dynamic<'ctx>) -> Self {
        let len = self.factory.list_len.apply(&[&self.value]);
        let elements = self
            .factory
            .list_elements
            .apply(&[&self.value])
            .as_array()
            .unwrap();
        let elements = elements.store(index.as_int(), value);
        List {
            factory: self.factory(),
            value: self
                .factory
                .list_mk
                .apply(&[&len, &elements])
                .as_datatype()
                .unwrap(),
        }
    }

    /// Return a Bool that asserts the index is in the list's bounds.
    pub fn is_valid_index(&self, index: &UInt<'ctx>) -> Bool<'ctx> {
        index.smt_le(&self.len())
    }

    pub fn as_dynamic(&self) -> Dynamic<'ctx> {
        Dynamic::from_ast(&self.value)
    }
}

impl<'ctx> SmtFactory<'ctx> for List<'ctx> {
    type FactoryType = Rc<ListFactory<'ctx>>;

    fn factory(&self) -> Factory<'ctx, Self> {
        self.factory.clone()
    }
}

impl<'ctx> SmtInvariant<'ctx> for List<'ctx> {
    fn smt_invariant(&self) -> Option<Bool<'ctx>> {
        self.len().smt_invariant()
    }
}

impl<'ctx> SmtFresh<'ctx> for List<'ctx> {
    fn allocate<'a>(
        factory: &Factory<'ctx, Self>,
        alloc: &mut SmtAlloc<'ctx, 'a>,
        prefix: &str,
    ) -> Self {
        let datatype_factory = (factory.ctx, factory.sort.clone());
        List {
            factory: factory.clone(),
            value: Datatype::allocate(&datatype_factory, alloc, prefix),
        }
    }
}

impl<'ctx> SmtEq<'ctx> for List<'ctx> {
    fn smt_eq(&self, other: &Self) -> Bool<'ctx> {
        let mut scope = SmtScope::new();
        let index = UInt::fresh(&self.len().factory(), &mut scope, "i");
        scope.add_constraint(&self.is_valid_index(&index));
        z3_and!(
            self.len().smt_eq(&other.len()),
            scope.forall(&[], &self.get(&index).smt_eq(&other.get(&index)))
        )
    }
}

impl<'ctx> SmtBranch<'ctx> for List<'ctx> {
    fn branch(cond: &Bool<'ctx>, a: &Self, b: &Self) -> Self {
        List {
            factory: a.factory(),
            value: Datatype::branch(cond, &a.value, &b.value),
        }
    }
}
