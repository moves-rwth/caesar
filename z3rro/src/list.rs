//! Symbolic lists based on Z3's arrays.

use std::{
    collections::BTreeMap,
    collections::HashSet,
    fmt::{self, Display},
    rc::Rc,
    sync::Mutex,
};

use num::{BigInt, ToPrimitive};
use once_cell::sync::Lazy;
use z3::{
    ast::{Array, Ast, Bool, Datatype, Dynamic},
    Context, DatatypeAccessor, DatatypeBuilder, FuncDecl, Sort,
};

use crate::{
    array::ConcreteArrayValue,
    model::{InstrumentedModel, SmtEval, SmtEvalError},
    orders::{SmtOrdering, SmtPartialOrd},
    quantifiers::QuantifierMeta,
    scope::{SmtFresh, SmtScope},
    util::parse_big_int,
    Factory, SmtBranch, SmtEq, SmtFactory, SmtInvariant, UInt,
};

const LIST_PREVIEW_LIMIT: usize = 16;

static REGISTERED_LIST_SORTS: Lazy<Mutex<HashSet<(usize, usize)>>> =
    Lazy::new(|| Mutex::new(HashSet::new()));

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConcreteList {
    len: BigInt,
    elements: Vec<String>,
    default: String,
    oob_overrides: BTreeMap<BigInt, String>,
    truncated: bool,
}

impl ConcreteList {
    pub fn from_dynamic(value: &Dynamic<'_>) -> Result<Self, SmtEvalError> {
        let datatype = value.as_datatype().ok_or(SmtEvalError::ParseError)?;
        if !is_registered_list_sort(value) {
            return Err(SmtEvalError::ParseError);
        }

        let len_child = datatype.nth_child(0).ok_or(SmtEvalError::ParseError)?;
        let elements_child = datatype.nth_child(1).ok_or(SmtEvalError::ParseError)?;
        if datatype.nth_child(2).is_some() {
            return Err(SmtEvalError::ParseError);
        }

        if len_child.get_sort() != Sort::int(len_child.get_ctx()) {
            return Err(SmtEvalError::ParseError);
        }

        let elements_sort = elements_child.get_sort();
        if !elements_sort.is_array()
            || elements_sort.array_domain() != Some(Sort::int(elements_child.get_ctx()))
        {
            return Err(SmtEvalError::ParseError);
        }

        let len = parse_big_int(&len_child.as_int().ok_or(SmtEvalError::ParseError)?)
            .ok_or(SmtEvalError::ParseError)?;
        if len < BigInt::from(0_u8) {
            return Err(SmtEvalError::ParseError);
        }

        let array_value =
            ConcreteArrayValue::from_dynamic(&elements_child).ok_or(SmtEvalError::ParseError)?;
        let len_usize = len.to_usize();
        let preview_len = len_usize
            .map(|len| len.min(LIST_PREVIEW_LIMIT))
            .unwrap_or(LIST_PREVIEW_LIMIT);

        let elements = (0..preview_len)
            .map(|index| {
                let index = BigInt::from(index);
                array_value
                    .stores
                    .get(&index)
                    .cloned()
                    .unwrap_or_else(|| array_value.default.clone())
            })
            .collect();

        let zero = BigInt::from(0_u8);
        let oob_overrides = array_value
            .stores
            .iter()
            .filter(|(index, _)| **index < zero || **index >= len)
            .map(|(index, value)| (index.clone(), value.clone()))
            .collect();

        Ok(ConcreteList {
            len,
            elements,
            default: array_value.default,
            oob_overrides,
            truncated: len_usize.is_none_or(|len| len > LIST_PREVIEW_LIMIT),
        })
    }
}

impl Display for ConcreteList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        if self.truncated {
            write!(f, "{}, ...]", self.elements.join(", "))?;
        } else {
            write!(f, "{}]", self.elements.join(", "))?;
        }

        write!(f, " (len={}", self.len)?;
        if !self.oob_overrides.is_empty() {
            write!(f, ", oob: default={}", self.default)?;
            for (index, value) in &self.oob_overrides {
                write!(f, ", {index} -> {value}")?;
            }
        }
        write!(f, ")")?;

        Ok(())
    }
}

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
        register_list_sort(&factory);
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
        index.smt_cmp(&self.len(), SmtOrdering::Less)
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
    fn allocate(factory: &Factory<'ctx, Self>, scope: &mut SmtScope<'ctx>, prefix: &str) -> Self {
        let datatype_factory = (factory.ctx, factory.sort.clone());
        List {
            factory: factory.clone(),
            value: Datatype::allocate(&datatype_factory, scope, prefix),
        }
    }
}

impl<'ctx> SmtEq<'ctx> for List<'ctx> {
    fn smt_eq(&self, other: &Self) -> Bool<'ctx> {
        let mut scope = SmtScope::new();
        let index = UInt::fresh(&self.len().factory(), &mut scope, "i");
        scope.add_constraint(&self.is_valid_index(&index));
        let meta = QuantifierMeta::new("list_eq");
        z3_and!(
            self.len().smt_eq(&other.len()),
            scope.forall(&meta, &self.get(&index).smt_eq(&other.get(&index)))
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

impl<'ctx> SmtEval<'ctx> for List<'ctx> {
    type Value = ConcreteList;

    fn eval(&self, model: &InstrumentedModel<'ctx>) -> Result<Self::Value, SmtEvalError> {
        let value = model
            .eval_ast(&self.as_dynamic(), true)
            .ok_or(SmtEvalError::EvalError)?;
        ConcreteList::from_dynamic(&value)
    }
}

fn register_list_sort(factory: &ListFactory<'_>) {
    REGISTERED_LIST_SORTS
        .lock()
        .unwrap()
        .insert(list_sort_key(factory.ctx, factory.sort()));
}

fn is_registered_list_sort(value: &Dynamic<'_>) -> bool {
    REGISTERED_LIST_SORTS
        .lock()
        .unwrap()
        .contains(&list_sort_key(value.get_ctx(), &value.get_sort()))
}

fn list_sort_key(ctx: &Context, sort: &Sort<'_>) -> (usize, usize) {
    (ctx.z3_ctx as usize, sort.get_z3_sort() as usize)
}

#[cfg(test)]
mod tests {
    use z3::{
        ast::{Array, Int},
        Config, Context, Sort,
    };

    use super::{ConcreteList, List, ListFactory};
    use crate::UInt;

    #[test]
    fn concrete_list_from_dynamic_shows_oob_overrides() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let factory = ListFactory::new(&ctx, &Sort::int(&ctx));
        let len = UInt::from_u64(&ctx, 2);

        let elements = Array::const_array(&ctx, &Sort::int(&ctx), &Int::from_i64(&ctx, 4))
            .store(&Int::from_i64(&ctx, 1), &Int::from_i64(&ctx, 10))
            .store(&Int::from_i64(&ctx, -1), &Int::from_i64(&ctx, 12));
        let list = List::new(factory, &len, elements);

        assert_eq!(
            ConcreteList::from_dynamic(&list.as_dynamic())
                .unwrap()
                .to_string(),
            "[4, 10] (len=2, oob: default=4, -1 -> 12)"
        );
    }
}
