//! Enums to represent all of our supported SMT types.

use std::convert::TryFrom;
use std::{borrow::Cow, fmt::Display};
use z3::{
    ast::{Bool, Dynamic, Int, Real},
    Sort,
};
use z3rro::{
    eureal,
    model::{InstrumentedModel, SmtEval, SmtEvalError},
    scope::{SmtFresh, SmtScope},
    util::PrettyRational,
    EUReal, Fuel, List, SmtInvariant, UInt, UReal,
};

use crate::ast::{Ident, TyKind};

use super::SmtCtx;

/// A symbolic expression.
///
/// This type is similar to Z3's [`Dynamic`], but here we explicitly enumerate
/// all possible Rust types for each type of SMT expression. Our types carry
/// more information than [`Dynamic`]: Some types will require constraints when
/// variables of that type are quantified over. Some of our types hold more
/// structure (e.g. the pair [`EUReal`] type).
#[derive(Debug, Clone)]
pub enum Symbolic<'ctx> {
    Bool(Bool<'ctx>),
    Int(Int<'ctx>),
    UInt(UInt<'ctx>),
    Real(Real<'ctx>),
    UReal(UReal<'ctx>),
    EUReal(EUReal<'ctx>),
    List(List<'ctx>),
    Fuel(Fuel<'ctx>),
    Uninterpreted(Dynamic<'ctx>),
}

impl<'ctx> Symbolic<'ctx> {
    /// Decode a symbolic value represented by a [`Dynamic`] value created
    /// through [`Symbolic::into_dynamic`].
    pub fn from_dynamic(ctx: &SmtCtx<'ctx>, ty: &TyKind, value: &Dynamic<'ctx>) -> Symbolic<'ctx> {
        match ty {
            TyKind::Bool => Symbolic::Bool(value.as_bool().unwrap()),
            TyKind::Int => Symbolic::Int(value.as_int().unwrap()),
            TyKind::UInt => Symbolic::UInt(UInt::unchecked_from_int(value.as_int().unwrap())),
            TyKind::Real => Symbolic::Real(value.as_real().unwrap()),
            TyKind::UReal => Symbolic::UReal(UReal::unchecked_from_real(value.as_real().unwrap())),
            TyKind::EUReal => {
                let super_realplus_factory = ctx.super_eureal();
                let datatype_factory = &super_realplus_factory.datatype_factory;
                let datatype_value =
                    eureal::datatype::EUReal::from_dynamic(datatype_factory, value);
                Symbolic::EUReal(super_realplus_factory.from_datatype(&datatype_value))
            }
            TyKind::Tuple(_) => unreachable!(),
            TyKind::List(element_ty) => {
                let factory = ctx.list_factory(element_ty);
                let list = List::from_dynamic(factory, value);
                Symbolic::List(list)
            }
            TyKind::Domain(_) => Symbolic::Uninterpreted(value.clone()),
            TyKind::String | TyKind::SpecTy | TyKind::Unresolved(_) | TyKind::None => {
                unreachable!()
            }
        }
    }

    pub fn into_bool(self) -> Option<Bool<'ctx>> {
        match self {
            Symbolic::Bool(v) => Some(v),
            _ => None,
        }
    }

    pub fn into_int(self) -> Option<Int<'ctx>> {
        match self {
            Symbolic::Int(v) => Some(v),
            _ => None,
        }
    }

    pub fn into_uint(self) -> Option<UInt<'ctx>> {
        match self {
            Symbolic::UInt(v) => Some(v),
            _ => None,
        }
    }

    pub fn into_real(self) -> Option<Real<'ctx>> {
        match self {
            Symbolic::Real(v) => Some(v),
            _ => None,
        }
    }

    pub fn into_ureal(self) -> Option<UReal<'ctx>> {
        match self {
            Symbolic::UReal(v) => Some(v),
            _ => None,
        }
    }

    pub fn into_eureal(self) -> Option<EUReal<'ctx>> {
        match self {
            Symbolic::EUReal(v) => Some(v),
            _ => None,
        }
    }

    pub fn into_list(self) -> Option<List<'ctx>> {
        match self {
            Symbolic::List(v) => Some(v),
            _ => None,
        }
    }

    pub fn into_fuel(self) -> Option<Fuel<'ctx>> {
        match self {
            Symbolic::Fuel(v) => Some(v),
            _ => None,
        }
    }

    pub fn into_uninterpreted(self) -> Option<Dynamic<'ctx>> {
        match self {
            Symbolic::Uninterpreted(v) => Some(v),
            _ => None,
        }
    }

    /// Represent this value as a [`Dynamic`] value. Those can be passed to Z3
    /// functions. See [`Self::from_dynamic`] to go back.
    pub fn into_dynamic(self, ctx: &SmtCtx<'ctx>) -> Dynamic<'ctx> {
        match self {
            Symbolic::Bool(v) => Dynamic::from(v),
            Symbolic::Int(v) => Dynamic::from(v),
            Symbolic::UInt(v) => Dynamic::from(v.as_int().clone()),
            Symbolic::Real(v) => Dynamic::from(v),
            Symbolic::UReal(v) => Dynamic::from(v.into_real()),
            Symbolic::EUReal(v) => ctx.super_eureal().to_datatype(&v).as_dynamic(),
            Symbolic::List(v) => v.as_dynamic(),
            Symbolic::Fuel(v) => v.as_dynamic(),
            Symbolic::Uninterpreted(v) => v,
        }
    }

    pub fn eval(&self, model: &InstrumentedModel<'ctx>) -> Result<Box<dyn Display>, SmtEvalError> {
        match self {
            Symbolic::Bool(v) => v.eval(model).map(|v| Box::new(v) as Box<dyn Display>),
            Symbolic::Int(v) => v.eval(model).map(|v| Box::new(v) as Box<dyn Display>),
            Symbolic::UInt(v) => v.eval(model).map(|v| Box::new(v) as Box<dyn Display>),
            Symbolic::Real(v) => v
                .eval(model)
                .map(|v| Box::new(PrettyRational(Cow::Owned(v))) as Box<dyn Display>),
            Symbolic::UReal(v) => v
                .eval(model)
                .map(|v| Box::new(PrettyRational(Cow::Owned(v))) as Box<dyn Display>),
            Symbolic::EUReal(v) => v.eval(model).map(|v| Box::new(v) as Box<dyn Display>),
            Symbolic::List(_) => Err(SmtEvalError::ParseError), // TODO
            Symbolic::Fuel(_) => Err(SmtEvalError::ParseError), // TODO
            Symbolic::Uninterpreted(_) => Err(SmtEvalError::ParseError), // TODO
        }
    }
}

impl<'ctx> SmtInvariant<'ctx> for Symbolic<'ctx> {
    fn smt_invariant(&self) -> Option<Bool<'ctx>> {
        match self {
            Symbolic::Bool(v) => v.smt_invariant(),
            Symbolic::Int(v) => v.smt_invariant(),
            Symbolic::UInt(v) => v.smt_invariant(),
            Symbolic::Real(v) => v.smt_invariant(),
            Symbolic::UReal(v) => v.smt_invariant(),
            Symbolic::EUReal(v) => v.smt_invariant(),
            Symbolic::List(v) => v.smt_invariant(),
            Symbolic::Fuel(v) => v.smt_invariant(),
            Symbolic::Uninterpreted(v) => v.smt_invariant(),
        }
    }
}

macro_rules! impl_into_try_from_symbolic {
    ($ast:ident, $symbolic:ident, $into_ast:ident) => {
        impl<'ctx> From<$ast<'ctx>> for Symbolic<'ctx> {
            fn from(value: $ast<'ctx>) -> Self {
                Symbolic::$symbolic(value)
            }
        }

        impl<'ctx> TryFrom<Symbolic<'ctx>> for $ast<'ctx> {
            type Error = std::string::String;

            fn try_from(value: Symbolic<'ctx>) -> Result<Self, Self::Error> {
                value.$into_ast().ok_or_else(|| {
                    format!(
                        "Symbolic is not of requested type: {:?}",
                        stringify!($symbolic)
                    )
                })
            }
        }
    };
}

impl_into_try_from_symbolic!(Bool, Bool, into_bool);
impl_into_try_from_symbolic!(Int, Int, into_int);
impl_into_try_from_symbolic!(UInt, UInt, into_uint);
impl_into_try_from_symbolic!(Real, Real, into_real);
impl_into_try_from_symbolic!(UReal, UReal, into_ureal);
impl_into_try_from_symbolic!(EUReal, EUReal, into_eureal);
impl_into_try_from_symbolic!(List, List, into_list);
impl_into_try_from_symbolic!(Dynamic, Uninterpreted, into_uninterpreted);

#[derive(Debug)]
pub enum SymbolicPair<'ctx> {
    Bools(Bool<'ctx>, Bool<'ctx>),
    Ints(Int<'ctx>, Int<'ctx>),
    UInts(UInt<'ctx>, UInt<'ctx>),
    Reals(Real<'ctx>, Real<'ctx>),
    UReals(UReal<'ctx>, UReal<'ctx>),
    EUReals(EUReal<'ctx>, EUReal<'ctx>),
    Lists(List<'ctx>, List<'ctx>),
    Uninterpreteds(Dynamic<'ctx>, Dynamic<'ctx>),
}

impl<'ctx> SymbolicPair<'ctx> {
    pub fn from_untypeds(a: Symbolic<'ctx>, b: Symbolic<'ctx>) -> Option<SymbolicPair<'ctx>> {
        match (a, b) {
            (Symbolic::Bool(a), Symbolic::Bool(b)) => Some(SymbolicPair::Bools(a, b)),
            (Symbolic::Int(a), Symbolic::Int(b)) => Some(SymbolicPair::Ints(a, b)),
            (Symbolic::UInt(a), Symbolic::UInt(b)) => Some(SymbolicPair::UInts(a, b)),
            (Symbolic::Real(a), Symbolic::Real(b)) => Some(SymbolicPair::Reals(a, b)),
            (Symbolic::UReal(a), Symbolic::UReal(b)) => Some(SymbolicPair::UReals(a, b)),
            (Symbolic::EUReal(a), Symbolic::EUReal(b)) => Some(SymbolicPair::EUReals(a, b)),
            (Symbolic::List(a), Symbolic::List(b)) => Some(SymbolicPair::Lists(a, b)),
            (Symbolic::Uninterpreted(a), Symbolic::Uninterpreted(b)) => {
                Some(SymbolicPair::Uninterpreteds(a, b))
            }
            _ => None,
        }
    }
}

/// A [`Symbolic`] value along with its corresponding [`SmtScope`].
///
/// This is used to track SMT representations of HeyVL variables.
pub struct ScopeSymbolic<'ctx> {
    pub symbolic: Symbolic<'ctx>,
    pub scope: SmtScope<'ctx>,
}

impl<'ctx> ScopeSymbolic<'ctx> {
    /// Construct a new TranslateLocal and check that the SmtScope is not empty.
    /// If the SmtScope is empty, we've got a bug.
    fn new(var: Symbolic<'ctx>, scope: SmtScope<'ctx>) -> Self {
        assert!(!scope.is_empty());
        ScopeSymbolic {
            symbolic: var,
            scope,
        }
    }

    pub fn fresh_bool(ctx: &SmtCtx<'ctx>, ident: Ident) -> Self {
        let mut scope = SmtScope::new();
        let value = Bool::fresh(&ctx.ctx, &mut scope, &ident.name.to_owned());
        ScopeSymbolic::new(Symbolic::Bool(value), scope)
    }

    pub fn fresh_int(ctx: &SmtCtx<'ctx>, ident: Ident) -> Self {
        let mut scope = SmtScope::new();
        let value = Int::fresh(&ctx.ctx, &mut scope, &ident.name.to_owned());
        ScopeSymbolic::new(Symbolic::Int(value), scope)
    }

    pub fn fresh_uint(ctx: &SmtCtx<'ctx>, ident: Ident) -> Self {
        let mut scope = SmtScope::new();
        let value = UInt::fresh(&ctx.ctx, &mut scope, &ident.name.to_owned());
        ScopeSymbolic::new(Symbolic::UInt(value), scope)
    }

    pub fn fresh_real(ctx: &SmtCtx<'ctx>, ident: Ident) -> Self {
        let mut scope = SmtScope::new();
        let value = Real::fresh(&ctx.ctx, &mut scope, &ident.name.to_owned());
        ScopeSymbolic::new(Symbolic::Real(value), scope)
    }

    pub fn fresh_ureal(ctx: &SmtCtx<'ctx>, ident: Ident) -> Self {
        let mut scope = SmtScope::new();
        let value = UReal::fresh(&ctx.ctx, &mut scope, &ident.name.to_owned());
        ScopeSymbolic::new(Symbolic::UReal(value), scope)
    }

    pub fn fresh_eureal(ctx: &SmtCtx<'ctx>, ident: Ident) -> Self {
        let mut scope = SmtScope::new();
        let value = EUReal::fresh(ctx.eureal(), &mut scope, &ident.name.to_owned());
        ScopeSymbolic::new(Symbolic::EUReal(value), scope)
    }

    pub fn fresh_list(ctx: &SmtCtx<'ctx>, ident: Ident, element_ty: &TyKind) -> Self {
        let factory = ctx.list_factory(element_ty);
        let mut scope = SmtScope::new();
        let value = List::fresh(&factory, &mut scope, &ident.name.to_owned());
        ScopeSymbolic::new(Symbolic::List(value), scope)
    }

    pub fn fresh_fuel(ctx: &SmtCtx<'ctx>) -> Self {
        let factory = ctx.fuel_factory();
        let mut scope = SmtScope::new();
        let value = Fuel::fresh(&factory, &mut scope, "fuel");
        ScopeSymbolic::new(Symbolic::Fuel(value), scope)
    }

    pub fn fresh_uninterpreted(ctx: &SmtCtx<'ctx>, ident: Ident, sort: &Sort<'ctx>) -> Self {
        let factory = (ctx.ctx(), sort.clone());
        let mut scope = SmtScope::new();
        let value = Dynamic::fresh(&factory, &mut scope, &ident.name.to_owned());
        ScopeSymbolic::new(Symbolic::Uninterpreted(value), scope)
    }
}
