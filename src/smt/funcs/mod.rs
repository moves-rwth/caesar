//! Encodings of (possibly recursive) funcs into SMT. We implement all kinds of
//! function encodings based on the literature, with various stages of
//! restrictions on instantiations of defining axioms. The benefit of those is
//! that we make verification (or even counter-examples) more stable and
//! sometimes also much faster.

pub mod axiomatic;
mod recfun;
mod util;
pub use recfun::RecFunFunctionEncoder;
use z3rro::quantifiers::Weight;
pub mod fuel;

use crate::{
    ast::{DeclRef, FuncDecl, Ident},
    smt::{symbolic::Symbolic, translate_exprs::TranslateExprs, SmtCtx},
};
use z3::{ast::Bool, Sort};

/// Higher weight that is used to deprioritize the computation axiom (c.f.
/// [`Weight::DEFAULT`]).
const WEIGHT_COMPUTATION: Weight = Weight(3);

type FunctionSignature<'ctx> = (Ident, Vec<Sort<'ctx>>, Sort<'ctx>);

/// A specific strategy for encoding custom interpreted functions
pub trait FunctionEncoder<'ctx>: 'ctx {
    /// Convert this encoder into a boxed trait object. We use it to make
    /// dynamic dispatch easier to access.
    fn into_boxed(self) -> Box<dyn FunctionEncoder<'ctx>>;

    /// Translate the function declaration. The result may be a list of
    /// signatures (e.g. if the function is translated to multiple variants, as
    /// is the case for [`fuel::fuel_mono`])).
    fn translate_signature(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
    ) -> Vec<FunctionSignature<'ctx>>;

    /// Translate all axioms related to the function.
    fn translate_axioms<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Vec<Bool<'ctx>>;

    /// Call the function with the given arguments.
    fn translate_call(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
        args: Vec<Symbolic<'ctx>>,
    ) -> Symbolic<'ctx>;

    /// Whether this function encoder would make use of lit wrapping for this
    /// function. This is only true for the fuel encodings and for funcs that
    /// have bodies.
    fn func_uses_lit_wrap(&self, func: &DeclRef<FuncDecl>) -> bool;
}
