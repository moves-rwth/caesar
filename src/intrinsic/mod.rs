//! Compiler _intrinsics_ are APIs available to the user that do something
//! special based on code integrated into the compiler. Distribution expressions
//! or functions mapping to certain SMT-LIB expressions are such intrinsics.
//!
//! This module provides a framework to define intrinsics in a modular way.

pub mod distributions;
pub mod list;

use std::fmt;

use crate::{
    ast::{Expr, ExprBuilder, Ident, Span, TyKind},
    front::tycheck::{Tycheck, TycheckError},
    smt::{symbolic::Symbolic, translate_exprs::TranslateExprs},
};

pub trait ProcIntrin: fmt::Debug {
    fn name(&self) -> Ident;

    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<TyKind, TycheckError>;

    fn vcgen(&self, builder: ExprBuilder, args: &[Expr], lhses: &[Ident], post: Expr) -> Expr;
}

pub trait FuncIntrin: fmt::Debug {
    fn name(&self) -> Ident;

    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<TyKind, TycheckError>;

    fn translate_call<'smt, 'ctx>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        args: &[Expr],
    ) -> Symbolic<'ctx>;
}
