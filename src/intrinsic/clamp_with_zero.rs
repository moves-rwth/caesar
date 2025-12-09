//! Intrinsics for list operations.

use std::rc::Rc;

use z3::ast::{Ast, Int, Real};
use z3rro::{eureal::pair::EURealFactory, EUReal, UInt, UReal};

use crate::{
    ast::{DeclKind, Expr, Files, Ident, Span, Symbol, TyKind},
    front::tycheck::{Tycheck, TycheckError},
    smt::{symbolic::Symbolic, translate_exprs::TranslateExprs},
    tyctx::TyCtx,
};

use super::FuncIntrin;

pub fn init_clamp_with_zero(_files: &mut Files, tcx: &mut TyCtx) {
    let clamp_with_zero_name = Ident::with_dummy_span(Symbol::intern("clamp_with_zero"));
    let clamp_with_zero = ClampWithZeroIntrin(clamp_with_zero_name);
    tcx.declare(DeclKind::FuncIntrin(Rc::new(clamp_with_zero)));
    tcx.add_global(clamp_with_zero_name);
}

/// A function that takes a number x and returns max(x,0)
/// TODO: Should be replaced by clamp_cast(type, number)
#[derive(Debug)]
pub struct ClampWithZeroIntrin(Ident);

impl FuncIntrin for ClampWithZeroIntrin {
    fn name(&self) -> Ident {
        self.0
    }

    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<TyKind, TycheckError> {
        let x = if let [ref mut x] = args {
            x
        } else {
            return Err(TycheckError::ArgumentCountMismatch {
                span: call_span,
                callee: args.len(),
                caller: 1,
            });
        };
        tycheck.try_cast(call_span, &TyKind::Real, x)?;
        Ok(TyKind::EUReal)
    }

    fn translate_call<'smt, 'ctx>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        args: &[Expr],
    ) -> Symbolic<'ctx> {
        let ty = &args[0].ty;

        match ty {
            Some(TyKind::Int) => {
                let x = translate.t_int(&args[0]);
                let ctx = x.get_ctx();
                let factory = EURealFactory::new(ctx);

                let zero = Int::from_i64(&ctx, 0);

                let cond = x.gt(&zero);
                let value =
                    EUReal::from_uint(&factory, &UInt::unchecked_from_int(cond.ite(&x, &zero)));

                Symbolic::EUReal(value)
            }

            Some(TyKind::UInt) => {
                let x_uint = translate.t_uint(&args[0]);
                let x = x_uint.as_int();
                let ctx = x.get_ctx();
                let factory = EURealFactory::new(ctx);

                let zero = Int::from_i64(&ctx, 0);

                let cond = x.gt(&zero);
                let value =
                    EUReal::from_uint(&factory, &UInt::unchecked_from_int(cond.ite(&x, &zero)));

                Symbolic::EUReal(value)
            }

            Some(TyKind::Real) => {
                let x = translate.t_real(&args[0]);
                let ctx = x.get_ctx();
                let factory = EURealFactory::new(ctx);
                let zero = Real::from_real(&ctx, 0, 1);

                let cond = x.gt(&zero);

                let value =
                    EUReal::from_ureal(&factory, &UReal::unchecked_from_real(cond.ite(&x, &zero)));

                Symbolic::EUReal(value)
            }

            Some(TyKind::UReal) => {
                let x = translate.t_ureal(&args[0]);
                let x = x.as_real();
                let ctx = x.get_ctx();
                let factory = EURealFactory::new(ctx);
                let zero = Real::from_real(&ctx, 0, 1);

                let cond = x.gt(&zero);

                let value =
                    EUReal::from_ureal(&factory, &UReal::unchecked_from_real(cond.ite(&x, &zero)));

                Symbolic::EUReal(value)
            }

            Some(TyKind::EUReal) => {println!("eurealll");Symbolic::EUReal(translate.t_eureal(&args[0]))},

            _ => unreachable!("clamp_with_zero only defined for numeric types"),
        }
    }
}
