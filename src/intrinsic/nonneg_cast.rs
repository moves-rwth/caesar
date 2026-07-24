//! Intrinsic for casting a signed expression to its unsigned counterpart
//! (Int -> UInt, Real -> UReal) without a bounds check. The non-negativity
//! obligation is added to the VC separately.

use std::rc::Rc;

use z3rro::{UInt, UReal};

use crate::{
    ast::{DeclKind, Expr, Files, Ident, Span, Symbol, TyKind},
    front::tycheck::{Tycheck, TycheckError},
    smt::{symbolic::Symbolic, translate_exprs::TranslateExprs},
    tyctx::TyCtx,
};

use super::FuncIntrin;

pub fn init_nonneg_cast(_files: &mut Files, tcx: &mut TyCtx) {
    let nonneg_cast_name = Ident::with_dummy_span(Symbol::intern("nonneg_cast"));
    let nonneg_cast = NonnegCastIntrin(nonneg_cast_name);
    tcx.declare(DeclKind::FuncIntrin(Rc::new(nonneg_cast)));
    tcx.add_global(nonneg_cast_name);
}

/// Unchecked cast from Int/Real to UInt/UReal. The argument must be >= 0;
/// this is tracked as a separate obligation added to the VC.
#[derive(Debug)]
pub struct NonnegCastIntrin(Ident);

impl FuncIntrin for NonnegCastIntrin {
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

        if tycheck.try_cast(call_span, &TyKind::Int, x).is_ok() {
            Ok(TyKind::UInt)
        } else {
            tycheck.try_cast(call_span, &TyKind::Real, x)?;
            Ok(TyKind::UReal)
        }
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
                Symbolic::UInt(UInt::unchecked_from_int(x))
            }

            Some(TyKind::UInt) => {
                let x_uint = translate.t_uint(&args[0]);
                let x = x_uint.as_int();
                Symbolic::UInt(UInt::unchecked_from_int(x.clone()))
            }

            Some(TyKind::Real) => {
                let x = translate.t_real(&args[0]);
                let value = UReal::unchecked_from_real(x);
                Symbolic::UReal(value)
            }

            Some(TyKind::UReal) => {
                let x = translate.t_ureal(&args[0]);
                let x = x.as_real();
                let value = UReal::unchecked_from_real(x.clone());
                Symbolic::UReal(value)
            }

            Some(TyKind::EUReal) => {
                let x = translate.t_eureal(&args[0]);
                let x = x.get_ureal();
                let x = x.as_real();
                let value = UReal::unchecked_from_real(x.clone());
                Symbolic::UReal(value)
            }

            _ => unreachable!("nonneg_cast only defined for numeric types"),
        }
    }
}
