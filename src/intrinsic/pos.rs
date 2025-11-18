//! Intrinsics for list operations.

use std::rc::Rc;

use z3::ast::{Ast, Int, Real};
use z3rro::{EUReal, UReal, eureal::pair::EURealFactory};

use crate::{
    ast::{DeclKind, Expr, Files, Ident, Span, Symbol, TyKind},
    front::tycheck::{Tycheck, TycheckError},
    smt::{symbolic::Symbolic, translate_exprs::TranslateExprs},
    tyctx::TyCtx,
};

use super::FuncIntrin;

pub fn init_pos(_files: &mut Files, tcx: &mut TyCtx) {
    let pos_name = Ident::with_dummy_span(Symbol::intern("pos"));
    let pos = PosIntrin(pos_name);
    tcx.declare(DeclKind::FuncIntrin(Rc::new(pos)));
    tcx.add_global(pos_name);
}

/// A function that takes a Real number x and returns max(x,0)
#[derive(Debug)]
pub struct PosIntrin(Ident);

impl FuncIntrin for PosIntrin {
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
        // Unsure about this
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
                let zero = Int::from_i64(&ctx, 0);

                let cond = x.gt(&zero);
                let value = cond.ite(&x, &zero);

                Symbolic::from_dynamic(translate.ctx, &ty.clone().unwrap(), &value.into())
            }

            Some(TyKind::UInt) => Symbolic::UInt(translate.t_uint(&args[0])),

            Some(TyKind::Real) => {
                let x = translate.t_real(&args[0]);
                let ctx = x.get_ctx();
                let factory = EURealFactory::new(ctx);
                let zero = Real::from_real(&ctx, 0, 1);

                let cond = x.gt(&zero);

                let value = EUReal::from_ureal(&factory,&UReal::unchecked_from_real(cond.ite(&x, &zero)));

                
                Symbolic::EUReal(value)
            }

            Some(TyKind::EUReal) => {println!("this is the reason {:?}", &args[0].ty); Symbolic::EUReal(translate.t_eureal(&args[0]))},

            _ => unreachable!("max(x,0) only defined for numeric types"),
        }
    }
}

// #[cfg(test)]
// mod test {
//     use crate::driver::commands::verify::verify_test;

//     #[test]
//     fn test_store() {
//         let code = r#"
//             proc proc_store(list: []UInt, index: UInt, value: UInt) -> (res: []UInt)
//                 pre ?(index < len(list))
//                 post ?(forall i: UInt. (i < len(list) && i != index) ==> (select(res, i) == select(list, i)))
//                 post ?(select(res, index) == value)
//             {
//                 res = store(list, index, value)
//             }
//         "#;
//         assert!(verify_test(code).0.unwrap());
//     }
// }
