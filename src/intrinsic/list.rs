//! Intrinsics for list operations.

use std::rc::Rc;

use crate::{
    ast::{DeclKind, Expr, Files, Ident, Span, Symbol, TyKind},
    front::tycheck::{ExpectedKind, Tycheck, TycheckError},
    smt::{symbolic::Symbolic, translate_exprs::TranslateExprs},
    tyctx::TyCtx,
};

use super::FuncIntrin;

pub fn init_lists(_files: &mut Files, tcx: &mut TyCtx) {
    let select_name = Ident::with_dummy_span(Symbol::intern("select"));
    let select = SelectIntrin(select_name);
    tcx.declare(DeclKind::FuncIntrin(Rc::new(select)));
    tcx.add_global(select_name);
    let store_name = Ident::with_dummy_span(Symbol::intern("store"));
    let store = StoreIntrin(store_name);
    tcx.declare(DeclKind::FuncIntrin(Rc::new(store)));
    tcx.add_global(store_name);
    let len_name = Ident::with_dummy_span(Symbol::intern("len"));
    let len = LenIntrin(len_name);
    tcx.declare(DeclKind::FuncIntrin(Rc::new(len)));
    tcx.add_global(len_name);
}

/// The function that retrieves an element from the list at some index.
///
/// It takes two arguments: The list `list` and the index `index` of type [`z3rro::UInt`].
#[derive(Debug)]
pub struct SelectIntrin(Ident);

impl FuncIntrin for SelectIntrin {
    fn name(&self) -> Ident {
        self.0
    }

    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<TyKind, TycheckError> {
        let (list, index) = if let [ref mut list, ref mut index] = args {
            (list, index)
        } else {
            return Err(TycheckError::ArgumentCountMismatch {
                span: call_span,
                callee: args.len(),
                caller: 2,
            });
        };
        let element_ty = if let TyKind::List(element_ty) = list.ty.as_ref().unwrap() {
            element_ty
        } else {
            return Err(TycheckError::ExpectedKind {
                span: call_span,
                expr: list.clone(),
                kind: ExpectedKind::List,
            });
        };
        tycheck.try_cast(call_span, &TyKind::UInt, index)?;
        Ok(*element_ty.clone())
    }

    fn translate_call<'smt, 'ctx>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        args: &[Expr],
    ) -> Symbolic<'ctx> {
        let element_ty = if let Some(TyKind::List(ref element_ty)) = &args[0].ty {
            element_ty
        } else {
            unreachable!()
        };

        let list = translate.t_list(&args[0]);
        let index = translate.t_uint(&args[1]);
        let value = list.get(&index);
        Symbolic::from_dynamic(translate.ctx, element_ty, &value)
    }
}

/// The function that stores an element into the list at some index.
///
/// It takes three arguments: The list `list` and the index `index` of type
/// [`z3rro::UInt`], and the value.
#[derive(Debug)]
pub struct StoreIntrin(Ident);

impl FuncIntrin for StoreIntrin {
    fn name(&self) -> Ident {
        self.0
    }

    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<TyKind, TycheckError> {
        let (list, index, value) = if let [ref mut list, ref mut index, ref mut value] = args {
            (list, index, value)
        } else {
            return Err(TycheckError::ArgumentCountMismatch {
                span: call_span,
                callee: args.len(),
                caller: 3,
            });
        };
        let list_ty = list.ty.as_ref().unwrap();
        let element_ty = if let TyKind::List(element_ty) = list_ty {
            element_ty
        } else {
            return Err(TycheckError::ExpectedKind {
                span: call_span,
                expr: list.clone(),
                kind: ExpectedKind::List,
            });
        };
        tycheck.try_cast(call_span, &TyKind::UInt, index)?;
        tycheck.try_cast(call_span, element_ty, value)?;
        Ok(list_ty.clone())
    }

    fn translate_call<'smt, 'ctx>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        args: &[Expr],
    ) -> Symbolic<'ctx> {
        let list = translate.t_list(&args[0]);
        let index = translate.t_uint(&args[1]);
        let value = translate.t_symbolic(&args[2]);
        let res = list.set(&index, &value.into_dynamic(translate.ctx));
        Symbolic::List(res)
    }
}

/// Retrieve the length of a list.
#[derive(Debug)]
pub struct LenIntrin(Ident);

impl FuncIntrin for LenIntrin {
    fn name(&self) -> Ident {
        self.0
    }

    fn tycheck(
        &self,
        _tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<TyKind, TycheckError> {
        if args.len() != 1 {
            return Err(TycheckError::ArgumentCountMismatch {
                span: call_span,
                callee: args.len(),
                caller: 1,
            });
        }
        Ok(TyKind::UInt)
    }

    fn translate_call<'smt, 'ctx>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        args: &[Expr],
    ) -> Symbolic<'ctx> {
        let list = translate.t_list(&args[0]);
        Symbolic::UInt(list.len())
    }
}

#[cfg(test)]
mod test {
    use crate::driver::commands::verify::verify_test;

    #[test]
    fn test_store() {
        let code = r#"
            proc proc_store(list: []UInt, index: UInt, value: UInt) -> (res: []UInt)
                pre ?(index < len(list))
                post ?(forall i: UInt. (i < len(list) && i != index) ==> (select(res, i) == select(list, i)))
                post ?(select(res, index) == value)
            {
                res = store(list, index, value)
            }
        "#;
        assert!(verify_test(code).0.unwrap());
    }
}
