use std::rc::Rc;

use crate::{
    ast::{DeclKind, ExprData, ExprKind, LitKind, Shared, Spanned, Stmt, StmtKind, Symbol, TyKind},
    intrinsic::annotations::AnnotationKind,
    tyctx::TyCtx,
};

use self::selection::{SliceAnnotation, SliceAnnotationKind};

pub mod model;
pub mod selection;
pub mod solver;
pub mod transform;
mod util;

/// Initialize the slicing annotations in this context.
pub fn init_slicing(tcx: &mut TyCtx) {
    for kind in [
        SliceAnnotationKind::SliceVerify,
        SliceAnnotationKind::SliceError,
        SliceAnnotationKind::SuccessMessage,
        SliceAnnotationKind::ErrorMessage,
    ] {
        let name = kind.name();
        let annotation = AnnotationKind::Slicing(Rc::new(SliceAnnotation { ident: name, kind }));
        tcx.add_global(annotation.name());
        tcx.declare(DeclKind::AnnotationDecl(annotation));
    }
}

pub fn wrap_with_error_message(stmt: Stmt, message: &str) -> Stmt {
    wrap_with_annotation(SliceAnnotationKind::ErrorMessage, stmt, message)
}

pub fn wrap_with_success_message(stmt: Stmt, message: &str) -> Stmt {
    wrap_with_annotation(SliceAnnotationKind::SuccessMessage, stmt, message)
}

fn wrap_with_annotation(annotation: SliceAnnotationKind, stmt: Stmt, message: &str) -> Stmt {
    let string_lit = Shared::new(ExprData {
        kind: ExprKind::Lit(Spanned::new(
            stmt.span,
            LitKind::Str(Symbol::intern(message)),
        )),
        ty: Some(TyKind::String),
        span: stmt.span,
    });
    Spanned::new(
        stmt.span,
        StmtKind::Annotation(
            stmt.span,
            annotation.name(),
            vec![string_lit],
            Box::new(stmt),
        ),
    )
}
