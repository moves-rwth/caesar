mod ert;
use std::{fmt, rc::Rc};

use ert::*;
mod wp;
use wp::*;
mod wlp;
use wlp::*;

#[cfg(test)]
mod tests;

use crate::{
    ast::{
        visit::{walk_stmt, VisitorMut},
        DeclKind, Direction, Files, Ident, SourceFilePath, Stmt, StmtKind,
    },
    intrinsic::annotations::{AnnotationError, AnnotationKind},
    proof_rules::EncodingKind,
    tyctx::TyCtx,
};

pub trait Calculus: fmt::Debug {
    fn name(&self) -> Ident;

    fn check_encoding(&self, encoding: EncodingKind, direction: Direction) -> Result<(), ()>;
}

pub struct CalculusVisitor<'tcx> {
    tcx: &'tcx mut TyCtx,
    calculus: Option<Rc<dyn Calculus>>,
    direction: Option<Direction>,
}

impl<'tcx> CalculusVisitor<'tcx> {
    pub fn new(tcx: &'tcx mut TyCtx) -> Self {
        CalculusVisitor {
            tcx,
            calculus: None,
            direction: None,
        }
    }
}

impl<'tcx> VisitorMut for CalculusVisitor<'tcx> {
    type Err = AnnotationError;

    fn visit_decl(&mut self, decl: &mut DeclKind) -> Result<(), Self::Err> {
        if let DeclKind::ProcDecl(decl_ref) = decl {
            self.direction = Some(decl_ref.borrow().direction);
            // If the procedure has a calculus annotation, store it as the current calculus
            if let Some(ident) = decl_ref.borrow().calculus.as_ref() {
                match self.tcx.get(*ident) {
                    Some(decl) => {
                        if let DeclKind::AnnotationDecl(AnnotationKind::Calculus(calculus)) =
                            decl.as_ref()
                        {
                            self.calculus = Some(calculus.clone());
                        }
                    }
                    None => {
                        return Err(AnnotationError::UnknownAnnotation(
                            decl_ref.borrow().span,
                            *ident,
                        ))
                    }
                }
            }
            self.visit_proc(decl_ref)?;
        }
        Ok(())
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        if let Some(calculus) = &self.calculus {
            if let StmtKind::Annotation(ident, _, _) = &mut s.node {
                match self.tcx.get(*ident) {
                    Some(decl_ref) => {
                        if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(encoding_ref)) =
                            decl_ref.as_ref()
                        {
                            if let Some(direction) = self.direction {
                                if calculus
                                    .check_encoding(encoding_ref.clone(), direction)
                                    .is_err()
                                {
                                    return Err(AnnotationError::CalculusEncodingMismatch(
                                        s.span,
                                        calculus.name(),
                                        encoding_ref.name(),
                                    ));
                                };
                            }
                        }
                    }
                    None => return Err(AnnotationError::UnknownAnnotation(s.span, *ident)),
                }
            }
        }
        walk_stmt(self, s)
    }
}

/// Add all built-in calculus annotations as globals into the [`TyCtx`].
pub fn init_calculi(files: &mut Files, tcx: &mut TyCtx) {
    let file = files
        .add(SourceFilePath::Builtin, "calculus".to_string())
        .id;

    let wp = AnnotationKind::Calculus(Rc::new(WpCalculus::new(file)));
    tcx.add_global(wp.name());
    tcx.declare(DeclKind::AnnotationDecl(wp));

    let wlp = AnnotationKind::Calculus(Rc::new(WlpCalculus::new(file)));
    tcx.add_global(wlp.name());
    tcx.declare(DeclKind::AnnotationDecl(wlp));

    let ert = AnnotationKind::Calculus(Rc::new(ErtCalculus::new(file)));
    tcx.add_global(ert.name());
    tcx.declare(DeclKind::AnnotationDecl(ert));
}
