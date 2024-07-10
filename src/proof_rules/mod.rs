//! This module provides annotations that encode proof rules and their desugaring transformations.

mod induction;
pub use induction::*;
mod unroll;
use unroll::*;
mod mciver_ast;
use mciver_ast::*;
mod omega;
use omega::*;
mod ost;
use ost::*;
mod past;
use past::*;
mod util;

#[cfg(test)]
mod tests;

use std::{any::Any, fmt, rc::Rc};

use crate::{
    ast::{
        visit::{walk_stmt, VisitorMut},
        Block, DeclKind, DeclRef, Direction, Expr, Files, Ident, Param, ProcDecl, ProcSpec,
        SourceFilePath, Span, Stmt, StmtKind,
    },
    driver::{Item, SourceUnit},
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{AnnotationError, AnnotationKind, Calculus},
    tyctx::TyCtx,
};

pub struct ProcInfo {
    name: String,
    inputs: Vec<Param>,
    outputs: Vec<Param>,
    spec: Vec<ProcSpec>,
    body: Block,
    direction: Direction,
}

/// The result of transforming an annotation call, it can contain generated statements and declarations
pub struct EncodingGenerated {
    block: Block,
    decls: Option<Vec<DeclKind>>,
}

/// The environment information when the encoding annotation is called
pub struct EncodingEnvironment {
    base_proc_ident: Ident,
    stmt_span: Span,
    call_span: Span,
    direction: Direction,
}

/// The trait that all encoding annotations must implement
pub trait Encoding: fmt::Debug {
    fn name(&self) -> Ident;

    /// Resolve the arguments of the annotation call
    fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError>;

    /// Typecheck the arguments of the annotation call
    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), TycheckError>;

    /// Transform the annotated loop into a sequence of statements and declarations
    fn transform(
        &self,
        tyctx: &TyCtx,
        args: &[Expr],
        inner_stmt: &Stmt,
        enc_env: EncodingEnvironment,
    ) -> Result<EncodingGenerated, AnnotationError>;

    /// Check if the given calculus annotation is compatible with the encoding annotation
    fn is_calculus_allowed(&self, calculus: &Calculus, direction: Direction) -> bool;

    /// Indicates if the encoding annotation is required to be the last statement of a procedure
    fn is_terminator(&self) -> bool;

    /// Return an [`Any`] reference for this encoding.
    fn as_any(&self) -> &dyn Any;
}

/// Initialize all intrinsic annotations by declaring them
pub fn init_encodings(files: &mut Files, tcx: &mut TyCtx) {
    let invariant = AnnotationKind::Encoding(Rc::new(InvariantAnnotation::new(tcx, files)));
    tcx.add_global(invariant.name());
    tcx.declare(DeclKind::AnnotationDecl(invariant));

    let k_ind = AnnotationKind::Encoding(Rc::new(KIndAnnotation::new(tcx, files)));
    tcx.add_global(k_ind.name());
    tcx.declare(DeclKind::AnnotationDecl(k_ind));

    let bmc = AnnotationKind::Encoding(Rc::new(UnrollAnnotation::new(tcx, files)));
    tcx.add_global(bmc.name());
    tcx.declare(DeclKind::AnnotationDecl(bmc));

    let omega_inv = AnnotationKind::Encoding(Rc::new(OmegaInvAnnotation::new(tcx, files)));
    tcx.add_global(omega_inv.name());
    tcx.declare(DeclKind::AnnotationDecl(omega_inv));

    let ost = AnnotationKind::Encoding(Rc::new(OSTAnnotation::new(tcx, files)));
    tcx.add_global(ost.name());
    tcx.declare(DeclKind::AnnotationDecl(ost));

    let past = AnnotationKind::Encoding(Rc::new(PASTAnnotation::new(tcx, files)));
    tcx.add_global(past.name());
    tcx.declare(DeclKind::AnnotationDecl(past));

    let ast = AnnotationKind::Encoding(Rc::new(ASTAnnotation::new(tcx, files)));
    tcx.add_global(ast.name());
    tcx.declare(DeclKind::AnnotationDecl(ast));
}

/// Walks the AST and transforms annotations into their desugared form
/// Correct and sound usage of the annotations should be checked before by the [`GuardrailsVisitor`].
/// Otherwise the transformation may fail or produce unsound results.
pub struct EncCall<'tcx, 'sunit> {
    tcx: &'tcx mut TyCtx,
    source_units_buf: &'sunit mut Vec<Item<SourceUnit>>,
    direction: Option<Direction>,
    current_proc_ident: Option<Ident>,
}

impl<'tcx, 'sunit> EncCall<'tcx, 'sunit> {
    pub fn new(tcx: &'tcx mut TyCtx, source_units_buf: &'sunit mut Vec<Item<SourceUnit>>) -> Self {
        EncCall {
            tcx,
            source_units_buf,
            direction: Option::None,
            current_proc_ident: None,
        }
    }
}

impl<'tcx, 'sunit> VisitorMut for EncCall<'tcx, 'sunit> {
    type Err = AnnotationError;

    fn visit_proc(&mut self, proc_ref: &mut DeclRef<ProcDecl>) -> Result<(), Self::Err> {
        let proc_ref = proc_ref.clone(); // lose the reference to &mut self
        let proc = proc_ref.borrow();

        // Store the procedure information for encoding context
        self.direction = Some(proc.direction);
        self.current_proc_ident = Some(proc.name);

        let mut body = proc.body.borrow_mut();
        if let Some(ref mut block) = &mut *body {
            self.visit_block(block)?;
        }

        Ok(())
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        match &mut s.node {
            // If the statement is an annotation, transform it
            StmtKind::Annotation(annotation_span, ident, inputs, inner_stmt) => {
                // First visit the statement that is annotated and handle inner annotations
                self.visit_stmt(inner_stmt)?;

                if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(anno_ref)) =
                    self.tcx.get(*ident).unwrap().as_ref()
                {
                    // This must be already be checked by the guardrails visitor
                    // We check again just to be sure if it is disabled for some reason
                    if let StmtKind::While(_, _) = inner_stmt.node {
                    } else {
                        return Err(AnnotationError::NotOnWhile(
                            s.span,
                            *ident,
                            inner_stmt.as_ref().clone(),
                        ));
                    }

                    let enc_env = EncodingEnvironment {
                        base_proc_ident: self
                            .current_proc_ident
                            .ok_or(AnnotationError::NotInProcedure(s.span, *ident))?,
                        stmt_span: s.span,
                        call_span: *annotation_span, // TODO: if I change this to stmt_span, explain core vc works :(
                        direction: self
                            .direction
                            .ok_or(AnnotationError::NotInProcedure(s.span, *ident))?,
                    };
                    // Generate new statements (and declarations) from the annotated loop
                    let mut enc_gen = anno_ref.transform(self.tcx, inputs, inner_stmt, enc_env)?;

                    // Visit generated statements
                    self.visit_block(&mut enc_gen.block)?;

                    // Replace the annotated loop with the generated statements
                    s.span = enc_gen.block.span;
                    s.node = StmtKind::Seq(enc_gen.block.node);

                    // Add the generated declarations to the list of source units of the compilation unit
                    if let Some(ref mut decls) = enc_gen.decls {
                        // Visit generated declarations
                        let temp = self.current_proc_ident;
                        self.visit_decls(decls)?;
                        self.current_proc_ident = temp;

                        // Wrap generated declarations in items
                        let items: Vec<Item<SourceUnit>> = decls
                            .iter_mut()
                            .map(|decl| {
                                SourceUnit::Decl(decl.to_owned())
                                    .wrap_item(&SourceFilePath::Generated)
                            })
                            .collect();

                        self.source_units_buf.extend(items)
                    }
                }
            }
            _ => walk_stmt(self, s)?,
        }
        Ok(())
    }
}
