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
    annotation_span: Span,
    direction: Direction,
}

/// The trait that all encoding annotations must implement
pub trait Encoding: fmt::Debug {
    fn name(&self) -> Ident;

    /// Typecheck the arguments of the annotation call
    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), TycheckError>;

    /// Resolve the arguments of the annotation call
    fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError>;

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
pub struct EncCall<'tcx, 'sunit> {
    tcx: &'tcx mut TyCtx,
    source_units_buf: &'sunit mut Vec<Item<SourceUnit>>,
    direction: Option<Direction>,
    terminator_annotation: Option<Ident>,
    nesting_level: usize,
    current_proc_ident: Option<Ident>,
    calculus: Option<Calculus>,
}

impl<'tcx, 'sunit> EncCall<'tcx, 'sunit> {
    pub fn new(tcx: &'tcx mut TyCtx, source_units_buf: &'sunit mut Vec<Item<SourceUnit>>) -> Self {
        EncCall {
            tcx,
            source_units_buf,
            direction: Option::None,
            terminator_annotation: None,
            nesting_level: 0,
            current_proc_ident: None,
            calculus: None,
        }
    }
}

impl<'tcx, 'sunit> VisitorMut for EncCall<'tcx, 'sunit> {
    type Err = AnnotationError;

    fn visit_proc(&mut self, proc_ref: &mut DeclRef<ProcDecl>) -> Result<(), Self::Err> {
        self.direction = Some(proc_ref.borrow().direction);
        self.current_proc_ident = Some(proc_ref.borrow().name);

        // If the procedure has a calculus annotation, store it as the current calculus
        if let Some(ident) = proc_ref.borrow().calculus.as_ref() {
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
                        proc_ref.borrow().span,
                        *ident,
                    ))
                }
            }
        }
        let proc = proc_ref.borrow_mut();
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
                self.nesting_level += 1;
                self.visit_stmt(inner_stmt)?;
                self.nesting_level -= 1;

                if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(anno_ref)) =
                    self.tcx.get(*ident).unwrap().as_ref()
                {
                    if let StmtKind::While(_, _) = inner_stmt.node {
                    } else {
                        return Err(AnnotationError::NotOnWhile(
                            s.span,
                            *ident,
                            inner_stmt.as_ref().clone(),
                        ));
                    }

                    // A terminator annotation can't be nested in a block
                    if anno_ref.is_terminator() && self.nesting_level > 0 {
                        return Err(AnnotationError::NotTerminator(s.span, anno_ref.name()));
                    }

                    // Check if the calculus annotation is compatible with the encoding annotation
                    if let Some(calculus) = &self.calculus {
                        // If calculus is not allowed, return an error
                        if !anno_ref.is_calculus_allowed(
                            calculus,
                            self.direction
                                .ok_or(AnnotationError::NotInProcedure(s.span, *ident))?,
                        ) {
                            return Err(AnnotationError::CalculusEncodingMismatch(
                                s.span,
                                calculus.name,
                                anno_ref.name(),
                            ));
                        };
                    }

                    let enc_env = EncodingEnvironment {
                        base_proc_ident: self
                            .current_proc_ident
                            .ok_or(AnnotationError::NotInProcedure(s.span, *ident))?,
                        annotation_span: *annotation_span,
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

                    // Check if the annotation is a terminator annotation and set the flag
                    if anno_ref.is_terminator() {
                        self.terminator_annotation = Some(anno_ref.name());
                    }
                }
            }
            // If the statement is a block, increase the nesting level and walk the block
            StmtKind::If(_, _, _)
            | StmtKind::Angelic(_, _)
            | StmtKind::Demonic(_, _)
            | StmtKind::Seq(_) => {
                if let Some(anno_name) = self.terminator_annotation {
                    return Err(AnnotationError::NotTerminator(s.span, anno_name));
                } else {
                    self.nesting_level += 1;
                    walk_stmt(self, s)?;
                    self.nesting_level -= 1;
                }
            }
            _ => {
                // If there was a terminator annotation before, don't allow further statements
                if let Some(anno_name) = self.terminator_annotation {
                    return Err(AnnotationError::NotTerminator(s.span, anno_name));
                } else {
                    walk_stmt(self, s)?
                }
            }
        }
        Ok(())
    }
}
