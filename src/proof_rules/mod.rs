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

use std::{any::Any, fmt, ops::DerefMut, rc::Rc};

use crate::{
    ast::{
        visit::{walk_stmt, VisitorMut},
        Block, DeclKind, DeclRef, Diagnostic, Direction, Expr, ExprKind, Files, Ident, Param,
        ProcDecl, ProcSpec, SourceFilePath, Span, Stmt, StmtKind,
    },
    driver::{Item, SourceUnit},
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{
        AnnotationError, AnnotationKind, AnnotationUnsoundnessError, Calculus,
    },
    tyctx::TyCtx,
};

/// The necessary information for generating new procedure declarations e.g. during the transformation of an encoding annotation
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
    fn is_calculus_allowed(&self, calculus: Calculus, direction: Direction) -> bool;

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

struct ProcContext {
    name: Ident,
    direction: Direction,
    calculus: Option<Calculus>,
}

/// Walks the AST and transforms encoding annotations into their desugared form.
/// Correct and sound usage of the encoding annotations are also checked during this process.
pub struct EncodingVisitor<'tcx, 'sunit> {
    tcx: &'tcx mut TyCtx,
    source_units_buf: &'sunit mut Vec<Item<SourceUnit>>,
    terminator_annotation: Option<Ident>, // The name of the terminator annotation if there is one
    nesting_level: usize,
    proc_context: Option<ProcContext>, // The relevant context of the current procedure being visited for soundness
}

impl<'tcx, 'sunit> EncodingVisitor<'tcx, 'sunit> {
    pub fn new(tcx: &'tcx mut TyCtx, source_units_buf: &'sunit mut Vec<Item<SourceUnit>>) -> Self {
        EncodingVisitor {
            tcx,
            source_units_buf,
            terminator_annotation: None,
            nesting_level: 0,
            proc_context: None,
        }
    }
}

/// Errors that can occur during the transformation of encoding annotations
/// AnnotationErrors are thrown when the usage of an annotation is incorrect (e.g. not on a while loop, not in a procedure, etc.)
/// UnsoundnessError are thrown when the usage of an annotation is unsound (e.g. mismatched calculus, not a terminator, etc.)
#[derive(Debug)]
pub enum EncodingVisitorError {
    AnnotationError(AnnotationError),
    UnsoundnessError(AnnotationUnsoundnessError),
}

impl EncodingVisitorError {
    pub fn diagnostic(self) -> Diagnostic {
        match self {
            EncodingVisitorError::AnnotationError(err) => err.diagnostic(),
            EncodingVisitorError::UnsoundnessError(err) => err.diagnostic(),
        }
    }
}

impl<'tcx, 'sunit> VisitorMut for EncodingVisitor<'tcx, 'sunit> {
    type Err = EncodingVisitorError;

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        if let ExprKind::Call(ref ident, _) = e.deref_mut().kind {
            if let DeclKind::ProcDecl(proc_ref) = self.tcx.get(*ident).unwrap().as_ref() {
                let proc_ref = proc_ref.clone(); // lose the reference to &mut self
                let proc = proc_ref.borrow();

                if let Some(proc_context) = &self.proc_context {
                    if let Some(context_calculus) = proc_context.calculus {
                        if let Some(call_calculus_ident) = proc.calculus {
                            if context_calculus.name != call_calculus_ident {
                                // Throw mismatched calculus unsoundness error
                                return Err(EncodingVisitorError::UnsoundnessError(
                                    AnnotationUnsoundnessError::CalculusCallMismatch {
                                        span: e.span,
                                        context_calculus: context_calculus.name,
                                        call_calculus: call_calculus_ident,
                                    },
                                ));
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn visit_proc(&mut self, proc_ref: &mut DeclRef<ProcDecl>) -> Result<(), Self::Err> {
        let proc_ref = proc_ref.clone(); // lose the reference to &mut self
        let proc = proc_ref.borrow();

        let mut curr_calculus: Option<Calculus> = None;
        // If the procedure has a calculus annotation, store it as the current calculus
        if let Some(ident) = proc.calculus.as_ref() {
            match self.tcx.get(*ident) {
                Some(decl) => {
                    if let DeclKind::AnnotationDecl(AnnotationKind::Calculus(calculus)) =
                        decl.as_ref()
                    {
                        curr_calculus = Some(*calculus);
                    }
                }
                None => {
                    // If there isn't any calculus declaration that matches the annotation, throw an error
                    return Err(EncodingVisitorError::AnnotationError(
                        AnnotationError::UnknownAnnotation {
                            span: proc.span,
                            annotation_name: *ident,
                        },
                    ));
                }
            }
        }

        // Store the current procedure context
        self.proc_context = Some(ProcContext {
            name: proc.name,
            direction: proc.direction,
            calculus: curr_calculus,
        });

        let mut body = proc.body.borrow_mut();
        if let Some(ref mut block) = &mut *body {
            self.visit_block(block)?;
        }

        // Reset the context
        self.proc_context = None;

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
                    // Try to get the current procedure context
                    let proc_context = self
                        .proc_context
                        .as_ref()
                        // If there is no procedure context, throw an error
                        .ok_or(EncodingVisitorError::AnnotationError(
                            AnnotationError::NotInProcedure {
                                span: s.span,
                                annotation_name: *ident,
                            },
                        ))?;

                    // Unpack the current procedure context
                    let direction = proc_context.direction;
                    let base_proc_ident = proc_context.name;

                    // Check whether the calculus annotation is actually on a while loop (annotations can only be on while loops)
                    if let StmtKind::While(_, _) = inner_stmt.node {
                    } else {
                        return Err(EncodingVisitorError::AnnotationError(
                            AnnotationError::NotOnWhile {
                                span: s.span,
                                annotation_name: *ident,
                                annotated: inner_stmt.as_ref().clone(),
                            },
                        ));
                    }

                    // A terminator annotation can't be nested in a block
                    if anno_ref.is_terminator() && self.nesting_level > 0 {
                        return Err(EncodingVisitorError::UnsoundnessError(
                            AnnotationUnsoundnessError::NotTerminator {
                                span: s.span,
                                enc_name: anno_ref.name(),
                            },
                        ));
                    }

                    // Check if the calculus annotation is compatible with the encoding annotation
                    if let Some(calculus) = proc_context.calculus {
                        // If calculus is not allowed, return an error
                        if !anno_ref.is_calculus_allowed(calculus, direction) {
                            return Err(EncodingVisitorError::UnsoundnessError(
                                AnnotationUnsoundnessError::CalculusEncodingMismatch {
                                    direction,
                                    span: s.span,
                                    calculus_name: calculus.name,
                                    enc_name: anno_ref.name(),
                                },
                            ));
                        };
                    }

                    let enc_env = EncodingEnvironment {
                        base_proc_ident,
                        stmt_span: s.span,
                        call_span: *annotation_span, // TODO: if I change this to stmt_span, explain core vc works :(
                        direction,
                    };

                    // Generate new statements (and declarations) from the annotated loop
                    let mut enc_gen = anno_ref
                        .transform(self.tcx, inputs, inner_stmt, enc_env)
                        .map_err(EncodingVisitorError::AnnotationError)?;

                    // Visit generated statements
                    self.visit_block(&mut enc_gen.block)?;

                    // Replace the annotated loop with the generated statements
                    s.span = enc_gen.block.span;
                    s.node = StmtKind::Seq(enc_gen.block.node);

                    // Add the generated declarations to the list of source units of the compilation unit
                    if let Some(ref mut decls) = enc_gen.decls {
                        // Visit generated declarations
                        // Save the current context and reset it after visiting the declarations
                        let temp = self.proc_context.take();
                        self.visit_decls(decls)?;
                        self.proc_context = temp;

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
                    return Err(EncodingVisitorError::UnsoundnessError(
                        AnnotationUnsoundnessError::NotTerminator {
                            span: s.span,
                            enc_name: anno_name,
                        },
                    ));
                } else {
                    self.nesting_level += 1;
                    walk_stmt(self, s)?;
                    self.nesting_level -= 1;
                }
            }
            _ => {
                // If there was a terminator annotation before, don't allow further statements
                if let Some(anno_name) = self.terminator_annotation {
                    return Err(EncodingVisitorError::UnsoundnessError(
                        AnnotationUnsoundnessError::NotTerminator {
                            span: s.span,
                            enc_name: anno_name,
                        },
                    ));
                } else {
                    walk_stmt(self, s)?
                }
            }
        }
        Ok(())
    }
}
