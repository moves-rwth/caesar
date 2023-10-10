//! This module provides annotations that encode proof rules and their desugaring transformations.

mod induction;
use induction::*;
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

use std::{fmt, rc::Rc};

use crate::{
    ast::{
        visit::{walk_stmt, VisitorMut},
        DeclKind, Direction, Expr, Files, Ident, Param, ProcSpec, SourceFilePath, Span, Stmt,
        StmtKind,
    },
    driver::{Item, SourceUnit},
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{AnnotationError, AnnotationKind},
    tyctx::TyCtx,
};

pub struct ProcInfo {
    name: String,
    inputs: Vec<Param>,
    outputs: Vec<Param>,
    spec: Vec<ProcSpec>,
    body: Vec<Stmt>,
    direction: Direction,
}

/// The result of transforming an annotation call, it can contain generated statements and declarations
pub struct EncodingGenerated {
    span: Span,
    stmts: Vec<Stmt>,
    decls: Option<Vec<DeclKind>>,
}

pub trait Encoding: fmt::Debug {
    fn name(&self) -> Ident;

    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), TycheckError>;

    fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError>;

    fn transform(
        &self,
        tyctx: &TyCtx,
        annotation_span: Span,
        args: &[Expr],
        inner_stmt: &Stmt,
        direction: Direction,
    ) -> Result<EncodingGenerated, AnnotationError>;

    fn is_one_loop(&self) -> bool;
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
    is_one_loop: bool,
    nesting_level: u128,
}

impl<'tcx, 'sunit> EncCall<'tcx, 'sunit> {
    pub fn new(tcx: &'tcx mut TyCtx, source_units_buf: &'sunit mut Vec<Item<SourceUnit>>) -> Self {
        EncCall {
            tcx,
            source_units_buf,
            direction: Option::None,
            is_one_loop: true,
            nesting_level: 0,
        }
    }
}

impl<'tcx, 'sunit> VisitorMut for EncCall<'tcx, 'sunit> {
    type Err = AnnotationError;

    fn visit_decl(&mut self, decl: &mut DeclKind) -> Result<(), Self::Err> {
        if let DeclKind::ProcDecl(decl_ref) = decl {
            self.direction = Some(decl_ref.borrow().direction);
            self.visit_proc(decl_ref)?;
        }
        Ok(())
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        match &mut s.node {
            // If the statement is a block, increase the nesting level and walk the block
            StmtKind::If(_, _, _)
            | StmtKind::Angelic(_, _)
            | StmtKind::Demonic(_, _)
            | StmtKind::Block(_) => {
                self.nesting_level += 1;
                // Save the context of the is_one_loop flag
                let is_one_loop_temp = self.is_one_loop;
                // Reset the is_one_loop flag
                self.is_one_loop = true;
                walk_stmt(self, s)?;
                // Restore the context of the is_one_loop flag
                self.is_one_loop = is_one_loop_temp;
                self.nesting_level -= 1;
            }
            // If the statement is an annotation, transform it
            StmtKind::Annotation(ident, inputs, inner_stmt) => {
                // First visit the statement that is annotated and handle inner annotations
                self.nesting_level += 1;
                let is_one_loop_temp = self.is_one_loop;
                self.is_one_loop = true;
                self.visit_stmt(inner_stmt)?;
                self.is_one_loop = is_one_loop_temp;
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

                    // If the annotated encoding only supports one loop programs but the program is not a one loop program throw an error
                    if anno_ref.is_one_loop() && (!self.is_one_loop || self.nesting_level > 0) {
                        return Err(AnnotationError::OneLoopOnly(s.span, anno_ref.name()));
                    }

                    let mut enc_gen = anno_ref.transform(
                        self.tcx,
                        s.span,
                        inputs,
                        inner_stmt,
                        self.direction
                            .ok_or(AnnotationError::NotInProcedure(s.span, *ident))?,
                    )?;

                    let stmts = &mut enc_gen.stmts;
                    let span = enc_gen.span;
                    let decls_opt = &mut enc_gen.decls;

                    // Visit generated statements
                    self.visit_stmts(stmts)?;
                    s.span = span;
                    s.node = StmtKind::Block(stmts.to_vec());

                    if let Some(ref mut decls) = decls_opt {
                        // Visit generated declarations
                        self.visit_decls(decls)?;

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
            // Var declarations are still allowed in one loop programs
            StmtKind::Var(_) => {
                walk_stmt(self, s)?;
            }
            // If the statement is not an annotation, it is not a one loop program anymore
            _ => {
                self.is_one_loop = true;
                walk_stmt(self, s)?;
            }
        }
        Ok(())
    }
}
