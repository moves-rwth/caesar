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
        visit::VisitorMut, DeclKind, Direction, Expr, Files, Ident, Param, ProcSpec,
        SourceFilePath, Span, Stmt, StmtKind,
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
}

impl<'tcx, 'sunit> EncCall<'tcx, 'sunit> {
    pub fn new(tcx: &'tcx mut TyCtx, source_units_buf: &'sunit mut Vec<Item<SourceUnit>>) -> Self {
        EncCall {
            tcx,
            source_units_buf,
            direction: Option::None,
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

    fn visit_stmts(&mut self, stmts: &mut Vec<Stmt>) -> Result<(), Self::Err> {
        // Check if the program consists of only one loop
        let mut encoding: Option<(Rc<dyn Encoding>, Span)> = None;

        let mut is_one_loop = true;
        for s in &mut *stmts {
            match &mut s.node {
                StmtKind::Annotation(ident, _, _) => {
                    if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(anno_ref)) =
                        self.tcx.get(*ident).unwrap().as_ref()
                    {
                        encoding = Some((anno_ref.clone(), s.span));
                    }
                }
                StmtKind::Var(_) => {}
                _ => {
                    is_one_loop = false;
                }
            }
        }
        // If the annotated encoding only supports one loop programs throw an error
        if let Some((enc, span)) = encoding {
            if enc.is_one_loop() && !is_one_loop {
                return Err(AnnotationError::OneLoopOnly(span, enc.name()));
            }
        }

        for s in stmts {
            self.visit_stmt(s)?;
        }
        Ok(())
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        walk_stmt(self, s)?;
        if let StmtKind::Annotation(ident, inputs, inner_stmt) = &mut s.node {
            if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(anno_ref)) =
                self.tcx.get(*ident).unwrap().as_ref()
            {
                if let StmtKind::While(_, _) = inner_stmt.node {
                } else {
                    return Err(AnnotationError::NotOnWhile(s.span, *ident, s.clone()));
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
                            SourceUnit::Decl(decl.to_owned()).wrap_item(&SourceFilePath::Generated)
                        })
                        .collect();

                    self.source_units_buf.extend(items)
                }
            }
        }
        Ok(())
    }
}

pub fn walk_stmt<V: VisitorMut>(visitor: &mut V, s: &mut Stmt) -> Result<(), V::Err> {
    match &mut s.node {
        StmtKind::Block(ref mut block) => {
            visitor.visit_stmts(block)?;
        }
        StmtKind::Var(decl_ref) => {
            visitor.visit_var_decl(decl_ref)?;
        }
        StmtKind::Assign(ref mut lhses, ref mut rhs) => {
            for lhs in lhses {
                visitor.visit_ident(lhs)?;
            }
            visitor.visit_expr(rhs)?;
        }
        StmtKind::Havoc(_dir, ref mut idents) => {
            for ident in idents {
                visitor.visit_ident(ident)?;
            }
        }
        StmtKind::Assert(_dir, ref mut expr) => {
            visitor.visit_expr(expr)?;
        }
        StmtKind::Assume(_dir, ref mut expr) => {
            visitor.visit_expr(expr)?;
        }
        StmtKind::Compare(_dir, ref mut expr) => {
            visitor.visit_expr(expr)?;
        }
        StmtKind::Negate(_dir) => {}
        StmtKind::Validate(_dir) => {}
        StmtKind::Tick(ref mut expr) => {
            visitor.visit_expr(expr)?;
        }
        StmtKind::Demonic(ref mut block1, ref mut block2) => {
            visitor.visit_stmts(block1)?;
            visitor.visit_stmts(block2)?;
        }
        StmtKind::Angelic(ref mut block1, ref mut block2) => {
            visitor.visit_stmts(block1)?;
            visitor.visit_stmts(block2)?;
        }
        StmtKind::If(ref mut cond, ref mut block1, ref mut block2) => {
            visitor.visit_expr(cond)?;
            visitor.visit_stmts(block1)?;
            visitor.visit_stmts(block2)?;
        }
        StmtKind::While(ref mut cond, ref mut block) => {
            visitor.visit_expr(cond)?;
            visitor.visit_stmts(block)?;
        }
        StmtKind::Annotation(ref mut ident, ref mut args, ref mut stmt) => {
            visitor.visit_ident(ident)?;
            visitor.visit_exprs(args)?;
            visitor.visit_stmt(stmt)?;
        }
        StmtKind::Label(ref mut ident) => {
            visitor.visit_ident(ident)?;
        }
    }
    Ok(())
}
