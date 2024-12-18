//! Implementation of the core `vc` calculus. Given a list of statements,
//! compute the verification conditions. The generated verification conditions
//! will contain substitution expressions and use sharing for post-expectations
//! that occur in multiple places.

use ariadne::ReportKind;

use crate::{
    ast::{
        BinOpKind, Block, DeclKind, Diagnostic, Direction, Expr, ExprBuilder, ExprKind, Ident,
        Label, QuantOpKind, Span, SpanVariant, Stmt, StmtKind, UnOpKind,
    },
    intrinsic::annotations::AnnotationKind,
    tyctx::TyCtx,
};

use super::explain::{explain_annotated_while, explain_proc_call, explain_subst, VcExplanation};

pub struct Vcgen<'tcx> {
    pub(super) tcx: &'tcx TyCtx,
    pub explanation: Option<VcExplanation>,
}

impl<'tcx> Vcgen<'tcx> {
    /// Create a new `Vcgen` instance. Initialize with an optional
    /// `VcExplanation` structure to enable explanations.
    pub fn new(tcx: &'tcx TyCtx, explanation: Option<VcExplanation>) -> Self {
        Vcgen { tcx, explanation }
    }

    pub fn vcgen_block(&mut self, block: &Block, post: Expr) -> Result<Expr, Diagnostic> {
        let prev_block_span = if let Some(ref mut explanation) = self.explanation {
            let prev_block_span = explanation.set_block_span(Some(block.span));
            let mut end_span = block.span;
            end_span.start = end_span.end - 1;
            explanation.add_expr(end_span, post.clone(), true);
            prev_block_span
        } else {
            None
        };
        let res = self.vcgen_stmts(&block.node, post);
        if let Some(ref mut explanation) = self.explanation {
            explanation.set_block_span(prev_block_span);
        }
        res
    }

    pub fn vcgen_stmts(&mut self, stmts: &[Stmt], post: Expr) -> Result<Expr, Diagnostic> {
        stmts
            .iter()
            .rev()
            .try_fold(post, |acc, x| self.vcgen_stmt(x, acc))
    }

    fn vcgen_stmt(&mut self, stmt: &Stmt, post: Expr) -> Result<Expr, Diagnostic> {
        let builder = ExprBuilder::new(stmt.span.variant(SpanVariant::VC));
        let spec_ty = Some(self.tcx.spec_ty().clone());
        let res = match &stmt.node {
            StmtKind::Seq(block) => self.vcgen_stmts(block, post)?,
            StmtKind::Var(var_def) => {
                let var_def = var_def.borrow();
                if let Some(init) = &var_def.init {
                    self.generate_assign(stmt.span, init, builder, &[var_def.name], post)
                } else {
                    post
                }
            }
            StmtKind::Assign(lhses, rhs) => {
                self.generate_assign(stmt.span, rhs, builder, lhses, post)
            }
            StmtKind::Havoc(dir, idents) => {
                let quant_op = match dir {
                    Direction::Down => QuantOpKind::Inf,
                    Direction::Up => QuantOpKind::Sup,
                };
                builder.quant(quant_op, idents.iter().cloned(), post)
            }
            StmtKind::Assert(dir, expr) => {
                let bin_op = match dir {
                    Direction::Down => BinOpKind::Inf,
                    Direction::Up => BinOpKind::Sup,
                };
                builder.binary(bin_op, spec_ty, expr.clone(), post)
            }
            StmtKind::Assume(dir, expr) => {
                let bin_op = match dir {
                    Direction::Down => BinOpKind::Impl,
                    Direction::Up => BinOpKind::CoImpl,
                };
                builder.binary(bin_op, spec_ty, expr.clone(), post)
            }
            StmtKind::Compare(dir, expr) => {
                let bin_op = match dir {
                    Direction::Down => BinOpKind::Compare,
                    Direction::Up => BinOpKind::CoCompare,
                };
                builder.binary(bin_op, spec_ty, expr.clone(), post)
            }
            StmtKind::Negate(dir) => {
                if let Some(ref mut explanation) = self.explanation {
                    explanation
                        .direction
                        .handle_negation_backwards(stmt)
                        .map_err(|_| unsupported_stmt_diagnostic(stmt))?;
                }
                let un_op = match dir {
                    Direction::Down => UnOpKind::Not,
                    Direction::Up => UnOpKind::Non,
                };
                builder.unary(un_op, spec_ty, post)
            }
            StmtKind::Validate(dir) => {
                // TODO: this optimization should be moved somewhere else
                match &post.kind {
                    ExprKind::Binary(bin_op, lhs, rhs)
                        if *dir == Direction::Down && bin_op.node == BinOpKind::Impl =>
                    {
                        return Ok(builder.binary(
                            BinOpKind::Compare,
                            spec_ty,
                            lhs.clone(),
                            rhs.clone(),
                        ));
                    }
                    ExprKind::Binary(bin_op, lhs, rhs)
                        if *dir == Direction::Up && bin_op.node == BinOpKind::CoImpl =>
                    {
                        return Ok(builder.binary(
                            BinOpKind::CoCompare,
                            spec_ty,
                            lhs.clone(),
                            rhs.clone(),
                        ));
                    }
                    _ => {}
                };

                let un_op = match dir {
                    Direction::Down => UnOpKind::Not,
                    Direction::Up => UnOpKind::Non,
                };
                builder.unary(un_op, spec_ty.clone(), builder.unary(un_op, spec_ty, post))
            }
            StmtKind::Tick(expr) => builder.binary(BinOpKind::Add, spec_ty, expr.clone(), post),
            StmtKind::Demonic(block1, block2) => {
                let post1 = self.vcgen_block(block1, post.clone())?;
                let post2 = self.vcgen_block(block2, post)?;
                builder.binary(BinOpKind::Inf, spec_ty, post1, post2)
            }
            StmtKind::Angelic(block1, block2) => {
                let post1 = self.vcgen_block(block1, post.clone())?;
                let post2 = self.vcgen_block(block2, post)?;
                builder.binary(BinOpKind::Sup, spec_ty, post1, post2)
            }
            StmtKind::If(cond, block1, block2) => {
                let post1 = self.vcgen_block(block1, post.clone())?;
                let post2 = self.vcgen_block(block2, post)?;
                builder.ite(spec_ty, cond.clone(), post1, post2)
            }
            StmtKind::While(_, _) => return Err(unsupported_while_loop_diagnostic(stmt)),
            StmtKind::Annotation(_, ident, _, inner_stmt) => {
                // there may be still slicing annotations left, which we just
                // walk through. this may happen if the slicing transformer
                // didn't run at all (slicing disabled) or when it errored, but
                // we still continue.
                if let Some(decl_ref) = self.tcx.get(*ident) {
                    if let DeclKind::AnnotationDecl(AnnotationKind::Slicing(_)) = *decl_ref {
                        return self.vcgen_stmt(inner_stmt, post);
                    }
                }
                // only if explanations are enabled, explain the while loop and
                // return the invariant as the pre. otherwise, error.
                if self.explanation.is_some() {
                    explain_annotated_while(self, stmt, &post)?
                } else {
                    return Err(unsupported_stmt_diagnostic(stmt));
                }
            }
            StmtKind::Label(_ident) => {
                // TODO
                post
            }
        };

        if let Some(ref mut explanation) = self.explanation {
            explanation.add_expr(stmt.span, res.clone(), false);
        }

        Ok(res)
    }

    fn generate_assign(
        &mut self,
        span: Span,
        rhs: &Expr,
        builder: ExprBuilder,
        lhses: &[Ident],
        post: Expr,
    ) -> Expr {
        if let ExprKind::Call(ident, args) = &rhs.kind {
            match self.tcx.get(*ident).as_deref() {
                Some(DeclKind::ProcIntrin(proc_intrin)) => {
                    let mut res = proc_intrin.vcgen(builder, args, lhses, post);
                    explain_subst(self, span, &mut res);
                    return res;
                }
                // only if explanations are enabled, return a simple explanation
                // for proc calls.
                Some(DeclKind::ProcDecl(decl_ref)) if self.explanation.is_some() => {
                    let mut res = explain_proc_call(decl_ref, args, &builder);
                    explain_subst(self, span, &mut res);
                    return res;
                }
                Some(DeclKind::FuncDecl(_)) | Some(DeclKind::FuncIntrin(_)) => {}
                Some(decl) => panic!("cannot do vc generation for {:?}", decl),
                None => panic!("missing declaration for call of {}", ident),
            }
        };
        if let [lhs] = lhses {
            let mut res = builder.subst(post, [(*lhs, rhs.clone())]);
            explain_subst(self, span, &mut res);
            res
        } else {
            panic!("for vc generation, there must be exactly one lhs in an assignment");
        }
    }
}

fn unsupported_while_loop_diagnostic(stmt: &Stmt) -> Diagnostic {
    Diagnostic::new(ReportKind::Error, stmt.span)
            .with_message("while loops must have a proof rule annotation")
            .with_note(
                "without a proof rule, Caesar cannot generate verification conditions. read more at: https://www.caesarverifier.org/docs/proof-rules/",
            )
            .with_label(
                Label::new(stmt.span).with_message("this loop needs an annotation"),
            )
}

pub(super) fn unsupported_stmt_diagnostic(stmt: &Stmt) -> Diagnostic {
    Diagnostic::new(ReportKind::Error, stmt.span)
        .with_message("this statement is not supported in vc generation")
        .with_note("this is most likely an internal error")
        .with_label(Label::new(stmt.span).with_message("this is not supported"))
}
