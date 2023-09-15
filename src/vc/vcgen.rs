//! Implementation of the core `vc` calculus. Given a list of statements,
//! compute the verification conditions. The generated verification conditions
//! will contain substitution expressions and use sharing for post-expectations
//! that occur in multiple places.

use crate::{
    ast::{
        BinOpKind, DeclKind, Direction, Expr, ExprBuilder, ExprKind, Ident, QuantOpKind,
        SpanVariant, Stmt, StmtKind, UnOpKind,
    },
    tyctx::TyCtx,
};

pub struct Vcgen<'tcx> {
    tcx: &'tcx TyCtx,
    print_label_vc: bool,
}

impl<'tcx> Vcgen<'tcx> {
    pub fn new(tcx: &'tcx TyCtx, print_label_vc: bool) -> Self {
        Vcgen {
            tcx,
            print_label_vc,
        }
    }

    pub fn vcgen_stmts(&self, stmts: &[Stmt], post: Expr) -> Expr {
        stmts
            .iter()
            .rev()
            .fold(post, |acc, x| self.vcgen_stmt(x, acc))
    }

    pub fn vcgen_stmt(&self, stmt: &Stmt, post: Expr) -> Expr {
        let builder = ExprBuilder::new(stmt.span.variant(SpanVariant::VC));
        let spec_ty = Some(self.tcx.spec_ty().clone());
        match &stmt.node {
            StmtKind::Block(block) => self.vcgen_stmts(block, post),
            StmtKind::Var(var_def) => {
                let var_def = var_def.borrow();
                if let Some(init) = &var_def.init {
                    self.generate_assign(init, builder, &[var_def.name], post)
                } else {
                    post
                }
            }
            StmtKind::Assign(lhses, rhs) => self.generate_assign(rhs, builder, lhses, post),
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
                        return builder.binary(
                            BinOpKind::Compare,
                            spec_ty,
                            lhs.clone(),
                            rhs.clone(),
                        );
                    }
                    ExprKind::Binary(bin_op, lhs, rhs)
                        if *dir == Direction::Up && bin_op.node == BinOpKind::CoImpl =>
                    {
                        return builder.binary(
                            BinOpKind::CoCompare,
                            spec_ty,
                            lhs.clone(),
                            rhs.clone(),
                        );
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
                let post1 = self.vcgen_stmts(block1, post.clone());
                let post2 = self.vcgen_stmts(block2, post);
                builder.binary(BinOpKind::Inf, spec_ty, post1, post2)
            }
            StmtKind::Angelic(block1, block2) => {
                let post1 = self.vcgen_stmts(block1, post.clone());
                let post2 = self.vcgen_stmts(block2, post);
                builder.binary(BinOpKind::Sup, spec_ty, post1, post2)
            }
            StmtKind::If(cond, block1, block2) => {
                let post1 = self.vcgen_stmts(block1, post.clone());
                let post2 = self.vcgen_stmts(block2, post);
                builder.ite(spec_ty, cond.clone(), post1, post2)
            }
            StmtKind::While(_, _) => todo!(),
            StmtKind::Annotation(_, _, _) => todo!(),
            StmtKind::Label(ident) => {
                if self.print_label_vc {
                    println!("VC at label `{}`: {}", ident, &post);
                }
                post
            }
        }
    }

    fn generate_assign(
        &self,
        rhs: &Expr,
        builder: ExprBuilder,
        lhses: &[Ident],
        post: Expr,
    ) -> Expr {
        if let ExprKind::Call(ident, args) = &rhs.kind {
            match self.tcx.get(*ident).as_deref() {
                Some(DeclKind::ProcIntrin(proc_intrin)) => {
                    return proc_intrin.vcgen(builder, args, lhses, post)
                }
                Some(DeclKind::FuncDecl(_)) | Some(DeclKind::FuncIntrin(_)) => {}
                Some(decl) => panic!("cannot do vc generation for {:?}", decl),
                None => panic!("missing declaration for call of {}", ident),
            }
        };
        if let [lhs] = lhses {
            builder.subst(post, [(*lhs, rhs.clone())])
        } else {
            panic!("for vc generation, there must be exactly one lhs in an assignment");
        }
    }
}
