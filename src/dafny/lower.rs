use std::collections::HashSet;

use ariadne::ReportKind;

use super::{
    ast as dafny_ast,
    index::{DeclIndex, FlatDeclKind, FlatDeclRecord, FlatDeclRef},
};
use crate::{
    ast::{
        BinOpKind, DeclKind, DeclRef, Diagnostic, Expr, ExprKind, FileId, FuncDecl, Ident, Label,
        LitKind, Param, ProcDecl, ProcSpec, QuantOpKind, QuantVar, Span, Stmt, StmtKind, TyKind,
        UnOpKind, VarDecl,
    },
    depgraph::DepGraph,
    driver::error::CaesarError,
    tyctx::TyCtx,
};

/// A lowering error that can be reported as a Caesar diagnostic at a precise source span.
#[derive(Debug, Clone)]
pub(crate) struct TranslationError {
    span: Span,
    message: String,
    label: String,
    note: Option<String>,
}

impl TranslationError {
    pub(crate) fn unsupported(
        span: Span,
        message: impl Into<String>,
        label: impl Into<String>,
    ) -> Self {
        TranslationError {
            span,
            message: message.into(),
            label: label.into(),
            note: None,
        }
    }

    pub(crate) fn diagnostic(&self, kind: ReportKind<'static>) -> Diagnostic {
        let diagnostic = Diagnostic::new(kind, self.span)
            .with_message(&self.message)
            .with_label(Label::new(self.span).with_message(&self.label));
        if let Some(note) = &self.note {
            diagnostic.with_note(note)
        } else {
            diagnostic
        }
    }
}

/// Stateful lowering context from surface HeyVL declarations to the internal Dafny AST.
pub(crate) struct DafnyLowerer<'a> {
    pub(crate) tcx: &'a TyCtx,
    pub(crate) depgraph: &'a DepGraph,
    pub(crate) index: &'a DeclIndex,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SupportedListIntrinsic {
    Len,
    Select,
    Store,
}

impl<'a> DafnyLowerer<'a> {
    /// Check whether one locally declared item can be lowered by this backend.
    pub(crate) fn local_support(&self, record: &FlatDeclRecord) -> Result<(), TranslationError> {
        match &record.decl {
            FlatDeclRef::Domain(_) => {
                self.lower_domain(record)?;
            }
            FlatDeclRef::Func(func_ref) => {
                self.lower_function(func_ref)?;
            }
            FlatDeclRef::Axiom(axiom_ref) => {
                self.lower_axiom_expr(&axiom_ref.borrow().axiom)?;
            }
            FlatDeclRef::Proc(proc_ref) => {
                self.lower_proc(proc_ref, &HashSet::new())?;
            }
        }
        Ok(())
    }

    /// Lower the declarations selected for one source file into a Dafny AST file.
    pub(crate) fn lower_file(
        &self,
        file_id: FileId,
        roots: &[Ident],
        included: &HashSet<Ident>,
    ) -> Result<dafny_ast::File, CaesarError> {
        let mut decls = Vec::new();

        for record in self.index.ordered.iter().filter(|record| {
            record.kind == FlatDeclKind::Domain && included.contains(&record.ident)
        }) {
            decls.push(dafny_ast::Decl::Type(self.lower_domain(record).map_err(
                |err| CaesarError::Diagnostic(err.diagnostic(ReportKind::Error)),
            )?));
        }

        for record in
            self.index.ordered.iter().filter(|record| {
                record.kind == FlatDeclKind::Func && included.contains(&record.ident)
            })
        {
            let FlatDeclRef::Func(func_ref) = &record.decl else {
                unreachable!();
            };
            decls.push(dafny_ast::Decl::Function(
                self.lower_function(func_ref)
                    .map_err(|err| CaesarError::Diagnostic(err.diagnostic(ReportKind::Error)))?,
            ));
        }

        let root_set: HashSet<_> = roots.iter().copied().collect();
        for record in self.index.ordered.iter().filter(|record| {
            record.kind == FlatDeclKind::Proc
                && included.contains(&record.ident)
                && !root_set.contains(&record.ident)
        }) {
            let FlatDeclRef::Proc(proc_ref) = &record.decl else {
                unreachable!();
            };
            decls.push(dafny_ast::Decl::Method(
                self.lower_proc(proc_ref, included)
                    .map_err(|err| CaesarError::Diagnostic(err.diagnostic(ReportKind::Error)))?,
            ));
        }

        for record in self.index.ordered.iter().filter(|record| {
            record.kind == FlatDeclKind::Proc
                && record.file_id == file_id
                && root_set.contains(&record.ident)
        }) {
            let FlatDeclRef::Proc(proc_ref) = &record.decl else {
                unreachable!();
            };
            decls.push(dafny_ast::Decl::Method(
                self.lower_proc(proc_ref, included)
                    .map_err(|err| CaesarError::Diagnostic(err.diagnostic(ReportKind::Error)))?,
            ));
        }

        Ok(dafny_ast::File { decls })
    }

    fn lower_domain(
        &self,
        record: &FlatDeclRecord,
    ) -> Result<dafny_ast::TypeDecl, TranslationError> {
        let FlatDeclRef::Domain(domain_ref) = &record.decl else {
            unreachable!();
        };
        let domain = domain_ref.borrow();
        Ok(dafny_ast::TypeDecl {
            name: domain.name.name.to_owned(),
        })
    }

    fn lower_function(
        &self,
        func_ref: &DeclRef<FuncDecl>,
    ) -> Result<dafny_ast::FunctionDecl, TranslationError> {
        let func = func_ref.borrow();
        let body = {
            let body = func.body.borrow();
            body.as_ref()
                .map(|expr| self.lower_expr(expr))
                .transpose()?
        };
        Ok(dafny_ast::FunctionDecl {
            name: func.name.name.to_owned(),
            params: func
                .inputs
                .node
                .iter()
                .map(|param| self.lower_param(param))
                .collect::<Result<Vec<_>, _>>()?,
            return_ty: self.lower_type(&func.output, func.span)?,
            body,
        })
    }

    fn lower_proc(
        &self,
        proc_ref: &DeclRef<ProcDecl>,
        included: &HashSet<Ident>,
    ) -> Result<dafny_ast::MethodDecl, TranslationError> {
        let proc = proc_ref.borrow();
        if proc.direction != crate::ast::Direction::Down {
            return Err(TranslationError::unsupported(
                proc.span,
                format!("Dafny: `coproc {}` is not supported", proc.name.name),
                "expected `proc` here",
            ));
        }
        if let Some(calculus) = proc.calculus {
            let calculus_name = calculus.name.to_owned();
            if calculus_name != "wp" && calculus_name != "ert" {
                return Err(TranslationError::unsupported(
                    calculus.span,
                    format!("Dafny: calculus `@{}` is not supported", calculus.name),
                    "expected no calculus, `@wp`, or `@ert`",
                ));
            }
        }

        let body = proc.body.borrow();
        let mut method_body = None;
        if let Some(block) = &*body {
            let mut stmts = Vec::new();
            let reachable = self.depgraph.get_reachable([proc.name]);
            for record in &self.index.ordered {
                if record.kind != FlatDeclKind::Axiom
                    || !included.contains(&record.ident)
                    || !reachable.contains(&record.ident)
                {
                    continue;
                }
                let FlatDeclRef::Axiom(axiom_ref) = &record.decl else {
                    unreachable!();
                };
                stmts.push(dafny_ast::Stmt::Assume(dafny_ast::AssumeStmt {
                    axiom: true,
                    expr: self.lower_axiom_expr(&axiom_ref.borrow().axiom)?,
                }));
            }
            stmts.extend(self.lower_block(block)?.stmts);
            method_body = Some(dafny_ast::Block { stmts });
        }

        Ok(dafny_ast::MethodDecl {
            axiom: body.is_none(),
            name: proc.name.name.to_owned(),
            params: proc
                .inputs
                .node
                .iter()
                .map(|param| self.lower_param(param))
                .collect::<Result<Vec<_>, _>>()?,
            returns: proc
                .outputs
                .node
                .iter()
                .map(|param| self.lower_param(param))
                .collect::<Result<Vec<_>, _>>()?,
            requires: proc
                .spec
                .iter()
                .filter_map(|spec| match spec {
                    ProcSpec::Requires(expr) => Some(self.lower_embedded_bool(expr)),
                    ProcSpec::Ensures(_) => None,
                })
                .collect::<Result<Vec<_>, _>>()?,
            ensures: proc
                .spec
                .iter()
                .filter_map(|spec| match spec {
                    ProcSpec::Requires(_) => None,
                    ProcSpec::Ensures(expr) => Some(self.lower_embedded_bool(expr)),
                })
                .collect::<Result<Vec<_>, _>>()?,
            decreases_star: body.is_some(),
            body: method_body,
        })
    }

    fn lower_block(&self, block: &crate::ast::Block) -> Result<dafny_ast::Block, TranslationError> {
        let mut stmts = Vec::new();
        for stmt in &block.node {
            stmts.extend(self.lower_stmt(stmt)?);
        }
        Ok(dafny_ast::Block { stmts })
    }

    fn lower_stmt(&self, stmt: &Stmt) -> Result<Vec<dafny_ast::Stmt>, TranslationError> {
        match &stmt.node {
            StmtKind::Seq(stmts) => {
                let block = crate::ast::Spanned::new(stmt.span, stmts.clone());
                Ok(vec![dafny_ast::Stmt::Block(self.lower_block(&block)?)])
            }
            StmtKind::Var(var_ref) => Ok(vec![self.lower_var_decl(&var_ref.borrow())?]),
            StmtKind::Assign(lhses, rhs) => {
                if let ExprKind::Call(ident, args) = &rhs.kind {
                    if let Some(decl) = self.tcx.get(*ident) {
                        match decl.as_ref() {
                            DeclKind::ProcDecl(_) => {
                                let lowered_args = self.lower_exprs(args)?;
                                return Ok(vec![if lhses.is_empty() {
                                    dafny_ast::Stmt::Call(dafny_ast::CallStmt {
                                        method: ident.name.to_owned(),
                                        args: lowered_args,
                                    })
                                } else {
                                    dafny_ast::Stmt::AssignCall(dafny_ast::AssignCallStmt {
                                        lhs: lhses
                                            .iter()
                                            .map(|ident| ident.name.to_owned())
                                            .collect(),
                                        method: ident.name.to_owned(),
                                        args: lowered_args,
                                    })
                                }]);
                            }
                            DeclKind::ProcIntrin(_) => {
                                return Err(TranslationError::unsupported(
                                    rhs.span,
                                    format!(
                                        "Dafny: intrinsic procedure `{}` is not supported",
                                        ident.name
                                    ),
                                    "unsupported procedure call",
                                ));
                            }
                            _ => {}
                        }
                    }
                }

                if lhses.len() != 1 {
                    return Err(TranslationError::unsupported(
                        stmt.span,
                        "Dafny: tuple assignment is only supported for procedure calls",
                        "unsupported assignment",
                    ));
                }

                Ok(vec![dafny_ast::Stmt::Assign(dafny_ast::AssignStmt {
                    lhs: lhses[0].name.to_owned(),
                    rhs: self.lower_expr(rhs)?,
                })])
            }
            StmtKind::Havoc(direction, vars) => {
                if *direction != crate::ast::Direction::Down {
                    return Err(TranslationError::unsupported(
                        stmt.span,
                        "Dafny: `cohavoc` is not supported",
                        "expected `havoc` here",
                    ));
                }

                Ok(vars
                    .iter()
                    .map(|ident| {
                        dafny_ast::Stmt::SuchThatAssign(dafny_ast::SuchThatAssignStmt {
                            lhs: vec![ident.name.to_owned()],
                            predicate: true_expr(),
                        })
                    })
                    .collect())
            }
            StmtKind::Assert(direction, expr) => {
                if *direction != crate::ast::Direction::Down {
                    return Err(TranslationError::unsupported(
                        stmt.span,
                        "Dafny: `coassert` is not supported",
                        "expected `assert ?(b)` here",
                    ));
                }

                Ok(vec![dafny_ast::Stmt::Assert(dafny_ast::AssertStmt {
                    expr: self.lower_embedded_bool(expr)?,
                })])
            }
            StmtKind::Assume(direction, expr) => {
                if *direction != crate::ast::Direction::Down {
                    return Err(TranslationError::unsupported(
                        stmt.span,
                        "Dafny: `coassume` is not supported",
                        "expected `assume ?(b)` here",
                    ));
                }

                Ok(vec![dafny_ast::Stmt::Assume(dafny_ast::AssumeStmt {
                    axiom: true,
                    expr: self.lower_embedded_bool(expr)?,
                })])
            }
            StmtKind::If(cond, lhs, rhs) => Ok(vec![dafny_ast::Stmt::If(dafny_ast::IfStmt {
                cond: self.lower_expr(cond)?,
                then_branch: self.lower_block(lhs)?,
                else_branch: self.lower_block(rhs)?,
            })]),
            StmtKind::While(_, _) => Err(TranslationError::unsupported(
                stmt.span,
                "Dafny: `while` loops must use `@invariant(?(...))`",
                "missing supported loop invariant",
            )),
            StmtKind::Annotation(_, ident, inputs, inner) => {
                if ident.name.to_owned() != "invariant" {
                    return Err(TranslationError::unsupported(
                        stmt.span,
                        format!("Dafny: annotation `@{}` is not supported", ident.name),
                        "unsupported annotation",
                    ));
                }
                if inputs.len() != 1 {
                    return Err(TranslationError::unsupported(
                        stmt.span,
                        "Dafny: `@invariant` expects exactly one argument",
                        "invalid invariant annotation",
                    ));
                }
                let StmtKind::While(cond, body) = &inner.node else {
                    return Err(TranslationError::unsupported(
                        stmt.span,
                        "Dafny: `@invariant` must annotate a `while` loop",
                        "expected `@invariant(?(...)) while ...`",
                    ));
                };

                Ok(vec![dafny_ast::Stmt::While(dafny_ast::WhileStmt {
                    cond: self.lower_expr(cond)?,
                    invariants: vec![self.lower_embedded_bool(&inputs[0])?],
                    decreases_star: true,
                    body: self.lower_block(body)?,
                })])
            }
            StmtKind::Compare(_, _)
            | StmtKind::Negate(_)
            | StmtKind::Validate(_)
            | StmtKind::Tick(_)
            | StmtKind::Weigh(_)
            | StmtKind::Demonic(_, _)
            | StmtKind::Angelic(_, _)
            | StmtKind::Additive(_, _)
            | StmtKind::Label(_) => Err(TranslationError::unsupported(
                stmt.span,
                "Dafny: statement is not supported by this backend",
                "unsupported statement",
            )),
        }
    }

    fn lower_var_decl(&self, var: &VarDecl) -> Result<dafny_ast::Stmt, TranslationError> {
        let ty = self.lower_type(&var.ty, var.span)?;
        let init = if let Some(init) = &var.init {
            if let ExprKind::Call(ident, args) = &init.kind {
                if let Some(decl) = self.tcx.get(*ident) {
                    match decl.as_ref() {
                        DeclKind::ProcDecl(_) => dafny_ast::VarInit::MethodCall {
                            method: ident.name.to_owned(),
                            args: self.lower_exprs(args)?,
                        },
                        DeclKind::ProcIntrin(_) => {
                            return Err(TranslationError::unsupported(
                                init.span,
                                format!(
                                    "Dafny: intrinsic procedure `{}` is not supported",
                                    ident.name
                                ),
                                "unsupported procedure call",
                            ));
                        }
                        _ => dafny_ast::VarInit::Expr(self.lower_expr(init)?),
                    }
                } else {
                    dafny_ast::VarInit::Expr(self.lower_expr(init)?)
                }
            } else {
                dafny_ast::VarInit::Expr(self.lower_expr(init)?)
            }
        } else {
            dafny_ast::VarInit::SuchThat(true_expr())
        };

        Ok(dafny_ast::Stmt::Var(dafny_ast::VarDecl {
            name: var.name.name.to_owned(),
            ty,
            init,
        }))
    }

    fn lower_axiom_expr(&self, expr: &Expr) -> Result<dafny_ast::Expr, TranslationError> {
        self.lower_expr(expr)
    }

    fn lower_embedded_bool(&self, expr: &Expr) -> Result<dafny_ast::Expr, TranslationError> {
        match &expr.kind {
            ExprKind::Unary(un_op, operand) if un_op.node == UnOpKind::Embed => {
                self.lower_expr(operand)
            }
            _ => Err(TranslationError::unsupported(
                expr.span,
                "Dafny: Boolean specifications must use the `?(b)` embedding",
                "expected `?(b)` here",
            )),
        }
    }

    fn lower_expr(&self, expr: &Expr) -> Result<dafny_ast::Expr, TranslationError> {
        match &expr.kind {
            ExprKind::Var(ident) => Ok(dafny_ast::Expr::Var(ident.name.to_owned())),
            ExprKind::Call(ident, args) => self.lower_call_expr(*ident, args, expr.span),
            ExprKind::Ite(cond, lhs, rhs) => Ok(dafny_ast::Expr::Ite {
                cond: Box::new(self.lower_expr(cond)?),
                then_expr: Box::new(self.lower_expr(lhs)?),
                else_expr: Box::new(self.lower_expr(rhs)?),
            }),
            ExprKind::Binary(op, lhs, rhs) => {
                let op = match op.node {
                    BinOpKind::Add => dafny_ast::BinaryOp::Add,
                    BinOpKind::Sub => dafny_ast::BinaryOp::Sub,
                    BinOpKind::Mul => dafny_ast::BinaryOp::Mul,
                    BinOpKind::Div => dafny_ast::BinaryOp::Div,
                    BinOpKind::Mod => dafny_ast::BinaryOp::Mod,
                    BinOpKind::And => dafny_ast::BinaryOp::And,
                    BinOpKind::Or => dafny_ast::BinaryOp::Or,
                    BinOpKind::Eq => dafny_ast::BinaryOp::Eq,
                    BinOpKind::Lt => dafny_ast::BinaryOp::Lt,
                    BinOpKind::Le => dafny_ast::BinaryOp::Le,
                    BinOpKind::Ne => dafny_ast::BinaryOp::Ne,
                    BinOpKind::Ge => dafny_ast::BinaryOp::Ge,
                    BinOpKind::Gt => dafny_ast::BinaryOp::Gt,
                    BinOpKind::Impl => dafny_ast::BinaryOp::Impl,
                    BinOpKind::Inf
                    | BinOpKind::Sup
                    | BinOpKind::CoImpl
                    | BinOpKind::Compare
                    | BinOpKind::CoCompare => {
                        return Err(TranslationError::unsupported(
                            expr.span,
                            "Dafny: this HeyVL operator is not supported",
                            "unsupported operator",
                        ));
                    }
                };
                Ok(dafny_ast::Expr::Binary {
                    op,
                    lhs: Box::new(self.lower_expr(lhs)?),
                    rhs: Box::new(self.lower_expr(rhs)?),
                })
            }
            ExprKind::Unary(un_op, operand) => match un_op.node {
                UnOpKind::Not => Ok(dafny_ast::Expr::Unary {
                    op: dafny_ast::UnaryOp::Not,
                    expr: Box::new(self.lower_expr(operand)?),
                }),
                UnOpKind::Parens => Ok(dafny_ast::Expr::Unary {
                    op: dafny_ast::UnaryOp::Parens,
                    expr: Box::new(self.lower_expr(operand)?),
                }),
                UnOpKind::Embed => Err(TranslationError::unsupported(
                    expr.span,
                    "Dafny: `?(b)` is only supported in pre/post/assert/assume/@invariant",
                    "unsupported Boolean embedding",
                )),
                UnOpKind::Iverson | UnOpKind::Non => Err(TranslationError::unsupported(
                    expr.span,
                    "Dafny: quantitative unary operators are not supported",
                    "unsupported unary operator",
                )),
            },
            ExprKind::Cast(operand) => self.lower_cast(expr, operand),
            ExprKind::Quant(quant_op, vars, ann, body) => {
                let quantifier = match quant_op.node {
                    QuantOpKind::Forall => dafny_ast::Quantifier::Forall,
                    QuantOpKind::Exists => dafny_ast::Quantifier::Exists,
                    QuantOpKind::Inf | QuantOpKind::Sup => {
                        return Err(TranslationError::unsupported(
                            expr.span,
                            "Dafny: quantitative quantifiers are not supported",
                            "unsupported quantifier",
                        ));
                    }
                };
                let vars = vars
                    .iter()
                    .map(|var| self.lower_quant_var(var))
                    .collect::<Result<Vec<_>, _>>()?;
                let triggers = ann
                    .triggers
                    .iter()
                    .map(|trigger| self.lower_exprs(trigger.terms()))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(dafny_ast::Expr::Quantified {
                    quantifier,
                    vars,
                    triggers,
                    body: Box::new(self.lower_expr(body)?),
                })
            }
            ExprKind::Subst(_, _, _) => Err(TranslationError::unsupported(
                expr.span,
                "Dafny: substitution expressions are not supported",
                "unsupported expression",
            )),
            ExprKind::Lit(lit) => self.lower_lit(&lit.node, expr.span),
        }
    }

    fn lower_call_expr(
        &self,
        ident: Ident,
        args: &[Expr],
        span: Span,
    ) -> Result<dafny_ast::Expr, TranslationError> {
        if let Some(intrinsic) = supported_list_intrinsic(self.tcx, ident) {
            return match intrinsic {
                SupportedListIntrinsic::Len => {
                    let [list] = args else {
                        return Err(TranslationError::unsupported(
                            span,
                            "Dafny: `len` expects one argument",
                            "invalid intrinsic call",
                        ));
                    };
                    Ok(dafny_ast::Expr::SeqLen(Box::new(self.lower_expr(list)?)))
                }
                SupportedListIntrinsic::Select => {
                    let [list, index] = args else {
                        return Err(TranslationError::unsupported(
                            span,
                            "Dafny: `select` expects two arguments",
                            "invalid intrinsic call",
                        ));
                    };
                    Ok(dafny_ast::Expr::Index {
                        collection: Box::new(self.lower_expr(list)?),
                        index: Box::new(self.lower_expr(index)?),
                    })
                }
                SupportedListIntrinsic::Store => {
                    let [list, index, value] = args else {
                        return Err(TranslationError::unsupported(
                            span,
                            "Dafny: `store` expects three arguments",
                            "invalid intrinsic call",
                        ));
                    };
                    Ok(dafny_ast::Expr::Update {
                        collection: Box::new(self.lower_expr(list)?),
                        index: Box::new(self.lower_expr(index)?),
                        value: Box::new(self.lower_expr(value)?),
                    })
                }
            };
        }

        let decl = self.tcx.get(ident).ok_or_else(|| {
            TranslationError::unsupported(
                span,
                format!("Dafny: unknown callee `{}`", ident.name),
                "unknown call target",
            )
        })?;
        match decl.as_ref() {
            DeclKind::FuncDecl(_) => Ok(dafny_ast::Expr::Call {
                function: ident.name.to_owned(),
                args: self.lower_exprs(args)?,
            }),
            DeclKind::FuncIntrin(_) => Err(TranslationError::unsupported(
                span,
                format!(
                    "Dafny: intrinsic function `{}` is not supported",
                    ident.name
                ),
                "unsupported intrinsic function",
            )),
            DeclKind::ProcDecl(_) | DeclKind::ProcIntrin(_) => Err(TranslationError::unsupported(
                span,
                format!(
                    "Dafny: procedure `{}` cannot be used in expression position",
                    ident.name
                ),
                "expected a pure function call",
            )),
            _ => Err(TranslationError::unsupported(
                span,
                format!("Dafny: call target `{}` is not supported", ident.name),
                "unsupported call target",
            )),
        }
    }

    fn lower_cast(&self, expr: &Expr, operand: &Expr) -> Result<dafny_ast::Expr, TranslationError> {
        let Some(target_ty) = expr.ty.as_ref() else {
            return Err(TranslationError::unsupported(
                expr.span,
                "Dafny: cast without a resolved target type is not supported",
                "unsupported cast",
            ));
        };
        match target_ty {
            TyKind::Bool | TyKind::Int | TyKind::UInt => self.lower_expr(operand),
            TyKind::Real | TyKind::UReal | TyKind::EUReal | TyKind::SpecTy => {
                Err(TranslationError::unsupported(
                    expr.span,
                    "Dafny: quantitative casts are not supported",
                    "unsupported cast",
                ))
            }
            _ => self.lower_expr(operand),
        }
    }

    fn lower_quant_var(&self, var: &QuantVar) -> Result<dafny_ast::QuantVar, TranslationError> {
        match var {
            QuantVar::Fresh(decl_ref) => {
                let decl = decl_ref.borrow();
                Ok(dafny_ast::QuantVar {
                    name: decl.name.name.to_owned(),
                    ty: self.lower_type(&decl.ty, decl.span)?,
                })
            }
            QuantVar::Shadow(ident) => {
                let decl = self.tcx.get(*ident).ok_or_else(|| {
                    TranslationError::unsupported(
                        ident.span,
                        format!(
                            "Dafny: could not resolve quantified variable `{}`",
                            ident.name
                        ),
                        "unresolved quantified variable",
                    )
                })?;
                if let DeclKind::VarDecl(var_ref) = decl.as_ref() {
                    let var = var_ref.borrow();
                    Ok(dafny_ast::QuantVar {
                        name: ident.name.to_owned(),
                        ty: self.lower_type(&var.ty, ident.span)?,
                    })
                } else {
                    Err(TranslationError::unsupported(
                        ident.span,
                        format!("Dafny: `{}` is not a variable", ident.name),
                        "invalid quantified variable",
                    ))
                }
            }
        }
    }

    fn lower_param(&self, param: &Param) -> Result<dafny_ast::Param, TranslationError> {
        Ok(dafny_ast::Param {
            name: param.name.name.to_owned(),
            ty: self.lower_type(&param.ty, param.span)?,
        })
    }

    fn lower_type(&self, ty: &TyKind, span: Span) -> Result<dafny_ast::Type, TranslationError> {
        match ty {
            TyKind::Bool => Ok(dafny_ast::Type::Bool),
            TyKind::Int => Ok(dafny_ast::Type::Int),
            TyKind::UInt => Ok(dafny_ast::Type::Nat),
            TyKind::List(element_ty) => Ok(dafny_ast::Type::Seq(Box::new(
                self.lower_type(element_ty, span)?,
            ))),
            TyKind::Domain(domain_ref) => Ok(dafny_ast::Type::Named(
                domain_ref.borrow().name.name.to_owned(),
            )),
            TyKind::Tuple(_) => Err(TranslationError::unsupported(
                span,
                "Dafny: tuple types are only supported in procedure returns",
                "unsupported type",
            )),
            TyKind::Real | TyKind::UReal | TyKind::EUReal | TyKind::String | TyKind::SpecTy => {
                Err(TranslationError::unsupported(
                    span,
                    format!("Dafny: type `{ty}` is not supported by this backend"),
                    "unsupported type",
                ))
            }
            TyKind::Unresolved(_) | TyKind::None => Err(TranslationError::unsupported(
                span,
                "Dafny: unresolved type is not supported",
                "unsupported type",
            )),
        }
    }

    fn lower_lit(&self, lit: &LitKind, span: Span) -> Result<dafny_ast::Expr, TranslationError> {
        match lit {
            LitKind::Bool(value) => Ok(dafny_ast::Expr::BoolLit(*value)),
            LitKind::UInt(value) => Ok(dafny_ast::Expr::NumberLit(value.to_string())),
            LitKind::Str(value) => Ok(dafny_ast::Expr::StringLit(value.to_string())),
            LitKind::Frac(_) | LitKind::Infinity => Err(TranslationError::unsupported(
                span,
                "Dafny: quantitative literals are not supported",
                "unsupported literal",
            )),
        }
    }

    fn lower_exprs(&self, exprs: &[Expr]) -> Result<Vec<dafny_ast::Expr>, TranslationError> {
        exprs.iter().map(|expr| self.lower_expr(expr)).collect()
    }
}

/// Ensure that every required dependency is either locally lowerable or a supported intrinsic.
pub(crate) fn ensure_required_decl_supported(
    ident: Ident,
    lowerer: &DafnyLowerer<'_>,
    tcx: &TyCtx,
) -> Result<(), CaesarError> {
    if let Some(record) = lowerer.index.get(ident) {
        lowerer
            .local_support(record)
            .map_err(|err| CaesarError::Diagnostic(err.diagnostic(ReportKind::Error)))?;
        return Ok(());
    }

    let decl = tcx.get(ident).ok_or_else(|| {
        CaesarError::UserError(
            format!("Missing declaration for dependency `{}`.", ident.name).into(),
        )
    })?;
    match decl.as_ref() {
        DeclKind::FuncIntrin(_) if supported_list_intrinsic(tcx, ident).is_some() => Ok(()),
        DeclKind::ProcIntrin(_) => Err(CaesarError::Diagnostic(
            TranslationError::unsupported(
                ident.span,
                format!(
                    "Dafny: intrinsic procedure `{}` is not supported",
                    ident.name
                ),
                "unsupported procedure call",
            )
            .diagnostic(ReportKind::Error),
        )),
        DeclKind::FuncIntrin(_) => Err(CaesarError::Diagnostic(
            TranslationError::unsupported(
                ident.span,
                format!(
                    "Dafny: intrinsic function `{}` is not supported",
                    ident.name
                ),
                "unsupported intrinsic function",
            )
            .diagnostic(ReportKind::Error),
        )),
        other => Err(CaesarError::Diagnostic(
            TranslationError::unsupported(
                ident.span,
                format!(
                    "Dafny: declaration kind `{}` is not supported",
                    other.kind_name()
                ),
                "unsupported dependency",
            )
            .diagnostic(ReportKind::Error),
        )),
    }
}

fn supported_list_intrinsic(tcx: &TyCtx, ident: Ident) -> Option<SupportedListIntrinsic> {
    let decl = tcx.get(ident)?;
    if !matches!(decl.as_ref(), DeclKind::FuncIntrin(_)) {
        return None;
    }

    match ident.name.to_owned().as_str() {
        "len" => Some(SupportedListIntrinsic::Len),
        "select" => Some(SupportedListIntrinsic::Select),
        "store" => Some(SupportedListIntrinsic::Store),
        _ => None,
    }
}

fn true_expr() -> dafny_ast::Expr {
    dafny_ast::Expr::BoolLit(true)
}
