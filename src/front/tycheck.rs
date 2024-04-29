//! Type checking and type inference happens here.

use std::{cmp::Ordering, ops::DerefMut, rc::Rc};

use ariadne::ReportKind;
use indexmap::IndexSet;
use replace_with::replace_with_or_abort;

use crate::{
    ast::{
        util::FreeVariableCollector,
        visit::{walk_expr, walk_func, walk_quant_ann, walk_stmt, VisitorMut},
        AxiomDecl, BinOpKind, DeclKind, DeclRef, Diagnostic, Expr, ExprData, ExprKind, FuncDecl,
        Ident, Label, Param, ProcDecl, ProcSpec, QuantOpKind, QuantVar, Shared, Span, SpanVariant,
        Stmt, StmtKind, TyKind, UnOpKind, VarDecl, VarKind,
    },
    pretty::join_commas,
    tyctx::TyCtx,
};

#[derive(Debug)]
pub struct Tycheck<'tcx> {
    tcx: &'tcx mut TyCtx,
    /// whether we are currently type-checking a `pre`, where the user is not
    /// allowed to use output variables.
    checking_pre: bool,
    /// whether we are in the topmost expression of the right-hand side of an
    /// assignment and thus are allowed to use side-effectful calls.
    allow_impure_calls: bool,
}

impl<'tcx> Tycheck<'tcx> {
    pub fn new(tcx: &'tcx mut TyCtx) -> Self {
        Tycheck {
            tcx,
            checking_pre: false,
            allow_impure_calls: false,
        }
    }

    /// Try to cast the expression to the left-hand side.
    pub fn try_cast(
        &self,
        span: Span,
        target_ty: &TyKind,
        expr: &mut Expr,
    ) -> Result<(), TycheckError> {
        let expr_ty = expr.ty.as_ref().unwrap();
        let target_ty = if *target_ty == TyKind::SpecTy {
            self.tcx.spec_ty()
        } else {
            target_ty
        };
        match target_ty.partial_cmp(expr_ty) {
            Some(Ordering::Equal) => Ok(()),
            Some(Ordering::Greater) => {
                wrap_cast_expr(target_ty, expr);
                Ok(())
            }
            _ => Err(TycheckError::CannotCast {
                span,
                target: target_ty.clone().into(),
                expr: expr.clone(),
            }),
        }
    }

    /// Try to assign the right-hand side to the left-hand side, where the right-hand side is unpacked as a tuple.
    fn try_assign_tuple(
        &self,
        span: Span,
        lhses: &[Ident],
        rhs_tys: &[TyKind],
        rhs: &Expr,
    ) -> Result<(), TycheckError> {
        if lhses.len() != rhs_tys.len() {
            return Err(TycheckError::UnpackMismatch {
                span,
                lhs: lhses.to_vec(),
                rhs: rhs.clone(),
            });
        }
        for (lhs, rhs_ty) in lhses.iter().zip(rhs_tys) {
            let lhs_decl_ref = self.get_var_decl(span, *lhs)?;
            let lhs_decl = lhs_decl_ref.borrow();
            if &lhs_decl.ty != rhs_ty {
                return Err(TycheckError::TypeMismatch {
                    span,
                    lhs: lhs_decl.ty.clone().into(),
                    rhs: rhs_ty.clone().into(),
                });
            }
            if !lhs_decl.kind.is_mutable() {
                return Err(TycheckError::CannotAssign {
                    span,
                    lhs_decl: lhs_decl_ref.clone(),
                });
            }
        }
        Ok(())
    }

    /// Try to unify the types of the expressions by casting either one of the types to the greater one.
    ///
    /// This method is intentionally dumb and does not try to cast both expressions to a common supertype.
    fn try_unify(&self, span: Span, a: &mut Expr, b: &mut Expr) -> Result<TyKind, TycheckError> {
        let a_ty = a.ty.as_ref().unwrap();
        let b_ty = b.ty.as_ref().unwrap();
        match a_ty.partial_cmp(b_ty) {
            Some(Ordering::Equal) => Ok(a_ty.clone()),
            Some(Ordering::Less) => {
                wrap_cast_expr(b_ty, a);
                Ok(b_ty.clone())
            }
            Some(Ordering::Greater) => {
                wrap_cast_expr(a_ty, b);
                Ok(a_ty.clone())
            }
            None => Err(TycheckError::TypeMismatch {
                span,
                lhs: a_ty.clone().into(),
                rhs: b_ty.clone().into(),
            }),
        }
    }

    /// Retrieve the declaration or throw an error.
    fn get_decl(&self, span: Span, ident: Ident) -> Result<Rc<DeclKind>, TycheckError> {
        self.tcx
            .get(ident)
            .ok_or(TycheckError::NotDeclared { span, name: ident })
    }

    /// Retrieve the variable declaration or throw an error.
    fn get_var_decl(&self, span: Span, ident: Ident) -> Result<DeclRef<VarDecl>, TycheckError> {
        let decl = self.get_decl(span, ident)?;
        if let DeclKind::VarDecl(var_decl) = decl.as_ref() {
            Ok(var_decl.clone())
        } else {
            Err(TycheckError::ExpectedKind {
                span,
                expr: Shared::new(ExprData {
                    kind: ExprKind::Var(ident),
                    ty: None,
                    span,
                }),
                kind: ExpectedKind::Variable,
            })
        }
    }

    /// Check the call with the given formal inputs and argument expressions.
    pub fn check_call(
        &self,
        span: Span,
        inputs: &[Param],
        args: &mut [Expr],
    ) -> Result<(), TycheckError> {
        if args.len() != inputs.len() {
            return Err(TycheckError::ArgumentCountMismatch {
                span,
                callee: inputs.len(),
                caller: args.len(),
            });
        }
        for (input, arg) in inputs.iter().zip(args) {
            if input.literal_only && !matches!(arg.kind, ExprKind::Lit(_)) {
                return Err(TycheckError::ExpectedKind {
                    span,
                    expr: arg.clone(),
                    kind: ExpectedKind::Literal,
                });
            }
            self.try_cast(arg.span, &input.ty, arg)?;
        }
        Ok(())
    }

    /// Check the procedure call.
    pub fn check_proc_call(
        &self,
        span: Span,
        proc: &ProcDecl,
        args: &mut [Expr],
    ) -> Result<TyKind, TycheckError> {
        self.check_call(span, &proc.inputs.node, args)?;
        Ok(proc.return_ty())
    }

    /// Check this function call.
    pub fn check_func_call(
        &self,
        span: Span,
        func: &FuncDecl,
        args: &mut [Expr],
    ) -> Result<TyKind, TycheckError> {
        self.check_call(span, &func.inputs.node, args)?;
        Ok(func.output.clone())
    }
}

/// Wrap this expression in a cast expression to the given type.
fn wrap_cast_expr(lhs_ty: &TyKind, expr: &mut Expr) {
    replace_with_or_abort(expr, |expr_| {
        let span = expr_.span.variant(SpanVariant::ImplicitCast);
        Shared::new(ExprData {
            kind: ExprKind::Cast(expr_),
            ty: Some(lhs_ty.clone()),
            span,
        })
    });
}

#[derive(Debug)]
pub enum TycheckError {
    NotDeclared {
        span: Span,
        name: Ident,
    },
    ExpectedKind {
        span: Span,
        expr: Expr,
        kind: ExpectedKind,
    },
    CannotCast {
        span: Span,
        target: Box<TyKind>,
        expr: Expr,
    },
    TypeMismatch {
        span: Span,
        lhs: Box<TyKind>,
        rhs: Box<TyKind>,
    },
    ArgumentCountMismatch {
        span: Span,
        callee: usize,
        caller: usize,
    },
    WrongOperandType {
        span: Span,
        operand_span: Span,
        ty: Box<TyKind>,
    },
    UnpackMismatch {
        span: Span,
        lhs: Vec<Ident>,
        rhs: Expr,
    },
    CannotAssign {
        span: Span,
        lhs_decl: DeclRef<VarDecl>,
    },
    CannotRead {
        span: Span,
        var_decl: DeclRef<VarDecl>,
    },
    TriggerCapture {
        span: Span,
        captured: IndexSet<Ident>,
    },
    CannotCallImpure {
        span: Span,
        ident: Ident,
    },
}

#[derive(Debug)]
pub enum ExpectedKind {
    Variable,
    Callable,
    Literal,
    List,
}

impl TycheckError {
    pub fn diagnostic(&self) -> Diagnostic {
        match &self {
            TycheckError::NotDeclared { span, name } => Diagnostic::new(ReportKind::Error, *span)
                .with_message(format!("Not declared: {}", name))
                .with_label(Label::new(*span)),
            TycheckError::ExpectedKind { span, expr, kind } => {
                let expected = match &kind {
                    ExpectedKind::Variable => "variable",
                    ExpectedKind::Callable => "proc or a func",
                    ExpectedKind::Literal => "literal",
                    ExpectedKind::List => "list",
                };
                Diagnostic::new(ReportKind::Error, *span)
                    .with_message(format!("Expected a {} here", expected))
                    .with_label(
                        Label::new(expr.span).with_message(format!("Expected {}", expected)),
                    )
            }
            TycheckError::CannotCast { span, target, expr } => {
                tracing::debug!(span = ?span, "cannot cast span");
                Diagnostic::new(ReportKind::Error, *span)
                    .with_message(format!("Cannot cast expression to type {}", &target))
                    .with_label(Label::new(expr.span).with_message(format!(
                        "expected {}, found {}",
                        &target,
                        &expr.ty.as_ref().unwrap()
                    )))
            }
            TycheckError::TypeMismatch { span, lhs, rhs } => {
                Diagnostic::new(ReportKind::Error, *span)
                    .with_message(format!("Mismatched types {} and {}", &lhs, &rhs))
                    .with_label(Label::new(*span).with_message("here")) // TODO: improve the labels
            }
            TycheckError::ArgumentCountMismatch {
                span,
                callee,
                caller,
            } => Diagnostic::new(ReportKind::Error, *span)
                .with_message(format!("Expected {} arguments, got {}", callee, caller))
                .with_label(Label::new(*span).with_message("here")),
            TycheckError::WrongOperandType {
                span,
                operand_span,
                ty,
            } => Diagnostic::new(ReportKind::Error, *span)
                .with_message(format!("Illegal type {} for operand", &ty))
                .with_label(Label::new(*operand_span).with_message("here")),
            TycheckError::UnpackMismatch { span, rhs, .. } => {
                Diagnostic::new(ReportKind::Error, *span)
                    .with_message("Could not unpack expression")
                    .with_label(
                        Label::new(rhs.span)
                            .with_message(format!("type {}", &rhs.ty.as_ref().unwrap())),
                    )
            }
            TycheckError::CannotAssign { span, lhs_decl } => {
                let lhs_decl = lhs_decl.borrow();
                let lhs = lhs_decl.name;
                if lhs_decl.kind.is_mutable() {
                    unreachable!();
                }
                Diagnostic::new(ReportKind::Error, *span)
                    .with_message(format!("Cannot assign to variable `{}`", lhs))
                    .with_label(Label::new(lhs_decl.span).with_message(format!("`{}` is declared as {}...", lhs, lhs_decl.kind)))
                    .with_label(
                        Label::new(*span).with_message("... so this assignment is not allowed"),
                    )
                    .with_note(format!(
                        "Consider declaring a new variable and initialize it with `{}`",
                        lhs_decl.name
                    ))
            }
            TycheckError::CannotRead { span, var_decl } => {
                let var_decl = var_decl.borrow();
                assert_eq!(var_decl.kind, VarKind::Output);
                let lhs = var_decl.name;
                Diagnostic::new(ReportKind::Error, *span)
                    .with_message(format!("Cannot access variable `{}`", lhs))
                    .with_label(
                        Label::new(var_decl.span).with_message(format!(
                            "`{}` is declared as an output variable...",
                            lhs
                        )),
                    )
                    .with_label(
                        Label::new(*span).with_message("... so you cannot use it in the pre"),
                    )
            }
            TycheckError::TriggerCapture { span, captured } => Diagnostic::new(
                ReportKind::Error,
                *span,
            )
            .with_message("Trigger does not capture all quantified variables")
            .with_label(Label::new(*span).with_message(format!(
                "Trigger captures {}",
                join_commas(captured.iter().map(|ident| format!("`{}`", ident)))
            )))
            .with_note(
                "Triggers on quantifiers must capture all variables bound by the quantifier.",
            ),
            TycheckError::CannotCallImpure { span, ident } => Diagnostic::new(
                ReportKind::Error,
                *span,
            )
            .with_message(format!("Cannot call proc `{}` nested inside of an expression", ident))
            .with_label(Label::new(*span).with_message("here"))
            .with_note(
                "Procedures must only be called on as the immediate right-hand side expression in an assignment. This makes execution order of assignments with side-effects explicit."
            ),
        }
    }
}

macro_rules! op_ty_check {
    ($span:expr, $operand:expr, $( $pat:pat )|+) => {
        {
            let operand = &$operand;
            let ty = operand.ty.as_ref().unwrap();
            match &ty {
                $( $pat )|+ => {},
                _ => return Err(TycheckError::WrongOperandType { span :$span, operand_span: operand.span, ty: ty.clone().into() }),
            }
        }
    };
}

macro_rules! ops_ty_check {
    ($expr:expr, $a:expr, $b:expr, $( $pat:pat )|+) => {
        {
            op_ty_check!($expr, $a, $( $pat )|+);
            op_ty_check!($expr, $b, $( $pat )|+);
        }
    };
}

impl<'tcx> VisitorMut for Tycheck<'tcx> {
    type Err = TycheckError;

    fn visit_var_decl(&mut self, var_ref: &mut DeclRef<VarDecl>) -> Result<(), Self::Err> {
        let mut var_decl = var_ref.borrow_mut();
        let var_decl = var_decl.deref_mut();
        if let Some(init) = &mut var_decl.init {
            self.allow_impure_calls = true;
            self.visit_expr(init)?;
            self.allow_impure_calls = false;

            // try to unpack a tuple first
            let init_ty = init.ty.as_ref().unwrap();
            if let TyKind::Tuple(tys) = init_ty {
                if let [lhs_ty] = tys.as_slice() {
                    if lhs_ty == &var_decl.ty {
                        return Ok(());
                    }
                }
            }
            // only if unpacking the tuple failed, try a normal assignment
            self.try_cast(init.span, &var_decl.ty, init)?;
        }
        Ok(())
    }

    fn visit_proc(&mut self, proc_ref: &mut DeclRef<ProcDecl>) -> Result<(), Self::Err> {
        let mut proc = proc_ref.borrow_mut();
        for spec in &mut proc.spec {
            let expr = match spec {
                ProcSpec::Requires(ref mut expr) => {
                    self.checking_pre = true;
                    expr
                }
                ProcSpec::Ensures(ref mut expr) => expr,
            };
            let res = self.visit_expr(expr);
            self.checking_pre = false;
            res?;
            let lhs_ty = self.tcx.spec_ty();
            self.try_cast(expr.span, lhs_ty, expr)?;
        }
        // drop the mutable reference to the proc and get a shared reference.
        // this way, we can access the procedure declaration in its body.
        drop(proc);
        let proc = proc_ref.borrow();
        let mut body = proc.body.borrow_mut();
        if let Some(ref mut block) = &mut *body {
            self.visit_stmts(block)?;
        }
        Ok(())
    }

    fn visit_func(&mut self, func_ref: &mut DeclRef<FuncDecl>) -> Result<(), Self::Err> {
        walk_func(self, func_ref)?;
        let func = func_ref.borrow();
        let mut body = func.body.borrow_mut();
        if let Some(ref mut body) = &mut *body {
            self.try_cast(body.span, &func.output, body)?;
        }
        Ok(())
    }

    fn visit_axiom(&mut self, axiom_ref: &mut DeclRef<AxiomDecl>) -> Result<(), Self::Err> {
        let mut axiom_decl = axiom_ref.borrow_mut();
        self.visit_ident(&mut axiom_decl.name)?;
        self.visit_expr(&mut axiom_decl.axiom)?;
        self.try_cast(axiom_decl.axiom.span, &TyKind::Bool, &mut axiom_decl.axiom)
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        self.allow_impure_calls = true;
        walk_stmt(self, s)?;
        self.allow_impure_calls = false;

        match &mut s.node {
            StmtKind::Block(_) => {}
            StmtKind::Var(var_decl) => {
                self.visit_var_decl(var_decl)?;
            }
            StmtKind::Assign(lhses, ref mut rhs) => {
                // TODO: handle mutability on LHS

                // this complicated code does some magic to make assignments
                // with tuples work. if rhs is a tuple, then try to assign the
                // contents to the lhses. in particular, when rhs is a 1-element
                // tuple and lhs is just one identifier, we try to assign the
                // contents of the 1-element tuple to lhs first (implictly
                // extracting the value). if that did not work and lhs is not a
                // single ident, we stop. otherwise try a normal assignment.

                let lhs_singleton = match lhses.as_slice() {
                    [lhs] => Some(lhs),
                    _ => None,
                };

                let rhs_ty = rhs.ty.as_ref().unwrap();

                // if rhs is a tuple, try to assign the inner values.
                if let TyKind::Tuple(tys) = &rhs_ty {
                    let tuple_res = self.try_assign_tuple(s.span, lhses, tys, rhs);
                    // if successful or lhs is a tuple, stop here.
                    if tuple_res.is_ok() || lhses.len() != 1 {
                        return tuple_res;
                    }
                }

                // we've not succeeded with the tuple assignment.
                // now try normal assignments.
                if let Some(lhs) = lhs_singleton {
                    let lhs_decl_ref = self.get_var_decl(s.span, *lhs)?;
                    let lhs_decl = lhs_decl_ref.borrow();
                    self.try_cast(s.span, &lhs_decl.ty, rhs)?;
                    if !lhs_decl.kind.is_mutable() {
                        return Err(TycheckError::CannotAssign {
                            span: s.span,
                            lhs_decl: lhs_decl_ref.clone(),
                        });
                    }
                } else {
                    return Err(TycheckError::UnpackMismatch {
                        span: s.span,
                        lhs: lhses.clone(),
                        rhs: rhs.clone(),
                    });
                };
            }
            StmtKind::Havoc(_, _) => {} // TODO: make input vars readable here or throw an error?
            StmtKind::Assert(_, ref mut expr) => self.try_cast(s.span, self.tcx.spec_ty(), expr)?,
            StmtKind::Assume(_, ref mut expr) => self.try_cast(s.span, self.tcx.spec_ty(), expr)?,
            StmtKind::Compare(_, ref mut expr) => {
                self.try_cast(s.span, self.tcx.spec_ty(), expr)?
            }
            StmtKind::Negate(_) => {}
            StmtKind::Validate(_) => {}
            StmtKind::Tick(ref mut expr) => self.try_cast(s.span, self.tcx.spec_ty(), expr)?,
            StmtKind::Demonic(_, _) => {}
            StmtKind::Angelic(_, _) => {}
            StmtKind::If(ref mut cond, _, _) => self.try_cast(s.span, &TyKind::Bool, cond)?,
            StmtKind::While(ref mut cond, _) => self.try_cast(s.span, &TyKind::Bool, cond)?,
            StmtKind::Annotation(ref ident, ref mut args, _) => {
                match self.tcx.get(*ident).as_deref() {
                    None => {} // Declaration not found
                    Some(DeclKind::AnnotationDecl(intrin)) => {
                        let intrin = intrin.clone(); // clone so we can mutably borrow self
                        intrin.tycheck(self, s.span, args)?
                    }
                    _ => {} // Not an annotation declaration
                }
            }
            StmtKind::Label(_) => {}
        }
        Ok(())
    }

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        // disallow proc calls inside nested expressions
        let allow_impure_calls_before = self.allow_impure_calls;
        self.allow_impure_calls = false;

        match &mut expr.kind {
            ExprKind::Subst(ident, val, expr) => {
                self.visit_ident(ident)?;
                self.visit_expr(val)?;
                if let Some(DeclKind::VarDecl(decl_ref)) = self.tcx.get_mut(*ident) {
                    let mut decl = decl_ref.borrow_mut();
                    if matches!(decl.ty, TyKind::None) {
                        decl.ty = val.ty.clone().unwrap();
                    }
                } else {
                    unreachable!();
                }
                self.visit_expr(expr)?;
            }
            _ => walk_expr(self, expr)?,
        }
        self.allow_impure_calls = allow_impure_calls_before;

        let expr_data: &mut ExprData = &mut *expr;
        let expr_span = expr_data.span;
        let res_ty = match &mut expr_data.kind {
            ExprKind::Var(ident) => {
                let var_decl_ref = self.get_var_decl(expr_span, *ident)?;
                let var_decl = var_decl_ref.borrow();
                if self.checking_pre && var_decl.kind == VarKind::Output {
                    return Err(TycheckError::CannotRead {
                        span: expr_span,
                        var_decl: var_decl_ref.clone(),
                    });
                }
                var_decl.ty.clone()
            }
            ExprKind::Call(ident, args) => {
                let decl = self.get_decl(expr_span, *ident)?;

                if !self.allow_impure_calls && decl.kind_name().is_proc() {
                    return Err(TycheckError::CannotCallImpure {
                        span: expr_span,
                        ident: *ident,
                    });
                }

                match decl.as_ref() {
                    DeclKind::ProcDecl(proc_ref) => {
                        let proc = proc_ref.borrow();
                        self.check_proc_call(expr_span, &proc, args)?
                    }
                    DeclKind::FuncDecl(func_ref) => {
                        let func = func_ref.borrow();
                        self.check_func_call(expr_span, &func, args)?
                    }
                    DeclKind::ProcIntrin(intrin) => {
                        let intrin = intrin.clone(); // clone so we can mutably borrow self
                        intrin.tycheck(self, expr_span, args)?
                    }
                    DeclKind::FuncIntrin(intrin) => {
                        let intrin = intrin.clone(); // clone so we can mutably borrow self
                        intrin.tycheck(self, expr_span, args)?
                    }
                    _ => {
                        return Err(TycheckError::ExpectedKind {
                            span: expr_span,
                            expr: Shared::new(ExprData {
                                kind: ExprKind::Var(*ident),
                                ty: None,
                                span: expr_span,
                            }),
                            kind: ExpectedKind::Callable,
                        })
                    }
                }
            }
            ExprKind::Ite(ref mut cond, ref mut lhs, ref mut rhs) => {
                self.try_cast(cond.span, &TyKind::Bool, cond)?;
                // TODO: forbid tuple types
                self.try_unify(expr_span, lhs, rhs)?
            }
            ExprKind::Binary(bin_op, ref mut a, ref mut b) => match bin_op.node {
                BinOpKind::Add | BinOpKind::Mul => {
                    ops_ty_check!(
                        expr_span,
                        a,
                        b,
                        TyKind::UInt | TyKind::Int | TyKind::UReal | TyKind::Real | TyKind::EUReal
                    );
                    self.try_unify(expr_span, a, b)?
                }
                BinOpKind::Sub => {
                    ops_ty_check!(
                        expr_span,
                        a,
                        b,
                        TyKind::UInt | TyKind::Int | TyKind::UReal | TyKind::Real | TyKind::EUReal
                    );
                    let res = self.try_unify(expr_span, a, b)?;
                    if matches!(res, TyKind::EUReal) {
                        tracing::warn!("Subtraction over the `EUReal` type detected. The semantics is really wonky, be careful!");
                    }
                    res
                }
                BinOpKind::Div => {
                    let res1 = self.try_cast(expr_span, &TyKind::UReal, a);
                    let res2 = self.try_cast(expr_span, &TyKind::UReal, b);
                    if res1.is_ok() && res2.is_ok() {
                        TyKind::UReal
                    } else {
                        self.try_cast(expr_span, &TyKind::Real, a)?;
                        self.try_cast(expr_span, &TyKind::Real, b)?;
                        TyKind::Real
                    }
                }
                BinOpKind::Mod => {
                    ops_ty_check!(expr_span, a, b, TyKind::UInt | TyKind::Int);
                    self.try_unify(expr_span, a, b)?
                }
                BinOpKind::And | BinOpKind::Or => {
                    ops_ty_check!(expr_span, a, b, TyKind::Bool);
                    TyKind::Bool
                }
                BinOpKind::Eq | BinOpKind::Ne => {
                    self.try_unify(expr_span, a, b)?;
                    TyKind::Bool
                }
                BinOpKind::Lt | BinOpKind::Le | BinOpKind::Ge | BinOpKind::Gt => {
                    ops_ty_check!(
                        expr_span,
                        a,
                        b,
                        TyKind::UInt | TyKind::Int | TyKind::UReal | TyKind::Real | TyKind::EUReal
                    );
                    self.try_unify(expr_span, a, b)?;
                    TyKind::Bool
                }
                BinOpKind::Inf | BinOpKind::Sup => {
                    ops_ty_check!(
                        expr_span,
                        a,
                        b,
                        TyKind::UInt | TyKind::Int | TyKind::UReal | TyKind::Real | TyKind::EUReal
                    );
                    self.try_unify(expr_span, a, b)?
                }
                BinOpKind::Impl | BinOpKind::CoImpl | BinOpKind::Compare | BinOpKind::CoCompare => {
                    ops_ty_check!(expr_span, a, b, TyKind::Bool | TyKind::EUReal);
                    self.try_unify(expr_span, a, b)?
                }
            },
            ExprKind::Unary(un_op, ref mut operand) => match un_op.node {
                UnOpKind::Not | UnOpKind::Non => {
                    op_ty_check!(expr_span, operand, TyKind::Bool | TyKind::EUReal);
                    operand.ty.clone().unwrap()
                }
                UnOpKind::Embed => {
                    self.try_cast(expr_span, &TyKind::Bool, operand)?;
                    self.tcx.spec_ty().clone()
                }
                UnOpKind::Iverson => {
                    self.try_cast(expr_span, &TyKind::Bool, operand)?;
                    TyKind::EUReal
                }
                UnOpKind::Parens => operand.ty.clone().unwrap(),
            },
            ExprKind::Cast(operand) => expr_data
                .ty
                .clone()
                .unwrap_or_else(|| operand.ty.clone().unwrap()),
            ExprKind::Quant(quant_op, idents, ann, operand) => {
                let operand_ty = operand.ty.clone().unwrap();
                walk_quant_ann(self, ann)?;
                match quant_op.node {
                    QuantOpKind::Inf | QuantOpKind::Sup => {
                        op_ty_check!(expr_span, operand, TyKind::EUReal)
                    }
                    QuantOpKind::Forall | QuantOpKind::Exists => {
                        op_ty_check!(expr_span, operand, TyKind::Bool)
                    }
                }
                // check that triggers contain all quantified variables
                let quantified: IndexSet<Ident> = idents.iter().map(QuantVar::name).collect();
                for trigger in &mut ann.triggers {
                    let mut captured = FreeVariableCollector::default();
                    for term in trigger.terms_mut() {
                        captured.visit_expr(term).unwrap();
                    }
                    if !quantified.is_subset(&captured.variables) {
                        return Err(TycheckError::TriggerCapture {
                            span: trigger.span,
                            captured: captured.variables,
                        });
                    }
                }
                operand_ty
            }
            ExprKind::Subst(_, _, operand) => operand.ty.clone().unwrap(),
            ExprKind::Lit(lit) => self.tcx.lit_ty(&lit.node),
        };

        if let Some(expr_ty) = &expr.ty {
            assert_eq!(expr_ty, &res_ty);
        }
        expr.ty = Some(res_ty);
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        ast::{visit::VisitorMut, Block, DeclKind, FileId, StmtKind, TyKind},
        front::{parser, resolve::Resolve},
        tyctx::TyCtx,
    };

    use super::{Tycheck, TycheckError};

    fn parse_decls_and_tycheck(input: &str) -> Result<Vec<DeclKind>, TycheckError> {
        let mut decls = parser::parse_decls(FileId::DUMMY, input).unwrap();

        let mut tcx = TyCtx::new(TyKind::EUReal);
        let mut resolve = Resolve::new(&mut tcx);
        resolve.visit_decls(&mut decls).unwrap();

        let mut tycheck = Tycheck::new(&mut tcx);
        tycheck.visit_decls(&mut decls)?;
        Ok(decls)
    }

    fn parse_block_and_tycheck(input: &str) -> Result<Block, TycheckError> {
        let mut block = parser::parse_raw(FileId::DUMMY, input).unwrap();

        let mut tcx = TyCtx::new(TyKind::EUReal);
        let mut resolve = Resolve::new(&mut tcx);
        resolve.visit_stmts(&mut block).unwrap();

        let mut tycheck = Tycheck::new(&mut tcx);
        tycheck.visit_stmts(&mut block)?;
        Ok(block)
    }

    #[test]
    fn test_type_casts() {
        let source = r#"
            var uint: UInt = 42;
            var int: Int = uint;
            var real: Real = int;
            var real2: Real = uint;
            var ureal: UReal = uint;
            var real3: Real = ureal;
            var eureal: EUReal = ureal;
            var ureal2: EUReal = uint;
        "#;
        let block = parse_block_and_tycheck(source).unwrap();
        assert!(matches!(block[0].node, StmtKind::Var(_)));

        let source = r#"
            var eureal: EUReal;
            var uint: UInt = eureal;
        "#;
        let res = parse_block_and_tycheck(source);
        assert!(matches!(
            res,
            Err(TycheckError::CannotCast {
                span: _,
                target: _,
                expr: _
            })
        ));
    }

    // issue #36: recursive definitions should work
    #[test]
    pub fn test_recursion() {
        let source = r#"
            domain Sum {
                func sum(n: UInt): UInt = ite(n > 0, 1 + sum(n-1), 0)
            }

            proc test() -> () {
                test()
            }
        "#;
        parse_decls_and_tycheck(&source).unwrap();
    }
}
