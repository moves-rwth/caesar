//! [Ident]s with local spans of their actual written location are changed to
//! [Ident]s of the definition, uniquely identifiying which definition is meant
//! in this place. Resolution is therefore concerned with creating and resolving
//! variable scopes.

use ariadne::ReportKind;

use crate::{
    ast::{
        visit::{walk_domain, walk_expr, walk_proc_spec, walk_stmt, VisitorMut},
        DeclKind, DeclRef, Diagnostic, DomainDecl, DomainSpec, Expr, ExprKind, FuncDecl, Ident,
        Label, ProcDecl, Span, Stmt, StmtKind, Symbol, TyKind, VarDecl, VarKind,
    },
    scope_map::ScopeMap,
    tyctx::TyCtx,
};

pub struct Resolve<'tcx> {
    tcx: &'tcx mut TyCtx,
    scope_map: ScopeMap<Symbol, Ident>,
}

impl<'tcx> Resolve<'tcx> {
    pub fn new(tcx: &'tcx mut TyCtx) -> Self {
        let mut scope_map: ScopeMap<_, _> = tcx
            .globals_iter()
            .map(|ident| (ident.name, *ident))
            .collect();
        // depth 2 is for globals in this scope, depth 1 is for imports
        scope_map.push();
        Self { tcx, scope_map }
    }

    /// Execute the closure in a subscope, pushing a new scope and popping it
    /// after the closure call.
    pub fn with_subscope<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let parent = self.scope_map.push();
        let res = f(self);
        self.scope_map.pop(parent);
        res
    }

    /// Forward-declare this declaration so that its name is available in other
    /// declarations.
    pub fn declare(&mut self, decl: DeclKind) -> Result<(), ResolveError> {
        let ident = decl.name();
        let prev_ident = self.scope_map.insert(ident.name, ident);
        if let Some(prev_ident) = prev_ident {
            if prev_ident != ident {
                tracing::error!(ident=?ident, prev_ident=?prev_ident, "declaration failed because there was an existing declaration.");
                return Err(ResolveError::AlreadyDefined(ident.span, prev_ident));
            }
        } else {
            if self.scope_map.depth() == 2 {
                // depth 2 is for globals in this scope, depth 1 is for imports
                self.tcx.add_global(ident);
            }
            self.tcx.declare(decl);
        }
        Ok(())
    }

    fn assert_declared(&self, ident: Ident) {
        assert_eq!(self.scope_map.get(&ident.name), Some(&ident));
    }
}

#[derive(Debug)]
pub enum ResolveError {
    AlreadyDefined(Span, Ident),
    NotFound(Ident),
}

impl ResolveError {
    pub fn diagnostic(self) -> Diagnostic {
        match self {
            ResolveError::AlreadyDefined(span, ident) => Diagnostic::new(ReportKind::Error, span)
                .with_message(format!("Name `{}` is already defined", ident))
                .with_label(Label::new(span).with_message("already defined")),
            ResolveError::NotFound(ident) => Diagnostic::new(ReportKind::Error, ident.span)
                .with_message(format!("Name `{}` is not declared", ident))
                .with_label(Label::new(ident.span).with_message("not declared")),
        }
    }
}

impl<'tcx> VisitorMut for Resolve<'tcx> {
    type Err = ResolveError;

    fn visit_decls(&mut self, decls: &mut Vec<DeclKind>) -> Result<(), ResolveError> {
        // name resolution for declarations is not sequential: we first create
        // all name-ident mappings for all declarations, and then do the
        // resolution in each declaration. this allows e.g. mutually recursive
        // declarations.
        for decl in decls.iter_mut() {
            self.declare(decl.clone())?;
        }
        for decl in decls.iter_mut() {
            self.visit_decl(decl)?;
        }
        Ok(())
    }

    fn visit_var_decl(&mut self, var_ref: &mut DeclRef<VarDecl>) -> Result<(), ResolveError> {
        let mut var_decl = var_ref.borrow_mut();

        // first visit the initializer
        if let Some(ref mut init) = &mut var_decl.init {
            self.visit_expr(init)?;
        }
        self.visit_ty(&mut var_decl.ty)?;
        drop(var_decl);
        self.declare(DeclKind::VarDecl(var_ref.clone()))
    }

    fn visit_proc(&mut self, proc_ref: &mut DeclRef<ProcDecl>) -> Result<(), ResolveError> {
        let mut proc = proc_ref.borrow_mut();
        self.assert_declared(proc.name);
        self.with_subscope(|this| {
            for param in proc.inputs.node.iter_mut() {
                this.visit_ty(&mut param.ty)?;
                let var_decl = VarDecl::from_param(param, VarKind::Input);
                this.declare(DeclKind::VarDecl(var_decl))?;
            }
            for param in proc.outputs.node.iter_mut() {
                this.visit_ty(&mut param.ty)?;
                let var_decl = VarDecl::from_param(param, VarKind::Output);
                this.declare(DeclKind::VarDecl(var_decl))?;
            }
            for spec in &mut proc.spec {
                walk_proc_spec(this, spec)?;
            }
            let mut body = proc.body.borrow_mut();
            if let Some(ref mut block) = &mut *body {
                this.visit_stmts(block)?;
            }
            Ok(())
        })?;
        drop(proc);
        self.declare(DeclKind::ProcDecl(proc_ref.clone()))?;
        Ok(())
    }

    fn visit_domain(&mut self, domain_ref: &mut DeclRef<DomainDecl>) -> Result<(), Self::Err> {
        let mut domain = domain_ref.borrow_mut();
        self.assert_declared(domain.name);

        // forward-declare all items in the domain's body
        for spec in &domain.body {
            match spec {
                DomainSpec::Function(func_ref) => {
                    self.declare(DeclKind::FuncDecl(func_ref.clone()))?
                }
                DomainSpec::Axiom(axiom_ref) => {
                    self.declare(DeclKind::AxiomDecl(axiom_ref.clone()))?
                }
            }
        }

        walk_domain(self, &mut domain)?;
        drop(domain);
        Ok(())
    }

    fn visit_func(&mut self, func_ref: &mut DeclRef<FuncDecl>) -> Result<(), Self::Err> {
        let mut func = func_ref.borrow_mut();
        self.assert_declared(func.name);
        self.with_subscope(|this| {
            for param in &mut func.inputs.node {
                this.visit_ty(&mut param.ty)?;
                let var_decl = VarDecl::from_param(param, VarKind::Input);
                this.declare(DeclKind::VarDecl(var_decl))?;
            }
            this.visit_ty(&mut func.output)?;
            let mut body = func.body.borrow_mut();
            if let Some(ref mut body) = &mut *body {
                this.visit_expr(body)?;
            }
            Ok(())
        })?;
        drop(func);
        self.declare(DeclKind::FuncDecl(func_ref.clone()))?;
        Ok(())
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        match &mut s.node {
            StmtKind::Block(ref mut block) => self.with_subscope(|this| this.visit_stmts(block)),
            StmtKind::Demonic(ref mut lhs, ref mut rhs) => {
                self.with_subscope(|this| this.visit_stmts(lhs))?;
                self.with_subscope(|this| this.visit_stmts(rhs))
            }
            StmtKind::Angelic(ref mut lhs, ref mut rhs) => {
                self.with_subscope(|this| this.visit_stmts(lhs))?;
                self.with_subscope(|this| this.visit_stmts(rhs))
            }
            StmtKind::If(ref mut cond, ref mut lhs, ref mut rhs) => {
                self.visit_expr(cond)?;
                self.with_subscope(|this| this.visit_stmts(lhs))?;
                self.with_subscope(|this| this.visit_stmts(rhs))
            }
            StmtKind::While(ref mut cond, ref mut block) => {
                self.visit_expr(cond)?;
                self.with_subscope(|this| this.visit_stmts(block))
            }
            StmtKind::Annotation(ref mut ident, ref mut args, ref mut inner_stmt) => {
                self.visit_ident(ident)?;

                match self.tcx.get(*ident).as_deref() {
                    None => {} // Declaration not found
                    Some(DeclKind::AnnotationDecl(intrin)) => {
                        let intrin = intrin.clone(); // clone so we can mutably borrow self
                        intrin.resolve(self, s.span, args)?;
                    }
                    _ => {} // Not an annotation declaration
                }

                self.with_subscope(|this| this.visit_stmt(inner_stmt))
            }
            StmtKind::Label(ident) => self.declare(DeclKind::LabelDecl(*ident)),
            _ => walk_stmt(self, s),
        }
    }

    fn visit_ty(&mut self, ty: &mut TyKind) -> Result<(), Self::Err> {
        match ty {
            TyKind::Unresolved(ident) => {
                if let Some(res) = resolve_builtin_ty(*ident) {
                    *ty = res;
                    return Ok(());
                }
                self.visit_ident(ident)?;
                let ident = *ident; // release the borrow on `ty`
                match self.tcx.get(ident).as_deref() {
                    Some(DeclKind::DomainDecl(domain_ref)) => {
                        *ty = TyKind::Domain(domain_ref.clone())
                    }
                    Some(_) => panic!("this is not a type!"), // TODO: proper error message
                    _ => {}
                }
            }
            TyKind::List(ref mut element_ty) => self.visit_ty(element_ty)?,
            TyKind::SpecTy => {
                *ty = self.tcx.spec_ty().clone(); // replace SpecTy with the actual type
                return Ok(());
            }
            _ => (),
        }
        Ok(())
    }

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        let span = e.span;
        match &mut e.kind {
            ExprKind::Quant(_, _, _, _) => self.with_subscope(|this| walk_expr(this, e)),
            ExprKind::Subst(ident, val, expr) => {
                self.visit_expr(val)?;
                let decl = DeclKind::VarDecl(DeclRef::new(VarDecl {
                    name: *ident,
                    ty: TyKind::None,
                    kind: VarKind::Subst,
                    init: Some(val.clone()),
                    span,
                    created_from: None,
                }));
                self.with_subscope(|this| {
                    this.declare(decl)?;
                    this.visit_expr(expr)
                })
            }
            _ => walk_expr(self, e),
        }
    }

    fn visit_ident(&mut self, ident: &mut Ident) -> Result<(), Self::Err> {
        if let Some(res) = self.scope_map.get(&ident.name) {
            *ident = *res;
            Ok(())
        } else {
            Err(ResolveError::NotFound(*ident))
        }
    }
}

/// Try to resolve this ident as a built-in type.
fn resolve_builtin_ty(ident: Ident) -> Option<TyKind> {
    let name = ident.name.to_owned();
    let kind = match name.as_str() {
        "Bool" => TyKind::Bool,
        "Int" => TyKind::Int,
        "Uint" | "UInt" => TyKind::UInt,
        "Real" => TyKind::Real,
        "UReal" => TyKind::UReal,
        "Realplus" | "EUReal" => TyKind::EUReal,
        _ => return None,
    };
    Some(kind)
}
