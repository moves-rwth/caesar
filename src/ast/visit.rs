use std::ops::DerefMut;

use super::{
    AxiomDecl, DeclKind, DeclRef, DomainDecl, DomainSpec, Expr, ExprKind, FuncDecl, Ident, Param,
    ProcDecl, ProcSpec, QuantAnn, QuantVar, Stmt, StmtKind, TyKind, VarDecl,
};

pub trait VisitorMut: Sized {
    type Err;

    fn visit_decls(&mut self, decls: &mut Vec<DeclKind>) -> Result<(), Self::Err> {
        for d in decls {
            self.visit_decl(d)?;
        }
        Ok(())
    }

    fn visit_decl(&mut self, decl: &mut DeclKind) -> Result<(), Self::Err> {
        match decl {
            DeclKind::VarDecl(var_decl) => self.visit_var_decl(var_decl),
            DeclKind::ProcDecl(proc) => self.visit_proc(proc),
            DeclKind::DomainDecl(domain) => self.visit_domain(domain),
            DeclKind::FuncDecl(func) => self.visit_func(func),
            DeclKind::AxiomDecl(axiom) => self.visit_axiom(axiom),
            DeclKind::ProcIntrin(_) | DeclKind::FuncIntrin(_) => Ok(()),
            DeclKind::LabelDecl(ref mut ident) => self.visit_ident(ident),
        }
    }

    fn visit_var_decl(&mut self, var_ref: &mut DeclRef<VarDecl>) -> Result<(), Self::Err> {
        let mut var_decl = var_ref.borrow_mut();
        self.visit_ident(&mut var_decl.name)?;
        self.visit_ty(&mut var_decl.ty)?;
        if let Some(ref mut init) = &mut var_decl.init {
            self.visit_expr(init)?;
        }
        Ok(())
    }

    fn visit_proc(&mut self, proc_ref: &mut DeclRef<ProcDecl>) -> Result<(), Self::Err> {
        walk_proc(self, proc_ref)
    }

    fn visit_domain(&mut self, domain_ref: &mut DeclRef<DomainDecl>) -> Result<(), Self::Err> {
        walk_domain(self, &mut domain_ref.borrow_mut())
    }

    fn visit_func(&mut self, func_ref: &mut DeclRef<FuncDecl>) -> Result<(), Self::Err> {
        walk_func(self, func_ref)
    }

    fn visit_axiom(&mut self, axiom_ref: &mut DeclRef<AxiomDecl>) -> Result<(), Self::Err> {
        let mut axiom_decl = axiom_ref.borrow_mut();
        self.visit_ident(&mut axiom_decl.name)?;
        self.visit_expr(&mut axiom_decl.axiom)
    }

    fn visit_stmts(&mut self, stmts: &mut Vec<Stmt>) -> Result<(), Self::Err> {
        for s in stmts {
            self.visit_stmt(s)?;
        }
        Ok(())
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        walk_stmt(self, s)
    }

    fn visit_ty(&mut self, ty: &mut TyKind) -> Result<(), Self::Err> {
        walk_ty(self, ty)
    }

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        walk_expr(self, e)
    }

    fn visit_exprs(&mut self, es: &mut Vec<Expr>) -> Result<(), Self::Err> {
        for e in es {
            self.visit_expr(e)?;
        }
        Ok(())
    }

    fn visit_ident(&mut self, _ident: &mut Ident) -> Result<(), Self::Err> {
        Ok(())
    }
}

pub fn walk_proc<V: VisitorMut>(
    visitor: &mut V,
    proc_ref: &mut DeclRef<ProcDecl>,
) -> Result<(), V::Err> {
    let mut proc = proc_ref.borrow_mut();
    visitor.visit_ident(&mut proc.name)?;
    for param in proc.params_iter_mut() {
        walk_param(visitor, param)?;
    }
    for spec in &mut proc.spec {
        walk_proc_spec(visitor, spec)?;
    }
    drop(proc);
    let proc = proc_ref.borrow(); // only take a shared reference to the declaration now
    let mut body = proc.body.borrow_mut();
    if let Some(ref mut block) = &mut *body {
        visitor.visit_stmts(block)?;
    }
    Ok(())
}

pub fn walk_param<V: VisitorMut>(visitor: &mut V, param: &mut Param) -> Result<(), V::Err> {
    visitor.visit_ident(&mut param.name)?;
    visitor.visit_ty(&mut param.ty)?;
    Ok(())
}

pub fn walk_proc_spec<V: VisitorMut>(visitor: &mut V, spec: &mut ProcSpec) -> Result<(), V::Err> {
    match spec {
        ProcSpec::Requires(ref mut expr) => visitor.visit_expr(expr)?,
        ProcSpec::Ensures(ref mut expr) => visitor.visit_expr(expr)?,
    }
    Ok(())
}

pub fn walk_domain<V: VisitorMut>(visitor: &mut V, domain: &mut DomainDecl) -> Result<(), V::Err> {
    visitor.visit_ident(&mut domain.name)?;
    for spec in &mut domain.body {
        match spec {
            DomainSpec::Function(func) => visitor.visit_func(func)?,
            DomainSpec::Axiom(axiom_ref) => {
                let mut axiom = axiom_ref.borrow_mut();
                visitor.visit_ident(&mut axiom.name)?;
                visitor.visit_expr(&mut axiom.axiom)?;
            }
        }
    }
    Ok(())
}

pub fn walk_func<V: VisitorMut>(
    visitor: &mut V,
    func_ref: &mut DeclRef<FuncDecl>,
) -> Result<(), V::Err> {
    let mut func = func_ref.borrow_mut();
    visitor.visit_ident(&mut func.name)?;
    for input in &mut func.inputs.node {
        walk_param(visitor, input)?;
    }
    visitor.visit_ty(&mut func.output)?;
    drop(func);
    let func = func_ref.borrow();
    let mut body = func.body.borrow_mut();
    if let Some(ref mut body) = &mut *body {
        visitor.visit_expr(body)?;
    }
    Ok(())
}

pub fn walk_ty<V: VisitorMut>(visitor: &mut V, ty: &mut TyKind) -> Result<(), V::Err> {
    match ty {
        TyKind::List(ref mut element_ty) => visitor.visit_ty(element_ty)?,
        TyKind::Unresolved(ref mut ident) => visitor.visit_ident(ident)?,
        _ => (),
    }
    Ok(())
}

pub fn walk_expr<V: VisitorMut>(visitor: &mut V, e: &mut Expr) -> Result<(), V::Err> {
    match e.deref_mut().kind {
        ExprKind::Var(ref mut ident) => visitor.visit_ident(ident)?,
        ExprKind::Call(ref mut ident, ref mut args) => {
            visitor.visit_ident(ident)?;
            visitor.visit_exprs(args)?;
        }
        ExprKind::Ite(ref mut cond, ref mut lhs, ref mut rhs) => {
            visitor.visit_expr(cond)?;
            visitor.visit_expr(lhs)?;
            visitor.visit_expr(rhs)?;
        }
        ExprKind::Binary(_op, ref mut lhs, ref mut rhs) => {
            visitor.visit_expr(lhs)?;
            visitor.visit_expr(rhs)?;
        }
        ExprKind::Unary(_op, ref mut expr) => visitor.visit_expr(expr)?,
        ExprKind::Cast(ref mut expr) => {
            visitor.visit_expr(expr)?;
        }
        ExprKind::Quant(_op, ref mut quant_vars, ref mut ann, ref mut expr) => {
            for quant_var in quant_vars {
                match quant_var {
                    QuantVar::Shadow(var) => visitor.visit_ident(var)?,
                    QuantVar::Fresh(decl_ref) => {
                        visitor.visit_var_decl(decl_ref)?;
                    }
                }
            }
            walk_quant_ann(visitor, ann)?;
            visitor.visit_expr(expr)?;
        }
        ExprKind::Subst(ref mut ident, ref mut by, ref mut expr) => {
            visitor.visit_ident(ident)?;
            visitor.visit_expr(by)?;
            visitor.visit_expr(expr)?;
        }
        ExprKind::Lit(_) => {}
    }
    Ok(())
}

pub fn walk_quant_ann<V: VisitorMut>(visitor: &mut V, ann: &mut QuantAnn) -> Result<(), V::Err> {
    for trigger in &mut ann.triggers {
        for term in trigger.terms_mut() {
            visitor.visit_expr(term)?;
        }
    }
    Ok(())
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
