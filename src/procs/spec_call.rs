//! Replacement of calls to procedures by their specification.

use crate::{
    ast::{
        util::FreeVariableCollector,
        visit::{walk_stmt, VisitorMut},
        DeclKind, DeclRef, Expr, ExprData, ExprKind, Ident, Param, ProcSpec, Shared, Span,
        SpanVariant, Spanned, Stmt, StmtKind, Symbol, VarDecl, VarKind,
    },
    tyctx::TyCtx,
};

pub struct SpecCall<'tcx> {
    tcx: &'tcx mut TyCtx,
}

impl<'tcx> SpecCall<'tcx> {
    pub fn new(tcx: &'tcx mut TyCtx) -> Self {
        SpecCall { tcx }
    }
}

impl<'tcx> VisitorMut for SpecCall<'tcx> {
    type Err = ();

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        match &mut s.node {
            StmtKind::Var(decl_ref) => {
                let decl = decl_ref.borrow();
                if let Some(rhs) = &decl.init {
                    if let Some((span, mut buf)) = self.encode_assign(s.span, &[decl.name], rhs) {
                        drop(decl);
                        {
                            let mut decl = decl_ref.borrow_mut();
                            decl.init = None;
                        }
                        buf.insert(0, Spanned::new(span, StmtKind::Var(decl_ref.clone())));
                        s.span = span;
                        s.node = StmtKind::Block(buf);
                        return Ok(());
                    }
                }
            }
            StmtKind::Assign(lhses, rhs) => {
                if let Some((span, buf)) = self.encode_assign(s.span, lhses, rhs) {
                    s.span = span;
                    s.node = StmtKind::Block(buf);
                    return Ok(());
                }
            }
            _ => {}
        };
        walk_stmt(self, s)
    }
}

impl<'tcx> SpecCall<'tcx> {
    fn encode_assign(
        &mut self,
        span: Span,
        lhses: &[Ident],
        rhs: &Expr,
    ) -> Option<(Span, Vec<Stmt>)> {
        if let ExprKind::Call(ident, args) = &rhs.kind {
            if let DeclKind::ProcDecl(proc_ref) = self.tcx.get(*ident).unwrap().as_ref() {
                let proc_ref = proc_ref.clone(); // lose the reference to &mut self
                let proc = proc_ref.borrow();

                let direction = proc.direction;

                let mut buf: Vec<Stmt> = vec![];

                let span = span.variant(SpanVariant::SpecCall);

                // first push all asserts
                for spec in &proc.spec {
                    #[allow(clippy::single_match)]
                    match spec {
                        ProcSpec::Requires(expr) => {
                            let assert_expr = subst(
                                expr.clone(),
                                proc.inputs.node.iter().zip(args.iter().cloned()),
                            );
                            let stmt_kind = StmtKind::Assert(direction, assert_expr);
                            buf.push(Spanned::new(span, stmt_kind));
                        }
                        _ => {}
                    }
                }

                // collect "old" values, these are the input variables
                // that also occur in the requires specs. we don't want
                // their values to be destroyed by the havoc.
                let stable_inputs: Vec<(&Param, Expr)> = {
                    let mut visitor = FreeVariableCollector::new();
                    for spec in &proc.spec {
                        if let ProcSpec::Ensures(expr) = &spec {
                            // the clone is only necessary because
                            // visit_expr requires a mutable reference
                            // (unnecessarily)
                            visitor.visit_expr(&mut expr.clone()).unwrap();
                        }
                    }
                    proc.inputs
                        .node
                        .iter()
                        .zip(args)
                        .map(|(input, arg)| {
                            if visitor.variables.contains(&input.name) {
                                let (stmt, expr) = self.assign_to_temp(input, arg.clone());
                                buf.push(stmt);
                                (input, expr)
                            } else {
                                (input, arg.clone())
                            }
                        })
                        .collect()
                };

                // now push the havoc
                {
                    let stmt_kind = StmtKind::Havoc(direction, lhses.to_vec());
                    buf.push(Spanned::new(span, stmt_kind));
                }

                // finally, push all compares
                {
                    let lhs_exprs = lhses
                        .iter()
                        .map(|ident| ident_to_expr(self.tcx, span, *ident));
                    let output_subst = proc.outputs.node.iter().zip(lhs_exprs);
                    let substs: Vec<(&Param, Expr)> =
                        stable_inputs.into_iter().chain(output_subst).collect();
                    for spec in &proc.spec {
                        if let ProcSpec::Ensures(expr) = spec {
                            let compare_expr = subst(expr.clone(), substs.iter().cloned());
                            let stmt_kind = StmtKind::Compare(direction, compare_expr);
                            buf.push(Spanned::new(span, stmt_kind));
                        };
                    }
                }
                return Some((span, buf));
            }
        }
        None
    }
}

impl<'tcx> SpecCall<'tcx> {
    /// Assign to a temporary variable for this parameter.
    fn assign_to_temp(&mut self, param: &Param, value: Expr) -> (Stmt, Expr) {
        let span = param.span.variant(SpanVariant::SpecCall);
        let name = Ident {
            name: Symbol::intern(&format!("old_{}", param.name)),
            span,
        };
        // Reuse an existing declaration if possible.
        if let Some(_decl) = self.tcx.get(name).as_deref() {
            let stmt = Spanned::new(span, StmtKind::Assign(vec![name], value));
            (stmt, ident_to_expr(self.tcx, span, name))
        } else {
            // TODO: creating a variable declaration only for the first
            // assignment to a temp for this parameter may generate invalid
            // code. the declaration will only be created in the first procedure
            // it's required in, but a second procedure won't have this
            // declaration. so technically there should be a variable
            // declaration there as well. this is not a problem for us now,
            // because we don't look for declarations locally anymore, but it's
            // annoying if one looks at the intermediate representations.
            let var_decl = VarDecl {
                name,
                ty: *param.ty.clone(),
                kind: VarKind::Mut, // we might use the variable again in another proc call
                init: Some(value),
                span,
                created_from: Some(param.name),
            };
            let decl = DeclRef::new(var_decl);
            self.tcx.declare(DeclKind::VarDecl(decl.clone()));
            let stmt = Spanned::new(span, StmtKind::Var(decl));
            (stmt, ident_to_expr(self.tcx, span, name))
        }
    }
}

fn ident_to_expr(tcx: &TyCtx, span: Span, ident: Ident) -> Expr {
    let ty = match tcx.get(ident).unwrap().as_ref() {
        DeclKind::VarDecl(var_ref) => var_ref.borrow().ty.clone(),
        _ => todo!(),
    };
    Shared::new(ExprData {
        kind: ExprKind::Var(ident),
        ty: Some(ty),
        span,
    })
}

fn subst<'a>(expr: Expr, iter: impl IntoIterator<Item = (&'a Param, Expr)>) -> Expr {
    iter.into_iter().fold(expr.clone(), |acc, (param, rhs)| {
        Shared::new(ExprData {
            kind: ExprKind::Subst(param.name, rhs, acc),
            ty: expr.ty.clone(),
            span: expr.span.variant(SpanVariant::SpecCall),
        })
    })
}

#[cfg(test)]
mod test {

    use crate::verify_test;

    /// Test the classic bug when encoding procedure calls. When a variable
    /// occurs on both the left-hand side and the right-hand side of a procedure
    /// call, then we have to employ some tricks to preserve the previous value
    /// of the parameters over the havoc that is generated.
    #[test]
    fn test_lhs_rhs_shared() {
        let source = r#"
            proc inc(p: UInt) -> (r: UInt)
                pre ?(true)
                post ?(r == p+1)

            proc main() -> () {
                var x: UInt = 4
                x = inc(x)
                assert ?(false) // this should never verify!
            }
        "#;
        let res = verify_test(&source).0.unwrap();
        assert_eq!(res, false);
    }
}
