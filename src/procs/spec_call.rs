//! Replacement of calls to procedures by their specification.

use std::ops::DerefMut;

use ariadne::ReportKind;

use crate::{
    ast::{
        util::FreeVariableCollector,
        visit::{walk_stmt, VisitorMut},
        Block, DeclKind, DeclRef, Diagnostic, Direction, Expr, ExprData, ExprKind, Ident, Label,
        Param, ProcSpec, Shared, Span, SpanVariant, Spanned, Stmt, StmtKind, Symbol, VarDecl,
        VarKind,
    },
    slicing::{wrap_with_error_message, wrap_with_success_message},
    tyctx::TyCtx,
};

pub struct SpecCall<'tcx> {
    tcx: &'tcx mut TyCtx,
    direction: Direction,
    proc_name: String,
}

impl<'tcx> SpecCall<'tcx> {
    pub fn new(tcx: &'tcx mut TyCtx, direction: Direction, proc_name: String) -> Self {
        SpecCall {
            tcx,
            direction,
            proc_name,
        }
    }
}

#[derive(Debug)]
pub enum SpecCallError {
    ProcDirectionMismatch {
        calling_direction: Direction,
        called_direction: Direction,
        span: Span,
        calling_proc: String,
        called_proc: Ident,
    },
}

impl SpecCallError {
    pub fn diagnostic(&self) -> Diagnostic {
        match self {
            SpecCallError::ProcDirectionMismatch {
                calling_direction,
                called_direction,
                span,
                calling_proc,
                called_proc,
            } => Diagnostic::new(ReportKind::Error, *span)
                .with_message(format!(
                    "The direction of '{} {}' does not match with the direction of the '{} {}'.",
                    calling_direction.prefix("proc"),
                    calling_proc,
                    called_direction.prefix("proc"),
                    called_proc.name
                ))
                .with_label(Label::new(*span).with_message(
                    "The direction of the called procedure must match the direction of the calling procedure.",
                )),
        }
    }
}

impl<'tcx> VisitorMut for SpecCall<'tcx> {
    type Err = SpecCallError;

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        if let ExprKind::Call(ref ident, _) = e.deref_mut().kind {
            if let DeclKind::ProcDecl(proc_ref) = self.tcx.get(*ident).unwrap().as_ref() {
                let proc_ref = proc_ref.clone(); // lose the reference to &mut self
                let proc = proc_ref.borrow();
                let context_direction = &self.direction;

                if *context_direction != proc.direction {
                    // Throw direction unsoundness mismatch error
                    return Err(SpecCallError::ProcDirectionMismatch {
                        calling_direction: *context_direction,
                        called_direction: proc.direction,
                        span: e.span,
                        calling_proc: self.proc_name.clone(), // If there is a direction, there should be an ident as well
                        called_proc: proc.name,
                    });
                }
            }
        }
        Ok(())
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        match &mut s.node {
            StmtKind::Var(decl_ref) => {
                let decl = decl_ref.borrow();
                if let Some(rhs) = &decl.init {
                    if let Some(mut block) = self.encode_assign(s.span, &[decl.name], rhs) {
                        drop(decl);
                        {
                            let mut decl = decl_ref.borrow_mut();
                            decl.init = None;
                        }
                        block
                            .node
                            .insert(0, Spanned::new(block.span, StmtKind::Var(decl_ref.clone())));
                        s.span = block.span;
                        s.node = StmtKind::Seq(block.node);
                        return Ok(());
                    }
                }
            }
            StmtKind::Assign(lhses, rhs) => {
                // Visit the right-hand side first to ensure that the procedure call is valid.
                self.visit_expr(rhs)?;
                if let Some(block) = self.encode_assign(s.span, lhses, rhs) {
                    s.span = block.span;
                    s.node = StmtKind::Seq(block.node);
                    return Ok(());
                }
            }
            _ => {}
        };
        walk_stmt(self, s)
    }
}

impl<'tcx> SpecCall<'tcx> {
    fn encode_assign(&mut self, span: Span, lhses: &[Ident], rhs: &Expr) -> Option<Block> {
        if let ExprKind::Call(ident, args) = &rhs.kind {
            if let DeclKind::ProcDecl(proc_ref) = self.tcx.get(*ident).unwrap().as_ref() {
                let proc_ref = proc_ref.clone(); // lose the reference to &mut self
                let proc = proc_ref.borrow();

                let direction = proc.direction;

                let mut buf: Vec<Stmt> = vec![];

                let span = span.variant(SpanVariant::SpecCall);

                // first push all asserts
                for (i, spec) in proc.spec.iter().enumerate() {
                    #[allow(clippy::single_match)]
                    match spec {
                        ProcSpec::Requires(expr) => {
                            let assert_expr = subst(
                                expr.clone(),
                                proc.inputs.node.iter().zip(args.iter().cloned()),
                            );
                            buf.push(wrap_with_error_message(
                                Spanned::new(span, StmtKind::Assert(direction, assert_expr)),
                                &format!("pre#{i} might not hold"),
                            ));
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
                    for (i, spec) in proc.spec.iter().enumerate() {
                        if let ProcSpec::Ensures(expr) = spec {
                            let compare_expr = subst(expr.clone(), substs.iter().cloned());
                            let stmt_kind = StmtKind::Compare(direction, compare_expr);
                            buf.push(wrap_with_success_message(
                                Spanned::new(span, stmt_kind),
                                &format!("post #{i} is not necessary"),
                            ));
                        };
                    }
                }
                return Some(Spanned::new(span, buf));
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

    use crate::driver::commands::verify::verify_test;

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
        let res = verify_test(source).0.unwrap();
        assert!(!res);
    }

    #[test]
    fn test_proc_direction_mismatch() {
        // this should produce an error
        let source = r#"

            coproc test1() -> () {}

            proc test2() -> () {
                test1() // a coproc is being called from a proc
            }
        "#;
        let res = verify_test(source).0;
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error: The direction of 'proc <builtin>::test2' does not match with the direction of the 'coproc test1'."
        );
    }
}
