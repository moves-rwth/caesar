//! Replacement of calls to procedures by their specification.

use ariadne::ReportKind;
use replace_with::replace_with_or_abort;

use crate::{
    ast::{
        util::VariableCollector,
        visit::{walk_stmt, VisitorMut},
        DeclKind, DeclRef, Diagnostic, Direction, Expr, ExprBuilder, ExprData, ExprKind, Ident,
        Label, Param, ProcSpec, Shared, Span, SpanVariant, Spanned, Stmt, StmtKind, Symbol,
        VarDecl, VarKind,
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
        if let ExprKind::Call(ident, _) = &e.kind {
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

    fn visit_stmts(&mut self, stmts: &mut Vec<Stmt>) -> Result<(), Self::Err> {
        let mut index = 0;
        while let Some(stmt) = stmts.get_mut(index) {
            index += 1;
            if let Some(call) = self.lower_stmt(stmt)? {
                // Keep the declaration in scope for the rest of the block.
                stmts.insert(index, call);
                index += 1;
            }
        }
        Ok(())
    }

    fn visit_stmt(&mut self, stmt: &mut Stmt) -> Result<(), Self::Err> {
        // An annotation gives its statement a scope for both the declaration and the call.
        if let Some(call) = self.lower_stmt(stmt)? {
            replace_with_or_abort(stmt, |stmt| {
                Spanned::new(stmt.span, StmtKind::Seq(vec![stmt, call]))
            });
        }
        Ok(())
    }
}

impl<'tcx> SpecCall<'tcx> {
    /// Lower calls and return a separate statement for a lowered initializer.
    fn lower_stmt(&mut self, stmt: &mut Stmt) -> Result<Option<Stmt>, SpecCallError> {
        // Check calls before lowering assignments or variable initializers.
        walk_stmt(self, stmt)?;
        match &mut stmt.node {
            StmtKind::Var(decl, init) => {
                let call = init
                    .as_ref()
                    .and_then(|rhs| self.encode_assign(stmt.span, &[decl.borrow().name], rhs));
                if call.is_some() {
                    *init = None;
                }
                return Ok(call);
            }
            StmtKind::Assign(lhses, rhs) => {
                if let Some(call) = self.encode_assign(stmt.span, lhses, rhs) {
                    *stmt = call;
                }
            }
            _ => {}
        }
        Ok(None)
    }

    fn encode_assign(&mut self, span: Span, lhses: &[Ident], rhs: &Expr) -> Option<Stmt> {
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

                // Save arguments used in postconditions before havocing the outputs.
                let stable_inputs: Vec<(&Param, Expr)> = {
                    let mut visitor = VariableCollector::new();
                    for spec in &proc.spec {
                        if let ProcSpec::Ensures(expr) = &spec {
                            visitor.add_expr(expr);
                        }
                    }
                    proc.inputs
                        .node
                        .iter()
                        .zip(args)
                        .map(|(input, arg)| {
                            if visitor.used_variables.contains(&input.name) {
                                let (stmt, expr) = self.save_argument(input, arg.clone());
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
                    let builder = ExprBuilder::new(span);
                    let lhs_exprs = lhses.iter().map(|ident| builder.var(*ident, self.tcx));
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
                return Some(Spanned::new(span, StmtKind::Seq(buf)));
            }
        }
        None
    }

    /// Declare a fresh local variable for the saved argument.
    fn save_argument(&mut self, param: &Param, value: Expr) -> (Stmt, Expr) {
        let span = param.span.variant(SpanVariant::SpecCall);
        let base = Ident {
            name: Symbol::intern(&format!("old_{}", param.name)),
            span,
        };
        let name = self.tcx.fresh_ident(base, span);
        let decl = DeclRef::new(VarDecl {
            name,
            ty: *param.ty.clone(),
            kind: VarKind::Mut,
            span,
            created_from: Some(param.name),
        });
        self.tcx.declare(DeclKind::VarDecl(decl.clone()));
        let stmt = Spanned::new(span, StmtKind::Var(decl, Some(value)));
        (stmt, ExprBuilder::new(span).var(name, self.tcx))
    }
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

    #[test]
    fn test_call_initializer_in_unroll() {
        let source = r#"
            proc dec(a: UInt) -> (r: UInt)
                pre 1
                post [r == a - 1]

            @wp proc countdown() -> (x: UInt)
                pre 1
                post [x == 0]
            {
                x = 2
                @unroll(3, 0)
                while x > 0 {
                    var y: UInt = dec(x)
                    x = y
                }
            }
        "#;
        assert!(verify_test(source).0.unwrap());
    }
}
