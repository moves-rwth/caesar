use std::collections::HashSet;

use super::{
    visit::{walk_expr, VisitorMut},
    Expr, ExprKind, Ident,
};

/// Helper to find all free variables in expressions.
///
/// Expressions with substitutions in them are not allowed and will lead to a panic!
#[derive(Debug, Default)]
pub struct FreeVariableCollector {
    pub variables: HashSet<Ident>,
}

impl FreeVariableCollector {
    pub fn new() -> Self {
        Self::default()
    }
}

impl VisitorMut for FreeVariableCollector {
    type Err = ();

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        match &mut expr.kind {
            ExprKind::Var(ident) => {
                self.variables.insert(*ident);
                Ok(())
            }
            ExprKind::Quant(_, bound, _, ref mut expr) => {
                // which variables are bound here and *not* free?
                let bound_and_not_free: Vec<Ident> = bound
                    .iter()
                    .map(|v| v.name())
                    .filter(|v| !self.variables.contains(v))
                    .collect();

                // visit the quantified expression.
                self.visit_expr(expr)?;

                // remove the set of bound variables that haven't been free
                // before from the set of free variables.
                for var in bound_and_not_free {
                    self.variables.remove(&var);
                }

                Ok(())
            }
            ExprKind::Subst(_, _, _) => {
                panic!(
                    "cannot find free variables in expressions with substitutions: {}",
                    expr
                )
            }
            _ => walk_expr(self, expr),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{
        ast::{
            visit::VisitorMut, BinOpKind, DeclRef, ExprBuilder, Ident, QuantOpKind, Span, Symbol,
            TyKind, VarDecl, VarKind,
        },
        tyctx::TyCtx,
    };

    use super::FreeVariableCollector;

    #[test]
    fn test_free() {
        // a lot of work to build `expr = x && (exists x: x)`, an expression
        // where `x` is both bound and free.
        let builder = ExprBuilder::new(Span::dummy_span());
        let ident = Ident::with_dummy_span(Symbol::intern("x"));
        let tcx = TyCtx::new(TyKind::EUReal);
        tcx.declare(crate::ast::DeclKind::VarDecl(DeclRef::new(VarDecl {
            name: ident,
            ty: TyKind::Bool,
            kind: VarKind::Const,
            init: None,
            span: Span::dummy_span(),
        })));
        let mut expr = builder.binary(
            BinOpKind::And,
            None,
            builder.var(ident, &tcx),
            builder.quant(QuantOpKind::Exists, [ident], builder.var(ident, &tcx)),
        );

        // collect the free variables.
        let mut collector = FreeVariableCollector::default();
        collector.visit_expr(&mut expr).unwrap();

        // `x` is bound, but also free!
        assert_eq!(
            collector.variables.into_iter().collect::<Vec<Ident>>(),
            vec![ident]
        );
    }
}
