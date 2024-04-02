// Using [`IndexSet`], which is a HashSet that preserves the insertion order, for deterministic results
use indexmap::IndexSet;

use super::{
    visit::{walk_expr, walk_stmt, VisitorMut},
    Expr, ExprKind, Ident, StmtKind,
};

/// Helper to find all free variables in expressions.
///
/// Expressions with substitutions in them are not allowed and will lead to a panic!
#[derive(Debug, Default)]
pub struct FreeVariableCollector {
    pub variables: IndexSet<Ident>,
}

impl FreeVariableCollector {
    pub fn new() -> Self {
        Self::default()
    }

    /// Collect variables from given [`Expr`] and clear the variables set for further use
    pub fn collect_and_clear(&mut self, expr: &mut Expr) -> IndexSet<Ident> {
        self.visit_expr(expr).unwrap();
        let vars = self.variables.clone();
        self.variables.clear();

        vars
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

#[derive(Debug, Default)]
/// Collect modified and declared variables in a statement. Note that modified variables can contain declared variables.
pub struct ModifiedVariableCollector {
    /// [`Ident`]s of variables that are declared in the statement
    pub declared_variables: IndexSet<Ident>,
    /// [`Ident`]s of variables that are modified in the statement
    pub modified_variables: IndexSet<Ident>,
    /// [`Ident`]s of variables that are used in an expression in the statement
    pub used_variables: IndexSet<Ident>,
}

impl ModifiedVariableCollector {
    pub fn new() -> Self {
        Self::default()
    }
}

impl VisitorMut for ModifiedVariableCollector {
    type Err = ();
    fn visit_stmt(&mut self, s: &mut super::Stmt) -> Result<(), Self::Err> {
        match &s.node {
            StmtKind::Assign(vars, _) => {
                self.modified_variables.extend(vars);
            }
            StmtKind::Var(var) => {
                self.declared_variables.insert(var.borrow().name);
            }
            _ => {}
        }
        walk_stmt(self, s)?;
        Ok(())
    }

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        match &mut e.kind {
            ExprKind::Var(ident) => {
                self.used_variables.insert(*ident);
                Ok(())
            }
            _ => walk_expr(self, e),
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
            kind: VarKind::Input,
            init: None,
            span: Span::dummy_span(),
            created_from: None,
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
