// Using [`IndexSet`], which is a HashSet that preserves the insertion order, for deterministic results
use indexmap::IndexSet;

use super::{
    visit::{walk_expr, walk_stmt, VisitorMut},
    Direction, Expr, ExprKind, Ident, Stmt, StmtKind,
};

/// Helper to find all free variables in expressions.
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
                    self.variables.shift_remove(&var);
                }

                Ok(())
            }
            ExprKind::Subst(ident, value, expr) => {
                self.visit_expr(value)?;
                let already_free = self.variables.contains(ident);
                self.visit_expr(expr)?;
                if !already_free {
                    self.variables.shift_remove(ident);
                }
                Ok(())
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

    /// Collect modified, declared, and used variables without changing the statement.
    pub fn from_stmt(stmt: &Stmt) -> Self {
        let mut collector = Self::new();
        collector.visit_stmt(&mut stmt.clone()).unwrap();
        collector
    }

    /// Return modified variables not declared in the statement, in encounter order.
    pub fn modified_outside_declarations(&self) -> Vec<Ident> {
        self.modified_variables
            .difference(&self.declared_variables)
            .copied()
            .collect()
    }
}

impl VisitorMut for ModifiedVariableCollector {
    type Err = ();
    fn visit_stmt(&mut self, s: &mut super::Stmt) -> Result<(), Self::Err> {
        match &s.node {
            StmtKind::Assign(vars, _) | StmtKind::Havoc(_, vars) => {
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

/// For [`Direction::Down`], this is [`is_top_lit`], for [`Direction::Up`] this
/// is [`is_bot_lit`].
pub fn is_dir_top_lit(direction: Direction, expr: &Expr) -> bool {
    match direction {
        Direction::Down => is_top_lit(expr),
        Direction::Up => is_bot_lit(expr),
    }
}

/// Whether this is a [`ExprKind::Lit`] that is a top element.
pub fn is_top_lit(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Lit(lit) => lit.node.is_top(),
        _ => false,
    }
}

/// Whether this is a [`ExprKind::Lit`] that is a bottom element. Will walk
/// through one [`ExprKind::Cast`] expression (as generated for 0 for EUReal).
pub fn is_bot_lit(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Lit(lit) => lit.node.is_bot(),
        ExprKind::Cast(inner) => match &inner.kind {
            ExprKind::Lit(lit) => lit.node.is_bot(),
            _ => false,
        },
        _ => false,
    }
}

/// Remove [`ExprKind::Cast`] from this expression. This is mainly used to make
/// the pretty-printed expression look less verbose.
pub fn remove_casts(expr: &Expr) -> Expr {
    let mut res = expr.clone();
    RemoveCastsVisitor.visit_expr(&mut res).unwrap();
    res
}

struct RemoveCastsVisitor;

impl VisitorMut for RemoveCastsVisitor {
    type Err = ();

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        if let ExprKind::Cast(inner) = &mut e.kind {
            *e = inner.clone();
        }
        walk_expr(self, e)
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

    #[test]
    fn test_free_bindings() {
        let builder = ExprBuilder::new(Span::dummy_span());
        let tcx = TyCtx::new(TyKind::EUReal);
        let [x, y, z] = ["x", "y", "z"].map(|name| {
            let ident = Ident::with_dummy_span(Symbol::intern(name));
            tcx.declare(crate::ast::DeclKind::VarDecl(DeclRef::new(VarDecl {
                name: ident,
                ty: TyKind::Bool,
                kind: VarKind::Input,
                init: None,
                span: Span::dummy_span(),
                created_from: None,
            })));
            ident
        });
        let var = |ident| builder.var(ident, &tcx);
        let and = |lhs, rhs| builder.binary(BinOpKind::And, None, lhs, rhs);

        for (mut expr, expected) in [
            (
                builder.subst(and(var(x), var(z)), [(x, var(y))]),
                vec![y, z],
            ),
            (
                builder.subst(and(var(x), var(z)), [(x, var(x))]),
                vec![x, z],
            ),
            (
                and(var(x), builder.subst(and(var(x), var(z)), [(x, var(y))])),
                vec![x, y, z],
            ),
            (
                builder.subst(
                    builder.subst(and(var(x), var(y)), [(y, var(z))]),
                    [(x, var(y))],
                ),
                vec![y, z],
            ),
            (
                builder.quant(QuantOpKind::Exists, [x], and(var(x), and(var(y), var(z)))),
                vec![y, z],
            ),
        ] {
            let actual = FreeVariableCollector::new().collect_and_clear(&mut expr);
            assert_eq!(actual.into_iter().collect::<Vec<_>>(), expected);
        }
    }
}
