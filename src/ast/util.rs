use indexmap::IndexSet;

use super::{
    visit::{walk_expr, VisitorMut},
    Direction, Expr, ExprKind, Ident, Stmt, StmtKind,
};

/// Collect variables used, modified, or declared in expressions and statements.
/// Each set preserves encounter order.
#[derive(Debug, Default)]
pub struct VariableCollector {
    /// Locally declared variables, including bindings supplied by callers.
    pub declared_variables: IndexSet<Ident>,
    /// Modified variables, including local variables.
    pub modified_variables: IndexSet<Ident>,
    /// Free variables used in expressions.
    pub used_variables: IndexSet<Ident>,
}

impl VariableCollector {
    pub fn new() -> Self {
        Self::default()
    }

    /// Collect free variables in `expr`.
    pub fn from_expr(expr: &Expr) -> Self {
        let mut collector = Self::new();
        collector.add_expr(expr);
        collector
    }

    /// Collect variables in `stmt`.
    pub fn from_stmt(stmt: &Stmt) -> Self {
        let mut collector = Self::new();
        collector.add_stmt(stmt);
        collector
    }

    /// Add variables from `stmt`.
    pub fn add_stmt(&mut self, stmt: &Stmt) {
        match &stmt.node {
            StmtKind::Seq(stmts) => self.add_stmts(stmts),
            StmtKind::Var(var) => {
                let var = var.borrow();
                self.declared_variables.insert(var.name);
                if let Some(init) = &var.init {
                    self.add_expr(init);
                }
            }
            StmtKind::Assign(vars, expr) => {
                self.modified_variables.extend(vars);
                self.add_expr(expr);
            }
            StmtKind::Havoc(_, vars) => self.modified_variables.extend(vars),
            StmtKind::Assert(_, expr)
            | StmtKind::Assume(_, expr)
            | StmtKind::Compare(_, expr)
            | StmtKind::Tick(expr)
            | StmtKind::Weigh(expr) => self.add_expr(expr),
            StmtKind::Demonic(first, second)
            | StmtKind::Angelic(first, second)
            | StmtKind::Additive(first, second) => {
                self.add_stmts(&first.node);
                self.add_stmts(&second.node);
            }
            StmtKind::If(cond, first, second) => {
                self.add_expr(cond);
                self.add_stmts(&first.node);
                self.add_stmts(&second.node);
            }
            StmtKind::While(cond, body) => {
                self.add_expr(cond);
                self.add_stmts(&body.node);
            }
            StmtKind::Annotation(_, _, args, stmt) => {
                for arg in args {
                    self.add_expr(arg);
                }
                self.add_stmt(stmt);
            }
            StmtKind::Negate(_) | StmtKind::Validate(_) | StmtKind::Label(_) => {}
        }
    }

    /// Add free variables from `expr`.
    pub fn add_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Var(ident) => {
                self.used_variables.insert(*ident);
            }
            ExprKind::Call(_, args) => {
                for arg in args {
                    self.add_expr(arg);
                }
            }
            ExprKind::Ite(cond, first, second) => {
                self.add_expr(cond);
                self.add_expr(first);
                self.add_expr(second);
            }
            ExprKind::Binary(_, lhs, rhs) => {
                self.add_expr(lhs);
                self.add_expr(rhs);
            }
            ExprKind::Unary(_, expr) | ExprKind::Cast(expr) => self.add_expr(expr),
            ExprKind::Quant(_, bound, _, expr) => {
                // Keep any variables that already occurred free outside this quantifier.
                let bound_and_not_free: Vec<Ident> = bound
                    .iter()
                    .map(|v| v.name())
                    .filter(|v| !self.used_variables.contains(v))
                    .collect();

                // Ignore quantifier annotations when collecting free variables.
                self.add_expr(expr);

                for var in bound_and_not_free {
                    self.used_variables.shift_remove(&var);
                }
            }
            ExprKind::Subst(ident, value, expr) => {
                self.add_expr(value);
                let already_free = self.used_variables.contains(ident);
                self.add_expr(expr);
                if !already_free {
                    self.used_variables.shift_remove(ident);
                }
            }
            ExprKind::Lit(_) => {}
        }
    }

    /// Iterate over modified variables not declared locally.
    pub fn free_modified(&self) -> impl Iterator<Item = Ident> + '_ {
        self.modified_variables
            .difference(&self.declared_variables)
            .copied()
    }

    /// Iterate over used variables that are neither modified nor declared.
    pub fn free_read_only(&self) -> impl Iterator<Item = Ident> + '_ {
        self.used_variables
            .iter()
            .filter(|ident| {
                !self.modified_variables.contains(*ident)
                    && !self.declared_variables.contains(*ident)
            })
            .copied()
    }

    fn add_stmts(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            self.add_stmt(stmt);
        }
    }
}

/// For [`Direction::Down`], this is [`is_top_lit`], for [`Direction::Up`] this is [`is_bot_lit`].
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

/// Whether this is a [`ExprKind::Lit`] that is a bottom element.
/// Walks through one [`ExprKind::Cast`] expression, as generated for 0 for EUReal.
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

/// Remove [`ExprKind::Cast`] nodes to simplify the printed expression.
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
    use crate::ast::{
        BinOpKind, DeclRef, Direction, ExprBuilder, Ident, QuantOpKind, Span, Spanned, StmtKind,
        Symbol, TyKind, VarDecl, VarKind,
    };

    use super::VariableCollector;

    #[test]
    fn test_free_bindings() {
        let builder = ExprBuilder::new(Span::dummy_span());
        let [x, y, z] = ["x", "y", "z"].map(|name| Ident::with_dummy_span(Symbol::intern(name)));
        let var = |ident| builder.var_ty(ident, TyKind::Bool);
        let and = |lhs, rhs| builder.binary(BinOpKind::And, None, lhs, rhs);

        for (expr, expected) in [
            (
                and(var(x), builder.quant(QuantOpKind::Exists, [x], var(x))),
                vec![x],
            ),
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
            let actual = VariableCollector::from_expr(&expr).used_variables;
            assert_eq!(actual.into_iter().collect::<Vec<_>>(), expected);
        }
    }

    #[test]
    fn test_statement_variables_and_annotation_reads() {
        let span = Span::dummy_span();
        let builder = ExprBuilder::new(span);
        let [x, y, a, b, local] =
            ["x", "y", "a", "b", "local"].map(|name| Ident::with_dummy_span(Symbol::intern(name)));
        let local_decl = DeclRef::new(VarDecl {
            name: local,
            ty: TyKind::Bool,
            kind: VarKind::Mut,
            init: None,
            span,
            created_from: None,
        });
        let var = |ident| builder.var_ty(ident, TyKind::Bool);
        let stmt = |kind| Spanned::new(span, kind);
        let annotated = stmt(StmtKind::Annotation(
            span,
            x,
            vec![var(b)],
            Box::new(stmt(StmtKind::Assert(
                Direction::Down,
                builder.binary(BinOpKind::And, None, var(a), var(local)),
            ))),
        ));
        let program = stmt(StmtKind::Seq(vec![
            stmt(StmtKind::Var(local_decl)),
            stmt(StmtKind::Havoc(Direction::Down, vec![x])),
            stmt(StmtKind::Havoc(Direction::Up, vec![y, local])),
            annotated,
        ]));

        let collector = VariableCollector::from_stmt(&program);
        assert_eq!(collector.free_modified().collect::<Vec<_>>(), vec![x, y]);
        assert_eq!(collector.free_read_only().collect::<Vec<_>>(), vec![b, a]);
    }
}
