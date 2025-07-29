use std::{
    collections::HashSet,
    convert::Infallible,
    fmt::{Display, Formatter},
};

use ref_cast::RefCast;
use tracing::info_span;

use crate::{ast::{
    visit::{walk_expr, VisitorMut},
    Expr, ExprData, ExprKind, Ident, RefEqShared,
}, smt::SmtCtx};

type RefEqExpr = RefEqShared<ExprData>;

/// A set of expressions that are considered literal. Equality is determined by
/// pointer equality of the expressions.
#[derive(Debug, Default, Clone)]
pub struct LiteralExprSet(HashSet<RefEqExpr>);

impl LiteralExprSet {
    pub fn is_literal(&self, expr: &Expr) -> bool {
        self.0.contains(RefEqExpr::ref_cast(expr))
    }

    pub fn insert(&mut self, expr: Expr) -> bool {
        self.0.insert(RefEqExpr::new(expr))
    }

    pub fn remove(&mut self, expr: &Expr) -> bool {
        self.0.remove(RefEqExpr::ref_cast(expr))
    }

    pub fn extend(&mut self, other: impl IntoIterator<Item = Expr>) {
        self.0.extend(other.into_iter().map(RefEqExpr::new));
    }
}

impl Display for LiteralExprSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (i, expr) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", expr.as_shared())?;
        }
        write!(f, "}}")
    }
}

/// Collects the maximal literal subexpressions of an expression. An expression
/// is to be considered literal if it is a literal, a known literal variable, or
/// all its children are literal. Maximality is in relation to the expression
/// size. Meaning if an expression is reported as literal, none of its children
/// are reported.
///
/// # Example
/// If `a` is a known literal variable then for the expression `a + 4 * b` this
/// analysis will return only `a + 4`.
///
/// # Note
/// Only reporting maximal subexpressions is an optimisation. The resulting
/// literal information is forwarded to the SMT-solver (wrapping them in
/// Lit-marker). Also, wrapping all the intermediate expressions severally
/// degrades solver performance.
#[derive(Debug, Clone)]
pub struct LiteralExprCollector {
    literal_exprs: LiteralExprSet,
    literal_vars: HashSet<Ident>,
    computable_functions: HashSet<Ident>,
}

impl LiteralExprCollector {
    pub fn new(ctx: &SmtCtx<'_>) -> Self {
        Self {
            literal_exprs: LiteralExprSet::default(),
            literal_vars: HashSet::new(),
            computable_functions: ctx.computable_functions()
                .into_iter()
                .collect(),
        }
    }

    fn is_literal(&self, expr: &Expr) -> bool {
        self.literal_exprs.is_literal(expr)
    }

    /// Add some variables to the set of literals.
    pub fn add_literal_vars(self, literal_vars: impl IntoIterator<Item = Ident>) -> Self {
        Self {
            literal_vars: literal_vars.into_iter().collect(),
            ..self
        }
    }

    /// Collect literals in this expression using the [VisitorMut] impl.
    pub fn collect_literals(mut self, expr: &mut Expr) -> LiteralExprSet {
        if self.literal_vars.is_empty() && self.computable_functions.is_empty() {
            return LiteralExprSet::default();
        }

        let span = info_span!("collect literal expressions");
        let _enter = span.enter();

        self.visit_expr(expr).unwrap();
        tracing::trace!(
            analized_expr=%expr,
            literal_vars=?self.literal_vars,
            functions_with_def=?self.computable_functions,
            literal_exprs=%self.literal_exprs,
            "collected literal expressions"
        );
        self.literal_exprs
    }
}

impl VisitorMut for LiteralExprCollector {
    type Err = Infallible;

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        walk_expr(self, expr)?; // visit children first

        match &expr.kind {
            ExprKind::Var(ident) => {
                if self.literal_vars.contains(ident) {
                    self.literal_exprs.insert(expr.clone());
                }
            }
            ExprKind::Call(func, args) => {
                // Function calls with only literal arguments are themselves literal.
                // This is intuitively true but can cause some problems in practice if the function
                // does not actually have a definition.
                // E.g. probCollision() only defined as:
                //     func probCollision(): UReal
                //     axiom collisionProb probCollision() <= 1
                // is trivially always literal but performing any kind of computation with
                // it is hopeless.
                if self.computable_functions.contains(func)
                    && args.iter().all(|arg| self.is_literal(arg))
                {
                    self.literal_exprs.insert(expr.clone());
                    // Do not remove arguments for calls. Otherwise, the computation axiom might
                    // not match because we lifted the Lit marker too far.
                    // Example: Lit(fac(5) == 125) does not let us compute fib(5)
                    //          Lit(fac(Lit(5)) == 125) lets us do this.
                }
            }
            ExprKind::Ite(cond, then, other) => {
                if self.is_literal(cond) && self.is_literal(then) && self.is_literal(other) {
                    self.literal_exprs.insert(expr.clone());
                    self.literal_exprs.remove(cond);
                    self.literal_exprs.remove(then);
                    self.literal_exprs.remove(other);
                }
            }
            ExprKind::Binary(_, lhs, rhs) => {
                if self.is_literal(lhs) && self.is_literal(rhs) {
                    self.literal_exprs.insert(expr.clone());
                    self.literal_exprs.remove(lhs);
                    self.literal_exprs.remove(rhs);
                }
            }
            ExprKind::Unary(_, inner_expr) => {
                if self.is_literal(inner_expr) {
                    self.literal_exprs.insert(expr.clone());
                    self.literal_exprs.remove(inner_expr);
                }
            }
            ExprKind::Cast(inner_expr) => {
                if self.is_literal(inner_expr) {
                    self.literal_exprs.insert(expr.clone());
                    self.literal_exprs.remove(inner_expr);
                }
            }
            ExprKind::Quant(_, _, _, _) => {}
            ExprKind::Subst(_, _, _) => {
                panic!(
                    "cannot determine literal subexpressions in expressions with substitutions: {expr}"
                );
            }
            ExprKind::Lit(_) => {
                self.literal_exprs.insert(expr.clone());
            }
        }

        Ok(())
    }
}
