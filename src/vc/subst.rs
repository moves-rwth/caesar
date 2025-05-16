//! Variable substitution.
//!
//! The [`Subst`] structure implements a [`VisitorMut`] which applies the
//! substitutions in a naive way recursively. An alternative implementation that
//! is much smarter about which pieces of expressions to expand can be found in
//! [`crate::opt::unfolder`].

use std::ops::DerefMut;

use tracing::instrument;

use crate::{
    ast::{
        util::FreeVariableCollector,
        visit::{walk_expr, VisitorMut},
        Expr, ExprBuilder, ExprKind, Ident, QuantVar, Span, SpanVariant, VarKind,
    },
    resource_limits::{LimitError, LimitsRef},
    tyctx::TyCtx,
};

/// A stack frame of substitutions.
///
/// This structure uses immutable data structures, so it is cheap to clone.
#[derive(Default, Clone)]
struct SubstFrame {
    /// The substitutions in this frame.
    substs: im_rc::HashMap<Ident, Expr>,
    /// The number of right-hand sides of the substitutions in this frame that
    /// the ident shows up in.
    ///
    /// This is used to compute whether a quantified variable needs to be
    /// shadowed.
    free_vars: im_rc::HashMap<Ident, usize>,
}

/// A structure to apply variable substitutions in expressions.
pub struct Subst<'a> {
    tcx: &'a TyCtx,
    cur: SubstFrame,
    stack: Vec<SubstFrame>,
    pub limits_ref: LimitsRef,
}

impl<'a> Subst<'a> {
    /// Create a new empty instance.
    pub fn new(tcx: &'a TyCtx, limits_ref: &LimitsRef) -> Self {
        Subst {
            tcx,
            cur: SubstFrame::default(),
            stack: Vec::new(),
            limits_ref: limits_ref.clone(),
        }
    }

    /// Push the stack and add a substitution.
    pub fn push_subst(&mut self, ident: Ident, mut expr: Expr) {
        self.stack.push(self.cur.clone());
        let mut free_var_collector = FreeVariableCollector::new();
        free_var_collector.visit_expr(&mut expr).unwrap();
        for free_var in free_var_collector.variables {
            *self.cur.free_vars.entry(free_var).or_insert(0) += 1;
        }
        self.cur.substs.insert(ident, expr);
    }

    /// Push the stack and handle quantified variables.
    ///
    /// This function removes all given variables from the substitutions. If a
    /// variable is contained in the free variables of the current substitution,
    /// then we create a "shadow" variable that is used instead of the original
    /// variable to avoid name clashes.
    pub fn push_quant(&mut self, span: Span, vars: &mut [QuantVar], tcx: &TyCtx) {
        self.stack.push(self.cur.clone());

        for var in vars {
            let ident = var.name();

            // remove the substitution for the variable (if present)
            let old_expr = self.cur.substs.remove(&ident);

            // if we removed an expression from the substitution map, update the
            // free variables counter.
            if let Some(mut old_expr) = old_expr {
                let mut free_var_collector = FreeVariableCollector::new();
                free_var_collector.visit_expr(&mut old_expr).unwrap();

                for free_var in free_var_collector.variables {
                    let counter = self.cur.free_vars.get_mut(&free_var).unwrap();
                    *counter -= 1;
                }
            }

            // if the variable is contained in the free variables of this
            // substitution, then shadow it: rename the variable and replace all
            // occurrences of the original variable with the new one.
            if self.cur.free_vars.get(&ident).unwrap_or(&0) > &0 {
                tracing::trace!(ident=?ident, "shadowing quantified variable");

                let new_span = span.variant(SpanVariant::Subst);
                let new_ident = tcx.clone_var(ident, new_span, VarKind::Subst);
                let builder = ExprBuilder::new(new_ident.span);
                let new_expr = builder.var(new_ident, tcx);

                // shadow the variable
                *var = QuantVar::Shadow(new_ident);

                // substitute original variable with the shadow variable
                self.cur.substs.insert(ident, new_expr);
            }
        }
    }

    /// Pop the stack.
    pub fn pop(&mut self) {
        self.cur = self.stack.pop().expect("more calls to pop than push!");
    }

    /// Lookup a variable in the current frame of substitutions.
    pub fn lookup_var(&self, ident: Ident) -> Option<&Expr> {
        self.cur.substs.get(&ident)
    }
}

impl<'a> VisitorMut for Subst<'a> {
    type Err = LimitError;

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        self.limits_ref.check_limits()?;

        let span = e.span;
        match &mut e.deref_mut().kind {
            ExprKind::Var(ident) => {
                if let Some(subst) = self.lookup_var(*ident) {
                    *e = subst.clone()
                }
                Ok(())
            }
            ExprKind::Quant(_, ref mut vars, _, ref mut expr) => {
                self.push_quant(span, vars, self.tcx);
                self.visit_expr(expr)?;
                self.pop();
                Ok(())
            }
            ExprKind::Subst(ident, subst, expr) => {
                self.visit_expr(subst)?;
                self.push_subst(*ident, subst.clone());
                self.visit_expr(expr)?;
                self.pop();
                *e = expr.clone(); // TODO: this is an unnecessary clone
                Ok(())
            }
            _ => walk_expr(self, e),
        }
    }
}

/// Apply the [`crate::ast::expr::ExprKind::Subst`] inside the given expression
/// so that it doesn't contain any substitutions anymore.
///
/// As said in the module description [`crate::vc::subst`], this is the "strict"
/// and simpler version of the [`crate::opt::unfolder`].
#[instrument(skip_all)]
pub fn apply_subst(tcx: &TyCtx, e: &mut Expr, limits_ref: &LimitsRef) -> Result<(), LimitError> {
    let mut subst = Subst::new(tcx, limits_ref);
    subst.visit_expr(e)
}
