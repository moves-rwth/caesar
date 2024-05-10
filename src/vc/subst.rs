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
    tyctx::TyCtx,
};

#[derive(Default, Clone)]
struct SubstLevel {
    substs: im_rc::HashMap<Ident, Expr>,
    free_vars: im_rc::HashSet<Ident>,
}

pub struct Subst<'a> {
    tcx: &'a TyCtx,
    cur: SubstLevel,
    stack: Vec<SubstLevel>,
}

impl<'a> Subst<'a> {
    pub fn new(tcx: &'a TyCtx) -> Self {
        Subst {
            tcx,
            cur: SubstLevel::default(),
            stack: Vec::new(),
        }
    }

    pub fn push_subst(&mut self, ident: Ident, mut expr: Expr) {
        self.stack.push(self.cur.clone());
        let mut free_var_collector = FreeVariableCollector::new();
        free_var_collector.visit_expr(&mut expr).unwrap();
        self.cur.free_vars.extend(free_var_collector.variables);
        self.cur.substs.insert(ident, expr);
    }

    pub fn push_quant(&mut self, span: Span, vars: &mut [QuantVar], tcx: &TyCtx) {
        self.stack.push(self.cur.clone());
        for var in vars {
            let ident = var.name();
            self.cur.substs.remove(&ident);
            // TODO: if we removed a previous substitution, we should rebuild
            // the set of free variables because it might contain variables that
            // won't be inserted anymore.
            //
            // right now, we over-approximate the set of free variables which is
            // sound, but might result in too many quantified variables being
            // renamed.

            if self.cur.free_vars.contains(&ident) {
                let new_ident =
                    tcx.clone_var(ident, span.variant(SpanVariant::Subst), VarKind::Subst);
                *var = QuantVar::Shadow(new_ident);
                let builder = ExprBuilder::new(new_ident.span);
                self.cur.substs.insert(ident, builder.var(new_ident, tcx));
            }
        }
    }

    pub fn pop(&mut self) {
        self.cur = self.stack.pop().expect("more calls to pop than push!");
    }

    pub fn lookup_var(&self, ident: Ident) -> Option<&Expr> {
        self.cur.substs.get(&ident)
    }
}

impl<'a> VisitorMut for Subst<'a> {
    type Err = ();

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
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

#[instrument(skip(tcx, e))]
pub fn apply_subst(tcx: &TyCtx, e: &mut Expr) {
    let mut subst = Subst::new(tcx);
    subst.visit_expr(e).unwrap()
}
