//! This module contains all functions related to fuel encoding from the paper
//! "Computing with an SMT Solver". The goal is to limit the number of quantifier instantiation
//! of a functions defining axiom. This is done by including an extra [z3rro::Fuel] parameter and
//! only providing axioms for non-zero fuel parameters. The fuel parameter is decremented in every
//! instantiation.
//!
//! # Note
//! For this to work the SMT solver is not allowed to synthesis fuel values itself.
//! Therefore, MBQI must be disabled.

use crate::ast::visit::{walk_expr, VisitorMut};
use crate::ast::{
    Expr, ExprBuilder, ExprData, ExprKind, FuncDecl, Ident, PointerHashShared, SpanVariant,
};
use crate::smt::translate_exprs::{FuelContext, TranslateExprs};
use crate::smt::{ty_to_sort, SmtCtx};
use crate::tyctx::TyCtx;
use indexmap::IndexSet;
use itertools::Itertools;
use std::convert::Infallible;
use z3::ast::{Ast, Bool};
use z3::{Pattern, Sort};
use z3rro::{SmtEq, SmtInvariant};

/// Builds the domain (parameter list) for `func`. If the limited function transformation is
/// applicable a fuel parameter is implicitly added as the first parameter.
pub fn build_func_domain<'a>(ctx: &SmtCtx<'a>, func: &FuncDecl) -> Vec<Sort<'a>> {
    let mut domain = if ctx.is_limited_function_decl(func) {
        vec![ctx.fuel_factory().sort().clone()]
    } else {
        vec![]
    };
    domain.extend(
        func.inputs
            .node
            .iter()
            .map(|param| ty_to_sort(ctx, &param.ty)),
    );
    domain
}

/// Creates an axiom that should be read from left to right.
/// It has the form:
/// ```txt
/// forall <vars...> @trigger(lhs) . lhs == rhs
/// ```
/// Where fuel parameters in `lhs` must be non-zero and are decremented in `rhs`.
fn translate_defining_axiom<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    lhs: &Expr,
    rhs: &Expr,
) -> Bool<'ctx> {
    translate.push();
    translate.set_fuel_context(FuelContext::Head);

    let symbolic_lhs = translate.t_symbolic(lhs).into_dynamic(translate.ctx);
    translate.set_fuel_context(FuelContext::Body);
    let symbolic_rhs = translate.t_symbolic(rhs).into_dynamic(translate.ctx);

    let axiom = translate.local_scope().forall(
        &[&Pattern::new(
            translate.ctx.ctx,
            &[&symbolic_lhs as &dyn Ast<'ctx>],
        )],
        &symbolic_lhs.smt_eq(&symbolic_rhs),
    );

    translate.set_fuel_context(FuelContext::Call); // reset to default
    translate.pop();

    axiom
}

/// Creates a call to the function.
fn build_call(tcx: &TyCtx, func: &FuncDecl) -> Expr {
    let span = func.span.variant(SpanVariant::VC);
    let builder = ExprBuilder::new(span);
    builder.call(
        func.name,
        func.inputs
            .node
            .iter()
            .map(|param| builder.var(param.name, tcx)),
        tcx,
    )
}

/// Creates the fuel synonym axiom that states that the result of the function is independent
/// of the fuel parameter. It has the form:
/// ```txt
/// forall fuel: Fuel, <args...> @trigger(func_name(Succ(fuel), <args...>)) . func_name(Succ(fuel), <args...>) = func_name(fuel, <args...>)
/// ```
///
/// The axiom is only generated for limited functions.
pub fn fuel_synonym_axiom<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    func: &FuncDecl,
) -> Option<Bool<'ctx>> {
    if translate.ctx.is_limited_function_decl(func) {
        let app = build_call(translate.ctx.tcx, func);
        Some(translate_defining_axiom(translate, &app, &app))
    } else {
        None
    }
}

/// Creates the default defining axiom for a function. It has the form:
/// ```txt
/// forall fuel: Fuel, <args...> @trigger(func_name(Succ(fuel), <args...>)) . func_name(Succ(fuel), <args...>) = <body>
/// ```
/// where only `fuel` is used as the fuel parameter in `<body>`.
///
/// The axiom is only generated for functions that have an immediate definition (body).
pub fn defining_axiom<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    func: &FuncDecl,
) -> Option<Bool<'ctx>> {
    func.body.borrow().as_ref().map(|body| {
        let app = build_call(translate.ctx.tcx, func);
        translate_defining_axiom(translate, &app, body)
    })
}

/// Creates the computation axiom that allows for constant arguments instantiation without
/// consuming fuel. It is very similar to the [defining_axiom]. The only differences are that
///  - all arguments must be known constant values (marked with [super::Lit]),
///  - the fuel value can be zero,
///  - the fuel value is not decreased in the body
///  - and the constant information is also propagated to the result.
///
/// It has the form:
/// ```txt
/// forall fuel: Fuel, <args...> @trigger(func_name(fuel, Lit(<args...>))) . func_name(fuel, Lit(<args...>)) = <body>
/// ```
///
/// The is axiom only generated for limited functions and if the corresponding feature is enabled.
pub fn computation_axiom<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    func: &FuncDecl,
) -> Option<Bool<'ctx>> {
    if !translate.ctx.lit_wrap {
        return None;
    }
    if !translate.ctx.is_limited_function_decl(func) {
        return None;
    }
    assert!(func.body.borrow().is_some());

    translate.push();
    translate.set_fuel_context(FuelContext::Body);
    {
        let constant_vars = func
            .inputs
            .node
            .iter()
            .map(|param| param.name)
            .collect_vec();

        translate.set_constant_exprs(
            constant_vars.as_slice(),
            func.body.borrow_mut().as_mut().unwrap(),
        );
    }

    let app = build_call(translate.ctx.tcx, func);

    let body_ref = func.body.borrow();
    let body = body_ref.as_ref().unwrap();

    let app_z3 = translate.t_symbolic(&app).into_dynamic(translate.ctx);
    let body_z3 = translate.t_symbolic(body).into_dynamic(translate.ctx);

    let axiom = translate.local_scope().forall(
        &[&Pattern::new(
            translate.ctx.ctx,
            &[&app_z3 as &dyn Ast<'ctx>],
        )],
        &app_z3.smt_eq(&body_z3),
    );
    translate.clear_constant_exprs();
    translate.set_fuel_context(FuelContext::Call);
    translate.pop();

    Some(axiom)
}

/// Invariant for the functions return value.
///
/// The axiom is only generated if the functions return type has an invariant.
pub fn return_value_invariant<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    func: &FuncDecl,
) -> Option<Bool<'ctx>> {
    translate.push();
    translate.set_fuel_context(FuelContext::Body);

    let app = build_call(translate.ctx.tcx, func);
    let app_z3 = translate.t_symbolic(&app);
    let axiom = app_z3
        .smt_invariant()
        .map(|invariant| translate.local_scope().forall(&[], &invariant));

    translate.set_fuel_context(FuelContext::Call);
    translate.pop();

    axiom
}

type HashExpr = PointerHashShared<ExprData>;

#[derive(Default)]
pub struct ConstantExprs(IndexSet<HashExpr>);

impl ConstantExprs {
    pub fn is_constant(&self, expr: &Expr) -> bool {
        self.0.contains(&HashExpr::new(expr.clone()))
    }

    fn insert(&mut self, expr: &Expr) -> bool {
        self.0.insert(HashExpr::new(expr.clone()))
    }

    fn remove(&mut self, expr: &Expr) -> bool {
        self.0.remove(&HashExpr::new(expr.clone()))
    }
}

/// Collects the maximal constant subexpressions of an expression.
/// An expression is to be considered constant if it is a literal, a known constant variable, or
/// all its children are constant. Maximality is in relation to the expression size. Meaning if an
/// expression is reported as constant, none of its children are reported.
///
/// # Example
/// If `a` is a known constant variable then for the expression `a + 4 * b` this analysis will
/// return only `a + 4`.
///
/// # Note
/// Only reporting maximal subexpressions is an optimisation. The resulting constant information
/// is forward to the SMT-solver (wrapping them in Lit-marker). Also, wrapping all the
/// intermediate expressions severally degrades solver performance.
#[derive(Default)]
pub struct ConstantExprCollector {
    constant_exprs: ConstantExprs,
    constant_vars: IndexSet<Ident>,
}

impl ConstantExprCollector {
    pub fn new(constant_vars: &[Ident]) -> Self {
        Self {
            constant_exprs: ConstantExprs::default(),
            constant_vars: constant_vars.iter().cloned().collect(),
        }
    }

    fn is_constant(&self, expr: &Expr) -> bool {
        self.constant_exprs.is_constant(expr)
    }

    pub fn into_constant_exprs(self) -> ConstantExprs {
        self.constant_exprs
    }
}

impl VisitorMut for ConstantExprCollector {
    type Err = Infallible;

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        walk_expr(self, expr)?; // visit children first

        match &expr.kind {
            ExprKind::Var(ident) => {
                if self.constant_vars.contains(ident) {
                    self.constant_exprs.insert(expr);
                }
            }
            ExprKind::Call(_, args) => {
                if args.iter().all(|arg| self.is_constant(arg)) {
                    self.constant_exprs.insert(expr);
                    for arg in args {
                        self.constant_exprs.remove(arg);
                    }
                }
            }
            ExprKind::Ite(cond, then, other) => {
                // TODO: maybe this should never be consider const?
                //       If-then-else is used as a stopper for constant values and therefore itself
                //       never considered constant. The paper mentions that this works well
                //       in practise.
                if self.is_constant(cond) && self.is_constant(then) && self.is_constant(other) {
                    self.constant_exprs.insert(expr);
                    self.constant_exprs.remove(cond);
                    self.constant_exprs.remove(then);
                    self.constant_exprs.remove(other);
                }
            }
            ExprKind::Binary(_, lhs, rhs) => {
                if self.is_constant(lhs) && self.is_constant(rhs) {
                    self.constant_exprs.insert(expr);
                    self.constant_exprs.remove(lhs);
                    self.constant_exprs.remove(rhs);
                }
            }
            ExprKind::Unary(_, inner_expr) => {
                if self.is_constant(inner_expr) {
                    self.constant_exprs.insert(expr);
                    self.constant_exprs.remove(inner_expr);
                }
            }
            ExprKind::Cast(inner_expr) => {
                if self.is_constant(inner_expr) {
                    self.constant_exprs.insert(expr);
                    self.constant_exprs.remove(inner_expr);
                }
            }
            ExprKind::Quant(_, _, _, _) => {}
            ExprKind::Subst(_, _, _) => {
                panic!(
                    "cannot determine constant subexpressions in expressions with substitutions: {}",
                    expr
                );
            }
            ExprKind::Lit(_) => {
                self.constant_exprs.insert(expr);
            }
        }

        Ok(())
    }
}
