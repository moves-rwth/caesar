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
    Expr, ExprBuilder, ExprData, ExprKind, FuncDecl, Ident, PointerHashShared, QuantVar,
    SpanVariant,
};
use crate::smt::translate_exprs::{FuelContext, TranslateExprs};
use crate::smt::{ty_to_sort, SmtCtx};
use crate::tyctx::TyCtx;
use itertools::Itertools;
use std::collections::HashSet;
use std::convert::Infallible;
use std::fmt::{Display, Formatter};
use tracing::info_span;
use z3::ast::{Ast, Bool};
use z3::{Pattern, Sort};
use z3rro::scope::{SmtScope, WEIGHT_DEFAULT};
use z3rro::{SmtEq, SmtInvariant};

/// (higher) weight that is used to deprioritize the computation axiom.
const WEIGHT_COMP: u32 = 3;

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

fn create_call_scope<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    func: &FuncDecl,
) -> SmtScope<'ctx> {
    let quant_vars = func
        .inputs
        .node
        .iter()
        .map(|p| QuantVar::Shadow(p.name))
        .collect_vec();
    let mut scope = translate.mk_scope(quant_vars.as_slice());
    scope.extend(translate.fuel_context().quantified_fuel_scope());
    scope
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

        translate.set_fuel_context(FuelContext::head());
        let symbolic_head_app = translate.t_symbolic(&app).into_dynamic(translate.ctx);

        // reuse same fuel in body
        let quantified_fuel = translate
            .fuel_context_mut()
            .take_quantified_fuel()
            .unwrap_or_default();
        translate.set_fuel_context(FuelContext::body_with_fuel(quantified_fuel));
        let symbolic_body_app = translate.t_symbolic(&app).into_dynamic(translate.ctx);

        let scope = create_call_scope(translate, func);
        let axiom = scope.forall(
            format!("{}(fuel_synonym)", func.name),
            WEIGHT_DEFAULT,
            &[&Pattern::new(
                translate.ctx.ctx,
                &[&symbolic_head_app as &dyn Ast<'ctx>],
            )],
            &symbolic_head_app.smt_eq(&symbolic_body_app),
        );

        translate.set_fuel_context(FuelContext::Call); // reset to default

        Some(axiom)
    } else {
        None
    }
}

/// Creates the default defining axiom for a function. It has the form:
/// ```txt
/// forall fuel: Fuel, <args...> @trigger(func_name(Succ(fuel), <args...>)) . func_name(fuel, <args...>) = <body>
/// ```
/// The trigger requires a non-zero fuel value to match. The axiom itself has no such requirement.
///
/// The axiom is only generated for functions that have an immediate definition (body).
pub fn defining_axiom<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    func: &FuncDecl,
) -> Option<Bool<'ctx>> {
    func.body.borrow().as_ref().map(|body| {
        let app = build_call(translate.ctx.tcx, func);

        translate.set_fuel_context(FuelContext::head());
        let app_pattern = translate.t_symbolic(&app).into_dynamic(translate.ctx);

        // reuse same fuel in body
        let quantified_fuel = translate
            .fuel_context_mut()
            .take_quantified_fuel()
            .unwrap_or_default();
        translate.set_fuel_context(FuelContext::body_with_fuel(quantified_fuel));
        let symbolic_app = translate.t_symbolic(&app).into_dynamic(translate.ctx);
        let symbolic_body = translate.t_symbolic(body).into_dynamic(translate.ctx);

        let scope = create_call_scope(translate, func);
        let axiom = scope.forall(
            format!("{}(definitional)", func.name),
            WEIGHT_DEFAULT,
            &[&Pattern::new(
                translate.ctx.ctx,
                &[&app_pattern as &dyn Ast<'ctx>],
            )],
            &symbolic_app.smt_eq(&symbolic_body),
        );

        translate.set_fuel_context(FuelContext::Call); // reset to default

        axiom
    })
}

/// Creates the computation axiom that allows instantiation with literal arguments without
/// consuming fuel. It is very similar to the [defining_axiom]. The only differences are that
///  - all arguments must be known literal values (marked with [z3rro::LitDecl]),
///  - the fuel value can be zero,
///  - the fuel value is not decreased in the body
///  - and the literal information is also propagated in the body.
///
/// It has the form:
/// ```txt
/// forall fuel: Fuel, <args...> @trigger(func_name(fuel, Lit(<args...>))) . func_name(fuel, Lit(<args...>)) = <body>
/// ```
///
/// This axiom is only generated for limited functions and if the corresponding feature is enabled.
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

    let mut app = build_call(translate.ctx.tcx, func);

    translate.set_fuel_context(FuelContext::body());
    {
        let literal_vars = func
            .inputs
            .node
            .iter()
            .map(|param| param.name)
            .collect_vec();
        let mut literal_exprs = LiteralExprCollector::new()
            .with_functions_with_def(translate.ctx.functions_with_def().as_slice())
            .with_literal_vars(literal_vars.as_slice())
            .collect(func.body.borrow_mut().as_mut().unwrap());

        // Add arguments to ensure that they are lit-wrapped in the trigger
        literal_exprs.extend(LiteralExprs(
            app.children_mut()
                .into_iter()
                .map(|c| HashExpr::new(c.clone()))
                .collect(),
        ));
        translate.set_literal_exprs(literal_exprs);
    }

    let body_ref = func.body.borrow();
    let body = body_ref.as_ref().unwrap();

    let app_z3 = translate.t_symbolic(&app).into_dynamic(translate.ctx);
    let body_z3 = translate.t_symbolic(body).into_dynamic(translate.ctx);

    let scope = create_call_scope(translate, func);
    let axiom = scope.forall(
        format!("{}(computation)", func.name),
        WEIGHT_COMP,
        &[&Pattern::new(
            translate.ctx.ctx,
            &[&app_z3 as &dyn Ast<'ctx>],
        )],
        &app_z3.smt_eq(&body_z3),
    );
    translate.clear_literal_exprs();
    translate.set_fuel_context(FuelContext::call());

    Some(axiom)
}

/// Invariant for the functions return value.
///
/// The axiom is only generated if the functions return type has an invariant.
pub fn return_value_invariant<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    func: &FuncDecl,
) -> Option<Bool<'ctx>> {
    translate.set_fuel_context(FuelContext::body());

    let app = build_call(translate.ctx.tcx, func);
    let app_z3 = translate.t_symbolic(&app);
    let axiom = app_z3.smt_invariant().map(|invariant| {
        let scope = create_call_scope(translate, func);
        scope.forall(
            format!("{}(return_invariant)", func.name),
            WEIGHT_DEFAULT,
            &[],
            &invariant,
        )
    });

    translate.set_fuel_context(FuelContext::call());

    axiom
}

/// Returns true if the [FuncDecl] can be transformed into a limited function.
/// Use [SmtCtx::is_limited_function_decl] to check if the transformation should actually be applied.
pub fn is_eligible_for_limited_function(func: &FuncDecl) -> bool {
    func.body.borrow().is_some()
}

type HashExpr = PointerHashShared<ExprData>;

#[derive(Default, Clone)]
pub struct LiteralExprs(HashSet<HashExpr>);

impl LiteralExprs {
    pub fn is_literal(&self, expr: &Expr) -> bool {
        self.0.contains(&HashExpr::new(expr.clone()))
    }

    fn insert(&mut self, expr: &Expr) -> bool {
        self.0.insert(HashExpr::new(expr.clone()))
    }

    fn remove(&mut self, expr: &Expr) -> bool {
        self.0.remove(&HashExpr::new(expr.clone()))
    }

    pub fn extend(&mut self, other: Self) {
        self.0.extend(other.0);
    }
}

impl Display for LiteralExprs {
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

/// Collects the maximal literal subexpressions of an expression.
/// An expression is to be considered literal if it is a literal, a known literal variable, or
/// all its children are literal. Maximality is in relation to the expression size. Meaning if an
/// expression is reported as literal, none of its children are reported.
///
/// # Example
/// If `a` is a known literal variable then for the expression `a + 4 * b` this analysis will
/// return only `a + 4`.
///
/// # Note
/// Only reporting maximal subexpressions is an optimisation. The resulting literal information
/// is forward to the SMT-solver (wrapping them in Lit-marker). Also, wrapping all the
/// intermediate expressions severally degrades solver performance.
#[derive(Default, Clone)]
pub struct LiteralExprCollector {
    literal_exprs: LiteralExprs,
    literal_vars: HashSet<Ident>,
    functions_with_def: HashSet<Ident>,
}

impl LiteralExprCollector {
    pub fn new() -> Self {
        Self::default()
    }

    fn is_literal(&self, expr: &Expr) -> bool {
        self.literal_exprs.is_literal(expr)
    }

    pub fn with_literal_vars(self, literal_vars: &[Ident]) -> Self {
        Self {
            literal_vars: literal_vars.iter().cloned().collect(),
            ..self
        }
    }

    pub fn with_functions_with_def(self, functions_with_def: &[Ident]) -> Self {
        Self {
            functions_with_def: functions_with_def.iter().cloned().collect(),
            ..self
        }
    }

    pub fn collect(mut self, expr: &mut Expr) -> LiteralExprs {
        let span = info_span!("collect literal expressions");
        let _enter = span.enter();

        self.visit_expr(expr).unwrap();
        tracing::trace!(
            analized_expr=%expr,
            literal_vars=?self.literal_vars,
            functions_with_def=?self.functions_with_def,
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
                    self.literal_exprs.insert(expr);
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
                if self.functions_with_def.contains(func)
                    && args.iter().all(|arg| self.is_literal(arg))
                {
                    self.literal_exprs.insert(expr);
                    // Do not remove arguments for calls. Otherwise, the computation axiom might
                    // not match because we lifted the Lit marker too far.
                    // Example: Lit(fac(5) == 125) does not let us compute fib(5)
                    //          Lit(fac(Lit(5)) == 125) lets us do this.
                }
            }
            ExprKind::Ite(cond, then, other) => {
                // TODO: maybe this should never be consider const?
                //       If-then-else is used as a stopper for literal values and therefore itself
                //       never considered literal. The paper mentions that this works well
                //       in practise.
                if self.is_literal(cond) && self.is_literal(then) && self.is_literal(other) {
                    self.literal_exprs.insert(expr);
                    self.literal_exprs.remove(cond);
                    self.literal_exprs.remove(then);
                    self.literal_exprs.remove(other);
                }
            }
            ExprKind::Binary(_, lhs, rhs) => {
                if self.is_literal(lhs) && self.is_literal(rhs) {
                    self.literal_exprs.insert(expr);
                    self.literal_exprs.remove(lhs);
                    self.literal_exprs.remove(rhs);
                }
            }
            ExprKind::Unary(_, inner_expr) => {
                if self.is_literal(inner_expr) {
                    self.literal_exprs.insert(expr);
                    self.literal_exprs.remove(inner_expr);
                }
            }
            ExprKind::Cast(inner_expr) => {
                if self.is_literal(inner_expr) {
                    self.literal_exprs.insert(expr);
                    self.literal_exprs.remove(inner_expr);
                }
            }
            ExprKind::Quant(_, _, _, _) => {}
            ExprKind::Subst(_, _, _) => {
                panic!(
                    "cannot determine literal subexpressions in expressions with substitutions: {}",
                    expr
                );
            }
            ExprKind::Lit(_) => {
                self.literal_exprs.insert(expr);
            }
        }

        Ok(())
    }
}
