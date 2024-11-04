//! This module contains all functions related to fuel encoding from the paper
//! "Computing with an SMT Solver". The goal is to limit the number of quantifier instantiation
//! of a functions defining axiom. This is done by including an extra [z3rro::Fuel] parameter and
//! only providing axioms for non-zero fuel parameters. The fuel parameter is decremented in every
//! instantiation.
//!
//! # Note
//! For this to work the SMT solver is not allowed to synthesis fuel values itself.
//! Therefore, MBQI must be disabled.

use crate::ast::{Expr, FuncDecl};
use crate::smt::translate_exprs::{FuelContext, TranslateExprs};
use crate::smt::{ty_to_sort, SmtCtx};
use z3::ast::{Ast, Bool};
use z3::{Pattern, Sort};
use z3rro::SmtEq;

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

/// Creates an axiom that can only be instantiated with a non-zero fuel parameter and decrements
/// the available fuel in the body.
/// It has the form:
/// ```txt
/// forall fuel: Fuel, <args...> . func_name(Succ(fuel), <args...>) = <body...> func_name(fuel, <args...>) <body...>
/// ```
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

/// Creates the fuel synonym axiom that states that the result of the function is independent
/// of the fuel parameter. It has the form:
/// ```txt
/// forall fuel: Fuel, <args...> . func_name(Succ(fuel), <args...>) = func_name(fuel, <args...>)
/// ```
pub fn fuel_synonym_axiom<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    app: &Expr,
) -> Bool<'ctx> {
    translate_defining_axiom(translate, app, app)
}

/// Creates the default defining axiom for a function. It has the form:
/// ```txt
/// forall fuel: Fuel, <args...> . func_name(Succ(fuel), <args...>) = <body>
/// ```
/// where only `fuel` is used as the fuel parameter in `<body>`.
pub fn defining_axiom<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    app: &Expr,
    body: &Expr,
) -> Bool<'ctx> {
    translate_defining_axiom(translate, app, body)
}
