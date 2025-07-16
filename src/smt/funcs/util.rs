use itertools::Itertools;
use z3::{
    ast::{Ast, Bool, Dynamic},
    Pattern, Sort,
};
use z3rro::{
    scope::{SmtScope, Weight},
    SmtEq, SmtInvariant,
};

use crate::{
    ast::{Expr, ExprBuilder, FuncDecl, Ident, QuantVar, SpanVariant, TyKind},
    smt::{
        funcs::axiomatic::AxiomInstantiation, symbolic::Symbolic, translate_exprs::TranslateExprs,
        ty_to_sort, SmtCtx,
    },
    tyctx::TyCtx,
};

/// An encoder that can return a scope containing the input variables of a function.
pub trait InputsEncoder<'ctx> {
    /// Create a scope containing the input variables of the function.
    fn inputs_scope<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> SmtScope<'ctx> {
        let quant_vars = func
            .inputs
            .node
            .iter()
            .map(|p| QuantVar::Shadow(p.name))
            .collect_vec();
        translate.mk_scope(quant_vars.as_slice())
    }
}

/// Generate the pattern list for the axiom direction. If the direction is
/// decreasing, it returns a single pattern with the head of the axiom
/// as the only element. If the direction is bidirectional, it returns an
/// empty pattern list.
fn generate_patterns<'ctx>(
    instantiation: AxiomInstantiation,
    head: &Dynamic<'ctx>,
) -> Vec<Pattern<'ctx>> {
    match instantiation {
        AxiomInstantiation::Decreasing => vec![Pattern::new(head.get_ctx(), &[head])],
        AxiomInstantiation::Bidirectional => vec![],
    }
}

/// Creates an axiom that universally quantifies over the function's inputs,
/// equating the function application (`head`) with its body (`body`).
pub fn translate_equational_axiom<'ctx>(
    instantiation: AxiomInstantiation,
    scope: &SmtScope<'ctx>,
    head: &Dynamic<'ctx>,
    body: &Dynamic<'ctx>,
    name: &str,
    weight: Weight,
) -> Bool<'ctx> {
    let patterns = generate_patterns(instantiation, head);
    let patterns = patterns.iter().collect_vec();
    scope.forall(name, weight, &patterns, &head.smt_eq(body))
}

/// Builds an axiom for the return type invariant of a func based on the
/// [`SmtInvariant`] implementation of the return type. Uses the func's
/// application as the quantifier's pattern. Returns `None` if the return type
/// has no invariant.
pub fn translate_return_invariant<'ctx, 'smt>(
    instantiation: AxiomInstantiation,
    scope: &SmtScope<'ctx>,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    func: &FuncDecl,
    name: &str,
) -> Option<Bool<'ctx>> {
    let app = mk_call_expr(translate.ctx.tcx, func);
    let app_translated = translate.t_symbolic(&app);

    app_translated.smt_invariant().map(|invariant| {
        let app_z3 = app_translated.clone().into_dynamic(translate.ctx);
        let patterns = generate_patterns(instantiation, &app_z3);
        let patterns = patterns.iter().collect_vec();
        scope.forall(name, Weight::DEFAULT, &patterns, &invariant)
    })
}

/// Applying a function, converting from our types to Z3 types.
pub fn translate_plain_call<'ctx>(
    ctx: &SmtCtx<'ctx>,
    name: Ident,
    return_ty: &TyKind,
    args: Vec<Symbolic<'ctx>>,
) -> Symbolic<'ctx> {
    let args = args.into_iter().map(|s| s.into_dynamic(ctx)).collect_vec();
    let args = args.iter().map(|d| d as &dyn Ast<'ctx>).collect_vec();
    let res_dynamic = ctx.uninterpreteds().apply_function(name, &args);
    Symbolic::from_dynamic(ctx, return_ty, &res_dynamic)
}

/// Builds the domain (parameter list) for `func`. If requested, the fuel parameter is
/// implicitly added as the first parameter.
pub fn translate_func_domain<'a>(
    ctx: &SmtCtx<'a>,
    func: &FuncDecl,
    add_fuel: bool,
) -> Vec<Sort<'a>> {
    let mut domain = if add_fuel {
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

/// Creates an expression for a call to the func.
pub fn mk_call_expr(tcx: &TyCtx, func: &FuncDecl) -> Expr {
    let span = func.span.variant(SpanVariant::Encoding);
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
