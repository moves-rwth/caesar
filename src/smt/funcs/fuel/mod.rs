mod fuel_mono;
mod fuel_param;
pub mod literals;

pub use fuel_mono::FuelMonoFunctionEncoder;
pub use fuel_param::FuelParamFunctionEncoder;

use itertools::Itertools;
use z3::ast::Bool;
use z3rro::quantifiers::Weight;

use crate::{
    ast::FuncDecl,
    smt::{
        funcs::{
            axiomatic::AxiomInstantiation,
            fuel::literals::LiteralExprCollector,
            util::{
                mk_call_expr, translate_equational_axiom, translate_return_invariant, InputsEncoder,
            },
            WEIGHT_COMPUTATION,
        },
        translate_exprs::TranslateExprs,
    },
};

#[derive(Debug)]
pub struct FuelEncodingOptions {
    /// The maximum fuel value to use in the encoding.
    pub max_fuel: usize,
    /// Whether to add computation axioms.
    pub computation: bool,
    /// Whether to add synonym axioms.
    /// If `false`, the synonym axiom is not added, which may lead to spurious
    /// counter-examples.
    pub synonym_axiom: bool,
}

trait FuelType: Clone + Sized {
    fn succ(&self) -> Self;
}

/// Defines a trait for encoders that handle fuel in function applications.
trait FuelEncoder<'ctx>: InputsEncoder<'ctx> + Sized {
    type Fuel: FuelType;

    /// Set the fuel value for the translation, based on the assumption that
    /// `self` is the current function encoder of `translate`. Returns the
    /// previous fuel value.
    ///
    /// Must also clear the cache of `translate` to ensure that the new fuel
    /// value is used in the translation.
    ///
    /// Panics if `translate.ctx.function_encoder()` is not `self`
    /// (via [`Self::assert_translate_this_encoder`]).
    fn set_translate_fuel<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        fuel: Self::Fuel,
    ) -> Self::Fuel;

    /// Asserts that `encoder` is the current function encoder of `translate`.
    /// Panics if this is not the case.
    fn assert_translate_this_encoder(encoder: &Self, translate: &TranslateExprs<'_, 'ctx>) {
        assert!(std::ptr::addr_eq(translate.ctx.function_encoder(), encoder));
    }
}

/// Build the definitional axiom for a function for `succ(fuel)`.
///
/// Intuitively, the generated axiom looks like this:
/// ```text
/// forall fuel, <args...> @trigger(func_name(succ(fuel), <args...>)) . func_name(succ(fuel), <args...>) = <body>
/// ```
/// where `<body>` is the body of the function with `fuel` as the fuel value.
///
/// The implementation uses the [`FuelEncoder`] and [`ApplicativeEncoder`]
/// traits to generate calls to the function, either encoding the fuel via a
/// variable [`fuel_mono`] or a parameter [`fuel_param`].
fn fuel_definitional_axiom<'ctx, 'smt, E: FuelEncoder<'ctx>>(
    encoder: &E,
    fuel: &E::Fuel,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    func: &FuncDecl,
) -> Bool<'ctx> {
    assert!(std::ptr::addr_eq(translate.ctx.function_encoder(), encoder));

    // The encoded application with the incremented fuel
    let app = mk_call_expr(translate.ctx.tcx, func);
    let original_fuel = encoder.set_translate_fuel(translate, fuel.succ());
    let symbolic_app = translate.t_symbolic(&app).into_dynamic(translate.ctx);

    // The translated body with fuel
    encoder.set_translate_fuel(translate, fuel.clone());
    let body_ref = func.body.borrow();
    let body = body_ref.as_ref().unwrap();
    let symbolic_body = translate.t_symbolic(body).into_dynamic(translate.ctx);

    let scope = encoder.inputs_scope(translate, func);
    let axiom = translate_equational_axiom(
        AxiomInstantiation::Decreasing,
        &scope,
        &symbolic_app,
        &symbolic_body,
        &format!("{}(definitional)", func.name),
        Weight::DEFAULT,
    );

    encoder.set_translate_fuel(translate, original_fuel);

    axiom
}

/// Build the return invariant axiom for a function with `fuel`.
///
/// Intuitively, the generated axiom looks like this:
/// ```text
/// forall fuel, <args...> @trigger(func_name(fuel, <args...>)) . smt_invariant(func_name(fuel, <args...>))
/// ```
/// where `smt_invariant` is based on the [`SmtInvariant`] trait of the return
/// value's type of the function.
fn fuel_return_invariant<'ctx, 'smt, E: FuelEncoder<'ctx>>(
    encoder: &E,
    fuel: &E::Fuel,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    func: &FuncDecl,
) -> Option<Bool<'ctx>> {
    assert!(std::ptr::addr_eq(translate.ctx.function_encoder(), encoder));

    let original_fuel = encoder.set_translate_fuel(translate, fuel.clone());
    let scope = encoder.inputs_scope(translate, func);
    let axiom = translate_return_invariant(
        AxiomInstantiation::Decreasing,
        &scope,
        translate,
        func,
        &format!("{}(return_invariant)", func.name),
    );
    encoder.set_translate_fuel(translate, original_fuel);

    axiom
}

/// Build the fuel synonym axiom for a function with `succ(fuel)`, saying that
/// the following holds:
/// ```text
/// f(succ(fuel), args...) = f(fuel, args...)
/// ```
fn fuel_synonym_axiom<'ctx, 'smt, E: FuelEncoder<'ctx>>(
    encoder: &E,
    fuel: &E::Fuel,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    func: &FuncDecl,
) -> Bool<'ctx> {
    assert!(std::ptr::addr_eq(translate.ctx.function_encoder(), encoder));

    let app = mk_call_expr(translate.ctx.tcx, func);

    // The encoded application in head context
    let original_fuel = encoder.set_translate_fuel(translate, fuel.succ());
    let symbolic_app = translate.t_symbolic(&app).into_dynamic(translate.ctx);

    // The encoded application in body context
    encoder.set_translate_fuel(translate, fuel.clone());
    let symbolic_body = translate.t_symbolic(&app).into_dynamic(translate.ctx);

    let scope = encoder.inputs_scope(translate, func);
    let axiom = translate_equational_axiom(
        AxiomInstantiation::Decreasing,
        &scope,
        &symbolic_app,
        &symbolic_body,
        &format!("{}(fuel_synonym)", func.name),
        Weight::DEFAULT,
    );
    encoder.set_translate_fuel(translate, original_fuel);

    axiom
}

/// Build the computation axiom for a function with `fuel`, allowing unbounded
/// computation for "literal" expressions. This is similar to the definitional
/// axiom, but the func's input parameters are wrapped in a literal marker
/// (using ``)
///
/// Intuitively, the generated axiom looks like this:
/// ```text
/// forall fuel, <args...> @trigger(func_name(fuel, Lit(<args...>))) . func_name(fuel, Lit(<args...>)) = <body>
/// ```
/// where `<body>` is the body of the function with `fuel` as the fuel value.
fn fuel_computation_axiom<'ctx, 'smt, E: FuelEncoder<'ctx>>(
    encoder: &E,
    fuel: &E::Fuel,
    translate: &mut TranslateExprs<'smt, 'ctx>,
    func: &FuncDecl,
) -> Bool<'ctx> {
    assert!(std::ptr::addr_eq(translate.ctx.function_encoder(), encoder));

    let app = mk_call_expr(translate.ctx.tcx, func);

    let original_fuel = encoder.set_translate_fuel(translate, fuel.clone());

    let param_vars = func
        .inputs
        .node
        .iter()
        .map(|param| param.name)
        .collect_vec();

    let mut literal_exprs = LiteralExprCollector::new(translate.ctx)
        .add_literal_vars(param_vars)
        .collect_literals(func.body.borrow_mut().as_mut().unwrap());

    // The result of the computation axiom should itself never be considered literal in practice.
    // Otherwise, some computation examples hang.
    // The paper uses if-then-else is used as a stopper for propagating literal information.
    // This has essentially the same effect in practice, but never making the result literal
    // is the more distilled version.
    literal_exprs.remove(func.body.borrow_mut().as_mut().unwrap());

    // Add arguments to ensure that they are lit-wrapped in the trigger
    literal_exprs.extend(app.children().into_iter().cloned());
    translate.set_literal_exprs(literal_exprs);

    let body_ref = func.body.borrow();
    let body = body_ref.as_ref().unwrap();

    let app_z3 = translate.t_symbolic(&app).into_dynamic(translate.ctx);
    let body_z3 = translate.t_symbolic(body).into_dynamic(translate.ctx);

    let scope = encoder.inputs_scope(translate, func);
    let axiom = translate_equational_axiom(
        AxiomInstantiation::Decreasing,
        &scope,
        &app_z3,
        &body_z3,
        &format!("{}(computation)", func.name),
        WEIGHT_COMPUTATION,
    );

    translate.set_literal_exprs(Default::default());
    encoder.set_translate_fuel(translate, original_fuel);

    axiom
}
