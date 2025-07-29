use std::cell::RefCell;

use z3::ast::Bool;
use z3rro::{
    scope::{SmtFresh, SmtScope},
    Fuel,
};

use crate::{
    ast::{DeclRef, FuncDecl},
    smt::{
        funcs::{
            axiomatic::{AxiomInstantiation, AxiomaticFunctionEncoder},
            fuel::{
                fuel_computation_axiom, fuel_definitional_axiom, fuel_return_invariant,
                fuel_synonym_axiom, FuelEncoder, FuelType,
            },
            is_eligible_for_limited_function,
            util::{translate_func_domain, translate_plain_call, InputsEncoder},
            FunctionEncoder, FunctionSignature,
        },
        symbolic::Symbolic,
        translate_exprs::TranslateExprs,
        ty_to_sort, SmtCtx,
    },
};

/// # Fuel Parameter Function Encoder
///
/// ## Definitional Axiom
/// It has the form:
/// ```txt
/// forall fuel: Fuel, <args...> @trigger(func_name(Succ(fuel), <args...>)) . func_name(Succ(fuel), <args...>) = <body>
/// ```
/// The trigger requires a non-zero fuel value to match. For recursive calls inside `<body>`
/// `fuel` is used, i.e. the fuel value is decremented.
///
/// # Fuel Synonym Axiom
/// It states that the result of the function is independent of the fuel parameter. It has the form:
/// ```txt
/// forall fuel: Fuel, <args...> @trigger(func_name(Succ(fuel), <args...>)) . func_name(Succ(fuel), <args...>) = func_name(fuel, <args...>)
/// ```
/// It can only be instantiated with non-zero fuel values and must decrease the fuel value in the body.
///
/// ## Computation Axiom
/// It allows instantiation with literal arguments without consuming fuel. It is very similar to
/// the definitional axiom. The only differences are that
///  - all arguments must be known literal values (marked with [z3rro::LitDecl]),
///  - the fuel value can be zero,
///  - the fuel value is not decreased in the body
///  - and the literal information is also propagated in the body.
///
/// It has the form:
/// ```txt
/// forall fuel: Fuel, <args...> @trigger(func_name(fuel, Lit(<args...>))) . func_name(fuel, Lit(<args...>)) = <body>
/// ```
pub struct FuelParamFunctionEncoder<'ctx> {
    default_encoding: AxiomaticFunctionEncoder,
    computation: bool,
    /// The current fuel value used in the translation.
    /// It is wrapped in a `RefCell` to allow for mutable access during the translation
    /// process. The value is `None` if the fuel is not initialized yet.
    current_fuel: RefCell<Option<Fuel<'ctx>>>,
    max_fuel: usize,
}

impl<'ctx> FuelParamFunctionEncoder<'ctx> {
    pub fn new(max_fuel: usize, computation: bool) -> Self {
        FuelParamFunctionEncoder {
            computation,
            default_encoding: AxiomaticFunctionEncoder::new(AxiomInstantiation::Decreasing),
            current_fuel: RefCell::new(None),
            max_fuel,
        }
    }

    fn get_fuel(&self, ctx: &SmtCtx<'ctx>) -> Fuel<'ctx> {
        self.current_fuel
            .borrow_mut()
            .get_or_insert_with(|| Fuel::from_constant(ctx.fuel_factory(), self.max_fuel))
            .clone()
    }
}

impl<'ctx> InputsEncoder<'ctx> for FuelParamFunctionEncoder<'ctx> {
    fn inputs_scope<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> SmtScope<'ctx> {
        let mut scope = self.default_encoding.inputs_scope(translate, func);

        // if we have a non-literal fuel, extract the bound variable and add it
        // to the scope.
        if let Some(fuel) = self.get_fuel(translate.ctx).extract_var() {
            scope.add_bound(&fuel.as_dynamic());
        }

        scope
    }
}

impl<'ctx> FuelType for Fuel<'ctx> {
    fn succ(&self) -> Self {
        Fuel::succ(self.clone())
    }
}

impl<'ctx> FuelEncoder<'ctx> for FuelParamFunctionEncoder<'ctx> {
    type Fuel = Fuel<'ctx>;

    fn set_translate_fuel<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        fuel: Self::Fuel,
    ) -> Self::Fuel {
        Self::assert_translate_this_encoder(self, translate);
        translate.clear_cache();

        let old_fuel = self.get_fuel(translate.ctx);
        *self.current_fuel.borrow_mut() = Some(fuel);
        old_fuel
    }
}

impl<'ctx> FunctionEncoder<'ctx> for FuelParamFunctionEncoder<'ctx> {
    fn into_boxed(self) -> Box<dyn FunctionEncoder<'ctx>> {
        Box::new(self)
    }

    fn translate_signature(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
    ) -> Vec<FunctionSignature<'ctx>> {
        if !is_eligible_for_limited_function(func) {
            return self.default_encoding.translate_signature(ctx, func);
        }

        let range = ty_to_sort(ctx, &func.output);
        let domain = translate_func_domain(ctx, func, true);
        vec![(func.name, domain, range)]
    }

    fn translate_axioms<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Vec<Bool<'ctx>> {
        if !is_eligible_for_limited_function(func) {
            return self.default_encoding.translate_axioms(translate, func);
        }

        let mut scope = SmtScope::new();
        let fuel = Fuel::fresh(translate.ctx.fuel_factory(), &mut scope, "$f");

        let mut axioms = vec![
            fuel_definitional_axiom(self, &fuel, translate, func),
            fuel_synonym_axiom(self, &fuel, translate, func),
        ];
        axioms.extend(fuel_return_invariant(self, &fuel, translate, func));
        if self.computation {
            axioms.push(fuel_computation_axiom(self, &fuel, translate, func));
        }
        axioms
    }

    fn translate_call(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
        mut args: Vec<Symbolic<'ctx>>,
    ) -> Symbolic<'ctx> {
        if !is_eligible_for_limited_function(func) {
            return self.default_encoding.translate_call(ctx, func, args);
        }
        args.insert(0, Symbolic::Fuel(self.get_fuel(ctx)));
        translate_plain_call(ctx, func.name, &func.output, args)
    }

    fn func_uses_lit_wrap(&self, func: &DeclRef<FuncDecl>) -> bool {
        self.computation && is_eligible_for_limited_function(&func.borrow())
    }
}
