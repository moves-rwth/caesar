use std::cell::Cell;

use z3::ast::Bool;

use crate::{
    ast::{DeclRef, FuncDecl, Ident, SpanVariant, Symbol},
    smt::{
        funcs::{
            axiomatic::{AxiomInstantiation, AxiomaticFunctionEncoder},
            fuel::{
                fuel_computation_axiom, fuel_definitional_axiom, fuel_return_invariant,
                fuel_synonym_axiom, FuelEncoder, FuelEncodingOptions, FuelType,
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

/// # Fuel Monomorphic Function Encoder
/// Encode funcs with fuel, but *monomorphize* them, i.e. generate one variant
/// of the function for each fuel value up to `max_fuel`.
///
/// ## Definitional Axiom
/// It has the form:
/// ```txt
/// func_name$n+1(<args...>) = <body>
/// ```
/// where `n` ranges from 0 to `max_fuel-1`. For recursive calls inside `<body>`
/// the function variant `func_name$n` is used, i.e. the fuel value is decremented.
///
/// # Fuel Synonym Axiom
/// It states that the result of the function is independent of the fuel parameter. It has the form:
/// ```txt
/// func_name$n+1(<args...>) = func_name$n(<args...>)
/// ```
/// where `n` ranges from 0 to `max_fuel-1`.
///
/// ## Computation Axiom
/// It allows instantiation with literal arguments without consuming fuel. It is very similar to
/// the definitional axiom. The only differences are that
///  - all arguments must be known literal values (marked with [z3rro::LitDecl]),
///  - the fuel value is not decreased in the body
///  - and the literal information is also propagated in the body.
///
/// It has the form:
/// ```txt
/// func_name$n(Lit(<args...>)) = <body>
/// ```
/// where `n` ranges from 1 to `max_fuel` and `<body>` is translated using
/// `func_name$n` again (i.e. the fuel value is *not* decremented).`
pub struct FuelMonoFunctionEncoder {
    options: FuelEncodingOptions,
    default_encoding: AxiomaticFunctionEncoder,
    /// The current fuel value used in the translation.
    current_fuel: Cell<usize>,
}

impl FuelMonoFunctionEncoder {
    pub fn new(options: FuelEncodingOptions) -> Self {
        let current_fuel = Cell::new(options.max_fuel);
        Self {
            options,
            default_encoding: AxiomaticFunctionEncoder::new(AxiomInstantiation::Decreasing),
            current_fuel,
        }
    }
}

impl<'ctx> InputsEncoder<'ctx> for FuelMonoFunctionEncoder {}

impl FuelType for usize {
    fn succ(&self) -> Self {
        self + 1
    }
}

impl<'ctx> FuelEncoder<'ctx> for FuelMonoFunctionEncoder {
    type Fuel = usize;

    fn set_translate_fuel<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        fuel: Self::Fuel,
    ) -> Self::Fuel {
        Self::assert_translate_this_encoder(self, translate);
        translate.clear_cache();
        assert!(fuel <= self.options.max_fuel);
        self.current_fuel.replace(fuel)
    }
}

impl<'ctx> FunctionEncoder<'ctx> for FuelMonoFunctionEncoder {
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
        let domain = translate_func_domain(ctx, func, false);
        (0..=self.options.max_fuel)
            .map(|fuel| {
                (
                    Self::ident_with_fuel(func, fuel),
                    domain.clone(),
                    range.clone(),
                )
            })
            .collect()
    }

    fn translate_axioms<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Vec<Bool<'ctx>> {
        if !is_eligible_for_limited_function(func) {
            return self.default_encoding.translate_axioms(translate, func);
        }

        let mut axioms = vec![];

        // definitional axioms (these are all generated defining for `succ(fuel)`)
        axioms.extend(
            (0..self.options.max_fuel)
                .map(|fuel| fuel_definitional_axiom(self, &fuel, translate, func)),
        );

        // return invariants (generated for `fuel`)
        axioms.extend(
            (0..=self.options.max_fuel)
                .filter_map(|fuel| fuel_return_invariant(self, &fuel, translate, func)),
        );

        // synonym axioms, equating values of `succ(fuel)` and `fuel`. generated
        // up to max_fuel - 1, so that the last synonym axiom is for `fuel = max_fuel`
        if self.options.synonym_axiom {
            axioms.extend(
                (0..self.options.max_fuel)
                    .map(|fuel| fuel_synonym_axiom(self, &fuel, translate, func)),
            );
        }

        // computation axioms, allowing unbounded computation for `fuel`.
        if self.options.computation {
            axioms.extend(
                (1..=self.options.max_fuel)
                    .map(|fuel| fuel_computation_axiom(self, &fuel, translate, func)),
            )
        }

        axioms
    }

    fn translate_call(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
        args: Vec<Symbolic<'ctx>>,
    ) -> Symbolic<'ctx> {
        if !is_eligible_for_limited_function(func) {
            return self.default_encoding.translate_call(ctx, func, args);
        }
        translate_plain_call(
            ctx,
            Self::ident_with_fuel(func, self.current_fuel.get()),
            &func.output,
            args.into_iter().collect(),
        )
    }

    fn func_uses_lit_wrap(&self, func: &DeclRef<FuncDecl>) -> bool {
        self.options.computation && is_eligible_for_limited_function(&func.borrow())
    }
}

impl FuelMonoFunctionEncoder {
    fn ident_with_fuel(func: &FuncDecl, fuel: usize) -> Ident {
        Ident {
            name: Symbol::intern(&format!("{}${}", func.name.name, fuel)),
            span: func.name.span.variant(SpanVariant::Encoding),
        }
    }
}
