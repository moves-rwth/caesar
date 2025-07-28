use z3::ast::Bool;
use z3rro::quantifiers::Weight;

use crate::{
    ast::{DeclRef, Expr, FuncDecl},
    smt::{
        funcs::{
            util::{
                mk_call_expr, translate_equational_axiom, translate_func_domain,
                translate_plain_call, translate_return_invariant, InputsEncoder,
            },
            FunctionEncoder, FunctionSignature,
        },
        symbolic::Symbolic,
        translate_exprs::TranslateExprs,
        ty_to_sort, SmtCtx,
    },
};

/// Whether the quantifier for axioms may be instantiated based on any occurring
/// function application, or only on the defining function's application.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AxiomInstantiation {
    /// Axioms may also be instantiated based on occurrences of other functions
    /// that occur in the definition of the defining function. We won't specify
    /// any patterns for these axioms, and the SMT solver will choose their own.
    Bidirectional,
    /// Axioms may only be instantiated based on an occurrence of defining
    /// function's application.
    ///
    /// We ensure this using Z3's patterns on quantifiers.
    Decreasing,
}

/// This encoder uses uninterpreted functions and a bunch of axioms to encode
/// func declarations. This is the default encoding for functions.
///
/// One may choose whether to restrict the axiom instantiation based on
/// direction ([`AxiomInstantiation`]). The [`Default`] implementation places no
/// restrictions (i.e. uses [`AxiomInstantiation::Bidirectional`]).
#[derive(Debug)]
pub struct AxiomaticFunctionEncoder {
    instantiation: AxiomInstantiation,
}

impl AxiomaticFunctionEncoder {
    /// Create a new axiomatic function encoder with the given direction.
    pub fn new(instantiation: AxiomInstantiation) -> Self {
        AxiomaticFunctionEncoder { instantiation }
    }
}

impl Default for AxiomaticFunctionEncoder {
    fn default() -> Self {
        AxiomaticFunctionEncoder {
            instantiation: AxiomInstantiation::Bidirectional,
        }
    }
}

impl<'ctx> InputsEncoder<'ctx> for AxiomaticFunctionEncoder {}

impl<'ctx> FunctionEncoder<'ctx> for AxiomaticFunctionEncoder {
    fn into_boxed(self) -> Box<dyn FunctionEncoder<'ctx>> {
        Box::new(self)
    }

    fn translate_signature(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
    ) -> Vec<FunctionSignature<'ctx>> {
        let range = ty_to_sort(ctx, &func.output);
        let domain = translate_func_domain(ctx, func, false);
        vec![(func.name, domain, range)]
    }

    fn translate_axioms<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Vec<Bool<'ctx>> {
        let mut axioms = vec![];
        if let Some(body) = func.body.borrow().as_ref() {
            axioms.push(self.definitional_axiom(translate, func, body));
        }

        let scope = self.inputs_scope(translate, func);
        axioms.extend(translate_return_invariant(
            self.instantiation,
            &scope,
            translate,
            func,
            &format!("{}(return_invariant)", func.name),
        ));
        axioms
    }

    fn translate_call(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
        args: Vec<Symbolic<'ctx>>,
    ) -> Symbolic<'ctx> {
        translate_plain_call(ctx, func.name, &func.output, args.into_iter().collect())
    }

    fn needs_lit_wrapping(&self, _func: &DeclRef<FuncDecl>) -> bool {
        false
    }
}

impl AxiomaticFunctionEncoder {
    fn definitional_axiom<'smt, 'ctx>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
        body: &Expr,
    ) -> Bool<'ctx> {
        let app = mk_call_expr(translate.ctx.tcx, func);

        let app_translated = translate.t_symbolic(&app).into_dynamic(translate.ctx);
        let body_translated = translate.t_symbolic(body).into_dynamic(translate.ctx);

        let scope = self.inputs_scope(translate, func);
        translate_equational_axiom(
            self.instantiation,
            &scope,
            &app_translated,
            &body_translated,
            &format!("{}(definitional)", func.name),
            Weight::DEFAULT,
        )
    }
}
