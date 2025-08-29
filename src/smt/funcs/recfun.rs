use std::{cell::RefCell, collections::HashMap};

use itertools::Itertools;
use z3::{
    ast::{Ast, Bool},
    RecFuncDecl,
};

use crate::{
    ast::{DeclRef, ExprBuilder, FuncDecl, Ident, SpanVariant},
    smt::{
        funcs::{
            axiomatic::{AxiomInstantiation, AxiomaticFunctionEncoder, PartialEncoding},
            util::{translate_func_domain, translate_return_invariant, InputsEncoder},
            FunctionEncoder, FunctionSignature,
        },
        symbolic::Symbolic,
        translate_exprs::TranslateExprs,
        ty_to_sort, SmtCtx,
    },
};

/// An encoder that uses SMT-LIB's (define-fun-rec) to encode recursive
/// functions (or rather Z3's bindings for it).
pub struct RecFunFunctionEncoder<'ctx> {
    pub(crate) decls: RefCell<HashMap<Ident, RecFuncDecl<'ctx>>>,
    pub(crate) default_encoding: AxiomaticFunctionEncoder,
}

impl<'ctx> RecFunFunctionEncoder<'ctx> {
    pub fn new() -> Self {
        RecFunFunctionEncoder {
            decls: RefCell::new(HashMap::new()),
            default_encoding: AxiomaticFunctionEncoder::new(
                AxiomInstantiation::Decreasing,
                PartialEncoding::Partial,
            ),
        }
    }

    /// Adds the function's definition to the [`RecFuncDecl`] (that must already
    /// be created by [`translate_signature`]).
    ///
    /// Currently, this may panic if the function's input parameter types have
    /// SMT invariants ([`SmtInvariant`]). Those are not supported.
    fn add_func_def_to_decl<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) {
        let decls_ref = self.decls.borrow();
        let decl = decls_ref.get(&func.name).expect("function is not declared");

        let span = func.span.variant(SpanVariant::Encoding);
        let builder = ExprBuilder::new(span);

        let args: Vec<_> = func
            .inputs
            .node
            .iter()
            .map(|param| builder.var(param.name, translate.ctx.tcx))
            .map(|var| {
                let symbolic = translate.t_symbolic(&var);
                // note that we do not translate smt invariants here. this is
                // impossible with Z3's [RecFunDecl] (if we don't go so far as
                // to create new uninterpreted sorts for such types). still, I
                // believe it is sound. in essence, the constrainted definition
                // would be something like:
                //
                //  (forall ((x T)) (=> (smt_invariant x) (f x)))
                //
                // we translate that definition without the smt invariant here,
                // but importantly every call to this function must be
                // well-typed (and will therefore satisfy the constraints on the
                // parameters).
                symbolic.into_dynamic(translate.ctx)
            })
            .collect();
        let args = args.iter().map(|d| d as &dyn Ast<'ctx>).collect_vec();
        decl.add_def(
            &args,
            &translate
                .t_symbolic(func.body.borrow().as_ref().unwrap())
                .into_dynamic(translate.ctx) as &dyn Ast<'ctx>,
        );
    }
}

impl<'ctx> InputsEncoder<'ctx> for RecFunFunctionEncoder<'ctx> {}

impl<'ctx> FunctionEncoder<'ctx> for RecFunFunctionEncoder<'ctx> {
    fn into_boxed(self) -> Box<dyn FunctionEncoder<'ctx>> {
        Box::new(self)
    }

    fn translate_signature(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
    ) -> Vec<FunctionSignature<'ctx>> {
        if func.body.borrow().is_none() {
            return self.default_encoding.translate_signature(ctx, func);
        }

        let domain = translate_func_domain(ctx, func, false);
        let domain: Vec<_> = domain.iter().collect();
        let decl = RecFuncDecl::new(
            ctx.ctx,
            func.name.name.to_owned(),
            &domain,
            &ty_to_sort(ctx, &func.output),
        );
        let previous = self.decls.borrow_mut().insert(func.name, decl);
        assert!(previous.is_none());
        vec![]
    }

    fn translate_axioms<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Vec<Bool<'ctx>> {
        if func.body.borrow().is_none() {
            return self.default_encoding.translate_axioms(translate, func);
        }

        // add the definition to the declaration
        self.add_func_def_to_decl(translate, func);

        // the only actual axiom is a possible return invariant
        let scope = self.inputs_scope(translate, func);
        translate_return_invariant(
            AxiomInstantiation::Decreasing,
            &scope,
            translate,
            func,
            &format!("{}(return_invariant)", func.name),
        )
        .into_iter()
        .collect()
    }

    fn translate_call(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
        args: Vec<Symbolic<'ctx>>,
    ) -> Symbolic<'ctx> {
        if func.body.borrow().is_none() {
            return self.default_encoding.translate_call(ctx, func, args);
        }

        let args = args.into_iter().map(|s| s.into_dynamic(ctx)).collect_vec();
        let args = args.iter().map(|d| d as &dyn Ast<'ctx>).collect_vec();
        let res_dynamic = self
            .decls
            .borrow()
            .get(&func.name)
            .map(|decl| decl.apply(&args))
            .expect("function is not declared");
        Symbolic::from_dynamic(ctx, &func.output, &res_dynamic)
    }

    fn func_uses_lit_wrap(&self, _func: &DeclRef<FuncDecl>) -> bool {
        false
    }
}
