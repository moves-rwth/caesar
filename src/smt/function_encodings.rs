//! This module contains all functions related to limited functions.
//! The goal is to limit the number of quantifier instantiation
//! of a functions defining axiom.
//!
//! # Note
//! For this to work the SMT solver is not allowed to synthesis fuel values itself.
//! Therefore, MBQI must be disabled.

use crate::ast::visit::{walk_expr, VisitorMut};
use crate::ast::{
    Expr, ExprBuilder, ExprData, ExprKind, FuncDecl, Ident, PointerHashShared, QuantVar,
    SpanVariant, Symbol, TyKind,
};
use crate::smt::symbolic::{ScopeSymbolic, Symbolic};
use crate::smt::translate_exprs::TranslateExprs;
use crate::smt::{ty_to_sort, SmtCtx};
use crate::tyctx::TyCtx;
use itertools::Itertools;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::convert::Infallible;
use std::fmt::{Display, Formatter};
use std::mem;
use std::num::NonZero;
use tracing::info_span;
use z3::ast::{Ast, Bool, Dynamic};
use z3::{Pattern, RecFuncDecl, Sort};
use z3rro::scope::{SmtScope, WEIGHT_DEFAULT};
use z3rro::{Fuel, SmtEq, SmtInvariant};

/// (higher) weight that is used to deprioritize the computation axiom.
const WEIGHT_COMP: u32 = 3;

/// Base trait that contains functionality common to the different encodings
trait EncodingBase<'ctx> {
    fn call_scope<'smt>(
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

    fn build_axiom<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
        head: &Dynamic<'ctx>,
        body: &Dynamic<'ctx>,
        name: &str,
        weight: u32,
    ) -> Bool<'ctx> {
        let scope = self.call_scope(translate, func);
        scope.forall(
            name,
            weight,
            &[&Pattern::new(head.get_ctx(), &[head as &dyn Ast<'ctx>])],
            &head.smt_eq(body),
        )
    }

    fn build_return_invariant<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
        name: &str,
    ) -> Option<Bool<'ctx>> {
        let app = build_call(translate.ctx.tcx, func);
        let app_translated = translate.t_symbolic(&app);

        app_translated.smt_invariant().map(|invariant| {
            let scope = self.call_scope(translate, func);
            let app_z3 = app_translated.clone().into_dynamic(translate.ctx);
            scope.forall(
                name,
                WEIGHT_DEFAULT,
                &[&Pattern::new(
                    translate.ctx.ctx,
                    &[&app_z3 as &dyn Ast<'ctx>],
                )],
                &invariant,
            )
        })
    }
}

type FunctionDeclaration<'ctx> = (Ident, Vec<Sort<'ctx>>, Sort<'ctx>);

/// A specific strategy for encoding custom interpreted functions
pub trait FunctionEncoder<'ctx> {
    /// Generate the necessary function declaration(s) on the SMT-level
    fn declare_function(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
    ) -> Vec<FunctionDeclaration<'ctx>>;

    /// Generate all axioms related to the function
    fn axioms<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Vec<Bool<'ctx>>;

    /// Call the function in the current context
    fn call_function(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
        args: Vec<Symbolic<'ctx>>,
    ) -> Symbolic<'ctx>;
}

enum FunctionEncodingInner<'ctx> {
    Default(DefaultFunctionEncoding),
    Variable(VariableFuelFunctionEncoding<'ctx>),
    Fixed(FixedFuelFunctionEncoding),
    DefineFunRec(DefineFunRecEncoding<'ctx>),
}

/// A value that represents one of the possible encodings
pub struct FunctionEncoding<'ctx>(FunctionEncodingInner<'ctx>);

impl<'ctx> Default for FunctionEncoding<'ctx> {
    fn default() -> Self {
        Self::default()
    }
}

impl<'ctx> FunctionEncoder<'ctx> for FunctionEncoding<'ctx> {
    fn declare_function(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
    ) -> Vec<FunctionDeclaration<'ctx>> {
        match &self.0 {
            FunctionEncodingInner::Default(enc) => enc.declare_function(ctx, func),
            FunctionEncodingInner::Variable(enc) => enc.declare_function(ctx, func),
            FunctionEncodingInner::Fixed(enc) => enc.declare_function(ctx, func),
            FunctionEncodingInner::DefineFunRec(enc) => enc.declare_function(ctx, func),
        }
    }

    fn axioms<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Vec<Bool<'ctx>> {
        match &self.0 {
            FunctionEncodingInner::Default(enc) => enc.axioms(translate, func),
            FunctionEncodingInner::Variable(enc) => enc.axioms(translate, func),
            FunctionEncodingInner::Fixed(enc) => enc.axioms(translate, func),
            FunctionEncodingInner::DefineFunRec(enc) => enc.axioms(translate, func),
        }
    }

    fn call_function(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
        args: Vec<Symbolic<'ctx>>,
    ) -> Symbolic<'ctx> {
        match &self.0 {
            FunctionEncodingInner::Default(enc) => enc.call_function(ctx, func, args),
            FunctionEncodingInner::Variable(enc) => enc.call_function(ctx, func, args),
            FunctionEncodingInner::Fixed(enc) => enc.call_function(ctx, func, args),
            FunctionEncodingInner::DefineFunRec(enc) => enc.call_function(ctx, func, args),
        }
    }
}

impl<'ctx> FunctionEncoding<'ctx> {
    /// Apply no special encoding
    pub fn default() -> Self {
        Self(FunctionEncodingInner::Default(DefaultFunctionEncoding))
    }

    /// Perform limited function encoding by including an extra [z3rro::Fuel] parameter and
    /// only providing axioms for non-zero fuel parameters. The fuel parameter is decremented in every
    /// instantiation.
    /// Based on the paper "Computing with an SMT Solver".
    pub fn variable(max_fuel: u8, computation: bool) -> Self {
        Self(FunctionEncodingInner::Variable(
            VariableFuelFunctionEncoding {
                computation,
                none_encoding: DefaultFunctionEncoding,
                fuel_context: RefCell::new(FuelContext::call()),
                max_fuel,
            },
        ))
    }

    /// Perform limited function encoding by introducing n versions of the function.
    /// Version x only references x - 1. There is no definition for version 0.
    pub fn fixed(max_fuel: u8, computation: bool) -> Self {
        Self(FunctionEncodingInner::Fixed(FixedFuelFunctionEncoding {
            default_encoding: DefaultFunctionEncoding,
            computation,
            fuel_value: Cell::new(max_fuel.try_into().unwrap()),
            fuel_context: Cell::new(max_fuel),
            max_fuel,
        }))
    }

    pub fn define_fun_rec() -> Self {
        Self(FunctionEncodingInner::DefineFunRec(DefineFunRecEncoding {
            default_encoding: DefaultFunctionEncoding,
            decls: RefCell::new(HashMap::new()),
        }))
    }

    pub fn is_limited_encoding(&self) -> bool {
        matches!(
            self.0,
            FunctionEncodingInner::Variable(_) | FunctionEncodingInner::Fixed(_)
        )
    }

    pub fn needs_lit_wrapping(&self) -> bool {
        match &self.0 {
            FunctionEncodingInner::Variable(enc) => enc.computation,
            FunctionEncodingInner::Fixed(enc) => enc.computation,
            _ => false,
        }
    }
}

struct DefaultFunctionEncoding;

impl<'ctx> EncodingBase<'ctx> for DefaultFunctionEncoding {}

impl<'ctx> FunctionEncoder<'ctx> for DefaultFunctionEncoding {
    fn declare_function(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
    ) -> Vec<FunctionDeclaration<'ctx>> {
        let range = ty_to_sort(ctx, &func.output);
        let domain = build_func_domain(ctx, func, false);
        vec![(func.name, domain, range)]
    }

    fn axioms<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Vec<Bool<'ctx>> {
        let mut axioms = vec![];
        if let Some(body) = func.body.borrow().as_ref() {
            axioms.push(self.definitional_axiom(translate, func, body));
        }
        axioms.extend(self.build_return_invariant(
            translate,
            func,
            &format!("{}(return_invariant)", func.name),
        ));
        axioms
    }

    fn call_function(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
        args: Vec<Symbolic<'ctx>>,
    ) -> Symbolic<'ctx> {
        apply_function(ctx, func.name, &func.output, args.into_iter().collect())
    }
}

impl DefaultFunctionEncoding {
    fn definitional_axiom<'smt, 'ctx>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
        body: &Expr,
    ) -> Bool<'ctx> {
        let app = build_call(translate.ctx.tcx, func);

        let app_translated = translate.t_symbolic(&app).into_dynamic(translate.ctx);
        let body_translated = translate.t_symbolic(body).into_dynamic(translate.ctx);

        self.build_axiom(
            translate,
            func,
            &app_translated,
            &body_translated,
            &format!("{}(definitional)", func.name),
            WEIGHT_DEFAULT,
        )
    }
}

/// Functionality common to the fuel encodings
trait EncodingFuel<'ctx>: EncodingBase<'ctx> {
    fn use_head_context(&self, ctx: &SmtCtx<'ctx>);
    fn use_body_context(&self, ctx: &SmtCtx<'ctx>);
    fn to_body_context(&self, ctx: &SmtCtx<'ctx>);
    fn reset_context(&self, ctx: &SmtCtx<'ctx>);

    fn definitional_axiom<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Bool<'ctx> {
        let body_ref = func.body.borrow();
        let body = body_ref.as_ref().unwrap();

        let app = build_call(translate.ctx.tcx, func);

        self.use_head_context(translate.ctx);
        let symbolic_app = translate.t_symbolic(&app).into_dynamic(translate.ctx);
        // reuse same fuel in body
        self.to_body_context(translate.ctx);
        let symbolic_body = translate.t_symbolic(body).into_dynamic(translate.ctx);
        let axiom = self.build_axiom(
            translate,
            func,
            &symbolic_app,
            &symbolic_body,
            &format!("{}(definitional)", func.name),
            WEIGHT_DEFAULT,
        );

        self.reset_context(translate.ctx);
        axiom
    }

    fn return_invariant<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Option<Bool<'ctx>> {
        self.use_body_context(translate.ctx);
        let axiom = self.build_return_invariant(
            translate,
            func,
            &format!("{}(return_invariant)", func.name),
        );
        self.reset_context(translate.ctx);
        axiom
    }

    fn fuel_synonym_axiom<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Bool<'ctx> {
        let app = build_call(translate.ctx.tcx, func);

        self.use_head_context(translate.ctx);
        let symbolic_app = translate.t_symbolic(&app).into_dynamic(translate.ctx);
        // reuse same fuel in body
        self.to_body_context(translate.ctx);
        let symbolic_body = translate.t_symbolic(&app).into_dynamic(translate.ctx);
        let axiom = self.build_axiom(
            translate,
            func,
            &symbolic_app,
            &symbolic_body,
            &format!("{}(fuel_synonym)", func.name),
            WEIGHT_DEFAULT,
        );

        self.reset_context(translate.ctx);
        axiom
    }

    fn computation_axiom<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Bool<'ctx> {
        let mut app = build_call(translate.ctx.tcx, func);

        self.use_body_context(translate.ctx);
        {
            let literal_vars = func
                .inputs
                .node
                .iter()
                .map(|param| param.name)
                .collect_vec();
            let mut literal_exprs = LiteralExprCollector::new()
                .with_computable_functions(translate.ctx.computable_functions().as_slice())
                .with_literal_vars(literal_vars.as_slice())
                .collect(func.body.borrow_mut().as_mut().unwrap());
            // The result of the computation axiom should itself never be considered literal in practice.
            // Otherwise, some computation examples hang.
            // The paper uses if-then-else is used as a stopper for propagating literal information.
            // This has essentially the same effect in practice, but never making the result literal
            // is the more distilled version.
            literal_exprs.remove(func.body.borrow_mut().as_mut().unwrap());

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

        let axiom = self.build_axiom(
            translate,
            func,
            &app_z3,
            &body_z3,
            &format!("{}(computation)", func.name),
            WEIGHT_COMP,
        );
        translate.clear_literal_exprs();
        self.reset_context(translate.ctx);

        axiom
    }
}

enum FuelContext<'ctx> {
    Head(ScopeSymbolic<'ctx>),
    Body(ScopeSymbolic<'ctx>),
    Call,
}

impl<'ctx> FuelContext<'ctx> {
    fn head(ctx: &SmtCtx<'ctx>) -> Self {
        Self::Head(ScopeSymbolic::fresh_fuel(ctx))
    }

    fn body(ctx: &SmtCtx<'ctx>) -> Self {
        Self::Body(ScopeSymbolic::fresh_fuel(ctx))
    }

    fn call() -> Self {
        Self::Call
    }

    fn replace_with_body(&mut self, ctx: &SmtCtx<'ctx>) {
        let old = mem::replace(self, Self::call());
        let new = match old {
            FuelContext::Head(scope_symbolic) => Self::Body(scope_symbolic),
            FuelContext::Body(_) => old,
            FuelContext::Call => Self::body(ctx),
        };
        *self = new;
    }
}

/// # Definitional Axiom
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
/// # Computation Axiom
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
struct VariableFuelFunctionEncoding<'ctx> {
    none_encoding: DefaultFunctionEncoding,
    computation: bool,
    fuel_context: RefCell<FuelContext<'ctx>>,
    max_fuel: u8,
}

impl<'ctx> EncodingBase<'ctx> for VariableFuelFunctionEncoding<'ctx> {
    fn call_scope<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> SmtScope<'ctx> {
        let mut scope = self.none_encoding.call_scope(translate, func);
        let fuel_context = self.fuel_context.borrow();
        let fuel_scope = match &*fuel_context {
            FuelContext::Head(ss) => Some(&ss.scope),
            FuelContext::Body(ss) => Some(&ss.scope),
            FuelContext::Call => None,
        };
        scope.extend(fuel_scope);
        scope
    }
}

impl<'ctx> EncodingFuel<'ctx> for VariableFuelFunctionEncoding<'ctx> {
    fn use_head_context(&self, ctx: &SmtCtx<'ctx>) {
        *self.fuel_context.borrow_mut() = FuelContext::head(ctx);
    }

    fn use_body_context(&self, ctx: &SmtCtx<'ctx>) {
        *self.fuel_context.borrow_mut() = FuelContext::body(ctx);
    }

    fn to_body_context(&self, ctx: &SmtCtx<'ctx>) {
        self.fuel_context.borrow_mut().replace_with_body(ctx);
    }

    fn reset_context(&self, _ctx: &SmtCtx<'ctx>) {
        *self.fuel_context.borrow_mut() = FuelContext::call();
    }
}

impl<'ctx> FunctionEncoder<'ctx> for VariableFuelFunctionEncoding<'ctx> {
    fn declare_function(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
    ) -> Vec<FunctionDeclaration<'ctx>> {
        if !ctx.is_limited_function_decl(func) {
            return self.none_encoding.declare_function(ctx, func);
        }

        let range = ty_to_sort(ctx, &func.output);
        let domain = build_func_domain(ctx, func, true);
        vec![(func.name, domain, range)]
    }

    fn axioms<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Vec<Bool<'ctx>> {
        if !translate.ctx.is_limited_function_decl(func) {
            return self.none_encoding.axioms(translate, func);
        }

        let mut axioms = vec![
            self.definitional_axiom(translate, func),
            self.fuel_synonym_axiom(translate, func),
        ];
        axioms.extend(self.return_invariant(translate, func));
        if self.computation {
            axioms.push(self.computation_axiom(translate, func));
        }
        axioms
    }

    fn call_function(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
        args: Vec<Symbolic<'ctx>>,
    ) -> Symbolic<'ctx> {
        if !ctx.is_limited_function_decl(func) {
            return self.none_encoding.call_function(ctx, func, args);
        }

        let fuel_arg: Symbolic<'ctx> = match &*self.fuel_context.borrow() {
            FuelContext::Head(ss) => Fuel::succ(ss.symbolic.clone().into_fuel().unwrap()).into(),
            FuelContext::Body(ss) => ss.symbolic.clone(),
            FuelContext::Call => Fuel::new(ctx.fuel_factory(), self.max_fuel as u32).into(),
        };
        let mut args_vec = vec![fuel_arg];
        args_vec.extend(args);
        apply_function(ctx, func.name, &func.output, args_vec)
    }
}

struct FixedFuelFunctionEncoding {
    default_encoding: DefaultFunctionEncoding,
    computation: bool,
    fuel_context: Cell<u8>, // The current contex. This value is in function calls
    fuel_value: Cell<NonZero<u8>>, // The current fuel value that axioms are generated for. Head/Body is relative to this value
    max_fuel: u8,
}

impl<'ctx> EncodingBase<'ctx> for FixedFuelFunctionEncoding {}

impl<'ctx> EncodingFuel<'ctx> for FixedFuelFunctionEncoding {
    fn use_head_context(&self, _ctx: &SmtCtx<'ctx>) {
        self.fuel_context.set(self.fuel_value.get().get());
    }

    fn use_body_context(&self, _ctx: &SmtCtx<'ctx>) {
        self.fuel_context.set(self.fuel_value.get().get() - 1);
    }

    fn to_body_context(&self, _ctx: &SmtCtx<'ctx>) {
        self.fuel_context.set(self.fuel_value.get().get() - 1);
    }

    fn reset_context(&self, _ctx: &SmtCtx<'ctx>) {
        self.fuel_context.set(self.max_fuel);
    }
}

impl<'ctx> FunctionEncoder<'ctx> for FixedFuelFunctionEncoding {
    fn declare_function(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
    ) -> Vec<FunctionDeclaration<'ctx>> {
        if !ctx.is_limited_function_decl(func) {
            return self.default_encoding.declare_function(ctx, func);
        }
        let range = ty_to_sort(ctx, &func.output);
        let domain = build_func_domain(ctx, func, false);
        (0..=self.max_fuel)
            .rev()
            .map(|fuel| {
                (
                    Self::ident_with_fuel(func, fuel),
                    domain.clone(),
                    range.clone(),
                )
            })
            .collect()
    }

    fn axioms<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Vec<Bool<'ctx>> {
        if !translate.ctx.is_limited_function_decl(func) {
            return self.default_encoding.axioms(translate, func);
        }

        let mut axioms = (1..=self.max_fuel)
            .rev()
            .map(|fuel| self.definitional_axiom(translate, func, fuel.try_into().unwrap()))
            .collect_vec();
        axioms.extend(
            (0..=self.max_fuel)
                .rev()
                .filter_map(|fuel| self.return_invariant(translate, func, fuel)),
        );
        axioms.extend(
            (1..=self.max_fuel)
                .rev()
                .map(|fuel| self.fuel_synonym_axiom(translate, func, fuel.try_into().unwrap())),
        );
        if self.computation {
            axioms.extend(
                (1..=self.max_fuel)
                    .rev()
                    .map(|fuel| self.computation_axiom(translate, func, fuel.try_into().unwrap())),
            )
        }
        axioms
    }

    fn call_function(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
        args: Vec<Symbolic<'ctx>>,
    ) -> Symbolic<'ctx> {
        if !ctx.is_limited_function_decl(func) {
            return self.default_encoding.call_function(ctx, func, args);
        }

        apply_function(
            ctx,
            Self::ident_with_fuel(func, self.fuel_context.get()),
            &func.output,
            args.into_iter().collect(),
        )
    }
}

impl FixedFuelFunctionEncoding {
    fn ident_with_fuel(func: &FuncDecl, fuel: u8) -> Ident {
        Ident {
            name: Symbol::intern(&format!("{}${}", func.name.name, fuel)),
            span: func.name.span.variant(SpanVariant::Encoding),
        }
    }

    /// Creates the default defining axiom for a function. It has the form:
    /// ```txt
    /// forall <args...> @trigger(func_name$n(<args...>)) . func_name$n(<args...>) = <body>
    /// ```
    /// The axiom is only generated for n > 0 (non-zero fuel values). Recursive calls inside `<body>`
    /// are replaced with `func_name$n-1`, i.e. the fuel value is decremented.
    fn definitional_axiom<'smt, 'ctx>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
        fuel_value: NonZero<u8>,
    ) -> Bool<'ctx> {
        self.fuel_value.set(fuel_value);
        EncodingFuel::definitional_axiom(self, translate, func)
    }

    fn return_invariant<'smt, 'ctx>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
        fuel_value: u8,
    ) -> Option<Bool<'ctx>> {
        self.fuel_value.set((fuel_value + 1).try_into().unwrap());
        EncodingFuel::return_invariant(self, translate, func)
    }

    /// Creates the fuel synonym axiom that states that the result of the function is independent
    /// of the fuel parameter. It has the form:
    /// ```txt
    /// forall <args...> @trigger(func_name$n(<args...>)) . func_name$n(<args...>) = func_name$n-1(<args...>)
    /// ```
    fn fuel_synonym_axiom<'smt, 'ctx>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
        fuel_value: NonZero<u8>,
    ) -> Bool<'ctx> {
        self.fuel_value.set(fuel_value);
        EncodingFuel::fuel_synonym_axiom(self, translate, func)
    }

    fn computation_axiom<'smt, 'ctx>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
        fuel_value: NonZero<u8>,
    ) -> Bool<'ctx> {
        self.fuel_value.set(fuel_value);
        EncodingFuel::computation_axiom(self, translate, func)
    }
}

struct DefineFunRecEncoding<'ctx> {
    decls: RefCell<HashMap<Ident, RecFuncDecl<'ctx>>>,
    default_encoding: DefaultFunctionEncoding,
}

impl<'ctx> EncodingBase<'ctx> for DefineFunRecEncoding<'ctx> {}
impl<'ctx> FunctionEncoder<'ctx> for DefineFunRecEncoding<'ctx> {
    fn declare_function(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
    ) -> Vec<FunctionDeclaration<'ctx>> {
        if func.body.borrow().is_none() {
            return self.default_encoding.declare_function(ctx, func);
        }

        let domain = build_func_domain(ctx, func, false);
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

    fn axioms<'smt>(
        &self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        func: &FuncDecl,
    ) -> Vec<Bool<'ctx>> {
        if func.body.borrow().is_none() {
            return self.default_encoding.axioms(translate, func);
        }

        let decl_borrow = self.decls.borrow();
        let decl = decl_borrow
            .get(&func.name)
            .expect("function is not declared");

        let span = func.span.variant(SpanVariant::Encoding);
        let builder = ExprBuilder::new(span);

        let args: Vec<_> = func
            .inputs
            .node
            .iter()
            .map(|param| builder.var(param.name, translate.ctx.tcx))
            .map(|var| {
                let symbolic = translate.t_symbolic(&var);
                if symbolic.smt_invariant().is_some() {
                    let type_name = var.ty.clone().map(|ty| format!("{}", ty)).unwrap_or_else(|| "<unknown>".into());
                    panic!("define-fun-rec encoding only supports parameter types without side conditions.\nParameter {} of function {} has type {}, which has a side condition.", var, func.name, type_name)
                }
                symbolic.into_dynamic(translate.ctx)
            })
            .collect();
        let args = args.iter().map(|d| d as &dyn Ast<'ctx>).collect_vec();
        decl.add_def(
            &args,
            &translate
                .t_symbolic(&func.body.borrow().as_ref().unwrap())
                .into_dynamic(translate.ctx) as &dyn Ast<'ctx>,
        );
        self.build_return_invariant(translate, func, &format!("{}(return_invariant)", func.name))
            .into_iter()
            .collect()
    }

    fn call_function(
        &self,
        ctx: &SmtCtx<'ctx>,
        func: &FuncDecl,
        args: Vec<Symbolic<'ctx>>,
    ) -> Symbolic<'ctx> {
        if func.body.borrow().is_none() {
            return self.default_encoding.call_function(ctx, func, args);
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
}

fn apply_function<'ctx>(
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
fn build_func_domain<'a>(ctx: &SmtCtx<'a>, func: &FuncDecl, add_fuel: bool) -> Vec<Sort<'a>> {
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

/// Creates a call to the function.
fn build_call(tcx: &TyCtx, func: &FuncDecl) -> Expr {
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
    computable_functions: HashSet<Ident>,
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

    pub fn with_computable_functions(self, computable_functions: &[Ident]) -> Self {
        Self {
            computable_functions: computable_functions.iter().cloned().collect(),
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
            functions_with_def=?self.computable_functions,
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
                if self.computable_functions.contains(func)
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
