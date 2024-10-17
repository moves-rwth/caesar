//! Encodings of declarations, definitions, and expressions into SMT.

use itertools::Itertools;
use std::{cell::RefCell, collections::HashMap, rc::Rc};
use z3::ast::Ast;
use z3::{ast::Bool, Context, Pattern, Sort};
use z3rro::{
    eureal::EURealSuperFactory, EUReal, Factory, FuelFactory, ListFactory, SmtEq, SmtInvariant,
};

use self::{translate_exprs::TranslateExprs, uninterpreted::Uninterpreteds};
use crate::ast::{DeclKind, Expr, FuncDecl};
use crate::smt::translate_exprs::FuelContext;
use crate::{
    ast::{DeclRef, DomainDecl, DomainSpec, ExprBuilder, Ident, SpanVariant, TyKind},
    tyctx::TyCtx,
};

pub mod pretty_model;
pub mod symbolic;
mod symbols;
pub mod translate_exprs;
mod uninterpreted;

pub struct SmtCtx<'ctx> {
    ctx: &'ctx Context,
    tcx: &'ctx TyCtx,
    eureal: EURealSuperFactory<'ctx>,
    fuel: Rc<FuelFactory<'ctx>>,
    lists: RefCell<HashMap<TyKind, Rc<ListFactory<'ctx>>>>,
    uninterpreteds: Uninterpreteds<'ctx>,
    use_limited_functions: bool,
}

impl<'ctx> SmtCtx<'ctx> {
    pub fn new(ctx: &'ctx Context, tcx: &'ctx TyCtx, use_limited_fuctions: bool) -> Self {
        let mut res = SmtCtx {
            ctx,
            tcx,
            eureal: EURealSuperFactory::new(ctx),
            fuel: FuelFactory::new(ctx),
            lists: RefCell::new(HashMap::new()),
            uninterpreteds: Uninterpreteds::new(ctx),
            use_limited_functions: use_limited_fuctions,
        };
        let domains: Vec<_> = tcx.domains_owned();
        res.declare_domains(domains.as_slice());
        res
    }

    fn declare_domains(&mut self, domains: &[DeclRef<DomainDecl>]) {
        // Step 1. declare sorts
        for decl_ref in domains {
            self.uninterpreteds.add_sort(decl_ref.borrow().name);
        }

        // Step 2. declare functions
        for decl_ref in domains {
            let decl = decl_ref.borrow();
            for spec in &decl.body {
                if let DomainSpec::Function(func_ref) = &spec {
                    let func = func_ref.borrow();

                    let mut domain = if self.is_limited_function_decl(&*func) {
                        // For function definitions we constrain the number
                        // of quantifier installations through a fuel parameter.
                        // The fuel parameter is automatically added as the first parameter.
                        vec![self.fuel_factory().sort().clone()]
                    } else {
                        vec![]
                    };
                    domain.extend(
                        func.inputs
                            .node
                            .iter()
                            .map(|param| ty_to_sort(self, &param.ty)),
                    );
                    let domain: Vec<&Sort<'_>> = domain.iter().collect();
                    let range = ty_to_sort(self, &func.output);
                    self.uninterpreteds.add_function(func.name, &domain, &range);
                }
            }
        }

        // Step 3. translate & add axioms and function definitions

        // note: you may ask yourself, why not use z3's RecFuncDecl's to declare
        // functions that have a body? Because that only allows for declarations
        // that quantify over constants (i.e. variables), not expressions. this
        // is a problem when dealing with more complex types such as the
        // pair::realplus representation which needs to quantify over two
        // variables (a Boolean and a Real).
        let mut axioms: Vec<(Ident, Bool<'ctx>)> = Vec::new();
        let mut translate = TranslateExprs::new(self);
        for decl_ref in domains {
            let decl = decl_ref.borrow();
            for spec in &decl.body {
                match &spec {
                    DomainSpec::Function(func_ref) => {
                        let func = func_ref.borrow();
                        let body = func.body.borrow();

                        let span = func.span.variant(SpanVariant::VC);
                        let builder = ExprBuilder::new(span);
                        let app = builder.call(
                            func.name,
                            func.inputs
                                .node
                                .iter()
                                .map(|param| builder.var(param.name, self.tcx)),
                            self.tcx,
                        );

                        // if there's an smt invariant for the return value type, add it
                        {
                            translate.push();
                            translate.set_local_fuel_context(FuelContext::Body);
                            let app_z3 = translate.t_symbolic(&app);
                            if let Some(invariant) = app_z3.smt_invariant() {
                                axioms.push((
                                    func.name, // TODO: create a new name for the axiom
                                    translate.local_scope().forall(&[], &invariant),
                                ));
                            }
                            translate.pop();
                        }

                        let mut add_defining_axiom = |name: Ident, lhs: &Expr, rhs: &Expr| {
                            translate.push();
                            translate.set_local_fuel_context(FuelContext::Head);
                            let symbolic_lhs = translate.t_symbolic(&lhs).into_dynamic(self);

                            translate.set_local_fuel_context(FuelContext::Body);
                            let symbolic_rhs = translate.t_symbolic(rhs).into_dynamic(self);

                            println!("lhs: {:?}\nrhs: {:?}", symbolic_lhs, symbolic_rhs);
                            println!(
                                "local scope bounds {:?}",
                                translate.local_scope().get_bounds().collect_vec()
                            );

                            axioms.push((
                                name, // TODO: create a new name for the axiom
                                translate.local_scope().forall(
                                    &[&Pattern::new(self.ctx, &[&symbolic_lhs as &dyn Ast<'ctx>])],
                                    &symbolic_lhs.smt_eq(&symbolic_rhs),
                                ),
                            ));
                            translate.pop();
                        };

                        if self.is_limited_function_decl(&*func) {
                            // fuel synonym axiom
                            add_defining_axiom(func.name, &app, &app); // TODO: create a new name for the axiom
                        }

                        // create the axiom for the definition if there is a body
                        if let Some(body) = &*body {
                            // Defining axiom
                            add_defining_axiom(func.name, &app, body); // TODO: create a new name for the axiom
                        }
                    }
                    DomainSpec::Axiom(axiom_ref) => {
                        let axiom = axiom_ref.borrow();
                        axioms.push((axiom.name, translate.t_bool(&axiom.axiom)));
                    }
                }
            }
        }
        drop(translate); // drop shared reference on self
        for (name, axiom) in axioms {
            self.uninterpreteds.add_axiom(name, axiom);
        }
    }

    /// Get the smt ctx's ctx.
    #[must_use]
    pub fn ctx(&self) -> &'ctx Context {
        self.ctx
    }

    /// Get the smt ctx's tcx.
    #[must_use]
    pub fn tcx(&self) -> &TyCtx {
        self.tcx
    }

    #[must_use]
    pub fn eureal(&self) -> &Factory<'ctx, EUReal<'ctx>> {
        self.eureal.default_factory()
    }

    #[must_use]
    pub fn super_eureal(&self) -> &EURealSuperFactory<'ctx> {
        &self.eureal
    }

    fn list_factory(&self, element_ty: &TyKind) -> Rc<ListFactory<'ctx>> {
        let lists = self.lists.borrow();
        if !lists.contains_key(element_ty) {
            // ty_to_sort can call list_factory again, so we release the handle
            // on lists here temporarily
            drop(lists);
            let factory = ListFactory::new(self.ctx, &ty_to_sort(self, element_ty));
            let mut lists = self.lists.borrow_mut();
            let prev = lists.insert(element_ty.clone(), factory);
            assert!(prev.is_none());
        }
        let lists = self.lists.borrow();
        lists.get(element_ty).unwrap().clone()
    }

    fn fuel_factory(&self) -> Rc<FuelFactory<'ctx>> {
        self.fuel.clone()
    }

    /// Get a reference to the smt ctx's uninterpreteds.
    #[must_use]
    pub fn uninterpreteds(&self) -> &Uninterpreteds<'ctx> {
        &self.uninterpreteds
    }

    pub fn is_limited_function(&self, ident: Ident) -> bool {
        if !self.use_limited_functions {
            return false;
        }
        self.tcx
            .get(ident)
            .filter(|decl| match decl.as_ref() {
                DeclKind::FuncDecl(func) => self.is_limited_function_decl(&func.borrow()),
                _ => false,
            })
            .is_some()
    }

    pub fn is_limited_function_decl(&self, func: &FuncDecl) -> bool {
        self.use_limited_functions && func.body.borrow().is_some()
    }
}

fn ty_to_sort<'ctx>(ctx: &SmtCtx<'ctx>, ty: &TyKind) -> Sort<'ctx> {
    match ty {
        TyKind::Bool => Sort::bool(ctx.ctx()),
        TyKind::Int | TyKind::UInt => Sort::int(ctx.ctx()),
        TyKind::Real | TyKind::UReal => Sort::real(ctx.ctx()),
        TyKind::EUReal => ctx.super_eureal().datatype_factory.sort().clone(),
        TyKind::Tuple(_) => todo!(),
        TyKind::List(element_ty) => ctx.list_factory(element_ty).sort().clone(),
        TyKind::Domain(domain_ref) => ctx
            .uninterpreteds
            .get_sort(domain_ref.borrow().name)
            .unwrap()
            .clone(),

        TyKind::String | TyKind::SpecTy | TyKind::Unresolved(_) | TyKind::None => {
            panic!("invalid type")
        }
    }
}
