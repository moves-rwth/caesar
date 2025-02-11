//! Encodings of declarations, definitions, and expressions into SMT.

use self::{translate_exprs::TranslateExprs, uninterpreted::Uninterpreteds};
use crate::ast::{DeclKind, FuncDecl};
use crate::smt::limited::{is_eligible_for_limited_function, EncodingFuel};
use crate::{
    ast::{DeclRef, DomainDecl, DomainSpec, Ident, TyKind},
    tyctx::TyCtx,
};
use itertools::Itertools;
use std::fmt::Debug;
use std::{cell::RefCell, collections::HashMap, rc::Rc};
use z3::ast::{Ast, Dynamic};
use z3::{ast::Bool, Context, Sort};
use z3rro::prover::Prover;
use z3rro::{
    eureal::EURealSuperFactory, EUReal, Factory, FuelFactory, ListFactory, LitDecl, LitFactory,
};

mod limited;
pub use limited::{FuelEncoding, LiteralExprCollector};

pub mod pretty_model;
pub mod symbolic;
mod symbols;
pub mod translate_exprs;
mod uninterpreted;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub struct SmtCtxOptions {
    pub use_limited_functions: bool,
    pub lit_wrap: bool,
    pub static_fuel: bool,
}

pub struct SmtCtx<'ctx> {
    ctx: &'ctx Context,
    tcx: &'ctx TyCtx,
    eureal: EURealSuperFactory<'ctx>,
    fuel: Rc<FuelFactory<'ctx>>,
    lists: RefCell<HashMap<TyKind, Rc<ListFactory<'ctx>>>>,
    lits: RefCell<Vec<(Sort<'ctx>, LitDecl<'ctx>)>>,
    uninterpreteds: Uninterpreteds<'ctx>,
    fuel_encoding: FuelEncoding<'ctx>,
    options: SmtCtxOptions,
}

impl<'ctx> SmtCtx<'ctx> {
    pub fn new(ctx: &'ctx Context, tcx: &'ctx TyCtx, options: SmtCtxOptions) -> Self {
        let domains: Vec<_> = tcx.domains_owned();
        // disable lit-wrapping if there are no limited functions that can profit from it
        let lit_wrap = options.lit_wrap
            && options.use_limited_functions
            && domains.iter().any(|d| {
                d.borrow()
                    .function_decls()
                    .any(|func| is_eligible_for_limited_function(&func.borrow()))
            });
        let options = SmtCtxOptions {
            lit_wrap,
            ..options
        };

        let fuel_encoding = if !options.use_limited_functions {
            FuelEncoding::none()
        } else if options.static_fuel {
            FuelEncoding::static_(options.lit_wrap)
        } else {
            FuelEncoding::dynamic(options.lit_wrap)
        };

        let mut res = SmtCtx {
            ctx,
            tcx,
            eureal: EURealSuperFactory::new(ctx),
            fuel: FuelFactory::new(ctx),
            lists: RefCell::new(HashMap::new()),
            lits: RefCell::new(Vec::new()),
            uninterpreteds: Uninterpreteds::new(ctx),
            fuel_encoding,
            options,
        };
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
                    for (name, domain, range) in self.fuel_encoding.declare_function(self, &func) {
                        let domain = domain.iter().collect_vec();
                        self.uninterpreteds.add_function(name, &domain, &range)
                    }
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
        let mut translate = TranslateExprs::new(self);
        let mut axioms: Vec<(Ident, Bool<'ctx>)> = Vec::new();
        for decl_ref in domains {
            let decl = decl_ref.borrow();
            for spec in &decl.body {
                match &spec {
                    DomainSpec::Function(func_ref) => {
                        let func = func_ref.borrow();

                        fn with_name<'ctx>(
                            name: Ident,
                        ) -> impl Fn(Bool<'ctx>) -> (Ident, Bool<'ctx>) {
                            move |axiom: Bool<'ctx>| (name, axiom)
                        }

                        // TODO: create a new name for the axioms
                        axioms.extend(
                            self.fuel_encoding
                                .axioms(&mut translate, &func)
                                .into_iter()
                                .map(with_name(func.name)),
                        );
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

    #[must_use]
    pub fn uninterpreteds_mut(&mut self) -> &mut Uninterpreteds<'ctx> {
        &mut self.uninterpreteds
    }

    pub fn add_lit_axioms_to_prover(&self, prover: &mut Prover<'ctx>) {
        for (_, lit) in self.lits.borrow().iter() {
            for axiom in lit.defining_axiom() {
                prover.add_assumption(&axiom);
            }
        }
    }

    pub fn is_limited_function(&self, ident: Ident) -> bool {
        if !self.options.use_limited_functions {
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
        self.options.use_limited_functions && is_eligible_for_limited_function(func)
    }

    pub fn fuel_encoding(&self) -> &FuelEncoding<'ctx> {
        &self.fuel_encoding
    }

    pub fn functions_with_def(&self) -> Vec<Ident> {
        self.tcx
            .get_function_decls()
            .values()
            .filter(|func_decl| func_decl.borrow().body.borrow().is_some())
            .map(|func_decl| func_decl.borrow().name)
            .collect()
    }
}

impl<'ctx> LitFactory<'ctx> for SmtCtx<'ctx> {
    fn lit_wrap_dynamic(&self, arg: &Dynamic<'ctx>) -> Dynamic<'ctx> {
        if !self.options.lit_wrap {
            return arg.clone();
        }

        let arg_sort = arg.get_sort();
        let mut lits = self.lits.borrow_mut();
        let lit_decl = if let Some((_, decl)) = lits.iter().find(|(sort, _)| *sort == arg_sort) {
            decl
        } else {
            lits.push((arg_sort.clone(), LitDecl::new(self.ctx, arg_sort)));
            &lits.last().unwrap().1
        };
        lit_decl.apply_call(arg)
    }
}

pub fn ty_to_sort<'ctx>(ctx: &SmtCtx<'ctx>, ty: &TyKind) -> Sort<'ctx> {
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
