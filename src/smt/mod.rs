//! Encodings of declarations, definitions, and expressions into SMT.

use self::{translate_exprs::TranslateExprs, uninterpreted::Uninterpreteds};
use crate::depgraph::Dependencies;
use crate::smt::funcs::FunctionEncoder;
use crate::{
    ast::{DomainSpec, Ident, TyKind},
    tyctx::TyCtx,
};
use itertools::Itertools;
use std::{cell::RefCell, collections::HashMap, rc::Rc};
use z3::ast::{Ast, Dynamic};
use z3::{ast::Bool, Context, Sort};
use z3rro::prover::Prover;
use z3rro::{
    eureal::EURealSuperFactory, EUReal, Factory, FuelFactory, ListFactory, LitDecl, LitFactory,
};

pub mod funcs;

pub mod pretty_model;
pub mod symbolic;
mod symbols;
pub mod translate_exprs;
mod uninterpreted;

/// Which dependencies to include in the SMT context.
#[derive(Debug)]
pub enum DepConfig<'a> {
    /// Include those specified in the set.
    Set(&'a Dependencies),
    /// Include everything that was declared by the user.
    All,
    /// Include all declarations by the user, but omit definitions.
    SpecsOnly,
}

/// An extension of the Z3 context with additional components to create
/// values of Caesar-specific SMT types.
pub struct SmtCtx<'ctx> {
    ctx: &'ctx Context,
    tcx: &'ctx TyCtx,
    eureal: EURealSuperFactory<'ctx>,
    fuel: Rc<FuelFactory<'ctx>>,
    lists: RefCell<HashMap<TyKind, Rc<ListFactory<'ctx>>>>,
    lits: RefCell<Vec<(Sort<'ctx>, LitDecl<'ctx>)>>,
    uninterpreteds: Uninterpreteds<'ctx>,
    function_encoder: Box<dyn FunctionEncoder<'ctx>>,
    pub lit_wrap: bool,
}

impl<'ctx> SmtCtx<'ctx> {
    pub fn new<'a>(
        ctx: &'ctx Context,
        tcx: &'ctx TyCtx,
        function_encoder: Box<dyn FunctionEncoder<'ctx>>,
        dep_config: DepConfig<'a>,
    ) -> Self {
        let mut res = SmtCtx {
            ctx,
            tcx,
            eureal: EURealSuperFactory::new(ctx),
            fuel: FuelFactory::new(ctx),
            lists: RefCell::new(HashMap::new()),
            lits: RefCell::new(Vec::new()),
            uninterpreteds: Uninterpreteds::new(ctx),
            function_encoder,
            lit_wrap: false,
        };
        res.init_dependencies(dep_config);
        res
    }

    /// Initializes the dependencies: domain sorts, functions, and axioms.
    fn init_dependencies(&mut self, dep_config: DepConfig<'_>) {
        let domains = self.tcx.domains_owned();

        // Step 1. declare sorts
        for decl_ref in &domains {
            let decl = decl_ref.borrow();
            match dep_config {
                DepConfig::Set(deps) if !deps.contains(&decl.name) => continue,
                _ => {}
            }
            self.uninterpreteds.add_sort(decl.name);
        }

        // Step 2. declare functions
        for decl_ref in &domains {
            let decl = decl_ref.borrow();
            for spec in &decl.body {
                if let DomainSpec::Function(func_ref) = &spec {
                    let func = func_ref.borrow();
                    match dep_config {
                        DepConfig::Set(deps) if !deps.contains(&func.name) => continue,
                        _ => {}
                    }
                    self.lit_wrap =
                        self.lit_wrap || self.function_encoder.func_uses_lit_wrap(&func_ref);
                    for (name, domain, range) in
                        self.function_encoder.translate_signature(self, &func)
                    {
                        let domain = domain.iter().collect_vec();
                        self.uninterpreteds.add_function(name, &domain, &range)
                    }
                }
            }
        }

        // Step 3. translate & add axioms and function definitions
        let mut axioms: Vec<(Ident, Bool<'ctx>)> = Vec::new();
        let mut translate = TranslateExprs::new(self);
        for decl_ref in &domains {
            let decl = decl_ref.borrow();
            for spec in &decl.body {
                match &spec {
                    DomainSpec::Function(func_ref) => {
                        let func = func_ref.borrow();
                        match dep_config {
                            DepConfig::Set(deps) if !deps.contains(&func.name) => continue,
                            DepConfig::SpecsOnly => continue,
                            _ => {}
                        }
                        let name = func.name;
                        axioms.extend(
                            self.function_encoder
                                .translate_axioms(&mut translate, &func)
                                .into_iter()
                                .map(move |axiom| (name, axiom)),
                        );
                    }
                    DomainSpec::Axiom(axiom_ref) => {
                        // TODO: translate axiom name as qid?
                        let axiom = axiom_ref.borrow();
                        match dep_config {
                            DepConfig::Set(deps) if !deps.contains(&axiom.name) => continue,
                            DepConfig::SpecsOnly => continue,
                            _ => {}
                        }
                        axioms.push((axiom.name, translate.t_bool(&axiom.axiom)));
                    }
                }
            }
        }
        drop(translate); // drops shared reference on self so we can modify
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

    fn fuel_factory(&self) -> &Rc<FuelFactory<'ctx>> {
        &self.fuel
    }

    /// Get a reference to the smt ctx's uninterpreteds.
    #[must_use]
    pub fn uninterpreteds(&self) -> &Uninterpreteds<'ctx> {
        &self.uninterpreteds
    }

    pub fn add_lit_axioms_to_prover(&self, prover: &mut Prover<'ctx>) {
        for (_, lit) in self.lits.borrow().iter() {
            for axiom in lit.defining_axiom() {
                prover.add_assumption(&axiom);
            }
        }
    }

    pub fn function_encoder(&self) -> &dyn FunctionEncoder<'ctx> {
        &*self.function_encoder
    }

    /// Return a list of functions that are computable, so that they are marked
    /// as literals when called with literal parameters.
    pub fn computable_functions(&self) -> Vec<Ident> {
        self.tcx
            .get_function_decls()
            .values()
            .filter(|func_decl| {
                let decl = func_decl.borrow();
                decl.computable || decl.body.borrow().is_some()
            })
            .map(|func_decl| func_decl.borrow().name)
            .collect()
    }
}

impl<'ctx> LitFactory<'ctx> for SmtCtx<'ctx> {
    fn lit_wrap_dynamic(&self, arg: &Dynamic<'ctx>) -> Dynamic<'ctx> {
        if !self.lit_wrap {
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
