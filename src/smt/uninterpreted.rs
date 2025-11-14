//! Uninterpreted sorts and functions.

use std::collections::HashMap;

use z3::{
    ast::{Ast, Bool, Dynamic},
    Context, FuncDecl, Sort,
};
use z3rro::prover::Prover;

use crate::ast::{Ident, Param, Spanned};

use super::symbols::Symbolizer;

/// Tracks the Z3 objects for the uninterpreted sorts and functions.
#[derive(Debug)]
pub struct Uninterpreteds<'ctx> {
    ctx: &'ctx Context,
    symbolizer: Symbolizer,
    sorts: HashMap<Ident, Sort<'ctx>>,
    functions: HashMap<Ident, FuncEntry<'ctx>>,
    axioms: Vec<(Ident, Bool<'ctx>, bool)>,
}

#[derive(Debug)]
pub(crate) struct FuncEntry<'ctx> {
    pub(crate) decl: FuncDecl<'ctx>,
    pub(crate) syn: bool,
    pub inputs: Spanned<Vec<Param>>,
}

impl<'ctx> Uninterpreteds<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            ctx,
            symbolizer: Default::default(),
            sorts: Default::default(),
            functions: Default::default(),
            axioms: Default::default(),
        }
    }
    pub(crate) fn functions(&self) -> &HashMap<Ident, FuncEntry<'ctx>> {
        &self.functions
    }

    pub fn add_sort(&mut self, ident: Ident) {
        let symbol = self.symbolizer.get(ident);
        let sort = Sort::uninterpreted(self.ctx, symbol);
        let prev = self.sorts.insert(ident, sort);
        assert!(prev.is_none());
    }

    pub fn add_function(
        &mut self,
        ident: Ident,
        domain: &[&Sort<'ctx>],
        range: &Sort<'ctx>,
        syn: bool,
        inputs: Spanned<Vec<Param>>,
    ) {
        let symbol = self.symbolizer.get(ident);
        let decl = FuncDecl::new(self.ctx, symbol, domain, range);
        let prev = self.functions.insert(
            ident,
            FuncEntry {
                decl,
                syn,
                inputs,
            },
        );
        assert!(prev.is_none());
    }

    pub fn get_sort(&self, ident: Ident) -> Option<&Sort<'ctx>> {
        self.sorts.get(&ident)
    }

    pub fn apply_function(&self, ident: Ident, args: &[&dyn Ast<'ctx>]) -> Dynamic<'ctx> {
        let decl = self
            .functions
            .get(&ident)
            .unwrap_or_else(|| panic!("function {ident} is not declared"));
        decl.decl.apply(args)
    }

    pub fn add_axiom(&mut self, ident: Ident, axiom: Bool<'ctx>, syn: bool) {
        self.axioms.push((ident, axiom, syn));
    }

    pub fn add_axioms_to_prover(&self, prover: &mut Prover<'ctx>) {
        for (_name, axiom,_syn) in &self.axioms {
            prover.add_assumption(axiom);
        }
    }

    pub fn is_empty(&self) -> bool {
        self.sorts.is_empty() && self.functions.is_empty() && self.axioms.is_empty()
    }
}
