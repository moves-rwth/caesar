//! Uninterpreted sorts and functions.

use std::collections::HashMap;

use z3::{
    ast::{Ast, Bool, Dynamic},
    Context, FuncDecl, Sort,
};
use z3rro::prover::Prover;

use crate::ast::Ident;

use super::symbols::Symbolizer;

/// Tracks the Z3 objects for the uninterpreted sorts and functions.
#[derive(Debug)]
pub struct Uninterpreteds<'ctx> {
    ctx: &'ctx Context,
    symbolizer: Symbolizer,
    sorts: HashMap<Ident, Sort<'ctx>>,
    functions: HashMap<Ident, FuncDecl<'ctx>>,
    axioms: Vec<(Ident, Bool<'ctx>)>,
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

    pub fn add_sort(&mut self, ident: Ident) {
        let symbol = self.symbolizer.get(ident);
        let sort = Sort::uninterpreted(self.ctx, symbol);
        let prev = self.sorts.insert(ident, sort);
        assert!(prev.is_none());
    }

    pub fn add_function(&mut self, ident: Ident, domain: &[&Sort<'ctx>], range: &Sort<'ctx>) {
        let symbol = self.symbolizer.get(ident);
        let decl = FuncDecl::new(self.ctx, symbol, domain, range);
        let prev = self.functions.insert(ident, decl);
        assert!(prev.is_none());
    }

    pub fn get_sort(&self, ident: Ident) -> Option<&Sort<'ctx>> {
        self.sorts.get(&ident)
    }

    pub fn apply_function(&self, ident: Ident, args: &[&dyn Ast<'ctx>]) -> Dynamic<'ctx> {
        let decl = self
            .functions
            .get(&ident)
            .expect("function is not declared");
        decl.apply(args)
    }

    pub fn add_axiom(&mut self, ident: Ident, axiom: Bool<'ctx>) {
        self.axioms.push((ident, axiom));
    }

    pub fn add_axioms_to_prover(&self, prover: &mut Prover<'ctx>) {
        for (_name, axiom) in &self.axioms {
            prover.add_assumption(axiom);
        }
    }

    pub fn is_empty(&self) -> bool {
        self.sorts.is_empty() && self.functions.is_empty() && self.axioms.is_empty()
    }
}
