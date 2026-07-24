use std::convert::Infallible;

use indexmap::IndexMap;
use num::BigUint;

use crate::{
    ast::util::lit_u128,
    ast::{
        visit::{walk_stmt, VisitorMut},
        ExprData, ExprKind, LitKind, Shared, Spanned, Stmt, StmtKind, Symbol,
    },
    driver::front::{Module, SourceUnit},
};

/// Returns the `k` argument of the first `@k_induction` annotation found in `module`, if any.
pub fn read_k_induction_k(module: &mut Module) -> Option<u128> {
    let mut visitor = FindK;
    for item in &mut module.items {
        let result = match item.value_mut() {
            SourceUnit::Decl(decl) => visitor.visit_decl(decl),
            SourceUnit::Raw(block) => visitor.visit_block(block),
        };
        if let Err(k) = result {
            return Some(k);
        }
    }
    None
}

/// Collects all `@k_induction(k, inv_call)` annotations in `module` and
/// returns a map from synth-function name to the invariant call string.
pub fn collect_k_induction_calls(module: &mut Module) -> IndexMap<Symbol, String> {
    let mut visitor = CollectKCalls(IndexMap::new());
    for item in &mut module.items {
        match item.value_mut() {
            SourceUnit::Decl(decl) => visitor.visit_decl(decl).unwrap(),
            SourceUnit::Raw(block) => visitor.visit_block(block).unwrap(),
        }
    }
    visitor.0
}

/// Traverses `module` and replaces the k literal in every `@k_induction(k, ...)`
/// annotation with `new_k`.
pub fn set_k_induction_k(module: &mut Module, new_k: u128) {
    let mut visitor = SetK(new_k);
    for item in &mut module.items {
        match item.value_mut() {
            SourceUnit::Decl(decl) => visitor.visit_decl(decl).unwrap(),
            SourceUnit::Raw(block) => visitor.visit_block(block).unwrap(),
        }
    }
}

struct FindK;

impl VisitorMut for FindK {
    type Err = u128;

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), u128> {
        if let StmtKind::Annotation(_, ident, args, _) = &s.node {
            if ident.name == *"k_induction" {
                if let Some(first) = args.first() {
                    return Err(lit_u128(first));
                }
            }
        }
        walk_stmt(self, s)
    }
}

struct CollectKCalls(IndexMap<Symbol, String>);

impl VisitorMut for CollectKCalls {
    type Err = Infallible;

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Infallible> {
        if let StmtKind::Annotation(_, ident, args, _) = &s.node {
            if ident.name == *"k_induction" && args.len() == 2 {
                let inv_expr = &args[1];
                let inv_str = inv_expr.to_string();
                if let ExprKind::Call(func_ident, _) = &inv_expr.kind {
                    self.0.entry(func_ident.name).or_insert(inv_str);
                }
            }
        }
        walk_stmt(self, s)
    }
}

struct SetK(u128);

impl VisitorMut for SetK {
    type Err = Infallible;

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Infallible> {
        if let StmtKind::Annotation(_, ident, args, _) = &mut s.node {
            if ident.name == *"k_induction" {
                if let Some(first) = args.first_mut() {
                    *first = Shared::new(ExprData {
                        kind: ExprKind::Lit(Spanned::with_dummy_span(LitKind::UInt(
                            BigUint::from(self.0),
                        ))),
                        ty: first.ty.clone(),
                        span: first.span,
                    });
                }
            }
        }
        walk_stmt(self, s)
    }
}
