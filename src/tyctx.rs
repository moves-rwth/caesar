//! Main data structure in the compiler that keeps definitions and so on.

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use indexmap::IndexMap;

use crate::ast::{DeclKind, DeclRef, DomainDecl, Ident, LitKind, Span, Symbol, TyKind, VarKind};

/// This is the central symbol table for the language. It keeps track of all
/// definitions,
#[derive(Debug)]
pub struct TyCtx {
    /// A map of identifiers to the associated declaration.
    ///
    /// It's an [`IndexMap`] to ensure stable iteration order over declarations.
    /// This keeps the SMT-LIB output deterministic.
    declarations: RefCell<IndexMap<Ident, Rc<DeclKind>>>,
    /// Global identifiers are those that are available in every new resolver at
    /// the top scope. Adding a global is essentially an "export" of a source
    /// and initializing a resolver with them is using "imports".
    globals: HashSet<Ident>,
    /// The Heyting algebra we're doing verification with. This is the type used
    /// in assert/assume/compare statements and in requires/ensures attributes.
    ///
    /// Classical deductive verifiers use booleans, and for probabilistic
    /// verification we use EUReal.
    spec_ty: TyKind,
    /// Counter for a suffix for each identifier to create a fresh variable.
    fresh: RefCell<HashMap<Ident, usize>>,
}

impl TyCtx {
    pub fn new(spec_ty: TyKind) -> Self {
        TyCtx {
            declarations: RefCell::new(IndexMap::new()),
            globals: HashSet::new(),
            spec_ty,
            fresh: RefCell::new(HashMap::new()),
        }
    }

    /// Add this declaration to the symbol table.
    pub fn declare(&self, decl: DeclKind) {
        let ident = decl.name();
        tracing::trace!(ident=?ident, "declare");
        let prev = self.declarations.borrow_mut().insert(ident, Rc::new(decl));
        assert!(
            prev.is_none(),
            "{} already has a previous declaration",
            ident
        );
    }

    /// Removes an existing declaration.
    ///
    /// Panics if there was no existing declaration.
    pub fn undeclare(&mut self, ident: Ident) -> Rc<DeclKind> {
        self.globals.remove(&ident);
        self.declarations.get_mut().remove(&ident).unwrap()
    }

    pub fn add_global(&mut self, ident: Ident) {
        tracing::trace!(ident=?ident, "add global");
        self.globals.insert(ident);
    }

    /// Generate a fresh [`Ident`] based on the given [`Ident`].
    ///
    /// Example: Given `x` as input [`Ident`], if `x` already exists than `x_1` is returned as long as `x_1` doesn't exist.
    pub fn fresh_ident(&self, ident: Ident, span: Span) -> Ident {
        loop {
            let mut fresh = self.fresh.borrow_mut();
            let index = fresh.entry(ident).and_modify(|e| *e += 1).or_insert(0);
            let new_name = format!("{}_{}", ident.name.to_owned(), index);
            let new_ident = Ident {
                name: Symbol::intern(&new_name),
                span,
            };
            if !self.declarations.borrow().contains_key(&new_ident) {
                return new_ident;
            }
        }
    }

    /// Generate a fresh variable declaration from an existing variable declaration with the given `var_kind`.
    /// Uses [`fresh_ident`](fn@fresh_ident) to generate a new name for the variable.
    pub fn clone_var(&self, ident: Ident, span: Span, var_kind: VarKind) -> Ident {
        let new_ident = self.fresh_ident(ident, span);

        // now take the old declaration and create a new one with the new name.
        // this is somewhat involved due to the [`DeclRef`]s everywhere.
        let old_decl = self.get(ident).unwrap();
        let var_decl = match old_decl.as_ref() {
            DeclKind::VarDecl(var_ref) => {
                // clone the underlying struct, _not_ the reference to it!
                let mut var_decl = var_ref.borrow().clone();
                var_decl.name = new_ident;
                var_decl.created_from.get_or_insert(ident);
                var_decl.kind = var_kind;
                DeclRef::new(var_decl)
            }
            _ => panic!("identifier is not a variable"),
        };
        self.declare(DeclKind::VarDecl(var_decl));
        new_ident
    }

    pub fn get(&self, ident: Ident) -> Option<Rc<DeclKind>> {
        self.declarations.borrow().get(&ident).cloned()
    }

    pub fn get_mut(&mut self, ident: Ident) -> Option<&mut DeclKind> {
        self.declarations
            .get_mut()
            .get_mut(&ident)
            .map(|val| Rc::get_mut(val).unwrap())
    }

    pub fn globals_iter(&self) -> impl Iterator<Item = &Ident> {
        self.globals.iter()
    }

    pub fn declarations_mut(&mut self) -> impl Iterator<Item = &mut DeclKind> {
        self.declarations
            .get_mut()
            .values_mut()
            .map(|val| Rc::get_mut(val).unwrap())
    }

    pub fn domains_owned(&self) -> Vec<DeclRef<DomainDecl>> {
        self.declarations
            .borrow()
            .values()
            .flat_map(|decl| match decl.as_ref() {
                DeclKind::DomainDecl(domain_ref) => Some(domain_ref.clone()),
                _ => None,
            })
            .collect()
    }

    pub fn spec_ty(&self) -> &TyKind {
        &self.spec_ty
    }

    pub fn lit_ty(&self, lit: &LitKind) -> TyKind {
        match lit {
            LitKind::Str(_) => todo!(),
            LitKind::UInt(_) => TyKind::UInt,
            LitKind::Frac(_) => TyKind::UReal,
            LitKind::Infinity => TyKind::EUReal,
            LitKind::Bool(_) => TyKind::Bool,
        }
    }
}
