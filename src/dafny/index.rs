use regex::Regex;

use crate::{
    ast::{
        AxiomDecl, DeclKind, DeclRef, DomainDecl, DomainSpec, FileId, FuncDecl, Ident, ProcDecl,
    },
    driver::{
        front::{Module, SourceUnit},
        item::SourceUnitName,
    },
};

/// A flattened reference to one declaration that may appear in an emitted file.
#[derive(Clone)]
pub(crate) enum FlatDeclRef {
    Proc(DeclRef<ProcDecl>),
    Domain(DeclRef<DomainDecl>),
    Func(DeclRef<FuncDecl>),
    Axiom(DeclRef<AxiomDecl>),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum FlatDeclKind {
    Proc,
    Domain,
    Func,
    Axiom,
}

/// Metadata used to group and order declarations during file emission.
#[derive(Clone)]
pub(crate) struct FlatDeclRecord {
    pub(crate) ident: Ident,
    pub(crate) file_id: FileId,
    pub(crate) kind: FlatDeclKind,
    pub(crate) decl: FlatDeclRef,
    pub(crate) source_name: Option<SourceUnitName>,
}

/// Lookup table from identifiers to the flattened declaration order used by the backend.
pub(crate) struct DeclIndex {
    pub(crate) ordered: Vec<FlatDeclRecord>,
    by_ident: std::collections::HashMap<Ident, usize>,
}

impl DeclIndex {
    /// Collect top-level and domain-nested declarations into a single stable order.
    pub(crate) fn new(module: &Module) -> Self {
        let mut ordered = Vec::new();
        let mut by_ident = std::collections::HashMap::new();

        for item in &module.items {
            match &**item {
                SourceUnit::Decl(DeclKind::ProcDecl(proc_ref)) => {
                    let record = FlatDeclRecord {
                        ident: proc_ref.borrow().name,
                        file_id: proc_ref.borrow().span.file,
                        kind: FlatDeclKind::Proc,
                        decl: FlatDeclRef::Proc(proc_ref.clone()),
                        source_name: Some(item.name().clone()),
                    };
                    by_ident.insert(record.ident, ordered.len());
                    ordered.push(record);
                }
                SourceUnit::Decl(DeclKind::DomainDecl(domain_ref)) => {
                    let domain = domain_ref.borrow();
                    let file_id = domain.span.file;
                    let record = FlatDeclRecord {
                        ident: domain.name,
                        file_id,
                        kind: FlatDeclKind::Domain,
                        decl: FlatDeclRef::Domain(domain_ref.clone()),
                        source_name: None,
                    };
                    by_ident.insert(record.ident, ordered.len());
                    ordered.push(record);

                    for spec in &domain.body {
                        let record = match spec {
                            DomainSpec::Function(func_ref) => FlatDeclRecord {
                                ident: func_ref.borrow().name,
                                file_id,
                                kind: FlatDeclKind::Func,
                                decl: FlatDeclRef::Func(func_ref.clone()),
                                source_name: None,
                            },
                            DomainSpec::Axiom(axiom_ref) => FlatDeclRecord {
                                ident: axiom_ref.borrow().name,
                                file_id,
                                kind: FlatDeclKind::Axiom,
                                decl: FlatDeclRef::Axiom(axiom_ref.clone()),
                                source_name: None,
                            },
                        };
                        by_ident.insert(record.ident, ordered.len());
                        ordered.push(record);
                    }
                }
                SourceUnit::Decl(DeclKind::FuncDecl(func_ref)) => {
                    let record = FlatDeclRecord {
                        ident: func_ref.borrow().name,
                        file_id: func_ref.borrow().span.file,
                        kind: FlatDeclKind::Func,
                        decl: FlatDeclRef::Func(func_ref.clone()),
                        source_name: None,
                    };
                    by_ident.insert(record.ident, ordered.len());
                    ordered.push(record);
                }
                SourceUnit::Decl(DeclKind::AxiomDecl(axiom_ref)) => {
                    let record = FlatDeclRecord {
                        ident: axiom_ref.borrow().name,
                        file_id: axiom_ref.borrow().span.file,
                        kind: FlatDeclKind::Axiom,
                        decl: FlatDeclRef::Axiom(axiom_ref.clone()),
                        source_name: None,
                    };
                    by_ident.insert(record.ident, ordered.len());
                    ordered.push(record);
                }
                SourceUnit::Decl(_) | SourceUnit::Raw(_) => {}
            }
        }

        DeclIndex { ordered, by_ident }
    }

    pub(crate) fn get(&self, ident: Ident) -> Option<&FlatDeclRecord> {
        self.by_ident.get(&ident).map(|index| &self.ordered[*index])
    }

    /// Return the selected top-level `proc` roots defined in one source file.
    pub(crate) fn selected_roots_for_file(
        &self,
        file_id: FileId,
        filter: Option<&Regex>,
    ) -> Vec<Ident> {
        self.ordered
            .iter()
            .filter(|record| {
                record.kind == FlatDeclKind::Proc
                    && record.file_id == file_id
                    && record
                        .source_name
                        .as_ref()
                        .map(|name| filter.is_none_or(|regex| regex.is_match(&name.to_string())))
                        .unwrap_or(false)
            })
            .map(|record| record.ident)
            .collect()
    }
}
