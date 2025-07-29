use std::collections::{HashMap, HashSet};

use ariadne::ReportKind;

use crate::ast::{
    visit::{walk_expr, walk_func, walk_proc, walk_ty, VisitorMut},
    AxiomDecl, DeclRef, Diagnostic, DomainDecl, DomainSpec, Expr, ExprKind, FuncDecl, Ident, Label,
    ProcDecl, Span, TyKind,
};

/// A collection of dependencies for some declaration.
#[derive(Debug, Clone)]
pub struct Dependencies(HashSet<Ident>);

impl Dependencies {
    /// Whether this [Ident] is contained in the dependencies.
    pub fn contains(&self, ident: &Ident) -> bool {
        self.0.contains(ident)
    }
}

/// A dependency graph for procedures, domains, functions, and axioms.
/// Implements [VisitorMut] to collect dependencies as it walks the AST.
#[derive(Debug, Default)]
pub struct DepGraph {
    /// Directed edges from identifiers to their dependencies. These come from
    /// procs, domains and definitional functions.
    directed_edges: HashMap<Ident, HashSet<Ident>>,
    /// Strongly connected subgraphs. These come from axioms and functions if
    /// the function encoding is undirected.
    strongly_connected: Vec<HashSet<Ident>>,
    pub current_deps: HashSet<Ident>,
}

impl DepGraph {
    pub fn new() -> Self {
        Default::default()
    }

    /// Add the `current_deps` to the directed edges of the given `from` Ident.
    fn collect_directed_deps(&mut self, from: Ident) {
        let deps = std::mem::take(&mut self.current_deps);
        self.directed_edges.entry(from).or_default().extend(deps);
    }

    /// Collect the `current_deps` as an undirected dependency.
    fn collect_undirected_deps(&mut self, from: Ident) {
        let mut deps = std::mem::take(&mut self.current_deps);
        deps.insert(from);
        self.strongly_connected.push(deps);
    }

    /// Do a transitive closure on the dependency graph starting from the given
    /// identifiers.
    pub fn get_reachable(&self, idents: impl IntoIterator<Item = Ident>) -> Dependencies {
        let mut worklist: Vec<Ident> = idents.into_iter().collect();
        let mut reachable = HashSet::new();
        while let Some(ident) = worklist.pop() {
            let newly_inserted = reachable.insert(ident);
            if !newly_inserted {
                continue;
            }
            if let Some(deps) = self.directed_edges.get(&ident) {
                worklist.extend(deps.difference(&reachable).cloned());
            }
            // TODO: for large SCCs, we'll probably iterate them over and over
            // here. ideally, we'd process an SCC only once.
            for scc in &self.strongly_connected {
                if scc.contains(&ident) {
                    worklist.extend(scc.difference(&reachable).cloned());
                }
            }
        }
        Dependencies(reachable)
    }
}

impl VisitorMut for DepGraph {
    type Err = DepGraphError;

    fn visit_proc(&mut self, proc_ref: &mut DeclRef<ProcDecl>) -> Result<(), Self::Err> {
        assert!(self.current_deps.is_empty());
        walk_proc(self, proc_ref)?;
        self.collect_directed_deps(proc_ref.borrow().name);
        Ok(())
    }

    fn visit_domain(&mut self, domain_ref: &mut DeclRef<DomainDecl>) -> Result<(), Self::Err> {
        // instead of just using the default impl here, we carefully walk
        // through the domain and only *immutably* borrow it. otherwise, we
        // won't be able to access the domain type later on in `visit_ty` (we
        // get a borrow error at runtime).
        for spec in &domain_ref.borrow().body {
            match spec {
                DomainSpec::Function(func_ref) => {
                    self.visit_func(&mut func_ref.clone())?;
                }
                DomainSpec::Axiom(axiom_ref) => {
                    self.visit_axiom(&mut axiom_ref.clone())?;
                }
            }
        }
        Ok(())
    }

    fn visit_func(&mut self, func_ref: &mut DeclRef<FuncDecl>) -> Result<(), Self::Err> {
        assert!(self.current_deps.is_empty());
        walk_func(self, func_ref)?;
        // TODO: make undirected if function encoding is undirected
        self.collect_directed_deps(func_ref.borrow().name);
        Ok(())
    }

    fn visit_axiom(&mut self, axiom_ref: &mut DeclRef<AxiomDecl>) -> Result<(), Self::Err> {
        assert!(self.current_deps.is_empty());
        let mut decl = axiom_ref.borrow_mut();
        self.visit_ident(&mut decl.name)?;
        self.visit_expr(&mut decl.axiom)?;

        if self.current_deps.is_empty() {
            return Err(DepGraphError::AxiomNoDeps(decl.name, decl.axiom.span));
        }

        self.collect_undirected_deps(decl.name);
        Ok(())
    }

    fn visit_ty(&mut self, ty: &mut TyKind) -> Result<(), Self::Err> {
        if let TyKind::Domain(domain_ref) = ty {
            self.current_deps.insert(domain_ref.borrow().name);
        }
        walk_ty(self, ty)
    }

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        if let ExprKind::Call(name, _) = &e.kind {
            self.current_deps.insert(*name);
        }
        walk_expr(self, e)
    }
}

#[derive(Debug)]
pub enum DepGraphError {
    AxiomNoDeps(Ident, Span),
}

impl DepGraphError {
    pub fn diagnostic(&self) -> Diagnostic {
        match self {
            DepGraphError::AxiomNoDeps(ident, span) => {
                Diagnostic::new(ReportKind::Error, ident.span)
                    .with_message(format!(
                        "axiom `{ident}` must mention at least one function or domain"
                    ))
                    .with_label(
                        Label::new(*span)
                            .with_message("expression does not mention any func or domain"),
                    )
            }
        }
    }
}
