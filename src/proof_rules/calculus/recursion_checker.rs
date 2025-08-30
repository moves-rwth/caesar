use std::{collections::HashMap, ops::DerefMut};

use petgraph::{graph::NodeIndex, visit::EdgeRef};

use crate::{
    ast::{visit::VisitorMut, DeclKind, DeclRef, Expr, ExprKind, Ident, ProcDecl, Span},
    driver::front::{Module, SourceUnit},
    tyctx::TyCtx,
};

/// A struct that contains the information about a recursive procedure.
#[derive(Debug, Copy, Clone)]
pub struct RecursiveProcBlame {
    /// The span of the 'recursive' call that might lead to the recursion
    pub call_span: Span,
    /// The name of the directly called procedure
    pub called_proc_name: Ident,
    /// The name of the first recursive procedure that can be reached from the call
    /// (i.e. the first procedure that is part of a cycle)
    pub recursive_proc_name: Ident,
}

/// A visitor that generates a call graph of the procedures in the program.
/// The call graph is represented as a directed graph where the nodes are the procedure names
/// and the directed edges are the calls between procedures.
/// The edges are also annotated with the span of the call expression.
/// The direction of the edge is from the callee to the caller.
pub struct CallGraphVisitor<'tcx> {
    tcx: &'tcx mut TyCtx,
    current_proc: Option<Ident>,
    graph: petgraph::graph::DiGraph<Ident, Span>,
    node_indices: std::collections::HashMap<Ident, petgraph::graph::NodeIndex>, // map of proc name to node index
}

impl<'tcx> CallGraphVisitor<'tcx> {
    pub fn new(tcx: &'tcx mut TyCtx) -> Self {
        CallGraphVisitor {
            tcx,
            current_proc: None,
            graph: petgraph::graph::DiGraph::new(),
            node_indices: std::collections::HashMap::new(),
        }
    }

    fn get_node(&mut self, ident: Ident) -> NodeIndex {
        *self
            .node_indices
            .entry(ident)
            .or_insert_with(|| self.graph.add_node(ident))
    }
}

impl VisitorMut for CallGraphVisitor<'_> {
    type Err = ();

    fn visit_proc(&mut self, proc_ref: &mut DeclRef<ProcDecl>) -> Result<(), Self::Err> {
        let proc_ref = proc_ref.clone(); // lose the reference to &mut self
        let proc = proc_ref.borrow();

        self.current_proc = Some(proc.name);

        // Visit the body of the procedure.
        let mut body = proc.body.borrow_mut();
        let res = {
            if let Some(ref mut block) = &mut *body {
                self.visit_block(block)
            } else {
                Ok(())
            }
        };
        // Reset the current procedure.
        self.current_proc = None;
        res
    }

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        if let ExprKind::Call(ref ident, _) = e.deref_mut().kind {
            if let DeclKind::ProcDecl(proc_ref) = self.tcx.get(*ident).unwrap().as_ref() {
                let proc_name = proc_ref.borrow().name;

                let Some(current_proc_ident) = self.current_proc else {
                    return Ok(());
                };

                let from_index = self.get_node(proc_name);
                let to_index = self.get_node(current_proc_ident);
                // Note that the direction of the edge is from the callee to the caller!
                self.graph.add_edge(from_index, to_index, e.span);
            }
        }
        Ok(())
    }
}

/// Generate the call graph of the procedures in the program with the ['CallGraphVisitor'].
fn generate_call_graph(
    tcx: &mut TyCtx,
    module: &mut Module,
) -> petgraph::graph::DiGraph<Ident, Span> {
    let mut visitor = CallGraphVisitor::new(tcx);
    // Generate the call graph
    for source_unit in &mut module.items {
        let mut source_unit = source_unit.enter_mut();
        match *source_unit {
            SourceUnit::Decl(ref mut decl) => {
                // only register procs since we do not check any other decls
                if let DeclKind::ProcDecl(proc_decl) = decl {
                    visitor.visit_proc(proc_decl).unwrap();
                }
            }
            SourceUnit::Raw(_) => {}
        }
    }
    visitor.graph
}

/// Find (co)procs that have a (co)proc call in their body that might effectively result in a recursion by reaching itself.
/// This analysis is done by generating a call graph of the procedures in the program and checking which (co)procs are part of a cycle
/// The function returns a map of the recursive procedures and the information about which call and (co)proc to blame for the recursion.
pub fn find_recursive_procs(
    tcx: &mut TyCtx,
    module: &mut Module,
) -> HashMap<Ident, RecursiveProcBlame> {
    let call_graph = generate_call_graph(tcx, module);

    // Find SCCs in the call graph
    let sccs = petgraph::algo::tarjan_scc(&call_graph);

    // Mark the components that are cyclic
    let mut recursive_procs = HashMap::new();

    for scc in sccs {
        // If the SCC has more than one node, it is cyclic
        // Or if the SCC has only one node and it has a self-loop, it is cyclic
        if scc.len() > 1 || call_graph.contains_edge(scc[0], scc[0]) {
            for node_index in &scc {
                for edge in call_graph.edges(*node_index) {
                    let neighbor = edge.target();
                    let neighbor_ident = call_graph[neighbor];

                    // If the neighbor is in the same SCC and is not already in the recursive_procs map,
                    if scc.contains(&neighbor) && !recursive_procs.contains_key(&neighbor_ident) {
                        // Add the span of the recursive call to the map with the caller procs name
                        recursive_procs.insert(
                            neighbor_ident,
                            RecursiveProcBlame {
                                call_span: *edge.weight(),
                                called_proc_name: call_graph[*node_index],
                                recursive_proc_name: neighbor_ident,
                            },
                        );
                    }
                }
            }
        }
    }

    recursive_procs
}
