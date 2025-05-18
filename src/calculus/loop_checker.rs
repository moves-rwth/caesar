use std::{collections::HashMap, ops::DerefMut};

use petgraph::visit::EdgeRef;

use crate::{
    ast::{visit::VisitorMut, DeclKind, DeclRef, Expr, ExprKind, Ident, ProcDecl, Span},
    driver::{Item, SourceUnit},
    tyctx::TyCtx,
};

/// A struct that contains the information about a looping procedure.
#[derive(Debug, Copy, Clone)]
pub struct LoopingProcBlame {
    /// The span of the 'looping' call that might lead to the recursion
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
/// The direction of the edge is from the callee to the caller to simplify our algorithm to find looping procs.
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
                let proc_ref = proc_ref.clone(); // lose the reference to &mut self
                let proc = proc_ref.borrow();

                let Some(current_proc_ident) = self.current_proc else {
                    return Ok(());
                };

                let to_index = *self
                    .node_indices
                    .entry(current_proc_ident)
                    .or_insert_with(|| self.graph.add_node(current_proc_ident));

                let from_index = *self
                    .node_indices
                    .entry(proc.name)
                    .or_insert_with(|| self.graph.add_node(proc.name));

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
    source_units: &mut Vec<Item<SourceUnit>>,
) -> petgraph::graph::DiGraph<Ident, Span> {
    let mut visitor = CallGraphVisitor::new(tcx);
    // Generate the call graph
    for source_unit in source_units {
        let mut source_unit = source_unit.enter();
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

/// Find (co)procs that have a (co)proc call in their body that might effectively result in a loop by reaching to a recursive (co)proc.
/// This analysis is done by generating a call graph of the procedures in the program and checking which (co)procs can reach to a cycle.
/// The function returns a map of the 'looping' procedures and the information about which call and (co)proc to blame for the recursion.
pub fn find_looping_procs(
    tcx: &mut TyCtx,
    source_units: &mut Vec<Item<SourceUnit>>,
) -> HashMap<Ident, LoopingProcBlame> {
    let call_graph = generate_call_graph(tcx, source_units);

    // Find SCCs in the call graph
    let sccs = petgraph::algo::tarjan_scc(&call_graph);

    // Mark the components that are cyclic
    let mut looping_procs = HashMap::new();

    for scc in sccs {
        // If the SCC has more than one node, it is cyclic
        // Or if the SCC has only one node and it has a self-loop, it is cyclic
        if scc.len() > 1 || call_graph.contains_edge(scc[0], scc[0]) {
            // Do a DFS to find all the nodes that are reachable from the cyclic SCC

            // The DFS here is unconventional: we do not immediately add the starting node to the 'looping_procs' map.
            // Instead, we push its neighbors onto the stack and only add a node to the map when we reach it via a neighbor.
            //
            // This approach allows us to record the span of the call that actually leads to recursion. (Note that the edges are directed from the callee to the caller.)
            // Since the starting node is part of a cyclic strongly connected component,
            // it will eventually be reached from one of its neighbors, at which point we can associate it with the span of the recursive call.
            // If we added it to the map immediately, we would not know which call led to the recursion.

            let mut stack = vec![scc[0]];
            let mut first_reachable_recursive_proc = call_graph[scc[0]];
            while let Some(node_index) = stack.pop() {
                // Track the last seen node from the same SCC to be able to deduce the first reachable recursive proc from any looping proc
                if scc.contains(&node_index) {
                    first_reachable_recursive_proc = call_graph[node_index];
                }

                for edge in call_graph.edges(node_index) {
                    let neighbor = edge.target();
                    let neighbor_ident = call_graph[neighbor];
                    if looping_procs.contains_key(&neighbor_ident) {
                        // If the neighbor is already in the map, skip it
                        continue;
                    }
                    // Add the span of the recursive call to the map with the caller procs name
                    looping_procs.insert(
                        neighbor_ident,
                        LoopingProcBlame {
                            call_span: *edge.weight(),
                            called_proc_name: call_graph[node_index],
                            recursive_proc_name: first_reachable_recursive_proc,
                        },
                    );
                    stack.push(neighbor);
                }
            }
        }
    }

    looping_procs
}
