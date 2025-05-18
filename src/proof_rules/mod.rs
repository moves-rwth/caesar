//! This module provides annotations that encode proof rules and their desugaring transformations.

mod induction;
pub mod negations;
pub use induction::*;
mod unroll;
pub use unroll::*;
mod mciver_ast;
use mciver_ast::*;
mod omega;
use omega::*;
mod ost;
use ost::*;
mod past;
use past::*;
mod util;
pub use util::*;

#[cfg(test)]
mod tests;

use std::{any::Any, collections::HashMap, fmt, ops::DerefMut, rc::Rc};

use petgraph::visit::EdgeRef;

use crate::{
    ast::{
        visit::{walk_stmt, VisitorMut},
        Block, DeclKind, DeclRef, Diagnostic, Direction, Expr, ExprKind, Files, Ident, Param,
        ProcDecl, ProcSpec, SourceFilePath, Span, Stmt, StmtKind,
    },
    driver::{Item, SourceUnit},
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{
        AnnotationError, AnnotationKind, AnnotationUnsoundnessError, Calculus,
    },
    tyctx::TyCtx,
};

/// The necessary information for generating new procedure declarations e.g. during the transformation of an encoding annotation
pub struct ProcInfo {
    name: String,
    inputs: Vec<Param>,
    outputs: Vec<Param>,
    spec: Vec<ProcSpec>,
    body: Block,
    direction: Direction,
}

/// The result of transforming an annotation call, it can contain generated statements and declarations
pub struct EncodingGenerated {
    block: Block,
    decls: Option<Vec<DeclKind>>,
}

/// The environment information when the encoding annotation is called
pub struct EncodingEnvironment {
    pub base_proc_ident: Ident,
    pub stmt_span: Span,
    pub call_span: Span,
    pub direction: Direction,
}

/// The trait that all encoding annotations must implement
pub trait Encoding: fmt::Debug {
    fn name(&self) -> Ident;

    /// Resolve the arguments of the annotation call
    fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError>;

    /// Typecheck the arguments of the annotation call
    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), TycheckError>;

    /// Transform the annotated loop into a sequence of statements and declarations
    fn transform(
        &self,
        tyctx: &TyCtx,
        args: &[Expr],
        inner_stmt: &Stmt,
        enc_env: EncodingEnvironment,
    ) -> Result<EncodingGenerated, AnnotationError>;

    /// Check if the given calculus annotation is compatible with the encoding annotation
    fn is_calculus_allowed(&self, calculus: Calculus, direction: Direction) -> bool;

    /// Indicates if the encoding annotation is required to be the last statement of a procedure
    fn is_terminator(&self) -> bool;

    /// Return an [`Any`] reference for this encoding.
    fn as_any(&self) -> &dyn Any;
}

/// Initialize all intrinsic annotations by declaring them
pub fn init_encodings(files: &mut Files, tcx: &mut TyCtx) {
    let invariant = AnnotationKind::Encoding(Rc::new(InvariantAnnotation::new(tcx, files)));
    tcx.add_global(invariant.name());
    tcx.declare(DeclKind::AnnotationDecl(invariant));

    let k_ind = AnnotationKind::Encoding(Rc::new(KIndAnnotation::new(tcx, files)));
    tcx.add_global(k_ind.name());
    tcx.declare(DeclKind::AnnotationDecl(k_ind));

    let bmc = AnnotationKind::Encoding(Rc::new(UnrollAnnotation::new(tcx, files)));
    tcx.add_global(bmc.name());
    tcx.declare(DeclKind::AnnotationDecl(bmc));

    let omega_inv = AnnotationKind::Encoding(Rc::new(OmegaInvAnnotation::new(tcx, files)));
    tcx.add_global(omega_inv.name());
    tcx.declare(DeclKind::AnnotationDecl(omega_inv));

    let ost = AnnotationKind::Encoding(Rc::new(OSTAnnotation::new(tcx, files)));
    tcx.add_global(ost.name());
    tcx.declare(DeclKind::AnnotationDecl(ost));

    let past = AnnotationKind::Encoding(Rc::new(PASTAnnotation::new(tcx, files)));
    tcx.add_global(past.name());
    tcx.declare(DeclKind::AnnotationDecl(past));

    let ast = AnnotationKind::Encoding(Rc::new(ASTAnnotation::new(tcx, files)));
    tcx.add_global(ast.name());
    tcx.declare(DeclKind::AnnotationDecl(ast));
}

struct ProcContext {
    name: Ident,
    direction: Direction,
    calculus: Option<Calculus>,
}

/// Walks the AST and transforms encoding annotations into their desugared form.
/// Correct and sound usage of the encoding annotations are also checked during this process.
pub struct EncodingVisitor<'tcx, 'sunit> {
    tcx: &'tcx mut TyCtx,
    source_units_buf: &'sunit mut Vec<Item<SourceUnit>>,
    /// The set of looping procedures along with the spans of their looping calls
    looping_procs: HashMap<Ident, LoopingProcBlame>,
    terminator_annotation: Option<Ident>, // The name of the terminator annotation if there is one
    nesting_level: usize,
    proc_context: Option<ProcContext>, // The relevant context of the current procedure being visited for soundness
}

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

impl<'tcx, 'sunit> EncodingVisitor<'tcx, 'sunit> {
    pub fn new(
        tcx: &'tcx mut TyCtx,
        source_units_buf: &'sunit mut Vec<Item<SourceUnit>>,
        looping_procs: HashMap<Ident, LoopingProcBlame>,
    ) -> Self {
        EncodingVisitor {
            tcx,
            source_units_buf,
            looping_procs,
            terminator_annotation: None,
            nesting_level: 0,
            proc_context: None,
        }
    }
}

/// Errors that can occur during the transformation of encoding annotations
/// AnnotationErrors are thrown when the usage of an annotation is incorrect (e.g. not on a while loop, not in a procedure, etc.)
/// UnsoundnessError are thrown when the usage of an annotation is unsound (e.g. mismatched calculus, not a terminator, etc.)
#[derive(Debug)]
pub enum EncodingVisitorError {
    AnnotationError(AnnotationError),
    UnsoundnessError(AnnotationUnsoundnessError),
}

impl EncodingVisitorError {
    pub fn diagnostic(self) -> Diagnostic {
        match self {
            EncodingVisitorError::AnnotationError(err) => err.diagnostic(),
            EncodingVisitorError::UnsoundnessError(err) => err.diagnostic(),
        }
    }
}

impl<'tcx, 'sunit> VisitorMut for EncodingVisitor<'tcx, 'sunit> {
    type Err = EncodingVisitorError;

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        if let ExprKind::Call(ref ident, _) = e.deref_mut().kind {
            if let DeclKind::ProcDecl(proc_ref) = self.tcx.get(*ident).unwrap().as_ref() {
                let proc_ref = proc_ref.clone(); // lose the reference to &mut self
                let proc = proc_ref.borrow();

                if let Some(proc_context) = &self.proc_context {
                    if let Some(context_calculus) = proc_context.calculus {
                        if let Some(call_calculus_ident) = proc.calculus {
                            if context_calculus.name != call_calculus_ident {
                                // Throw mismatched calculus unsoundness error
                                return Err(EncodingVisitorError::UnsoundnessError(
                                    AnnotationUnsoundnessError::CalculusCallMismatch {
                                        span: e.span,
                                        context_calculus: context_calculus.name,
                                        call_calculus: call_calculus_ident,
                                    },
                                ));
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn visit_proc(&mut self, proc_ref: &mut DeclRef<ProcDecl>) -> Result<(), Self::Err> {
        let proc_ref = proc_ref.clone(); // lose the reference to &mut self
        let proc = proc_ref.borrow();

        let mut curr_calculus: Option<Calculus> = None;
        // If the procedure has a calculus annotation, store it as the current calculus
        if let Some(ident) = proc.calculus.as_ref() {
            match self.tcx.get(*ident) {
                Some(decl) => {
                    if let DeclKind::AnnotationDecl(AnnotationKind::Calculus(calculus)) =
                        decl.as_ref()
                    {
                        curr_calculus = Some(*calculus);
                    }
                }
                None => {
                    // If there isn't any calculus declaration that matches the annotation, throw an error
                    return Err(EncodingVisitorError::AnnotationError(
                        AnnotationError::UnknownAnnotation {
                            span: proc.span,
                            annotation_name: *ident,
                        },
                    ));
                }
            }
        }

        // If the procedure has a calculus annotation, check the call graph for cycles
        if let Some(calculus) = curr_calculus {
            // If induction is not allowed, check whether the procedure has a looping call
            if !calculus.calculus_type.is_induction_allowed(proc.direction)
                && self.looping_procs.contains_key(&proc.name)
            {
                return Err(EncodingVisitorError::UnsoundnessError(
                    AnnotationUnsoundnessError::UnsoundRecursion {
                        direction: proc.direction,
                        calculus_name: calculus.name,
                        blame: *self.looping_procs.get(&proc.name).unwrap(),
                    },
                ));
            }
        }

        // Store the current procedure context
        self.proc_context = Some(ProcContext {
            name: proc.name,
            direction: proc.direction,
            calculus: curr_calculus,
        });

        let mut body = proc.body.borrow_mut();
        if let Some(ref mut block) = &mut *body {
            self.visit_block(block)?;
        }

        // Reset the context
        self.proc_context = None;

        Ok(())
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        match &mut s.node {
            // If the statement is an annotation, transform it
            StmtKind::Annotation(annotation_span, ident, inputs, inner_stmt) => {
                // First visit the statement that is annotated and handle inner annotations
                self.nesting_level += 1;
                self.visit_stmt(inner_stmt)?;
                self.nesting_level -= 1;

                if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(anno_ref)) =
                    self.tcx.get(*ident).unwrap().as_ref()
                {
                    // Try to get the current procedure context
                    let proc_context = self
                        .proc_context
                        .as_ref()
                        // If there is no procedure context, throw an error
                        .ok_or(EncodingVisitorError::AnnotationError(
                            AnnotationError::NotInProcedure {
                                span: s.span,
                                annotation_name: *ident,
                            },
                        ))?;

                    // Unpack the current procedure context
                    let direction = proc_context.direction;
                    let base_proc_ident = proc_context.name;

                    // Check whether the calculus annotation is actually on a while loop (annotations can only be on while loops)
                    if let StmtKind::While(_, _) = inner_stmt.node {
                    } else {
                        return Err(EncodingVisitorError::AnnotationError(
                            AnnotationError::NotOnWhile {
                                span: *annotation_span,
                                annotation_name: *ident,
                                annotated: Box::new(inner_stmt.as_ref().clone()),
                            },
                        ));
                    }

                    // A terminator annotation can't be nested in a block
                    if anno_ref.is_terminator() && self.nesting_level > 0 {
                        return Err(EncodingVisitorError::UnsoundnessError(
                            AnnotationUnsoundnessError::NotTerminator {
                                span: s.span,
                                enc_name: anno_ref.name(),
                            },
                        ));
                    }

                    // Check if the calculus annotation is compatible with the encoding annotation
                    if let Some(calculus) = proc_context.calculus {
                        // If calculus is not allowed, return an error
                        if !anno_ref.is_calculus_allowed(calculus, direction) {
                            return Err(EncodingVisitorError::UnsoundnessError(
                                AnnotationUnsoundnessError::CalculusEncodingMismatch {
                                    direction,
                                    span: s.span,
                                    calculus_name: calculus.name,
                                    enc_name: anno_ref.name(),
                                },
                            ));
                        };
                    }

                    let enc_env = EncodingEnvironment {
                        base_proc_ident,
                        stmt_span: s.span,
                        call_span: *annotation_span, // TODO: if I change this to stmt_span, explain core vc works :(
                        direction,
                    };

                    // Generate new statements (and declarations) from the annotated loop
                    let mut enc_gen = anno_ref
                        .transform(self.tcx, inputs, inner_stmt, enc_env)
                        .map_err(EncodingVisitorError::AnnotationError)?;

                    // Visit generated statements
                    self.visit_block(&mut enc_gen.block)?;

                    // Replace the annotated loop with the generated statements
                    s.span = enc_gen.block.span;
                    s.node = StmtKind::Seq(enc_gen.block.node);

                    // Add the generated declarations to the list of source units of the compilation unit
                    if let Some(ref mut decls) = enc_gen.decls {
                        // Visit generated declarations
                        // Save the current context and reset it after visiting the declarations
                        let temp = self.proc_context.take();
                        self.visit_decls(decls)?;
                        self.proc_context = temp;

                        // Wrap generated declarations in items
                        let items: Vec<Item<SourceUnit>> = decls
                            .iter_mut()
                            .map(|decl| {
                                SourceUnit::Decl(decl.to_owned())
                                    .wrap_item(&SourceFilePath::Generated)
                            })
                            .collect();

                        self.source_units_buf.extend(items)
                    }

                    // Check if the annotation is a terminator annotation and set the flag
                    if anno_ref.is_terminator() {
                        self.terminator_annotation = Some(anno_ref.name());
                    }
                }
            }

            // If the statement is a block, increase the nesting level and walk the block
            StmtKind::If(_, _, _)
            | StmtKind::Angelic(_, _)
            | StmtKind::Demonic(_, _)
            | StmtKind::Seq(_) => {
                if let Some(anno_name) = self.terminator_annotation {
                    return Err(EncodingVisitorError::UnsoundnessError(
                        AnnotationUnsoundnessError::NotTerminator {
                            span: s.span,
                            enc_name: anno_name,
                        },
                    ));
                } else {
                    self.nesting_level += 1;
                    walk_stmt(self, s)?;
                    self.nesting_level -= 1;
                }
            }
            _ => {
                // If there was a terminator annotation before, don't allow further statements
                if let Some(anno_name) = self.terminator_annotation {
                    return Err(EncodingVisitorError::UnsoundnessError(
                        AnnotationUnsoundnessError::NotTerminator {
                            span: s.span,
                            enc_name: anno_name,
                        },
                    ));
                } else {
                    walk_stmt(self, s)?
                }
            }
        }
        Ok(())
    }
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
