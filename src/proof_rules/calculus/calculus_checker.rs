use std::{collections::HashMap, ops::DerefMut};

use crate::{
    ast::{
        visit::{walk_stmt, VisitorMut},
        DeclKind, DeclRef, Diagnostic, Expr, ExprKind, Ident, ProcDecl, Stmt, StmtKind,
    },
    intrinsic::annotations::{
        AnnotationError, AnnotationKind, AnnotationUnsoundnessError, Calculus,
    },
    proof_rules::ProcContext,
    tyctx::TyCtx,
};

use super::RecursiveProcBlame;

/// Walk the AST and check the rules of calculus annotations. For more information about the rules, see <https://www.caesarverifier.org/docs/proof-rules/calculi>
pub struct CalculusVisitor<'tcx> {
    tcx: &'tcx mut TyCtx,
    /// The set of recursive procedures along with the blame information for generating error messages
    recursive_procs: HashMap<Ident, RecursiveProcBlame>,
    proc_context: Option<ProcContext>, // The relevant context of the current procedure being visited for soundness
}

impl<'tcx> CalculusVisitor<'tcx> {
    pub fn new(tcx: &'tcx mut TyCtx, recursive_procs: HashMap<Ident, RecursiveProcBlame>) -> Self {
        CalculusVisitor {
            tcx,
            recursive_procs,
            proc_context: None,
        }
    }
}

/// Errors that can occur during the checking of calculus annotation rules.
/// AnnotationErrors are thrown when the usage of an annotation is incorrect (e.g. not on a while loop, not in a procedure, etc.)
/// UnsoundnessError are thrown when the usage of an annotation is unsound (e.g. mismatched calculus )
#[derive(Debug)]
pub enum CalculusVisitorError {
    AnnotationError(AnnotationError),
    UnsoundnessError(AnnotationUnsoundnessError),
}

impl CalculusVisitorError {
    pub fn diagnostic(self) -> Diagnostic {
        match self {
            CalculusVisitorError::AnnotationError(err) => err.diagnostic(),
            CalculusVisitorError::UnsoundnessError(err) => err.diagnostic(),
        }
    }
}

impl<'tcx> VisitorMut for CalculusVisitor<'tcx> {
    type Err = CalculusVisitorError;

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
                                return Err(CalculusVisitorError::UnsoundnessError(
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
                    return Err(CalculusVisitorError::AnnotationError(
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
            // If induction is not allowed, check whether the procedure has a recursive call
            if !calculus.calculus_type.is_induction_allowed(proc.direction)
                && self.recursive_procs.contains_key(&proc.name)
            {
                return Err(CalculusVisitorError::UnsoundnessError(
                    AnnotationUnsoundnessError::UnsoundRecursion {
                        direction: proc.direction,
                        calculus_name: calculus.name,
                        blame: *self.recursive_procs.get(&proc.name).unwrap(),
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
        let res = {
            if let Some(ref mut block) = &mut *body {
                self.visit_block(block)
            } else {
                Ok(())
            }
        };
        // Reset the context
        self.proc_context = None;

        res
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        match &mut s.node {
            // If the statement is an annotation, transform it
            StmtKind::Annotation(_, ident, _, inner_stmt) => {
                // First visit the statement that is annotated and handle inner annotations
                self.visit_stmt(inner_stmt)?;

                if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(anno_ref)) =
                    self.tcx.get(*ident).unwrap().as_ref()
                {
                    // Try to get the current procedure context
                    let proc_context = self
                        .proc_context
                        .as_ref()
                        // If there is no procedure context, throw an error
                        .ok_or(CalculusVisitorError::AnnotationError(
                            AnnotationError::NotInProcedure {
                                span: s.span,
                                annotation_name: *ident,
                            },
                        ))?;

                    // Unpack the current procedure context
                    let direction = proc_context.direction;

                    // Check if the calculus annotation is compatible with the encoding annotation
                    if let Some(calculus) = proc_context.calculus {
                        // If calculus is not allowed, return an error
                        if !anno_ref.is_calculus_allowed(calculus, direction) {
                            return Err(CalculusVisitorError::UnsoundnessError(
                                AnnotationUnsoundnessError::CalculusEncodingMismatch {
                                    direction,
                                    span: s.span,
                                    calculus_name: calculus.name,
                                    enc_name: anno_ref.name(),
                                },
                            ));
                        };
                    }
                }
            }
            _ => walk_stmt(self, s)?,
        }
        Ok(())
    }
}
