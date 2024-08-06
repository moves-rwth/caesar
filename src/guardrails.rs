use std::ops::DerefMut;

use ariadne::ReportKind;

use crate::{
    ast::{
        visit::{walk_stmt, VisitorMut},
        DeclKind, DeclRef, Diagnostic, Direction, Expr, ExprKind, Ident, Label, ProcDecl, Span,
        Stmt, StmtKind,
    },
    intrinsic::annotations::{AnnotationError, AnnotationKind, Calculus},
    tyctx::TyCtx,
};

#[derive(Debug)]
pub enum UnsoundnessError {
    NotTerminator(Span, Ident),
    CalculusEncodingMismatch(Direction, Span, Ident, Ident),
    CalculusCalculusMismatch(Span, Ident, Ident),
    ProcDirectionMismatch(Direction, Direction, Span, Ident, Ident),
}

impl UnsoundnessError {
    pub fn diagnostic(self) -> Diagnostic {
        match self {
            UnsoundnessError::NotTerminator(span, encoding_name) => {
                Diagnostic::new(ReportKind::Error, span)
                    .with_message(format!(
                        "The '{}' annotation must annotate the last statement of the program.",
                        encoding_name.name
                    ))
                    .with_label(Label::new(span).with_message(
                        "There must not be any statements after this annotated statement (and the annotated statement must not be nested in a block).",
                    ))
            }
            UnsoundnessError::CalculusEncodingMismatch(direction, span, calculus_name, encoding_name ) => {
                Diagnostic::new(ReportKind::Error, span)
                    .with_message(format!(
                        "In {}s, the '{}' calculus does not support the '{}' encoding.",
                        direction.prefix("proc"), calculus_name.name, encoding_name.name
                    ))
                    .with_label(Label::new(span).with_message(
                        "The calculus, proof rule, and direction are incompatible.",
                    ))
            }
            UnsoundnessError::CalculusCalculusMismatch(span,calling_calculus,called_calculus) => {
                Diagnostic::new(ReportKind::Error, span)
                    .with_message(format!(
                        "The '{}' calculus does not match with the '{}' calculus .",
                         calling_calculus.name, called_calculus.name
                    ))
                    .with_label(Label::new(span).with_message(
                        "The calculus of the called procedure must match the calculus of the calling procedure.",
                    ))
            }
            UnsoundnessError::ProcDirectionMismatch(calling_direction,called_direction,span, calling_proc,called_proc) => {
                Diagnostic::new(ReportKind::Error, span)
                    .with_message(format!(
                        "The direction of '{} {}' does not match with the direction of the '{} {}'.",
                         calling_direction.prefix("proc"), calling_proc.name, called_direction.prefix("proc"), called_proc.name
                    ))
                    .with_label(Label::new(span).with_message(
                        "The direction of the called procedure must match the direction of the calling procedure.",
                    ))
            }
        }
    }
}

#[derive(Debug)]
pub enum GuardrailError {
    AnnotationError(AnnotationError),
    UnsoundnessError(UnsoundnessError),
}

impl GuardrailError {
    pub fn diagnostic(self) -> Diagnostic {
        match self {
            GuardrailError::AnnotationError(e) => e.diagnostic(),
            GuardrailError::UnsoundnessError(e) => e.diagnostic(),
        }
    }
}

/// Walks the AST and checks if the intent of the user results in a sound verification process and guards against falling into unsoundness.
/// Additionally it checks if the annotations are used correctly and throws errors if they are not.
/// This visitor should be used before the encoding annotations are applied to the AST, otherwise the annotations will be lost.
/// ---
/// Unsoundness can be caused by multiple factors that need to be checked e.g. annotations, direction and calculus mismatches etc.

pub struct GuardrailsVisitor<'tcx> {
    tcx: &'tcx mut TyCtx,
    direction: Option<Direction>,
    terminator_annotation: Option<Ident>,
    nesting_level: usize,
    current_proc_ident: Option<Ident>,
    calculus: Option<Calculus>,
}

impl<'tcx> GuardrailsVisitor<'tcx> {
    pub fn new(tcx: &'tcx mut TyCtx) -> Self {
        GuardrailsVisitor {
            tcx,
            direction: Option::None,
            terminator_annotation: None,
            nesting_level: 0,
            current_proc_ident: None,
            calculus: None,
        }
    }
}

impl<'tcx> VisitorMut for GuardrailsVisitor<'tcx> {
    type Err = GuardrailError;

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        if let ExprKind::Call(ref ident, _) = e.deref_mut().kind {
            if let DeclKind::ProcDecl(proc_ref) = self.tcx.get(*ident).unwrap().as_ref() {
                let proc_ref = proc_ref.clone(); // lose the reference to &mut self
                let proc = proc_ref.borrow();

                if let Some(context_direction) = &self.direction {
                    if *context_direction != proc.direction {
                        // Throw direction unsoundness mismatch error
                        return Err(GuardrailError::UnsoundnessError(
                            UnsoundnessError::ProcDirectionMismatch(
                                *context_direction,
                                proc.direction,
                                e.span,
                                self.current_proc_ident.unwrap(), // If there is a direction, there should be an ident as well
                                proc.name,
                            ),
                        ));
                    }
                }

                if let Some(context_calculus) = &self.calculus {
                    if let Some(call_calculus_ident) = proc.calculus {
                        if context_calculus.name != call_calculus_ident {
                            // Throw mismatched calculus unsoundness error
                            return Err(GuardrailError::UnsoundnessError(
                                UnsoundnessError::CalculusCalculusMismatch(
                                    e.span,
                                    context_calculus.name,
                                    call_calculus_ident,
                                ),
                            ));
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

        self.direction = Some(proc.direction);
        self.current_proc_ident = Some(proc.name);

        // If the procedure has a calculus annotation, store it as the current calculus
        if let Some(ident) = proc.calculus.as_ref() {
            match self.tcx.get(*ident) {
                Some(decl) => {
                    if let DeclKind::AnnotationDecl(AnnotationKind::Calculus(calculus)) =
                        decl.as_ref()
                    {
                        self.calculus = Some(calculus.clone());
                    }
                }
                None => {
                    return Err(GuardrailError::AnnotationError(
                        AnnotationError::UnknownAnnotation(proc.span, *ident),
                    ))
                }
            }
        }

        let mut body = proc.body.borrow_mut();
        if let Some(ref mut block) = &mut *body {
            self.visit_block(block)?;
        }

        Ok(())
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        match &mut s.node {
            // If the statement is an annotation, transform it
            StmtKind::Annotation(_, ident, _, inner_stmt) => {
                // First visit the statement that is annotated and handle inner annotations
                self.nesting_level += 1;
                self.visit_stmt(inner_stmt)?;
                self.nesting_level -= 1;

                if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(anno_ref)) =
                    self.tcx.get(*ident).unwrap().as_ref()
                {
                    if let StmtKind::While(_, _) = inner_stmt.node {
                    } else {
                        return Err(GuardrailError::AnnotationError(
                            AnnotationError::NotOnWhile(
                                s.span,
                                *ident,
                                inner_stmt.as_ref().clone(),
                            ),
                        ));
                    }

                    // A terminator annotation can't be nested in a block
                    if anno_ref.is_terminator() && self.nesting_level > 0 {
                        return Err(GuardrailError::UnsoundnessError(
                            UnsoundnessError::NotTerminator(s.span, anno_ref.name()),
                        ));
                    }

                    // Check if the calculus annotation is compatible with the encoding annotation
                    if let Some(calculus) = &self.calculus {
                        // If calculus is not allowed, return an error
                        if !anno_ref.is_calculus_allowed(
                            calculus,
                            self.direction.ok_or(GuardrailError::AnnotationError(
                                AnnotationError::NotInProcedure(s.span, *ident),
                            ))?,
                        ) {
                            return Err(GuardrailError::UnsoundnessError(
                                UnsoundnessError::CalculusEncodingMismatch(
                                    self.direction.unwrap(),
                                    s.span,
                                    calculus.name,
                                    anno_ref.name(),
                                ),
                            ));
                        };
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
                    return Err(GuardrailError::UnsoundnessError(
                        UnsoundnessError::NotTerminator(s.span, anno_name),
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
                    return Err(GuardrailError::UnsoundnessError(
                        UnsoundnessError::NotTerminator(s.span, anno_name),
                    ));
                } else {
                    walk_stmt(self, s)?
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {

    use crate::verify_test;

    #[test]
    fn test_wrong_annotation_usage() {
        // this should produce an error
        let source = r#"
            proc main() -> () {
                @invariant(1) // must be on a loop
                var x: UInt
            }
        "#;
        let res = verify_test(source).0; // should fail
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error: The proof rule `invariant` must be used on a while loop."
        );
    }

    #[test]
    fn test_calculus_mismatch() {
        // this should produce an error
        let source = r#"
            @wp
            proc wp_proc() -> () {}
            @wlp
            proc wlp_proc() -> () {
                wp_proc() // this should not be called inside a @wlp annotated procedure
            }
        "#;

        let res = verify_test(source).0.is_err();
        assert!(res);
    }

    #[test]
    fn test_correct_calculus_call() {
        let source = r#"
            @wp
            proc wp_proc() -> () {}
            @wp
            proc main() -> () {
                wp_proc() // this should be allowed
            }
        "#;
        let res = verify_test(source).0.is_ok();
        assert!(res);
    }

    #[test]
    fn test_missing_calculus_call() {
        let source = r#"
            
            proc default_proc() -> () {}

            @wp
            proc wp_proc() -> () {
                default_proc() // this should be allowed
            }
        "#;
        let res = verify_test(source).0.is_ok();
        assert!(res);
    }

    #[test]
    fn test_proc_direction_mismatch() {
        // this should produce an error
        let source = r#"
            
            coproc test1() -> () {}
            
            proc test2() -> () {
                test1() // a coproc is being called from a proc
            }
        "#;
        let res = verify_test(source).0.is_err();
        assert!(res);
    }

    #[test]
    fn test_calculus_encoding_mismatch() {
        // this should produce an error
        let source = r#"
            @wp
            proc main() -> () {
                var x: UInt
                @invariant(x) // invariant encoding within wp reasoning is not sound!
                while 1 <= x {
                    x = x - 1
                }
            }
        "#;
        let res = verify_test(source).0.is_err();
        assert!(res);
    }
}
