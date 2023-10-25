//! Intrinsic annotations
use std::rc::Rc;

use ariadne::ReportKind;

use crate::{
    ast::{Diagnostic, Expr, Ident, Label, Param, Span, Spanned, Stmt},
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    proof_rules::Encoding,
};

#[derive(Debug, Clone)]
pub struct AnnotationInfo {
    pub name: Ident,
    pub inputs: Spanned<Vec<Param>>,
    pub span: Span,
}

#[derive(Debug)]
pub enum AnnotationError {
    NotInProcedure(Span, Ident),
    NotOnWhile(Span, Ident, Stmt),
    WrongArgument(Span, Expr, String),
    NotTerminator(Span, Ident),
}

impl AnnotationError {
    pub fn diagnostic(self) -> Diagnostic {
        match self {
            AnnotationError::NotInProcedure(span, annotation) => {
                Diagnostic::new(ReportKind::Error, span)
                    .with_message(format!(
                        "The annotation `{}` is not in a procedure",
                        annotation
                    ))
                    .with_label(
                        Label::new(annotation.span).with_message("This should be in a procedure"),
                    )
            }
            AnnotationError::NotOnWhile(span, annotation, annotated) => {
                Diagnostic::new(ReportKind::Error, span)
                    .with_message(format!(
                        "The annotation `{}` is not on a while statement",
                        annotation
                    ))
                    .with_label(
                        Label::new(annotated.span).with_message("This should be a while statement"),
                    )
            }
            AnnotationError::WrongArgument(span, arg, message) => {
                Diagnostic::new(ReportKind::Error, span)
                    .with_message(format!("The argument {} is invalid.", arg))
                    .with_label(Label::new(arg.span).with_message(message))
            }
            AnnotationError::NotTerminator(span, encoding_name) => {
                Diagnostic::new(ReportKind::Error, span)
                    .with_message(format!(
                        "The '{}' annotation must annotate the last statement of the program.",
                        encoding_name.name
                    ))
                    .with_label(Label::new(span).with_message(
                        "There must not be any statements after this annotated statement (and the annotated statement must not be nested in a block).",
                    ))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum AnnotationKind {
    Encoding(Rc<dyn Encoding>),
}

impl AnnotationKind {
    pub fn name(&self) -> Ident {
        match self {
            AnnotationKind::Encoding(encoding) => encoding.name(),
        }
    }

    pub fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), TycheckError> {
        match self {
            AnnotationKind::Encoding(encoding) => encoding.tycheck(tycheck, call_span, args),
        }
    }

    pub fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError> {
        match self {
            AnnotationKind::Encoding(encoding) => encoding.resolve(resolve, call_span, args),
        }
    }
}

/// Typecheck annotation call
pub fn check_annotation_call(
    tycheck: &mut Tycheck<'_>,
    span: Span,
    annotation: &AnnotationInfo,
    args: &mut [Expr],
) -> Result<(), TycheckError> {
    tycheck.check_call(span, &annotation.inputs.node, args)?;
    Ok(())
}
