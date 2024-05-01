//! Encode the proof for refuting a lower/upper bound of an expectation of a loop by unrolling the loop k times
//!
//! @unroll takes the arguments:
//!
//! - `k`: the number of times the loop will be unrolled
//! - `terminator`: the terminator of the loop

use std::fmt;

use crate::{
    ast::{
        visit::VisitorMut, Direction, Expr, ExprKind, Files, Ident, SourceFilePath, Span, Spanned,
        Stmt, Symbol, TyKind,
    },
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{
        check_annotation_call, AnnotationDecl, AnnotationError, Calculus, CalculusType,
    },
    tyctx::TyCtx,
};

use super::{Encoding, EncodingEnvironment, EncodingGenerated};

use super::util::*;

pub struct UnrollAnnotation(AnnotationDecl);

impl UnrollAnnotation {
    pub fn new(_tcx: &mut TyCtx, files: &mut Files) -> Self {
        let file = files.add(SourceFilePath::Builtin, "unroll".to_string()).id;

        // TODO: replace the dummy span with a proper span
        let name = Ident::with_dummy_file_span(Symbol::intern("unroll"), file);

        let k_param = intrinsic_param(file, "k", TyKind::UInt, true);
        let invariant_param = intrinsic_param(file, "terminator", TyKind::SpecTy, false);

        let anno_decl = AnnotationDecl {
            name,
            inputs: Spanned::with_dummy_file_span(vec![k_param, invariant_param], file),
            span: Span::dummy_file_span(file),
        };

        UnrollAnnotation(anno_decl)
    }
}

impl fmt::Debug for UnrollAnnotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("UnrollAnnotation")
            .field("annotation", &self.0)
            .finish()
    }
}

impl Encoding for UnrollAnnotation {
    fn name(&self) -> Ident {
        self.0.name
    }

    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), TycheckError> {
        check_annotation_call(tycheck, call_span, &self.0, args)?;
        Ok(())
    }

    fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        _call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError> {
        let [k, invariant] = mut_two_args(args);
        resolve.visit_expr(k)?;
        resolve.visit_expr(invariant)
    }

    fn is_calculus_allowed(&self, calculus: &Calculus, direction: Direction) -> bool {
        matches!(
            (&calculus.calculus_type, direction),
            (CalculusType::Wp | CalculusType::Ert, Direction::Down)
                | (CalculusType::Wlp, Direction::Up)
        )
    }

    fn transform(
        &self,
        tcx: &TyCtx,
        args: &[Expr],
        inner_stmt: &Stmt,
        enc_env: EncodingEnvironment,
    ) -> Result<EncodingGenerated, AnnotationError> {
        // Unpack values from struct
        let annotation_span = enc_env.annotation_span;
        let direction = enc_env.direction;

        let [k, terminator] = two_args(args);

        let k: u128 = lit_u128(k);

        if let ExprKind::Lit(lit) = &terminator.kind {
            match direction {
                Direction::Down => {
                    if !lit.node.is_top() {
                        tracing::warn!("Top terminator is not used with down direction!");
                    }
                }
                Direction::Up => {
                    if !lit.node.is_bot() {
                        tracing::warn!("Bottom terminator is not used with up direction!");
                    }
                }
            }
        }

        // Extend the loop k times without asserts (unlike k-induction) because bmc flag is set
        let buf = encode_unroll(
            annotation_span,
            inner_stmt,
            k,
            hey_const(annotation_span, terminator, direction, tcx),
        );

        Ok(EncodingGenerated {
            span: annotation_span,
            stmts: buf,
            decls: None,
        })
    }

    fn is_terminator(&self) -> bool {
        false
    }
}
