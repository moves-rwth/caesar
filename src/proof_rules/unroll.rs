//! Encode the proof for refuting a lower/upper bound of an expectation of a loop by unrolling the loop k times
//!
//! @unroll takes the arguments:
//!
//! - `k`: the number of times the loop will be unrolled
//! - `terminator`: the terminator of the loop

use std::{any::Any, fmt};

use crate::{
    ast::{
        util::{is_bot_lit, is_top_lit},
        visit::VisitorMut,
        Direction, Expr, Files, Ident, SourceFilePath, Span, Spanned, Stmt, Symbol, TyKind,
    },
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{
        tycheck_annotation_call, AnnotationDecl, AnnotationError, Calculus, CalculusType,
    },
    proof_rules::{calculus::ApproximationKind, FixpointSemanticsKind},
    tyctx::TyCtx,
};

use super::{
    util::{encode_unroll, hey_const, intrinsic_param, lit_u128, two_args},
    Encoding, EncodingEnvironment, GeneratedEncoding,
};

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
        tycheck_annotation_call(tycheck, call_span, &self.0, args)?;
        Ok(())
    }

    fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        _call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError> {
        resolve.visit_exprs(args)
    }

    fn is_calculus_allowed(&self, calculus: Calculus, direction: Direction) -> bool {
        matches!(
            (&calculus.calculus_type, direction),
            (CalculusType::Wp | CalculusType::Ert, Direction::Down)
                | (CalculusType::Wlp, Direction::Up)
        )
    }

    fn get_approximation(
        &self,
        fixpoint_semantics: FixpointSemanticsKind,
        inner_approximation_kind: ApproximationKind,
    ) -> ApproximationKind {
        match fixpoint_semantics {
            FixpointSemanticsKind::LeastFixedPoint => ApproximationKind::Under,
            FixpointSemanticsKind::GreatestFixedPoint => ApproximationKind::Over,
        }
        .infimum(inner_approximation_kind)
    }

    fn sound_fixpoint_semantics_kind(&self, direction: Direction) -> FixpointSemanticsKind {
        match direction {
            Direction::Up => FixpointSemanticsKind::GreatestFixedPoint,
            Direction::Down => FixpointSemanticsKind::LeastFixedPoint,
        }
    }

    fn transform(
        &self,
        tcx: &TyCtx,
        args: &[Expr],
        inner_stmt: &Stmt,
        enc_env: EncodingEnvironment,
    ) -> Result<GeneratedEncoding, AnnotationError> {
        let [k, terminator] = two_args(args);

        let k: u128 = lit_u128(k);

        // TODO: these should be warning diagnostics emitted to the user
        match enc_env.direction {
            Direction::Down => {
                if !is_top_lit(terminator) {
                    tracing::warn!("Unrolling terminator is not top element (down direction)");
                }
            }
            Direction::Up => {
                if !is_bot_lit(terminator) {
                    tracing::warn!("Unrolling terminator is not bottom element (up direction)");
                }
            }
        }

        // Extend the loop k times without asserts (unlike k-induction) because bmc flag is set
        let buf = encode_unroll(
            &enc_env,
            inner_stmt,
            k,
            hey_const(&enc_env, terminator, enc_env.direction, tcx),
        );

        Ok(GeneratedEncoding {
            block: Spanned::new(enc_env.stmt_span, buf),
            decls: None,
        })
    }

    fn is_terminator(&self) -> bool {
        false
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
