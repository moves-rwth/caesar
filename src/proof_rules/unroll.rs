//! Encode the proof for refuting a lower/upper bound of an expectation of a loop by unrolling the loop k times
//!
//! @unroll takes the arguments:
//!
//! - `k`: the number of times the loop will be unrolled
//! - `terminator` (optional): the terminator of the loop, inferred from the calculus when omitted

use std::{any::Any, fmt};

use crate::{
    ast::{
        visit::VisitorMut, Direction, Expr, ExprBuilder, Files, Ident, SourceFilePath, Span,
        Spanned, Stmt, Symbol, TyKind,
    },
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{
        tycheck_annotation_call_with_optional_args, AnnotationDecl, AnnotationError, Calculus,
    },
    proof_rules::calculus::{ApproximationKind, FixpointKind},
    tyctx::TyCtx,
};

use super::{
    infer_fixpoint_kind,
    util::{
        default_fixpoint_kind_from_terminator, encode_unroll, hey_const, intrinsic_param, lit_u128,
        select_terminator, terminator_mismatch_diagnostic,
    },
    Encoding, EncodingEnvironment, GeneratedEncoding,
};

pub struct UnrollAnnotation(AnnotationDecl);

impl UnrollAnnotation {
    pub fn new(_tcx: &mut TyCtx, files: &mut Files) -> Self {
        let file = files.add(SourceFilePath::Builtin, "unroll".to_string()).id;

        // TODO: replace the dummy span with a proper span
        let name = Ident::with_dummy_file_span(Symbol::intern("unroll"), file);

        let k_param = intrinsic_param(file, "k", TyKind::UInt, true);
        let terminator_param = intrinsic_param(file, "terminator", TyKind::SpecTy, false);

        let anno_decl = AnnotationDecl {
            name,
            inputs: Spanned::with_dummy_file_span(vec![k_param, terminator_param], file),
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
        tycheck_annotation_call_with_optional_args(tycheck, call_span, &self.0, args, 1)
    }

    fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        _call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError> {
        resolve.visit_exprs(args)
    }

    fn get_approximation(
        &self,
        fixpoint_kind: FixpointKind,
        inner_approximation_kind: ApproximationKind,
        _calculus: Option<Calculus>,
    ) -> ApproximationKind {
        let approx = match fixpoint_kind {
            FixpointKind::Least => ApproximationKind::UNDER,
            FixpointKind::Greatest { .. } => ApproximationKind::OVER,
        };
        approx & inner_approximation_kind
    }

    fn default_fixpoint_kind(&self, direction: Direction, args: &[Expr]) -> FixpointKind {
        default_fixpoint_kind_from_terminator(direction, args.get(1))
    }

    fn transform(
        &self,
        tcx: &TyCtx,
        args: &[Expr],
        inner_stmt: &Stmt,
        enc_env: EncodingEnvironment,
    ) -> Result<GeneratedEncoding, AnnotationError> {
        let k = lit_u128(&args[0]);
        let explicit_terminator = args.get(1);

        let semantics = infer_fixpoint_kind(self, enc_env.calculus, enc_env.direction, args);
        let builder = ExprBuilder::new(enc_env.call_span);
        let terminator = select_terminator(semantics, explicit_terminator, builder);
        let diagnostic =
            terminator_mismatch_diagnostic(self.name(), semantics, explicit_terminator, builder);

        // Extend the loop k times without asserts (unlike k-induction) because bmc flag is set
        let buf = encode_unroll(
            &enc_env,
            inner_stmt,
            k,
            hey_const(&enc_env, &terminator, enc_env.direction, tcx),
        );

        Ok(GeneratedEncoding {
            block: Spanned::new(enc_env.stmt_span, buf),
            decls: None,
            diagnostics: diagnostic.into_iter().collect(),
        })
    }

    fn is_terminator(&self) -> bool {
        false
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
