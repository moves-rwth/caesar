//! Encode the proof for a lower/upper bound of an expectation of a loop using k-induction
//!
//! @k-induction takes the arguments:
//!
//! - `k`: the number of times the loop will be extended
//! - `invariant`: the invariant of the loop
//!
//! `@invariant` is a syntactic sugar for 1-induction and it is equivalent to `@k-induction(1, expr)`.

use std::{any::Any, fmt};

use crate::{
    ast::{
        util::ModifiedVariableCollector, visit::VisitorMut, Direction, Expr, ExprBuilder, Files,
        Ident, SourceFilePath, Span, Spanned, Stmt, StmtKind, Symbol, TyKind,
    },
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{
        tycheck_annotation_call, AnnotationDecl, AnnotationError, Calculus, CalculusType,
    },
    proof_rules::{calculus::ApproximationKind, FixpointSemanticsKind},
    slicing::{wrap_with_error_message, wrap_with_success_message},
    tyctx::TyCtx,
};

use super::{
    util::{encode_extend, encode_iter, intrinsic_param, lit_u128, one_arg, two_args},
    Encoding, EncodingEnvironment, GeneratedEncoding,
};

/// The "@induction" encoding is just syntactic sugar for 1-induction.
pub struct InvariantAnnotation(pub AnnotationDecl);

impl InvariantAnnotation {
    pub fn new(_tcx: &mut TyCtx, files: &mut Files) -> Self {
        let file = files
            .add(SourceFilePath::Builtin, "invariant".to_string())
            .id;
        // TODO: replace the dummy span with a proper span
        let name = Ident::with_dummy_file_span(Symbol::intern("invariant"), file);

        let invariant_param = intrinsic_param(file, "inv", TyKind::SpecTy, false);

        let anno_decl = AnnotationDecl {
            name,
            inputs: Spanned::with_dummy_file_span(vec![invariant_param], file),
            span: Span::dummy_file_span(file),
        };

        InvariantAnnotation(anno_decl)
    }
}

impl fmt::Debug for InvariantAnnotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InvariantAnnotation")
            .field("annotation", &self.0)
            .finish()
    }
}

impl Encoding for InvariantAnnotation {
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
            (CalculusType::Wp | CalculusType::Ert, Direction::Up)
                | (CalculusType::Wlp, Direction::Down)
        )
    }

    fn get_approximation(
        &self,
        fixpoint_semantics: FixpointSemanticsKind,
        inner_approximation_kind: ApproximationKind,
    ) -> ApproximationKind {
        match fixpoint_semantics {
            FixpointSemanticsKind::LeastFixedPoint => ApproximationKind::Over,
            FixpointSemanticsKind::GreatestFixedPoint => ApproximationKind::Under,
        }
        .infimum(inner_approximation_kind)
    }

    fn sound_fixpoint_semantics_kind(&self, direction: Direction) -> FixpointSemanticsKind {
        match direction {
            Direction::Up => FixpointSemanticsKind::LeastFixedPoint,
            Direction::Down => FixpointSemanticsKind::GreatestFixedPoint,
        }
    }

    fn transform(
        &self,
        tcx: &TyCtx,
        args: &[Expr],
        inner_stmt: &Stmt,
        enc_env: EncodingEnvironment,
    ) -> Result<GeneratedEncoding, AnnotationError> {
        let [invariant] = one_arg(args);
        let k = 1;
        transform_k_induction(tcx, inner_stmt, enc_env, k, invariant)
    }

    fn is_terminator(&self) -> bool {
        false
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct KIndAnnotation(AnnotationDecl);

impl KIndAnnotation {
    pub fn new(_tcx: &mut TyCtx, files: &mut Files) -> Self {
        let file = files
            .add(SourceFilePath::Builtin, "k_induction".to_string())
            .id;
        // TODO: replace the dummy span with a proper span
        let name = Ident::with_dummy_file_span(Symbol::intern("k_induction"), file);

        let k_param = intrinsic_param(file, "k", TyKind::UInt, true);
        let invariant_param = intrinsic_param(file, "inv", TyKind::SpecTy, false);

        let anno_decl = AnnotationDecl {
            name,
            inputs: Spanned::with_dummy_file_span(vec![k_param, invariant_param], file),
            span: Span::dummy_file_span(file),
        };

        KIndAnnotation(anno_decl)
    }
}

impl fmt::Debug for KIndAnnotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KIndAnnotation")
            .field("annotation", &self.0)
            .finish()
    }
}

impl Encoding for KIndAnnotation {
    fn name(&self) -> Ident {
        self.0.name
    }

    fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        _call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError> {
        resolve.visit_exprs(args)
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

    fn is_calculus_allowed(&self, calculus: Calculus, direction: Direction) -> bool {
        matches!(
            (&calculus.calculus_type, direction),
            (CalculusType::Wp | CalculusType::Ert, Direction::Up)
                | (CalculusType::Wlp, Direction::Down)
        )
    }

    fn get_approximation(
        &self,
        fixpoint_semantics: FixpointSemanticsKind,
        inner_approximation_kind: ApproximationKind,
    ) -> ApproximationKind {
        match fixpoint_semantics {
            FixpointSemanticsKind::LeastFixedPoint => ApproximationKind::Over,
            FixpointSemanticsKind::GreatestFixedPoint => ApproximationKind::Under,
        }
        .infimum(inner_approximation_kind)
    }

    fn sound_fixpoint_semantics_kind(&self, direction: Direction) -> FixpointSemanticsKind {
        match direction {
            Direction::Up => FixpointSemanticsKind::LeastFixedPoint,
            Direction::Down => FixpointSemanticsKind::GreatestFixedPoint,
        }
    }

    fn transform(
        &self,
        tcx: &TyCtx,
        args: &[Expr],
        inner_stmt: &Stmt,
        enc_env: EncodingEnvironment,
    ) -> Result<GeneratedEncoding, AnnotationError> {
        let [k, invariant] = two_args(args);
        let k_val: u128 = lit_u128(k);

        if k_val == 0 {
            return Err(AnnotationError::WrongArgument {
                span: enc_env.call_span,
                arg: k.clone(),
                message: String::from("k must be greater than 0."),
            });
        }

        transform_k_induction(tcx, inner_stmt, enc_env, k_val, invariant)
    }

    fn is_terminator(&self) -> bool {
        false
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

/// Generic implementation of the encoding for both k-induction and induction.
/// Since induction is just 1-induction, we can reuse almost all of the code.
fn transform_k_induction(
    tcx: &TyCtx,
    inner_stmt: &Stmt,
    enc_env: EncodingEnvironment,
    k: u128,
    invariant: &Expr,
) -> Result<GeneratedEncoding, AnnotationError> {
    let annotation_span = enc_env.call_span;
    let direction = enc_env.direction;

    let mut visitor = ModifiedVariableCollector::new();
    visitor.visit_stmt(&mut inner_stmt.clone()).unwrap();
    let havoc_vars = visitor.modified_variables.into_iter().collect();

    let mut buf = vec![];

    // Construct the specification of the k-induction encoding
    buf.extend(encode_loop_spec(
        annotation_span,
        invariant,
        havoc_vars,
        direction,
    ));

    // If we do Park induction here, then use the terminator with error and
    // success messages. If we do k-induction with k > 1, then do not emit
    // these messages - they're not accurate then.
    let terminator = if k == 1 {
        park_iteration_terminator(annotation_span, invariant, direction, tcx)
    } else {
        iteration_terminator(annotation_span, invariant, direction, tcx)
    };

    // Extend the loop k-1 times with the opposite direction
    let next_iter = encode_extend(
        &enc_env,
        inner_stmt,
        k - 1,
        invariant,
        direction.toggle(),
        terminator,
    );

    // Encode the last iteration in the normal direction
    buf.push(encode_iter(&enc_env, inner_stmt, next_iter).unwrap());

    Ok(GeneratedEncoding {
        block: Spanned::new(enc_env.stmt_span, buf),
        decls: None,
    })
}

/// Encode the loop "spec call" with respective error messages.
fn encode_loop_spec(
    span: Span,
    invariant: &Expr,
    variables: Vec<Ident>,
    direction: Direction,
) -> Vec<Stmt> {
    let error_condition = match direction {
        Direction::Down => "pre ≰ I",
        Direction::Up => "pre ≱ I",
    };
    let error_msg = format!("pre might not entail the invariant ({error_condition})");
    vec![
        wrap_with_error_message(
            Spanned::new(span, StmtKind::Assert(direction, invariant.clone())),
            &error_msg,
        ),
        Spanned::new(span, StmtKind::Havoc(direction, variables)),
        Spanned::new(span, StmtKind::Validate(direction)),
        wrap_with_success_message(
            Spanned::new(span, StmtKind::Assume(direction, invariant.clone())),
            "invariant not necessary for inductivity",
        ),
    ]
}

/// For Park induction only: HeyVL statements which always evaluate to `expr`,
/// used as terminating statements in the loop iteration.
fn park_iteration_terminator(
    span: Span,
    expr: &Expr,
    direction: Direction,
    tcx: &TyCtx,
) -> Vec<Stmt> {
    let error_condition = match direction {
        Direction::Down => "I ≰ 𝚽(I)",
        Direction::Up => "I ≱ 𝚽(I)",
    };
    let error_msg = format!("invariant might not be inductive ({error_condition})");
    let builder = ExprBuilder::new(span);
    let extreme_lit = match direction {
        Direction::Up => builder.top_lit(tcx.spec_ty()),
        Direction::Down => builder.bot_lit(tcx.spec_ty()),
    };
    vec![
        wrap_with_error_message(
            Spanned::new(span, StmtKind::Assert(direction, expr.clone())),
            &error_msg,
        ),
        wrap_with_success_message(
            Spanned::new(span, StmtKind::Assume(direction, extreme_lit)),
            "while could be an if statement",
        ),
    ]
}

/// HeyVL statements which always evaluate to `expr`, used as terminating
/// statements in the loop iteration. This is like
/// [`park_iteration_terminator`], but without the error messages. It is used
/// for k-Induction.
fn iteration_terminator(span: Span, expr: &Expr, direction: Direction, tcx: &TyCtx) -> Vec<Stmt> {
    let builder = ExprBuilder::new(span);
    let extreme_lit = match direction {
        Direction::Up => builder.top_lit(tcx.spec_ty()),
        Direction::Down => builder.bot_lit(tcx.spec_ty()),
    };
    vec![
        Spanned::new(span, StmtKind::Assert(direction, expr.clone())),
        Spanned::new(span, StmtKind::Assume(direction, extreme_lit)),
    ]
}
