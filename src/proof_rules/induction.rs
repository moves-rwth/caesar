//! Encode the proof for a lower/upper bound of an expectation of a loop using k-induction
//!
//! @k-induction takes the arguments:
//!
//! - `k`: the number of times the loop will be extended
//! - `invariant`: the invariant of the loop
//! `@invariant` is a syntactic sugar for 1-induction and it is equivalent to `@k-induction(1, expr)`.

use std::fmt;

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
        check_annotation_call, AnnotationDecl, AnnotationError, Calculus, CalculusType,
    },
    slicing::{wrap_with_error_message, wrap_with_success_message},
    tyctx::TyCtx,
};

use super::{Encoding, EncodingEnvironment, EncodingGenerated};

use super::util::*;

/// Syntactic sugar encoding for K-Induction encodings of type k=1

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
        check_annotation_call(tycheck, call_span, &self.0, args)?;
        Ok(())
    }

    fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        _call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError> {
        let [invariant] = mut_one_arg(args);
        resolve.visit_expr(invariant)
    }

    fn is_calculus_allowed(&self, calculus: &Calculus, direction: Direction) -> bool {
        matches!(
            (&calculus.calculus_type, direction),
            (CalculusType::Wp | CalculusType::Ert, Direction::Up)
                | (CalculusType::Wlp, Direction::Down)
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

        let mut visitor = ModifiedVariableCollector::new();
        visitor.visit_stmt(&mut inner_stmt.clone()).unwrap();
        let havoc_vars = visitor.modified_variables.into_iter().collect();

        let [invariant] = one_arg(args);

        let mut buf = vec![];

        // Construct the specification of the k-induction encoding
        buf.extend(encode_loop_spec(
            annotation_span,
            invariant,
            invariant,
            havoc_vars,
            direction,
        ));

        // Extend the loop k-1 times with the opposite direction
        let next_iter = encode_extend(
            annotation_span,
            inner_stmt,
            0,
            invariant,
            direction.toggle(),
            park_iteration_terminator(annotation_span, invariant, direction, tcx),
        );

        // Encode the last iteration in the normal direction
        buf.push(encode_iter(annotation_span, inner_stmt, next_iter).unwrap());

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
            (CalculusType::Wp | CalculusType::Ert, Direction::Up)
                | (CalculusType::Wlp, Direction::Down)
        )
    }
    fn transform(
        &self,
        tcx: &TyCtx,
        args: &[Expr],
        inner_stmt: &Stmt,
        enc_env: EncodingEnvironment,
    ) -> Result<EncodingGenerated, AnnotationError> {
        let annotation_span = enc_env.annotation_span;
        let direction = enc_env.direction;

        let mut visitor = ModifiedVariableCollector::new();
        visitor.visit_stmt(&mut inner_stmt.clone()).unwrap();
        let havoc_vars = visitor.modified_variables.into_iter().collect();

        let [k, invariant] = two_args(args);

        let k: u128 = lit_u128(k);

        let mut buf = vec![];

        // Construct the specification of the k-induction encoding
        buf.extend(encode_loop_spec(
            annotation_span,
            invariant,
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
            annotation_span,
            inner_stmt,
            k - 1,
            invariant,
            direction.toggle(),
            terminator,
        );

        // Encode the last iteration in the normal direction
        buf.push(encode_iter(annotation_span, inner_stmt, next_iter).unwrap());

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

/// Encode the loop "spec call" with respective error messages.
fn encode_loop_spec(
    span: Span,
    pre: &Expr,
    post: &Expr,
    variables: Vec<Ident>,
    direction: Direction,
) -> Vec<Stmt> {
    let error_condition = match direction {
        Direction::Down => "pre ≰ I",
        Direction::Up => "pre ≱ I",
    };
    let error_msg = format!("pre might not entail the invariant ({})", error_condition);
    vec![
        wrap_with_error_message(
            Spanned::new(span, StmtKind::Assert(direction, pre.clone())),
            &error_msg,
        ),
        Spanned::new(span, StmtKind::Havoc(direction, variables)),
        Spanned::new(span, StmtKind::Validate(direction)),
        wrap_with_success_message(
            Spanned::new(span, StmtKind::Assume(direction, post.clone())),
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
    let error_msg = format!("invariant might not be inductive ({})", error_condition);
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
/// [`park_termination_iterator`], but without the error messages. It is used
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
