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
        util::ModifiedVariableCollector, visit::VisitorMut, Direction, Expr, Files, Ident,
        SourceFilePath, Span, Spanned, Stmt, Symbol, TyKind,
    },
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{check_annotation_call, AnnotationError, AnnotationInfo},
    tyctx::TyCtx,
};

use super::{Encoding, EncodingGenerated};

use super::util::*;

/// Syntactic sugar encoding for K-Induction encodings of type k=1
pub struct InvariantAnnotation(AnnotationInfo);

impl InvariantAnnotation {
    pub fn new(_tcx: &mut TyCtx, files: &mut Files) -> Self {
        let file = files
            .add(SourceFilePath::Builtin, "invariant".to_string())
            .id;
        // TODO: replace the dummy span with a proper span
        let name = Ident::with_dummy_file_span(Symbol::intern("invariant"), file);

        let invariant_param = intrinsic_param(file, "inv", TyKind::SpecTy, false);

        let anno_info = AnnotationInfo {
            name,
            inputs: Spanned::with_dummy_file_span(vec![invariant_param], file),
            span: Span::dummy_file_span(file),
        };

        InvariantAnnotation(anno_info)
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

    fn transform(
        &self,
        tcx: &TyCtx,
        annotation_span: Span,
        args: &[Expr],
        inner_stmt: &Stmt,
        direction: Direction,
    ) -> Result<EncodingGenerated, AnnotationError> {
        let mut visitor = ModifiedVariableCollector::new();
        visitor.visit_stmt(&mut inner_stmt.clone()).unwrap();
        let havoc_vars = visitor.modified_variables.into_iter().collect();

        let [invariant] = one_arg(args);

        let mut buf = vec![];

        // Construct the specification of the k-induction encoding
        buf.extend(encode_spec(
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
            false,
            hey_const(annotation_span, invariant, tcx),
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

pub struct KIndAnnotation(AnnotationInfo);

impl KIndAnnotation {
    pub fn new(_tcx: &mut TyCtx, files: &mut Files) -> Self {
        let file = files
            .add(SourceFilePath::Builtin, "k_induction".to_string())
            .id;
        // TODO: replace the dummy span with a proper span
        let name = Ident::with_dummy_file_span(Symbol::intern("k_induction"), file);

        let k_param = intrinsic_param(file, "k", TyKind::UInt, true);
        let invariant_param = intrinsic_param(file, "inv", TyKind::SpecTy, false);

        let anno_info = AnnotationInfo {
            name,
            inputs: Spanned::with_dummy_file_span(vec![k_param, invariant_param], file),
            span: Span::dummy_file_span(file),
        };

        KIndAnnotation(anno_info)
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

    fn transform(
        &self,
        tcx: &TyCtx,
        annotation_span: Span,
        args: &[Expr],
        inner_stmt: &Stmt,
        direction: Direction,
    ) -> Result<EncodingGenerated, AnnotationError> {
        let mut visitor = ModifiedVariableCollector::new();
        visitor.visit_stmt(&mut inner_stmt.clone()).unwrap();
        let havoc_vars = visitor.modified_variables.into_iter().collect();

        let [k, invariant] = two_args(args);

        let k: u128 = lit_u128(k);

        let mut buf = vec![];

        // Construct the specification of the k-induction encoding
        buf.extend(encode_spec(
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
            k - 1,
            invariant,
            direction.toggle(),
            false,
            hey_const(annotation_span, invariant, tcx),
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
