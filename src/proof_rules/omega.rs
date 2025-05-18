//! Encoding of omega invariant proof rule for lower/upper-bounds of expectations of a loop
//!
//! @omega_invariant takes the arguments:
//!
//! - `free_variable`: the variable that is used in the omega invariant
//! - `omega_inv`: the omega invariant of the loop
//!

use std::{any::Any, fmt};

use crate::{
    ast::{
        visit::VisitorMut, BinOpKind, DeclKind, DeclRef, Direction, Expr, ExprBuilder, ExprKind,
        Files, Ident, SourceFilePath, Span, Spanned, Stmt, StmtKind, Symbol, TyKind, VarDecl,
        VarKind,
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

use super::{
    util::{encode_iter, hey_const, intrinsic_param, two_args},
    Encoding, EncodingEnvironment, GeneratedEncoding,
};

pub struct OmegaInvAnnotation(AnnotationDecl);

impl OmegaInvAnnotation {
    pub fn new(_tcx: &mut TyCtx, files: &mut Files) -> Self {
        let file = files
            .add(SourceFilePath::Builtin, "omega_invariant".to_string())
            .id;
        // TODO: replace the dummy span with a proper span
        let name = Ident::with_dummy_file_span(Symbol::intern("omega_invariant"), file);

        let omega_inv_param = intrinsic_param(file, "omega_inv", TyKind::EUReal, false);
        let free_var_param = intrinsic_param(file, "free_variable", TyKind::UInt, false);

        let anno_decl = AnnotationDecl {
            name,
            inputs: Spanned::with_dummy_file_span(vec![free_var_param, omega_inv_param], file),
            span: Span::dummy_file_span(file),
        };

        OmegaInvAnnotation(anno_decl)
    }
}

impl fmt::Debug for OmegaInvAnnotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OmegaInvAnnotation")
            .field("annotation", &self.0)
            .finish()
    }
}

impl Encoding for OmegaInvAnnotation {
    fn name(&self) -> Ident {
        self.0.name
    }

    fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError> {
        let mut args_iter = args.iter_mut();
        if let Some(free_var) = args_iter.next() {
            if let ExprKind::Var(var_ref) = &free_var.kind {
                let var_decl = VarDecl {
                    name: *var_ref,
                    ty: TyKind::UInt,
                    kind: VarKind::Mut,
                    init: None,
                    span: call_span,
                    created_from: None,
                };
                // Declare the free variable to be used in the omega invariant
                resolve.declare(DeclKind::VarDecl(DeclRef::new(var_decl)))?;
            } else {
                return Err(ResolveError::NotIdent(free_var.span));
            }
        }
        resolve.visit_exprs(args_iter.into_slice())
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

    fn is_calculus_allowed(&self, calculus: Calculus, direction: Direction) -> bool {
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
    ) -> Result<GeneratedEncoding, AnnotationError> {
        // Unpack values from struct
        let annotation_span = enc_env.call_span;
        let direction = enc_env.direction;

        let [free_var, omega_inv] = two_args(args);

        let omega_var = if let ExprKind::Var(var_ref) = &free_var.kind {
            *var_ref
        } else {
            unreachable!("error should have been caught during resolve")
        };

        let builder = ExprBuilder::new(annotation_span);

        // Construct n+1 expression to substitute n with n+1, in order to construct I_{n+1} later
        let omega_var_plus_1 = builder.binary(
            BinOpKind::Add,
            Some(TyKind::UInt),
            builder.var(omega_var, tcx),
            builder.uint(1),
        );

        // Construct necessary expressions for the conditions
        // I_{n+1}
        let next_omega_inv = builder.subst(omega_inv.clone(), [(omega_var, omega_var_plus_1)]);
        // I_{0}
        let null_omega_inv = builder.subst(omega_inv.clone(), [(omega_var, builder.uint(0))]);

        // Phi_x(I_n)
        let iter = encode_iter(
            &enc_env,
            inner_stmt,
            hey_const(&enc_env, omega_inv, direction, tcx),
        )
        .unwrap();

        // Phi_x(0)
        let null_iter = encode_iter(
            &enc_env,
            inner_stmt,
            hey_const(
                &enc_env,
                &builder.cast(tcx.spec_ty().clone(), builder.uint(0)),
                direction,
                tcx,
            ),
        )
        .unwrap();

        // I_0 <= Phi_{post}(0)
        let cond1 = Spanned::new(
            annotation_span,
            vec![
                Spanned::new(annotation_span, StmtKind::Validate(direction)),
                Spanned::new(annotation_span, StmtKind::Assume(direction, null_omega_inv)),
                null_iter,
            ],
        );

        // for all n. I_{n+1} <= Phi_{post}(I_n)
        let cond2 = Spanned::new(
            annotation_span,
            vec![
                Spanned::new(annotation_span, StmtKind::Havoc(direction, vec![omega_var])),
                Spanned::new(annotation_span, StmtKind::Validate(direction)),
                Spanned::new(annotation_span, StmtKind::Assume(direction, next_omega_inv)),
                iter,
            ],
        );

        // conditions are checked with demonic if,
        // we take sup or inf of the omega_inv before the demonic if
        // to propagate the lower(upper) bound backwards for compositionality
        // (if the conditions hold)

        let buf = vec![
            // (co)havoc n
            Spanned::new(
                annotation_span,
                StmtKind::Havoc(direction.toggle(), vec![omega_var]),
            ),
            // (co)assert omega_inv
            Spanned::new(
                annotation_span,
                StmtKind::Assert(direction, omega_inv.clone()),
            ),
            // conditions
            Spanned::new(
                annotation_span,
                if direction == Direction::Down {
                    StmtKind::Demonic(cond1, cond2)
                } else {
                    StmtKind::Angelic(cond1, cond2)
                },
            ),
        ];

        Ok(GeneratedEncoding {
            block: Spanned::new(annotation_span, buf),
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
