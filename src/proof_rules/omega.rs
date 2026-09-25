//! Encode omega-invariant proof rules for loop expectations.
//!
//! @omega_invariant takes the arguments:
//!
//! - `free_variable`: the variable that is used in the omega invariant
//! - `omega_inv`: the omega invariant of the loop
//! - `terminator` (optional): the terminator of the loop unfolding in the base case, inferred from the calculus when omitted
//!

use std::{any::Any, fmt};

use crate::{
    ast::{
        util::ModifiedVariableCollector, visit::VisitorMut, BinOpKind, Block, DeclKind, DeclRef,
        Direction, Expr, ExprBuilder, ExprKind, Files, Ident, QuantOpKind, SourceFilePath, Span,
        Spanned, Stmt, StmtKind, Symbol, TyKind, VarDecl, VarKind,
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
        default_fixpoint_kind_from_terminator, encode_iter, hey_const, intrinsic_param,
        select_terminator, warn_if_terminator_differs,
    },
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
        let terminator_param = intrinsic_param(file, "terminator", TyKind::SpecTy, false);

        let anno_decl = AnnotationDecl {
            name,
            inputs: Spanned::with_dummy_file_span(
                vec![free_var_param, omega_inv_param, terminator_param],
                file,
            ),
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
        // Scope the index to the invariant expression.
        let (invariant_args, terminator_args) = args.split_at_mut(args.len().min(2));
        resolve.with_subscope(|resolve| {
            let mut args_iter = invariant_args.iter_mut();
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
                    resolve.declare(DeclKind::VarDecl(DeclRef::new(var_decl)))?;
                } else {
                    return Err(ResolveError::NotIdent(free_var.span));
                }
            }
            resolve.visit_exprs(args_iter.into_slice())
        })?;
        resolve.visit_exprs(terminator_args)
    }

    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), TycheckError> {
        tycheck_annotation_call_with_optional_args(tycheck, call_span, &self.0, args, 2)
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
        default_fixpoint_kind_from_terminator(direction, args.get(2))
    }

    fn transform(
        &self,
        tcx: &TyCtx,
        args: &[Expr],
        inner_stmt: &Stmt,
        mut enc_env: EncodingEnvironment,
    ) -> Result<GeneratedEncoding, AnnotationError> {
        let span = enc_env.call_span;
        let free_var = &args[0];
        let omega_inv = &args[1];
        let explicit_terminator = args.get(2);
        let ExprKind::Var(omega_var) = &free_var.kind else {
            unreachable!("error should have been caught during resolve")
        };
        let omega_var = *omega_var;

        // The calculus determines the approximation, including when refuting a bound.
        let semantics = infer_fixpoint_kind(self, enc_env.calculus, enc_env.direction, args);
        let direction = match semantics {
            FixpointKind::Least => Direction::Down,
            FixpointKind::Greatest { .. } => Direction::Up,
        };
        enc_env.direction = direction;

        let mut visitor = ModifiedVariableCollector::new();
        visitor.visit_stmt(&mut inner_stmt.clone()).unwrap();
        let havoc_vars = (&visitor.modified_variables - &visitor.declared_variables)
            .into_iter()
            .collect();

        let builder = ExprBuilder::new(span);
        let terminator = select_terminator(semantics, explicit_terminator, builder);
        warn_if_terminator_differs(self.name(), semantics, explicit_terminator, builder);
        let base_case =
            encode_base_case(tcx, &enc_env, inner_stmt, omega_var, omega_inv, &terminator);
        let induction_step = encode_induction_step(tcx, &enc_env, inner_stmt, omega_var, omega_inv);
        let conditions = match direction {
            Direction::Down => StmtKind::Demonic(base_case, induction_step),
            Direction::Up => StmtKind::Angelic(base_case, induction_step),
        };

        // Quantify only the invariant so the solver can simplify the proof obligations separately.
        let bound = ExprBuilder::new(span).quant(
            match direction {
                Direction::Down => QuantOpKind::Sup,
                Direction::Up => QuantOpKind::Inf,
            },
            [omega_var],
            omega_inv.clone(),
        );
        let stmts = vec![
            // Evaluate the bound at loop entry before havocing the modified variables.
            Spanned::new(span, StmtKind::Assert(direction, bound)),
            Spanned::new(span, StmtKind::Havoc(direction, havoc_vars)),
            Spanned::new(span, conditions),
        ];

        Ok(GeneratedEncoding {
            block: Spanned::new(span, stmts),
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

/// Check I_0 <= Phi_f(terminator), or Psi_f(terminator) <= I_0 for greatest fixed points.
fn encode_base_case(
    tcx: &TyCtx,
    enc_env: &EncodingEnvironment,
    loop_stmt: &Stmt,
    index: Ident,
    invariant: &Expr,
    terminator: &Expr,
) -> Block {
    let span = enc_env.call_span;
    let direction = enc_env.direction;
    let builder = ExprBuilder::new(span);
    let initial_invariant = builder.subst(invariant.clone(), [(index, builder.uint(0))]);

    let iteration = encode_iter(
        enc_env,
        loop_stmt,
        hey_const(enc_env, terminator, direction, tcx),
    )
    .unwrap();

    Spanned::new(
        span,
        vec![
            Spanned::new(span, StmtKind::Validate(direction)),
            Spanned::new(span, StmtKind::Assume(direction, initial_invariant)),
            iteration,
        ],
    )
}

/// Check I_{n+1} <= Phi_f(I_n) for every n, or the dual inequality.
fn encode_induction_step(
    tcx: &TyCtx,
    enc_env: &EncodingEnvironment,
    loop_stmt: &Stmt,
    index: Ident,
    invariant: &Expr,
) -> Block {
    let span = enc_env.call_span;
    let direction = enc_env.direction;
    let builder = ExprBuilder::new(span);
    let next_index = builder.binary(
        BinOpKind::Add,
        Some(TyKind::UInt),
        builder.var(index, tcx),
        builder.uint(1),
    );
    let next_invariant = builder.subst(invariant.clone(), [(index, next_index)]);
    let iteration = encode_iter(
        enc_env,
        loop_stmt,
        hey_const(enc_env, invariant, direction, tcx),
    )
    .unwrap();

    Spanned::new(
        span,
        vec![
            Spanned::new(span, StmtKind::Havoc(direction, vec![index])),
            Spanned::new(span, StmtKind::Validate(direction)),
            Spanned::new(span, StmtKind::Assume(direction, next_invariant)),
            iteration,
        ],
    )
}
