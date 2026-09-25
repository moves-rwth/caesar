//! Encode the proof rule for positive almost-sure termination by Chakarov et al. (2013).
//!
//! @past takes the arguments:
//!
//! - `inv`: the invariant of the loop
//! - `eps`: a positive real number used for the epsilon value from the proof rule, must be a literal
//! - `k`: a positive real number used for the k value from the proof rule, must be a literal
//!
//! Note that eps must be smaller than k!
//!
use std::{any::Any, fmt};

use crate::{
    ast::{
        util::{FreeVariableCollector, ModifiedVariableCollector},
        visit::VisitorMut,
        BinOpKind, DeclKind, Direction, Expr, ExprBuilder, Files, Ident, ProcSpec, SourceFilePath,
        Span, Spanned, Stmt, StmtKind, Symbol, TyKind, UnOpKind,
    },
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{tycheck_annotation_call, AnnotationDecl, AnnotationError, Calculus},
    proof_rules::calculus::{ApproximationKind, CalculusType, FixpointKind},
    tyctx::TyCtx,
};

use super::{Encoding, EncodingEnvironment, GeneratedEncoding, ProcInfo};

use super::util::*;

pub struct PASTAnnotation(AnnotationDecl);

impl PASTAnnotation {
    pub fn new(_tcx: &mut TyCtx, files: &mut Files) -> Self {
        let file = files.add(SourceFilePath::Builtin, "past".to_string()).id;
        // TODO: replace the dummy span with a proper span
        let name = Ident::with_dummy_file_span(Symbol::intern("past"), file);

        let invariant_param = intrinsic_param(file, "inv", TyKind::SpecTy, false);
        let eps_param = intrinsic_param(file, "eps", TyKind::UReal, true);
        let k_param = intrinsic_param(file, "k", TyKind::UReal, true);

        let anno_decl = AnnotationDecl {
            name,
            inputs: Spanned::with_dummy_file_span(vec![invariant_param, eps_param, k_param], file),
            span: Span::dummy_file_span(file),
        };

        PASTAnnotation(anno_decl)
    }
}

impl fmt::Debug for PASTAnnotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PASTAnnotation")
            .field("annotation", &self.0)
            .finish()
    }
}

impl Encoding for PASTAnnotation {
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

    fn get_approximation(
        &self,
        fixpoint_kind: FixpointKind,
        inner_approximation_kind: ApproximationKind,
        calculus: Option<Calculus>,
    ) -> ApproximationKind {
        // @past is only sound with @ert; any other explicit calculus yields unknown.
        if let Some(c) = calculus {
            if !matches!(c.calculus_type, CalculusType::Ert) {
                return ApproximationKind::UNKNOWN;
            }
        }
        match (fixpoint_kind, inner_approximation_kind) {
            (FixpointKind::Least, ApproximationKind::EXACT) => ApproximationKind::EXACT,
            _ => ApproximationKind::UNKNOWN,
        }
    }

    fn default_fixpoint_kind(&self, _direction: Direction, _args: &[Expr]) -> FixpointKind {
        FixpointKind::Least
    }

    fn transform(
        &self,
        tcx: &TyCtx,
        args: &[Expr],
        inner_stmt: &Stmt,
        enc_env: EncodingEnvironment,
    ) -> Result<GeneratedEncoding, AnnotationError> {
        let annotation_span = enc_env.call_span;

        let [inv, eps, k] = three_args(args);
        let builder = ExprBuilder::new(annotation_span);

        let eps_val = lit_rational(eps);
        let k_val = lit_rational(k);
        if eps_val >= k_val {
            return Err(AnnotationError::WrongArgument {
                span: annotation_span,
                arg: eps.clone(),
                message: String::from("eps must be smaller than k."),
            });
        }

        // Cast eps and k from UReal to EUReal for the later operations
        let eps = builder.cast(TyKind::EUReal, eps.clone());
        let k = builder.cast(TyKind::EUReal, k.clone());

        let loop_guard = if let StmtKind::While(guard, _) = &inner_stmt.node {
            guard
        } else {
            return Err(AnnotationError::NotOnWhile {
                span: annotation_span,
                annotation_name: self.name(),
                annotated: Box::new(inner_stmt.clone()),
            });
        };

        let bounded_on_exit = encode_exit_bound(tcx, &enc_env, loop_guard, inv, &k);
        let k_bounded_by_invariant = encode_continuation_bound(tcx, &enc_env, loop_guard, inv, &k);
        let decreases = encode_decrease(tcx, &enc_env, inner_stmt, loop_guard, inv, &eps);

        Ok(GeneratedEncoding {
            block: Spanned::new(annotation_span, vec![]),
            decls: Some(vec![bounded_on_exit, k_bounded_by_invariant, decreases]),
            diagnostics: vec![],
        })
    }

    fn is_terminator(&self) -> bool {
        false
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

/// Check `[!G] * I <= K` on terminating states.
fn encode_exit_bound(
    tcx: &TyCtx,
    enc_env: &EncodingEnvironment,
    loop_guard: &Expr,
    inv: &Expr,
    k: &Expr,
) -> DeclKind {
    let span = enc_env.call_span;
    let builder = ExprBuilder::new(span);
    let condition = builder.unary(
        UnOpKind::Embed,
        Some(tcx.spec_ty().clone()),
        builder.binary(
            BinOpKind::Le,
            Some(TyKind::Bool),
            builder.binary(
                BinOpKind::Mul,
                Some(TyKind::EUReal),
                builder.unary(
                    UnOpKind::Iverson,
                    Some(TyKind::EUReal),
                    builder.unary(UnOpKind::Not, Some(TyKind::Bool), loop_guard.clone()),
                ),
                inv.clone(),
            ),
            k.clone(),
        ),
    );

    let mut free_var_collector = FreeVariableCollector::new();
    let variables = free_var_collector
        .collect_and_clear(&mut condition.clone())
        .into_iter()
        .collect();
    let proc_info = ProcInfo {
        name: "past_bounded_on_exit".to_string(),
        inputs: params_from_idents(variables, tcx),
        outputs: vec![],
        spec: vec![],
        body: Spanned::new(
            span,
            vec![Spanned::new(
                span,
                StmtKind::Assert(Direction::Down, condition),
            )],
        ),
        direction: Direction::Down,
    };
    generate_proc(span, proc_info, enc_env.base_proc_ident, tcx)
}

/// Check `[G] * K <= [G] * I + [!G]` on continuing states.
fn encode_continuation_bound(
    tcx: &TyCtx,
    enc_env: &EncodingEnvironment,
    loop_guard: &Expr,
    inv: &Expr,
    k: &Expr,
) -> DeclKind {
    let span = enc_env.call_span;
    let builder = ExprBuilder::new(span);
    let condition = builder.binary(
        BinOpKind::Le,
        Some(TyKind::Bool),
        // [guard] * k
        builder.binary(
            BinOpKind::Mul,
            Some(TyKind::EUReal),
            builder.unary(UnOpKind::Iverson, Some(TyKind::EUReal), loop_guard.clone()),
            k.clone(),
        ),
        // ([guard] * invariant) + [!guard]
        builder.binary(
            BinOpKind::Add,
            Some(TyKind::EUReal),
            builder.binary(
                BinOpKind::Mul,
                Some(TyKind::EUReal),
                builder.unary(UnOpKind::Iverson, Some(TyKind::EUReal), loop_guard.clone()),
                inv.clone(),
            ),
            builder.unary(
                UnOpKind::Iverson,
                Some(TyKind::EUReal),
                builder.unary(UnOpKind::Not, Some(TyKind::Bool), loop_guard.clone()),
            ),
        ),
    );

    let mut free_var_collector = FreeVariableCollector::new();
    let variables = free_var_collector
        .collect_and_clear(&mut condition.clone())
        .into_iter()
        .collect();
    let proc_info = ProcInfo {
        name: "past_k_bounded_by_invariant".to_string(),
        inputs: params_from_idents(variables, tcx),
        outputs: vec![],
        spec: vec![],
        body: Spanned::new(
            span,
            vec![Spanned::new(
                span,
                StmtKind::Assert(Direction::Down, condition),
            )],
        ),
        direction: Direction::Down,
    };
    generate_proc(span, proc_info, enc_env.base_proc_ident, tcx)
}

/// Check `Phi_0(I) <= [G] * (I - eps)` after one loop iteration.
fn encode_decrease(
    tcx: &TyCtx,
    enc_env: &EncodingEnvironment,
    loop_stmt: &Stmt,
    loop_guard: &Expr,
    inv: &Expr,
    eps: &Expr,
) -> DeclKind {
    let span = enc_env.call_span;
    let builder = ExprBuilder::new(span);

    // Collect modified variables, excluding those declared within the loop.
    let mut visitor = ModifiedVariableCollector::new();
    visitor.visit_stmt(&mut loop_stmt.clone()).unwrap();
    let modified_vars: Vec<Ident> = (&visitor.modified_variables - &visitor.declared_variables)
        .into_iter()
        .collect();

    let mut free_var_collector = FreeVariableCollector::new();
    let inv_variables: Vec<Ident> = free_var_collector
        .collect_and_clear(&mut inv.clone())
        .into_iter()
        .collect();

    // Initialize modified variables from the inputs of the generated procedure.
    let init_idents = get_init_idents(tcx, span, &modified_vars);
    let init_exprs = init_idents
        .iter()
        .map(|ident| ident_to_expr(tcx, span, *ident))
        .collect();
    let mut body = multiple_assign(span, modified_vars.clone(), init_exprs);
    let init_inv = to_init_expr(tcx, span, inv, &inv_variables);
    body.push(
        encode_iter(
            enc_env,
            loop_stmt,
            hey_const(enc_env, inv, Direction::Down, tcx),
        )
        .unwrap(),
    );

    // Evaluate the guard in the same initial state as the invariant.
    let init_guard = to_init_expr(tcx, span, loop_guard, &modified_vars);
    let pre = builder.binary(
        BinOpKind::Mul,
        Some(TyKind::EUReal),
        builder.unary(UnOpKind::Iverson, Some(TyKind::EUReal), init_guard),
        builder.binary(BinOpKind::Sub, Some(TyKind::EUReal), init_inv, eps.clone()),
    );

    let proc_info = ProcInfo {
        name: "past_decreases".to_string(),
        inputs: params_from_idents(init_idents, tcx),
        outputs: params_from_idents(modified_vars, tcx),
        spec: vec![
            ProcSpec::Requires(pre),
            ProcSpec::Ensures(builder.cast(TyKind::EUReal, builder.uint(0))),
        ],
        body: Spanned::new(span, body),
        direction: Direction::Up,
    };
    generate_proc(span, proc_info, enc_env.base_proc_ident, tcx)
}
