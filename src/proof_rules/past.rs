//! Encode the proof rule for positive almost-sure termination by Chakarov et al. (2013).
//!
//! @past takes the arguments:
//!
//! - `inv`: the invariant of the loop
//! - `eps`: a positive real number used for the epsilon value from the proof rule, must be a literal
//! - `k`: a positive real number used for the k value from the proof rule, must be a literal
//!
//! The decrease must be positive and smaller than k.
//!
use std::{any::Any, fmt};

use num::Zero;

use crate::{
    ast::{
        util::VariableCollector,
        visit::{walk_expr, walk_stmt, VisitorMut},
        BinOpKind, DeclKind, Diagnostic, Direction, Expr, ExprBuilder, ExprKind, Files, Ident,
        ProcSpec, SourceFilePath, Span, Spanned, Stmt, StmtKind, Symbol, TyKind, UnOpKind,
    },
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{
        tycheck_annotation_call, AnnotationDecl, AnnotationError, AnnotationKind, Calculus,
    },
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

    fn validate(
        &self,
        tcx: &TyCtx,
        call_span: Span,
        _args: &[Expr],
        inner_stmt: &Stmt,
    ) -> Result<Vec<Diagnostic>, AnnotationError> {
        if let StmtKind::While(_, body) = &inner_stmt.node {
            PastBodyValidator {
                tcx,
                annotation_name: self.name(),
                call_span,
            }
            .visit_block(&mut body.clone())?;
        }
        Ok(vec![])
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
            (FixpointKind::Least, ApproximationKind::EXACT) => ApproximationKind::OVER,
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

        if enc_env.direction != Direction::Up {
            return Err(AnnotationError::WrongProcedureDirection {
                span: annotation_span,
                annotation_name: self.name(),
                required: Direction::Up,
            });
        }

        let [inv, eps, k] = three_args(args);
        let builder = ExprBuilder::new(annotation_span);

        let eps_val = lit_rational(eps);
        let k_val = lit_rational(k);
        if eps_val.is_zero() || eps_val >= k_val {
            return Err(AnnotationError::WrongArgument {
                span: annotation_span,
                arg: eps.clone(),
                message: String::from("epsilon must be positive and smaller than k."),
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
        let mut variables = VariableCollector::from_stmt(inner_stmt);
        variables.add_expr(inv);
        let decreases =
            encode_decrease(tcx, &enc_env, inner_stmt, loop_guard, inv, &eps, &variables);
        let summary = encode_summary(
            annotation_span,
            loop_guard,
            inv,
            variables.free_modified().collect(),
        );

        Ok(GeneratedEncoding {
            block: Spanned::new(annotation_span, vec![summary]),
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

/// Summarize the loop using its possible exit states and an upper bound on its expected reward.
///
/// ```text
/// if G { tick I; cohavoc modified; coassume ?(G) } else {}
/// ```
///
/// `modified` consists of the variables modified by the body and visible after it.
/// The summary charges the ranking `I` from the entry state.
fn encode_summary(span: Span, guard: &Expr, invariant: &Expr, modified_vars: Vec<Ident>) -> Stmt {
    let builder = ExprBuilder::new(span);
    let mut body = vec![Spanned::new(span, StmtKind::Tick(invariant.clone()))];
    if !modified_vars.is_empty() {
        body.push(Spanned::new(
            span,
            StmtKind::Havoc(Direction::Up, modified_vars),
        ));
    }
    let condition = builder.unary(UnOpKind::Embed, Some(TyKind::EUReal), guard.clone());
    body.push(Spanned::new(
        span,
        StmtKind::Assume(Direction::Up, condition),
    ));

    Spanned::new(
        span,
        StmtKind::If(
            guard.clone(),
            Spanned::new(span, body),
            Spanned::new(span, vec![]),
        ),
    )
}

/// The ranking argument needs a terminating probabilistic transition for each body execution.
struct PastBodyValidator<'tcx> {
    tcx: &'tcx TyCtx,
    annotation_name: Ident,
    call_span: Span,
}

impl PastBodyValidator<'_> {
    fn unsupported(&self, span: Span, message: &str) -> AnnotationError {
        AnnotationError::UnsupportedStatement {
            span: self.call_span,
            annotation_name: self.annotation_name,
            statement_span: span,
            message: message.to_owned(),
            note: Some("`@past` requires a loop-free probabilistic body."),
        }
    }
}

impl VisitorMut for PastBodyValidator<'_> {
    type Err = AnnotationError;

    fn visit_stmt(&mut self, stmt: &mut Stmt) -> Result<(), Self::Err> {
        match &stmt.node {
            StmtKind::Seq(_)
            | StmtKind::Var(_)
            | StmtKind::Assign(_, _)
            | StmtKind::Tick(_)
            | StmtKind::If(_, _, _)
            | StmtKind::Label(_) => {}
            StmtKind::Annotation(_, name, _, _)
                if matches!(
                    self.tcx.get(*name).unwrap().as_ref(),
                    DeclKind::AnnotationDecl(AnnotationKind::Slicing(_))
                ) => {}
            _ => return Err(self.unsupported(stmt.span, "Unsupported statement in the loop body.")),
        }
        walk_stmt(self, stmt)
    }

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        if let ExprKind::Call(ident, _) = &expr.kind {
            if matches!(
                self.tcx.get(*ident).unwrap().as_ref(),
                DeclKind::ProcDecl(_)
            ) {
                return Err(self.unsupported(expr.span, "Procedure calls are not supported."));
            }
        }
        walk_expr(self, expr)
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

    let variables = VariableCollector::from_expr(&condition)
        .used_variables
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

/// Check finiteness of the ranking and `[G] * K <= [G] * I + [!G]`.
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

    let finite = builder.binary(
        BinOpKind::Lt,
        Some(TyKind::Bool),
        inv.clone(),
        builder.infinity_lit(),
    );
    let condition = builder.binary(BinOpKind::And, Some(TyKind::Bool), finite, condition);
    let condition = builder.unary(UnOpKind::Embed, Some(TyKind::EUReal), condition);
    let variables = VariableCollector::from_expr(&condition)
        .used_variables
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
    variables: &VariableCollector,
) -> DeclKind {
    let span = enc_env.call_span;
    let builder = ExprBuilder::new(span);

    let modified_vars: Vec<Ident> = variables.free_modified().collect();

    // Substitute initial values only for modified variables, in expression order.
    let inv_variables: Vec<Ident> = VariableCollector::from_expr(inv)
        .used_variables
        .into_iter()
        .filter(|ident| modified_vars.contains(ident))
        .collect();

    // Initialize modified variables from the inputs of the generated procedure.
    let (mut input_init_vars, mut body) = encode_initial_state(tcx, span, &modified_vars);
    input_init_vars.extend(variables.free_read_only());
    let init_inv = to_init_expr(tcx, span, inv, &inv_variables);
    body.push(
        encode_iter(
            enc_env,
            loop_stmt,
            hey_const(span, inv, Direction::Down, tcx).into(),
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
        inputs: params_from_idents(input_init_vars, tcx),
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
