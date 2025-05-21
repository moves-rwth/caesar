//! *Prove* using the SMT solver that our transformations are correct.

use itertools::Itertools;
use z3rro::{
    model::SmtEval,
    prover::{IncrementalMode, ProveResult, Prover, SolverType},
};

use crate::{
    ast::{
        visit::VisitorMut, BinOpKind, Block, DeclKind, DeclRef, Direction, Expr, ExprBuilder,
        ExprData, ExprKind, Ident, Shared, Span, Spanned, Stmt, StmtKind, Symbol, TyKind, UnOpKind,
        VarDecl, VarKind,
    },
    resource_limits::LimitsRef,
    smt::{translate_exprs::TranslateExprs, SmtCtx},
    tyctx::TyCtx,
    vc::vcgen::Vcgen,
};

use super::{
    selection::SliceSelection,
    transform::{SliceStmt, SliceStmts, StmtSliceVisitor},
};

/// Prove that the transformation for assert, assume, and tick statements is
/// correct. We run the transformation and prove using the SMT solver for all
/// parameters and posts that slicing/not slicing is equivalent to the skip/the
/// original statement, respectively.
#[test]
fn prove_unary_stmts() {
    let mut transform_tcx = TransformTestCtx::new();
    let stmt_kind_ctors = vec![
        |dir: Direction, expr: Expr| StmtKind::Assert(dir, expr),
        |dir: Direction, expr: Expr| StmtKind::Assume(dir, expr),
        |_dir: Direction, expr: Expr| StmtKind::Tick(expr),
    ];
    for ctor in stmt_kind_ctors {
        for direction in [Direction::Down, Direction::Up] {
            let stmt = Spanned::with_dummy_span(ctor(direction, transform_tcx.exp1.clone()));
            prove_slice_skip(&mut transform_tcx, &stmt).unwrap();
        }
    }
}

/// Prove that the transformation for demonic and angelic choices is correct. We
/// run the transformation and prove using the SMT solver for all constant
/// expectations in the branches and posts that slicing lhs/slicing rhs/not
/// slicing is equivalent to the constant lhs/constant rhs, or the original
/// statement, respectively.
#[test]
fn prove_nondet_branches() -> Result<(), String> {
    let mut transform_tcx = TransformTestCtx::new();
    let stmt_kind_ctors = vec![
        |stmt1: Block, stmt2: Block| StmtKind::Demonic(stmt1, stmt2),
        |stmt1: Block, stmt2: Block| StmtKind::Angelic(stmt1, stmt2),
    ];
    for ctor in stmt_kind_ctors {
        let stmt = Spanned::with_dummy_span(ctor(
            Spanned::with_dummy_span(hey_const(&transform_tcx.exp1, &transform_tcx.tcx)),
            Spanned::with_dummy_span(hey_const(&transform_tcx.exp2, &transform_tcx.tcx)),
        ));
        prove_slice_branch(&mut transform_tcx, &stmt)?;
    }
    Ok(())
}

struct TransformTestCtx {
    tcx: TyCtx,
    post: Expr,
    exp1: Expr,
    exp2: Expr,
}

impl TransformTestCtx {
    fn new() -> Self {
        let tcx = TyCtx::new(TyKind::EUReal);
        let names: Vec<Ident> = ["post", "exp1", "exp2"]
            .iter()
            .map(|&s| Ident::with_dummy_span(Symbol::intern(s)))
            .collect();
        for name in &names {
            tcx.declare(DeclKind::VarDecl(DeclRef::new(VarDecl {
                name: *name,
                ty: TyKind::EUReal,
                kind: VarKind::Input,
                init: None,
                span: Span::dummy_span(),
                created_from: None,
            })))
        }
        Self {
            tcx,
            post: ident_to_expr(names[0], TyKind::EUReal),
            exp1: ident_to_expr(names[1], TyKind::EUReal),
            exp2: ident_to_expr(names[2], TyKind::EUReal),
        }
    }
}

fn prove_equiv(
    transform_tcx: &TransformTestCtx,
    stmt1: &[Stmt],
    stmt2: &[Stmt],
    assumptions: &[Expr],
) -> Result<(), String> {
    let tcx = &transform_tcx.tcx;
    let builder = ExprBuilder::new(Span::dummy_span());

    let mut vcgen = Vcgen::new(tcx, &LimitsRef::new(None, None), None);
    let stmt1_vc = vcgen
        .vcgen_stmts(stmt1, transform_tcx.post.clone())
        .unwrap();
    let stmt2_vc = vcgen
        .vcgen_stmts(stmt2, transform_tcx.post.clone())
        .unwrap();

    let eq_expr = builder.binary(
        BinOpKind::Eq,
        Some(TyKind::Bool),
        stmt1_vc.clone(),
        stmt2_vc.clone(),
    );
    let ctx = z3::Context::new(&z3::Config::new());
    let smt_ctx = SmtCtx::new(&ctx, tcx);
    let mut translate = TranslateExprs::new(&smt_ctx);
    let eq_expr_z3 = translate.t_bool(&eq_expr);
    let mut prover = Prover::new(&ctx, IncrementalMode::Native, SolverType::Z3);
    translate
        .local_scope()
        .add_assumptions_to_prover(&mut prover);
    for assumption in assumptions {
        let assumption_z3 = translate.t_bool(assumption);
        prover.add_assumption(&assumption_z3);
    }
    prover.add_provable(&eq_expr_z3);
    let x = match prover.check_proof() {
        Ok(ProveResult::Proof) => Ok(()),
        Ok(ProveResult::Counterexample) => {
            let model = prover.get_model().unwrap();
            Err(format!(
                "we want to rewrite {:?} ...into... {:?} under assumptions {:?}, but those are not equivalent:\n{}\n original evaluates to {}\n rewritten evaluates to {}",
            stmt1, stmt2, assumptions, &model, translate.t_eureal(&stmt1_vc).eval(&model).unwrap(), translate.t_eureal(&stmt2_vc).eval(&model).unwrap()
        ))
        }
        Ok(ProveResult::Unknown(reason)) => Err(format!("unknown result ({})", reason)),
        Err(err) => Err(format!("{}", err)),
    };
    x
}

fn prove_slice_skip(transform_tcx: &mut TransformTestCtx, stmt: &Stmt) -> Result<(), String> {
    for direction in [Direction::Down, Direction::Up] {
        let (stmt_sliced, slice_stmts) = transform_stmt(transform_tcx, stmt, direction);
        assert_eq!(slice_stmts.stmts.len(), 1);
        let slice_variable = slice_variable_to_expr(&slice_stmts.stmts[0]);
        let negated_slice_variable = negate(slice_variable.clone());

        prove_equiv(
            transform_tcx,
            &[stmt.clone()],
            &[stmt_sliced.clone()],
            &[slice_variable],
        )?;

        let skip_stmt = Spanned::with_dummy_span(StmtKind::Seq(vec![]));
        prove_equiv(
            transform_tcx,
            &[skip_stmt],
            &[stmt_sliced],
            &[negated_slice_variable],
        )?;
    }
    Ok(())
}

fn prove_slice_branch(transform_tcx: &mut TransformTestCtx, stmt: &Stmt) -> Result<(), String> {
    for direction in [Direction::Down, Direction::Up] {
        let (stmt_sliced, slice_stmts) = transform_stmt(transform_tcx, stmt, direction);
        assert_eq!(slice_stmts.stmts.len(), 6);
        let slice_lhs = slice_variable_to_expr(&slice_stmts.stmts[4]);
        let not_slice_lhs = negate(slice_lhs.clone());
        let slice_rhs = slice_variable_to_expr(&slice_stmts.stmts[5]);
        let not_slice_rhs = negate(slice_rhs.clone());

        let with_context = |vars: Vec<Expr>| -> Vec<Expr> {
            slice_stmts
                .constraints
                .iter()
                .cloned()
                .chain(vars.into_iter())
                .chain((0..=3).map(|i| slice_variable_to_expr(&slice_stmts.stmts[i])))
                .collect_vec()
        };

        prove_equiv(
            transform_tcx,
            &hey_const(&transform_tcx.exp2, &transform_tcx.tcx),
            &[stmt_sliced.clone()],
            &with_context(vec![not_slice_lhs.clone()]),
        )?;

        prove_equiv(
            transform_tcx,
            &hey_const(&transform_tcx.exp1, &transform_tcx.tcx),
            &[stmt_sliced.clone()],
            &with_context(vec![not_slice_rhs.clone()]),
        )?;

        prove_equiv(
            transform_tcx,
            &[stmt.clone()],
            &[stmt_sliced.clone()],
            &with_context(vec![not_slice_lhs, not_slice_rhs]),
        )?;
    }
    Ok(())
}

fn transform_stmt(
    transform_tcx: &mut TransformTestCtx,
    stmt: &Stmt,
    direction: Direction,
) -> (Stmt, SliceStmts) {
    let mut stmt_sliced = stmt.clone();
    let mut transformer = StmtSliceVisitor::new(
        &mut transform_tcx.tcx,
        direction,
        SliceSelection::EVERYTHING,
    );
    transformer.visit_stmt(&mut stmt_sliced).unwrap();
    let slice_stmts = transformer.finish();
    (stmt_sliced, slice_stmts)
}

fn slice_variable_to_expr(slice_stmt: &SliceStmt) -> Expr {
    ident_to_expr(slice_stmt.ident, TyKind::Bool)
}

fn negate(expr: Expr) -> Expr {
    let builder = ExprBuilder::new(Span::dummy_span());
    builder.unary(UnOpKind::Not, Some(TyKind::Bool), expr)
}

fn ident_to_expr(ident: Ident, ty: TyKind) -> Expr {
    Shared::new(ExprData {
        kind: ExprKind::Var(ident),
        ty: Some(ty),
        span: Span::dummy_span(),
    })
}

fn hey_const(expr: &Expr, tcx: &TyCtx) -> Vec<Stmt> {
    let span = Span::dummy_span();
    let builder = ExprBuilder::new(span);
    vec![
        Spanned::new(span, StmtKind::Assert(Direction::Down, expr.clone())),
        Spanned::new(
            span,
            StmtKind::Assume(Direction::Down, builder.bot_lit(tcx.spec_ty())),
        ),
    ]
}
