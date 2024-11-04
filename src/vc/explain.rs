//! Computation of weakest (liberal) pre-expectations and variants for
//! explanations of how expectation-based reasoning works. These are not used by
//! Caesar internally, but rather used for visualizations in VSCode that are
//! used for teaching.

use std::{
    mem,
    time::{Duration, Instant},
};

use itertools::Itertools;
use z3::{Config, Context};

use super::{
    subst::apply_subst,
    vcgen::{unsupported_stmt_diagnostic, Vcgen},
};
use crate::smt::SmtCtxOptions;
use crate::{
    ast::{
        util::remove_casts, visit::VisitorMut, BinOpKind, Block, DeclKind, DeclRef, Diagnostic,
        Direction, Expr, ExprBuilder, Files, Ident, ProcDecl, Span, Spanned, Stmt, StmtKind,
        Symbol, TyKind,
    },
    intrinsic::annotations::AnnotationKind,
    opt::unfolder::Unfolder,
    pretty::SimplePretty,
    proof_rules::{
        self, encode_unroll, hey_const, negations::DirectionTracker, EncodingEnvironment,
        InvariantAnnotation, UnrollAnnotation,
    },
    resource_limits::LimitsRef,
    smt::SmtCtx,
    tyctx::TyCtx,
};

/// Maintains a list of [`Expr`]s for successive simplification steps.
#[derive(Debug)]
pub struct ExprExplanation {
    pub span: Span,
    pub is_block_itself: bool,
    pub block: Option<Span>,
    steps: Vec<Expr>,
}

impl ExprExplanation {
    /// Remove all steps that cannot fit into the surrounding block, starting
    /// with the earliest steps.
    pub fn shrink_to_block(&mut self, files: &Files) {
        let block_span = if let Some(block_span) = self.block {
            block_span
        } else {
            return;
        };
        let (_file, block_start_line, _block_start_col) =
            files.get_human_span_start(block_span).unwrap();
        let (_file, span_start_line, _span_start_col) =
            files.get_human_span_start(self.span).unwrap();

        if span_start_line < block_start_line {
            let expl = self.to_strings().map(|p| p.0).collect_vec();
            tracing::debug!(
                ?span_start_line,
                ?block_start_line,
                ?expl,
                "Not printing explanation because its span starts before its surrounding block"
            );
        }
        let space = span_start_line
            .saturating_sub(block_start_line)
            .saturating_sub(1);
        self.steps.drain(0..self.steps.len().saturating_sub(space));
    }

    /// Get the expression explanation steps as strings in the order they were added.
    ///
    /// Consecutive duplicate elements will be removed.
    pub fn to_strings(&self) -> impl Iterator<Item = (String, String)> + '_ {
        self.steps
            .iter()
            .map(|expr| {
                let expr = remove_casts(expr);
                let pretty = expr.pretty();
                let one_line = format!("{}", pretty::Doc::pretty(&pretty, usize::MAX));
                let hover = format!("{}", pretty::Doc::pretty(&pretty, 80));
                (one_line, hover)
            })
            .dedup()
    }
}

/// Data structure to track all vc explanation information that is generated
/// during vc generation.
///
/// It is important that the `direction` field is correctly updated to ensure
/// that the encodings are done with respect to the correct direction when using
/// negation statements.
#[derive(Debug, Default)]
pub struct VcExplanation {
    /// The direction is needed to run proof rule encodings in explanations.
    pub direction: DirectionTracker,
    /// A stack of explanations for expressions.
    exprs: Vec<ExprExplanation>,
    /// The current block which is being processed. This is used to remove
    /// explanations which would show up outside of the surrounding block.
    current_block: Option<Span>,
}

impl VcExplanation {
    pub fn new(direction: Direction) -> Self {
        Self {
            direction: DirectionTracker::new(direction),
            ..Default::default()
        }
    }

    /// Adds an explanation step to the explanations. If multiple explanation
    /// steps are added for the same span, this must be done consecutively.
    pub fn add_expr(&mut self, span: Span, expr: Expr, is_block_itself: bool) {
        if let Some(last) = self.exprs.last_mut() {
            if last.span == span {
                assert_eq!(last.block, self.current_block);
                last.steps.push(expr);
                return;
            }
        }
        self.exprs.push(ExprExplanation {
            span,
            is_block_itself,
            block: self.current_block,
            steps: vec![expr],
        });
    }

    pub fn set_block_span(&mut self, span: Option<Span>) -> Option<Span> {
        mem::replace(&mut self.current_block, span)
    }
}

impl IntoIterator for VcExplanation {
    type Item = ExprExplanation;
    type IntoIter = std::vec::IntoIter<ExprExplanation>;

    fn into_iter(self) -> Self::IntoIter {
        self.exprs.into_iter()
    }
}

/// Explain an expression with substitutions. This will add the expression
/// itself and the expression with applied substitutions to the explanations.
/// Finally, simplifications are applied (then the modified expression should be
/// added to explanations by the caller).
pub(super) fn explain_subst(vcgen: &mut Vcgen, span: Span, expr: &mut Expr) {
    if let Some(explanation) = &mut vcgen.explanation {
        // first add the original expression with substitutions
        explanation.add_expr(span, expr.clone(), false);

        // now the simple substitutions
        apply_subst(vcgen.tcx, expr);
        explanation.add_expr(span, expr.clone(), false);

        // finally, run the unfolder for more detailed simplifications
        let ctx = Context::new(&Config::default());
        let smt_ctx = SmtCtx::new(&ctx, vcgen.tcx, SmtCtxOptions::default());
        let deadline = Instant::now() + Duration::from_millis(1);
        let mut unfolder = Unfolder::new(LimitsRef::new(Some(deadline)), &smt_ctx);
        let _ = unfolder.visit_expr(expr);
        // the last value will be added to the explanations automatically in vcgen_stmt
    }
}

pub(super) fn explain_annotated_while(
    vcgen: &mut Vcgen,
    stmt: &Stmt,
    _post: &Expr,
) -> Result<Expr, Diagnostic> {
    if let StmtKind::Annotation(anno_span, ident, args, inner_stmt) = &stmt.node {
        if let StmtKind::While(_, body) = &inner_stmt.node {
            if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(anno_ref)) =
                vcgen.tcx.get(*ident).unwrap().as_ref()
            {
                if anno_ref
                    .as_any()
                    .downcast_ref::<InvariantAnnotation>()
                    .is_some()
                {
                    return explain_park_induction(vcgen, &args[0], body);
                }

                if anno_ref
                    .as_any()
                    .downcast_ref::<UnrollAnnotation>()
                    .is_some()
                {
                    return explain_unroll(vcgen, inner_stmt, args, stmt.span, *anno_span);
                }
            }
        }
    }

    Err(unsupported_stmt_diagnostic(stmt))
}

/// Explain verification condition of a declaration. Right now, this only
/// returns `Some` for [`DeclKind::ProcDecl`].
pub fn explain_decl_vc(
    tcx: &TyCtx,
    decl_kind: &DeclKind,
) -> Result<Option<VcExplanation>, Diagnostic> {
    if let DeclKind::ProcDecl(decl_ref) = decl_kind {
        let proc = decl_ref.borrow();
        let body = proc.body.borrow();
        if let Some(ref body) = *body {
            let post = fold_spec(&proc, proc.ensures());
            let res = explain_raw_vc(tcx, body, post, proc.direction)?;
            return Ok(Some(res));
        }
    }
    Ok(None)
}

/// Explain verification condition generation of a [`Block`] given a post.
pub fn explain_raw_vc(
    tcx: &TyCtx,
    block: &Block,
    post: Expr,
    direction: Direction,
) -> Result<VcExplanation, Diagnostic> {
    let mut vcgen = Vcgen::new(tcx, Some(VcExplanation::new(direction)));
    vcgen.vcgen_block(block, post)?;
    Ok(vcgen.explanation.unwrap())
}

fn explain_park_induction(
    vcgen: &mut Vcgen,
    invariant: &Expr,
    body: &Block,
) -> Result<Expr, Diagnostic> {
    let _inner_pre = vcgen.vcgen_block(body, invariant.clone());
    Ok(invariant.clone())
}

fn explain_unroll(
    vcgen: &mut Vcgen,
    loop_stmt: &Stmt,
    args: &[Expr],
    stmt_span: Span,
    call_span: Span,
) -> Result<Expr, Diagnostic> {
    let k = proof_rules::lit_u128(&args[0]);
    let terminator = &args[1];
    let direction = *vcgen.explanation.as_ref().unwrap().direction;

    // 1. generate the explanations for the loop body in the initial iteration
    if let StmtKind::While(_d, body) = &loop_stmt.node {
        // we do not use the pre-vc of the initial iteration, but the generated
        // explanations are stored in `vcgen`.
        let _inner_pre = vcgen.vcgen_block(body, terminator.clone());
    } else {
        unreachable!();
    }

    // 2. compute the pre-vc of of unrolling

    // unroll the loop
    let enc_env = EncodingEnvironment {
        // this name is not used during unrolling, so we use a dummy
        base_proc_ident: Ident::with_dummy_span(Symbol::intern("unroll_env")),
        stmt_span,
        call_span,
        direction,
    };
    let unrolled_stmts = encode_unroll(
        &enc_env,
        loop_stmt,
        k,
        hey_const(&enc_env, terminator, direction, vcgen.tcx),
    );
    let unrolled_block = Spanned::new(enc_env.stmt_span, unrolled_stmts);

    // generate pre-vc of unrolled loop with temporary vcgen
    let mut temp_vcgen = Vcgen::new(vcgen.tcx, None);
    let mut return_expr = temp_vcgen.vcgen_block(&unrolled_block, terminator.clone())?;

    // apply substitutions and simplify the pre-vc of the unrolled loop, add it
    // to our explanations in `vcgen`.
    explain_subst(vcgen, stmt_span, &mut return_expr);

    Ok(return_expr)
}

/// To explain a proc call, we just return the pre with the parameters
/// substituted.
pub(super) fn explain_proc_call(
    decl_ref: &DeclRef<ProcDecl>,
    args: &[Expr],
    builder: &ExprBuilder,
) -> Expr {
    let decl = decl_ref.borrow();
    builder.subst(
        fold_spec(&decl, decl.requires()),
        decl.inputs
            .node
            .iter()
            .zip(args)
            .map(|(param, arg)| (param.name, arg.clone())),
    )
}

/// Fold a list of specification parts (either requires or ensures) into a
/// single expression depending on the proc direction.
fn fold_spec<'a>(proc: &'a ProcDecl, spec: impl IntoIterator<Item = &'a Expr>) -> Expr {
    let expr_builder = ExprBuilder::new(Span::dummy_span());
    let bin_op = proc.direction.map(BinOpKind::Inf, BinOpKind::Sup);
    spec.into_iter()
        .cloned()
        .reduce(|acc, e| expr_builder.binary(bin_op, Some(TyKind::EUReal), acc, e))
        .unwrap_or_else(|| match proc.direction {
            Direction::Down => expr_builder.top_lit(&TyKind::EUReal),
            Direction::Up => expr_builder.bot_lit(&TyKind::EUReal),
        })
}
