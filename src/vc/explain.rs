//! Computation of weakest (liberal) pre-expectations and variants for
//! explanations of how expectation-based reasoning works. These are not used by
//! Caesar internally, but rather used for visualizations in VSCode that are
//! used for teaching.

use std::time::{Duration, Instant};

use itertools::Itertools;
use z3::{Config, Context};

use crate::{
    ast::{
        util::remove_casts, visit::VisitorMut, BinOpKind, Block, DeclKind, Diagnostic, Direction,
        Expr, ExprBuilder, ProcDecl, Span, Stmt, StmtKind, TyKind,
    },
    intrinsic::annotations::AnnotationKind,
    opt::unfolder::Unfolder,
    pretty::SimplePretty,
    proof_rules::InvariantAnnotation,
    resource_limits::LimitsRef,
    smt::SmtCtx,
    tyctx::TyCtx,
};

use super::{
    subst::apply_subst,
    vcgen::{unsupported_stmt_diagnostic, Vcgen},
};

/// Maintains a list of [`Expr`]s for successive simplification steps.
#[derive(Debug)]
pub struct ExprExplanation {
    pub span: Span,
    steps: Vec<Expr>,
}

impl ExprExplanation {
    /// Get the expression explanation steps as strings in the order they were added.
    ///
    /// Consecutive duplicate elements will be removed.
    pub fn to_strings(&self) -> impl Iterator<Item = String> + '_ {
        self.steps
            .iter()
            .map(|expr| {
                let expr = remove_casts(expr);
                format!("{}", pretty::Doc::pretty(&expr.pretty(), usize::MAX))
            })
            .dedup()
    }
}

#[derive(Debug, Default)]
pub struct VcExplanation {
    explanations: Vec<ExprExplanation>,
}

impl VcExplanation {
    /// Adds an explanation step to the explanations. If multiple explanation
    /// steps are added for the same span, this must be done consecutively.
    pub fn add(&mut self, span: Span, expr: Expr) {
        if let Some(last) = self.explanations.last_mut() {
            if last.span == span {
                last.steps.push(expr);
                return;
            }
        }
        self.explanations.push(ExprExplanation {
            span,
            steps: vec![expr],
        });
    }
}

impl IntoIterator for VcExplanation {
    type Item = ExprExplanation;
    type IntoIter = std::vec::IntoIter<ExprExplanation>;

    fn into_iter(self) -> Self::IntoIter {
        self.explanations.into_iter()
    }
}

pub(super) fn explain_subst(vcgen: &mut Vcgen, span: Span, expr: &mut Expr) {
    if let Some(explanation) = &mut vcgen.explanation {
        // first add the original expression with substitutions
        explanation.add(span, expr.clone());

        // now the simple substitutions
        apply_subst(vcgen.tcx, expr);
        explanation.add(span, expr.clone());

        // finally, run the unfolder for more detailed simplifications
        let ctx = Context::new(&Config::default());
        let smt_ctx = SmtCtx::new(&ctx, vcgen.tcx);
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
    if let StmtKind::Annotation(ident, args, inner_stmt) = &stmt.node {
        if let StmtKind::While(_cond, body) = &inner_stmt.node {
            if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(anno_ref)) =
                vcgen.tcx.get(*ident).unwrap().as_ref()
            {
                if anno_ref
                    .as_any()
                    .downcast_ref::<InvariantAnnotation>()
                    .is_some()
                {
                    let loop_span = inner_stmt.span;
                    return explain_park_induction(vcgen, loop_span, &args[0], body);
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
            let post = extract_post(&proc);
            return Ok(Some(explain_raw_vc(tcx, body, post)?));
        }
    }
    Ok(None)
}

/// Explain verification condition generation of a [`Block`] given a post.
pub fn explain_raw_vc(tcx: &TyCtx, block: &Block, post: Expr) -> Result<VcExplanation, Diagnostic> {
    let mut vcgen = Vcgen::new(tcx, true);
    vcgen.vcgen_stmts(block, post)?;
    Ok(vcgen.explanation.unwrap())
}

fn explain_park_induction(
    vcgen: &mut Vcgen,
    loop_span: Span,
    invariant: &Expr,
    body: &Block,
) -> Result<Expr, Diagnostic> {
    let _inner_pre = explain_block(vcgen, loop_span, body, invariant);
    Ok(invariant.clone())
}

fn explain_block(
    vcgen: &mut Vcgen,
    span: Span,
    block: &Block,
    post: &Expr,
) -> Result<Expr, Diagnostic> {
    // TODO: somehow indent the span because right now the span points to the
    // column of the closing brace
    if let Some(ref mut explanation) = vcgen.explanation {
        let mut end_span = span;
        end_span.start = end_span.end - 1;
        explanation.add(end_span, post.clone());
    }
    vcgen.vcgen_stmts(block, post.clone())
}

/// Extract the post from a [`ProcDecl`].
fn extract_post(proc: &ProcDecl) -> Expr {
    let expr_builder = ExprBuilder::new(Span::dummy_span());
    let bin_op = proc.direction.map(BinOpKind::Inf, BinOpKind::Sup);
    proc.ensures()
        .cloned()
        .reduce(|acc, e| expr_builder.binary(bin_op, Some(TyKind::EUReal), acc, e))
        .unwrap_or_else(|| match proc.direction {
            Direction::Down => expr_builder.top_lit(&TyKind::EUReal),
            Direction::Up => expr_builder.bot_lit(&TyKind::EUReal),
        })
}
