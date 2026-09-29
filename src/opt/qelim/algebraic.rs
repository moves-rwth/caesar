//! Value-preserving algebraic quantifier elimination.
//!
//! These identities apply in all expression contexts, independently of proof polarity.

use std::ops::BitAnd;

use crate::ast::{
    util::FreeVariableCollector,
    visit::{walk_expr, VisitorMut},
    BinOpKind, Expr, ExprBuilder, ExprKind, Ident, QuantOpKind, SpanVariant, TyKind, UnOpKind,
};

use super::is_finite;

#[derive(Clone, Copy, PartialEq, Eq)]
enum BoundKind {
    Infimum,
    Supremum,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attainment {
    /// For every valuation of the other variables, some index makes the original body equal to the replacement.
    Guaranteed,
    /// No assertion about attainment.
    Unknown,
}

impl BitAnd for Attainment {
    type Output = Self;

    /// Conjunction of guarantees: guaranteed only when both operands are guaranteed.
    fn bitand(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::Guaranteed, Self::Guaranteed) => Self::Guaranteed,
            _ => Self::Unknown,
        }
    }
}

/// An equal-valued `EUReal` replacement for an infimum or supremum, with an attainment guarantee for its original body.
struct EliminationResult {
    replacement: Expr,
    attainment: Attainment,
}

pub fn eliminate(expr: &mut Expr) {
    AlgebraicQelim.visit_expr(expr).unwrap();
}

struct AlgebraicQelim;

impl VisitorMut for AlgebraicQelim {
    type Err = ();

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        walk_expr(self, expr)?;
        if let Some(replacement) =
            elim_single_index(expr).or_else(|| push_quantifier_into_embed(expr))
        {
            *expr = replacement;
        }
        Ok(())
    }
}

/// inf_i ?P_i = ?(forall i. P_i), and sup_i ?P_i = ?(exists i. P_i).
fn push_quantifier_into_embed(expr: &Expr) -> Option<Expr> {
    let ExprKind::Quant(op, vars, ann, body) = &expr.kind else {
        return None;
    };
    let quantifier = match op.node {
        QuantOpKind::Inf => QuantOpKind::Forall,
        QuantOpKind::Sup => QuantOpKind::Exists,
        QuantOpKind::Forall | QuantOpKind::Exists => return None,
    };
    let ExprKind::Unary(embedding, predicate) = &strip_numeric_wrappers(body).kind else {
        return None;
    };
    if embedding.node != UnOpKind::Embed {
        return None;
    }
    let builder = ExprBuilder::new(expr.span.variant(SpanVariant::Qelim));
    let predicate =
        builder.quant_with_bindings(quantifier, vars.clone(), ann.clone(), predicate.clone());
    Some(builder.unary(UnOpKind::Embed, Some(TyKind::EUReal), predicate))
}

/// Apply the numeric identities to a quantifier with one bound variable.
fn elim_single_index(expr: &Expr) -> Option<Expr> {
    let ExprKind::Quant(op, vars, _, body) = &expr.kind else {
        return None;
    };
    let [var] = vars.as_slice() else {
        return None;
    };
    let bound = match op.node {
        QuantOpKind::Inf => BoundKind::Infimum,
        QuantOpKind::Sup => BoundKind::Supremum,
        QuantOpKind::Forall | QuantOpKind::Exists => return None,
    };
    let builder = ExprBuilder::new(expr.span.variant(SpanVariant::Qelim));
    elim_quantified_body(bound, var.name(), body, builder).map(|result| result.replacement)
}

/// Eliminate `inf index. body` or `sup index. body`.
/// Returns a replacement with its attainment guarantee, or `None` if no rule applies.
fn elim_quantified_body(
    bound: BoundKind,
    index: Ident,
    body: &Expr,
    builder: ExprBuilder,
) -> Option<EliminationResult> {
    use Attainment::{Guaranteed, Unknown};
    use BoundKind::{Infimum, Supremum};

    if !is_nonnegative(body) {
        return None;
    }
    // inf_i c = c and sup_i c = c, when c does not depend on i.
    // Every index attains the bound.
    if independent_of(body, index) {
        return Some(EliminationResult {
            replacement: builder.cast(TyKind::EUReal, body.clone()),
            attainment: Guaranteed,
        });
    }
    let eliminate = |body| elim_quantified_body(bound, index, body, builder);
    let body = strip_numeric_wrappers(body);
    match &body.kind {
        // inf_i i = 0 and sup_i i = ∞, for i: UInt, UReal, or EUReal.
        // Zero belongs to all three domains; infinity belongs only to EUReal.
        ExprKind::Var(var) if *var == index => Some(EliminationResult {
            replacement: match bound {
                Infimum => builder.bot_lit(&TyKind::EUReal),
                Supremum => builder.infinity_lit(),
            },
            attainment: if bound == Infimum || body.ty == Some(TyKind::EUReal) {
                Guaranteed
            } else {
                Unknown
            },
        }),
        // inf_i ite(b, f_i, g_i) = ite(b, inf_i f_i, inf_i g_i).
        // sup_i ite(b, f_i, g_i) = ite(b, sup_i f_i, sup_i g_i).
        // An index-independent condition preserves attainment if both branches guarantee it.
        ExprKind::Ite(cond, lhs, rhs) if independent_of(cond, index) => {
            let lhs = eliminate(lhs)?;
            let rhs = eliminate(rhs)?;
            Some(EliminationResult {
                replacement: builder.ite(
                    Some(TyKind::EUReal),
                    cond.clone(),
                    lhs.replacement,
                    rhs.replacement,
                ),
                attainment: lhs.attainment & rhs.attainment,
            })
        }
        // inf_i (f_i + c) = (inf_i f_i) + c, and sup_i (f_i + c) = (sup_i f_i) + c.
        // inf_i (f_i * c) = (inf_i f_i) * c, and sup_i (f_i * c) = (sup_i f_i) * c.
        // The operands must be nonnegative, and c must not depend on i.
        ExprKind::Binary(op, lhs, rhs) if matches!(op.node, BinOpKind::Add | BinOpKind::Mul) => {
            let constant = if independent_of(lhs, index) {
                lhs
            } else if independent_of(rhs, index) {
                rhs
            } else {
                return None;
            };
            let lhs = eliminate(lhs)?;
            let rhs = eliminate(rhs)?;
            // The constant is attained, so conjunction retains the dependent operand's guarantee.
            let attainment = lhs.attainment & rhs.attainment;
            // For infimum scaling, c < ∞ or attainment of inf_i f_i is sufficient.
            // For f_i = 1/(i+1), inf_i (∞ * f_i) = ∞, whereas ∞ * (inf_i f_i) = 0.
            if op.node == BinOpKind::Mul
                && bound == Infimum
                && !is_finite(constant)
                && attainment != Guaranteed
            {
                return None;
            }
            // Addition and scaling preserve any index attaining the dependent operand's bound.
            Some(EliminationResult {
                replacement: builder.binary(
                    op.node,
                    Some(TyKind::EUReal),
                    lhs.replacement,
                    rhs.replacement,
                ),
                attainment,
            })
        }
        ExprKind::Unary(op, condition) if op.node == UnOpKind::Iverson => Some(EliminationResult {
            replacement: elim_threshold(bound, index, condition, builder)?,
            attainment: Guaranteed,
        }),
        _ => None,
    }
}

/// Infima and suprema of threshold indicators.
/// The index has type `UInt`, `UReal`, or `EUReal`, and `t` is independent of the index with `0 ≤ t < ∞`.
///
/// | Condition | Supremum | Infimum |
/// |-----------|----------|---------|
/// | i < t     | [t > 0]  | 0       |
/// | i <= t    | 1        | 0       |
/// | i > t     | 1        | 0       |
/// | i >= t    | 1        | [t = 0] |
///
/// Both bounds are attained because each indicator has a nonempty, finite range.
fn elim_threshold(
    bound: BoundKind,
    index: Ident,
    condition: &Expr,
    builder: ExprBuilder,
) -> Option<Expr> {
    let (comparison, threshold) = match_threshold(index, condition)?;
    let zero_comparison = match (bound, comparison) {
        (BoundKind::Supremum, BinOpKind::Le | BinOpKind::Ge | BinOpKind::Gt) => {
            return Some(builder.one_lit(&TyKind::EUReal));
        }
        (BoundKind::Infimum, BinOpKind::Lt | BinOpKind::Le | BinOpKind::Gt) => {
            return Some(builder.bot_lit(&TyKind::EUReal));
        }
        (BoundKind::Supremum, BinOpKind::Lt) => BinOpKind::Gt,
        (BoundKind::Infimum, BinOpKind::Ge) => BinOpKind::Eq,
        _ => return None,
    };
    let condition = builder.binary(
        zero_comparison,
        Some(TyKind::Bool),
        threshold.clone(),
        builder.bot_lit(threshold.ty.as_ref().unwrap()),
    );
    Some(builder.unary(UnOpKind::Iverson, Some(TyKind::EUReal), condition))
}

/// Match a threshold comparison with the nonnegative index on the left.
/// The threshold must be nonnegative, finite, and independent of the index.
fn match_threshold(index: Ident, condition: &Expr) -> Option<(BinOpKind, &Expr)> {
    let ExprKind::Binary(comparison, lhs, rhs) = &strip_numeric_wrappers(condition).kind else {
        return None;
    };
    // Put the index on the left: t < i becomes i > t, and t <= i becomes i >= t.
    let (comparison, threshold) = if is_nonnegative_index(lhs, index) {
        (comparison.node, rhs)
    } else if is_nonnegative_index(rhs, index) {
        let reversed = match comparison.node {
            BinOpKind::Le => BinOpKind::Ge,
            BinOpKind::Lt => BinOpKind::Gt,
            BinOpKind::Ge => BinOpKind::Le,
            BinOpKind::Gt => BinOpKind::Lt,
            _ => return None,
        };
        (reversed, lhs)
    } else {
        return None;
    };
    let threshold = strip_numeric_wrappers(threshold);
    if !is_nonnegative(threshold) || !is_finite(threshold) || !independent_of(threshold, index) {
        return None;
    }
    Some((comparison, threshold))
}

/// Whether `index` is absent from the free variables of `expr`.
fn independent_of(expr: &Expr, index: Ident) -> bool {
    !FreeVariableCollector::new()
        .collect_and_clear(&mut expr.clone())
        .contains(&index)
}

fn is_nonnegative(expr: &Expr) -> bool {
    matches!(expr.ty, Some(TyKind::UInt | TyKind::UReal | TyKind::EUReal))
}

/// Ignore parentheses and value-preserving casts between nonnegative numeric types.
fn strip_numeric_wrappers(expr: &Expr) -> &Expr {
    match &expr.kind {
        ExprKind::Unary(op, inner) if op.node == UnOpKind::Parens => strip_numeric_wrappers(inner),
        ExprKind::Cast(inner) if is_nonnegative(expr) && is_nonnegative(inner) => {
            strip_numeric_wrappers(inner)
        }
        _ => expr,
    }
}

fn is_nonnegative_index(expr: &Expr, index: Ident) -> bool {
    let expr = strip_numeric_wrappers(expr);
    is_nonnegative(expr) && matches!(&expr.kind, ExprKind::Var(var) if *var == index)
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{
            stats::StatsVisitor, util::remove_casts, visit::VisitorMut, DeclKind, DeclRef,
            Direction, Expr, ExprBuilder, ExprKind, FileId, Ident, QuantOpKind, Span, Symbol,
            TyKind, VarDecl, VarKind,
        },
        depgraph::DepGraph,
        driver::quant_proof::QuantVcProveTask,
        front::{parser, resolve::Resolve, tycheck::Tycheck},
        opt::RemoveParens,
        smt::funcs::axiomatic::AxiomInstantiation,
        tyctx::TyCtx,
    };

    use super::super::qelim;
    use super::{elim_quantified_body, eliminate, Attainment, BoundKind};

    fn parse_typed(source: &str) -> (TyCtx, Expr) {
        let mut tcx = TyCtx::new(TyKind::EUReal);
        for (name, ty) in [
            ("t", TyKind::UInt),
            ("r", TyKind::UReal),
            ("f", TyKind::EUReal),
            ("g", TyKind::EUReal),
            ("b", TyKind::Bool),
            ("z", TyKind::Int),
        ] {
            let name = Ident::with_dummy_span(Symbol::intern(name));
            tcx.declare(DeclKind::VarDecl(DeclRef::new(VarDecl {
                name,
                ty,
                kind: VarKind::Input,
                init: None,
                span: Span::dummy_span(),
                created_from: None,
            })));
            tcx.add_global(name);
        }
        let mut expr = parser::parse_expr(FileId::DUMMY, source).unwrap();
        Resolve::new(&mut tcx).visit_expr(&mut expr).unwrap();
        Tycheck::new(&mut tcx).visit_expr(&mut expr).unwrap();
        (tcx, expr)
    }

    fn assert_rewrite(source: &str, expected: &str) {
        let (_, mut expr) = parse_typed(source);
        eliminate(&mut expr);
        assert_replacement(expr, expected, source);
    }

    fn assert_elimination(source: &str, expected: &str, attainment: Attainment) {
        let (_, expr) = parse_typed(source);
        let ExprKind::Quant(op, vars, _, body) = &expr.kind else {
            panic!("expected a quantifier: {source}");
        };
        let [var] = vars.as_slice() else {
            panic!("expected one bound variable: {source}");
        };
        let bound = match op.node {
            QuantOpKind::Inf => BoundKind::Infimum,
            QuantOpKind::Sup => BoundKind::Supremum,
            _ => panic!("expected inf or sup: {source}"),
        };
        let result = elim_quantified_body(bound, var.name(), body, ExprBuilder::new(expr.span))
            .unwrap_or_else(|| panic!("{source}"));
        assert_eq!(result.attainment, attainment, "{source}");
        assert_replacement(result.replacement, expected, source);
    }

    fn assert_replacement(mut expr: Expr, expected: &str, source: &str) {
        RemoveParens.visit_expr(&mut expr).unwrap();
        let (_, mut expected) = parse_typed(expected);
        // Match the EUReal result type of inf/sup.
        expected = ExprBuilder::new(Span::dummy_span()).cast(TyKind::EUReal, expected);
        RemoveParens.visit_expr(&mut expected).unwrap();
        assert_eq!(expr.ty, expected.ty, "{source}");
        assert_eq!(
            remove_casts(&expr).to_string(),
            remove_casts(&expected).to_string(),
            "{source}"
        );
    }

    #[test]
    fn numeric_bounds_and_attainment() {
        use Attainment::{Guaranteed, Unknown};

        for (ty, index_supremum) in [
            ("UInt", Unknown),
            ("UReal", Unknown),
            ("EUReal", Guaranteed),
        ] {
            for (body, infimum, supremum, attained) in [
                ("f", "f", "f", Guaranteed),
                ("i * f + g", "0 * f + g", "∞ * f + g", index_supremum),
                (
                    "ite(b, i, f)",
                    "ite(b, 0, f)",
                    "ite(b, ∞, f)",
                    index_supremum,
                ),
                (
                    "ite(b, [i < r], f)",
                    "ite(b, 0, f)",
                    "ite(b, [r > 0], f)",
                    Guaranteed,
                ),
            ] {
                assert_elimination(&format!("inf i: {ty}. {body}"), infimum, Guaranteed);
                assert_elimination(&format!("sup i: {ty}. {body}"), supremum, attained);
            }
        }
        assert_elimination(
            "sup i: UInt. ite(b, f, g * (f + i))",
            "ite(b, f, g * (f + ∞))",
            Unknown,
        );
        assert_elimination("inf i: Int. f", "f", Guaranteed);
        assert_elimination("sup i: Bool. f", "f", Guaranteed);
    }

    #[test]
    fn threshold_extrema() {
        for (condition, reversed, infimum, supremum) in [
            ("i < r", "r > i", "0", "[r > 0]"),
            ("i <= r", "r >= i", "0", "1"),
            ("i > r", "r < i", "0", "1"),
            ("i >= r", "r <= i", "[r == 0]", "1"),
        ] {
            for condition in [condition, reversed] {
                assert_rewrite(&format!("inf i: UInt. [{condition}]"), infimum);
                assert_rewrite(&format!("sup i: UInt. [{condition}]"), supremum);
            }
        }
        assert_rewrite("sup i: UReal. [r <= i]", "1");
        assert_rewrite("inf i: EUReal. [i >= r]", "[r == 0]");
        assert_rewrite("sup i: UInt. [[b] <= i]", "1");
    }

    #[test]
    fn embedded_quantifiers() {
        for (bound, boolean_bound) in [("inf", "forall"), ("sup", "exists")] {
            for (binders, predicate) in [
                ("i: Real", "i * i == 2"),
                ("i: Int, j: Bool", "i < z && j"),
                ("i: UInt @trigger(i + 1)", "i == t"),
            ] {
                let source = format!("{bound} {binders}. ?({predicate})");
                let expected = format!("?({boolean_bound} {binders}. {predicate})");
                assert_rewrite(&source, &expected);
            }
            assert_rewrite(&format!("{bound} i: UInt. ?b"), "?b");
        }
    }

    #[test]
    fn recursive_arithmetic_and_infinite_scaling() {
        assert_rewrite("sup i: UInt. f * i * g", "f * ∞ * g");
        assert_rewrite("inf i: UInt. f * (i + g)", "f * (0 + g)");
        assert_rewrite("sup i: UInt. 0 * (i + g)", "0 * (∞ + g)");
        assert_rewrite("sup i: UInt. i * ∞ * 0", "∞ * ∞ * 0");
        assert_rewrite("inf i: UInt. ∞ * (i + g)", "∞ * (0 + g)");
        assert_rewrite("sup i: UInt. [t + 1 <= i] * f + g", "1 * f + g");
    }

    #[test]
    fn algebraic_and_polarity_elimination() {
        use Direction::{Down, Up};

        for (direction, source) in [
            (Down, "inf i: UInt. ?(i == t)"),
            (Up, "sup i: UInt. ?(i == t)"),
            (
                Down,
                "((inf i: UInt. i + [true]) ⊓ (inf j: Bool. [j])) * (1 ⊓ (inf k: Bool. [k]))",
            ),
            (
                Up,
                "((sup i: UInt. [i <= t]) ⊓ (sup j: Bool. [j])) * (1 ⊓ (sup k: Bool. [k]))",
            ),
        ] {
            let (mut tcx, expr) = parse_typed(source);
            let mut task = QuantVcProveTask {
                deps: DepGraph::new(AxiomInstantiation::Decreasing).get_reachable([]),
                direction,
                expr,
            };
            qelim(&mut tcx, &mut task);
            let mut stats = StatsVisitor::default();
            stats.visit_expr(&mut task.expr).unwrap();
            assert_eq!(stats.stats.num_quants, 0, "{source}: {}", task.expr);
        }
        assert_rewrite("inf i: UInt. i * (sup j: UInt. [i <= j])", "0 * 1");
    }

    #[test]
    fn reject_unsupported_bodies() {
        for source in [
            "sup i: UInt. [i + 1 <= i] * f",
            "sup i: UInt. [t <= i] * i",
            "sup i: UInt. [f <= i] * g",
            "sup i: UInt. [z <= i] * f",
            "sup i: UInt. [t <= i] * f + [i < t] * g",
            "sup i: UInt. ite(i <= t, i * f, g)",
            "sup i: Int. [t <= i] * f",
            "sup i: UInt, j: UInt. [t <= i] * f",
            // inf_i 1/(i+1) = 0 is unattained, so infinite scaling would be invalid.
            "inf i: UInt. ∞ * (1 / (i + 1))",
        ] {
            assert_rewrite(source, source);
        }
    }
}
