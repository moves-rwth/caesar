use std::{
    collections::HashMap,
    fmt,
    ops::{BitAnd, DerefMut},
    vec,
};

use ariadne::ReportKind;
use itertools::Itertools;
use z3rro::prover::ProveResult;

use crate::{
    ast::{Block, DeclKind, Diagnostic, Direction, Label, ProcDecl, Span, Stmt, StmtKind},
    driver::{
        front::{Module, SourceUnit},
        item::SourceUnitName,
    },
    intrinsic::annotations::{AnnotationKind, Calculus},
    proof_rules::{get_proc_calculus, infer_fixpoint_semantics_kind},
    tyctx::TyCtx,
};

#[derive(Debug, Clone)]
pub enum StmtKindName {
    Stmt,
    Loop,
}

impl fmt::Display for StmtKindName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StmtKindName::Stmt => write!(f, "statement"),
            StmtKindName::Loop => write!(f, "loop"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ApproximationRecord {
    pub span: Span,
    pub stmt_kind: StmtKindName,
    pub kind: ApproximationKind,
}

pub type ApproximationList = Vec<ApproximationRecord>;

#[derive(Debug, Clone)]
pub struct ProcSoundness {
    direction: Direction,
    approx: ApproximationKind,
    pub sound_proofs: bool,
    pub sound_refutations: bool,
    approximations: ApproximationList,
    pub calculus: Option<Calculus>,
}

impl Default for ProcSoundness {
    /// Returns a soundness with no approximations and no calculus, which is exact and thus sound for both proofs and refutations.
    fn default() -> Self {
        Self::new(Direction::Down, vec![], None)
    }
}

impl ProcSoundness {
    /// Compute soundness from approximations, calculus, and direction.
    pub fn new(
        direction: Direction,
        approximations: ApproximationList,
        calculus: Option<Calculus>,
    ) -> Self {
        let approx = ApproximationKind::infimum(&approximations);
        // Down (proc): sound proofs need under-approximation; sound refutations need over-approximation.
        // Up (coproc): the roles of under/over are swapped.
        let (sound_proofs, sound_refutations) = match direction {
            Direction::Down => (approx.under, approx.over),
            Direction::Up => (approx.over, approx.under),
        };
        Self {
            direction,
            approx,
            sound_proofs,
            sound_refutations,
            approximations,
            calculus,
        }
    }

    /// Generate a diagnostic note explaining the overall approximation of the procedure.
    fn diagnostic_note(&self) -> Option<String> {
        if !self.sound_proofs {
            Some(format!(
                "{} conflicts with {} direction, leading to unsound proof",
                self.approx,
                self.direction.map("proc", "coproc")
            ))
        } else {
            None
        }
    }

    /// Generate diagnostic labels for all approximating statements in the procedure.
    fn diagnostic_labels(&self) -> Vec<Label> {
        self.approximations
            .iter()
            .filter(|approx| approx.kind != ApproximationKind::EXACT)
            .map(|approx| {
                let msg = match (self.calculus, approx.kind) {
                    (Some(c), ApproximationKind::OVER) => format!(
                        "For this {} S, {c} is over-approximated i.e., vc[S] ≥ {c}[S]",
                        approx.stmt_kind
                    ),
                    (Some(c), ApproximationKind::UNDER) => format!(
                        "For this {} S, {c} is under-approximated i.e., vc[S] ≤ {c}[S]",
                        approx.stmt_kind
                    ),
                    _ => format!(
                        "This statement is an {} of the real program behavior",
                        approx.kind
                    ),
                };
                Label::new(approx.span).with_message(msg)
            })
            .collect_vec()
    }

    pub fn soundness_diagnostic(
        &self,
        span: Span,
        prove_result: &ProveResult,
    ) -> Option<Diagnostic> {
        match prove_result {
            ProveResult::Proof if !self.sound_proofs => {
                let diag =
                    Diagnostic::new(ReportKind::Error, span).with_message("Unsound verification");
                let diag = if let Some(note) = self.diagnostic_note() {
                    diag.with_note(note)
                } else {
                    diag
                };
                Some(diag.with_labels(self.diagnostic_labels()))
            }
            _ => None,
        }
    }
}

/// The approximation relationship between vc semantics and original program semantics.
///
/// The two boolean fields `under` and `over` track whether the vc under- and/or over-approximates
/// the original semantics. See the constants [`EXACT`][Self::EXACT], [`UNDER`][Self::UNDER],
/// [`OVER`][Self::OVER], and [`UNKNOWN`][Self::UNKNOWN] for the four possible combinations.
///
/// Approximations arise from encoding annotations on loops or from negations in the program.
/// The reference semantics is determined by the calculus annotation, or inferred from loop direction
/// and encoding (see [`infer_fixpoint_semantics_kind`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ApproximationKind {
    /// True if the vc semantics under-approximates the original program semantics.
    pub under: bool,
    /// True if the vc semantics over-approximates the original program semantics.
    pub over: bool,
}

impl BitAnd for ApproximationKind {
    type Output = ApproximationKind;

    // This corresponds to infimum in the lattice of approximations
    fn bitand(self, rhs: Self) -> Self::Output {
        ApproximationKind {
            under: self.under && rhs.under,
            over: self.over && rhs.over,
        }
    }
}

impl ApproximationKind {
    /// Greatest lower bound of a list of approximation kinds. Returns [`EXACT`][Self::EXACT] for an empty list.
    pub fn infimum(approximations: &[ApproximationRecord]) -> Self {
        approximations
            .iter()
            .fold(Self::EXACT, |acc, entry| acc & entry.kind)
    }

    /// vc exactly matches the original semantics (both under- and over-approximating).
    pub const EXACT: Self = Self {
        under: true,
        over: true,
    };
    /// vc under-approximates the original semantics (vc[S] ≤ semantics[S]).
    pub const UNDER: Self = Self {
        under: true,
        over: false,
    };
    /// vc over-approximates the original semantics (vc[S] ≥ semantics[S]).
    pub const OVER: Self = Self {
        under: false,
        over: true,
    };
    /// vc neither under- nor over-approximates the original semantics.
    pub const UNKNOWN: Self = Self {
        under: false,
        over: false,
    };
}

impl fmt::Display for ApproximationKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            ApproximationKind::EXACT => write!(f, "exact approximation"),
            ApproximationKind::UNDER => write!(f, "under-approximation"),
            ApproximationKind::OVER => write!(f, "over-approximation"),
            ApproximationKind::UNKNOWN => write!(f, "unknown approximation"),
        }
    }
}

/// Get a map from source unit names to their corresponding [`ProcSoundness`].
pub fn get_soundness_map(
    module: &mut Module,
    tcx: &mut TyCtx,
) -> HashMap<SourceUnitName, ProcSoundness> {
    let mut soundness_map = HashMap::new();
    let source_units = &mut module.items;

    for source_unit in source_units {
        let soundness = match source_unit.enter_mut().deref_mut() {
            SourceUnit::Decl(decl) => match decl {
                DeclKind::ProcDecl(proc_decl) => soundness_blame_of_proc(&proc_decl.borrow(), tcx),
                _ => None,
            },
            SourceUnit::Raw(ref block) => Some(soundness_blame_of_raw(block, tcx)),
        };
        if let Some(soundness_blame) = soundness {
            soundness_map.insert(source_unit.name().clone(), soundness_blame);
        }
    }
    soundness_map
}

/// Track under-, over- and unknown approximating statements in a block.
///
/// Returns a list of spans and their corresponding approximation kinds of non-exact approximating statements.
fn track_approximation_in_block(
    block: &Block,
    direction: Direction,
    calculus: Option<Calculus>,
    tcx: &mut TyCtx,
) -> ApproximationList {
    block
        .node
        .iter()
        .flat_map(|stmt| track_approximation_in_statement(stmt, direction, calculus, tcx))
        .collect()
}

/// Determine the approximation kind of a statement and track approximation in its sub-statements.
fn track_approximation_in_statement(
    s: &Stmt,
    direction: Direction,
    calculus: Option<Calculus>,
    tcx: &mut TyCtx,
) -> ApproximationList {
    match &s.node {
        StmtKind::Seq(stmts) => stmts
            .iter()
            .flat_map(|stmt| track_approximation_in_statement(stmt, direction, calculus, tcx))
            .collect(),
        StmtKind::If(_, ref block1, ref block2)
        | StmtKind::Demonic(ref block1, ref block2)
        | StmtKind::Angelic(ref block1, ref block2) => {
            let mut acc = track_approximation_in_block(block1, direction, calculus, tcx);
            acc.extend(track_approximation_in_block(
                block2, direction, calculus, tcx,
            ));
            acc
        }
        // While loops don't introduce approximations themselves — any approximation comes from the
        // encoding annotation wrapping them. Recurse so the annotation case picks up inner approximations.
        StmtKind::While(_, ref block) => {
            track_approximation_in_block(block, direction, calculus, tcx)
        }
        // Encoding annotations introduce approximations based on direction, calculus, and the loop body's approximation.
        StmtKind::Annotation(_, ident, args, inner_stmt) => {
            let mut inner_approximation_list =
                track_approximation_in_statement(inner_stmt, direction, calculus, tcx);

            if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(anno_ref)) =
                tcx.get(*ident).unwrap().as_ref()
            {
                let semantics_type = infer_fixpoint_semantics_kind(
                    // Qualified because of the RefCell::borrow naming clash
                    std::borrow::Borrow::borrow(anno_ref),
                    calculus,
                    direction,
                    args,
                );

                let inner_approximation = ApproximationKind::infimum(&inner_approximation_list);

                // Ask the respective annotation what the resulting approximation(s) will be
                let approximation =
                    anno_ref.get_approximation(semantics_type, inner_approximation, calculus);
                inner_approximation_list.push(ApproximationRecord {
                    span: s.span,
                    stmt_kind: StmtKindName::Loop,
                    kind: approximation,
                });
            }
            inner_approximation_list
        }
        // Negations lead to unknown approximations
        StmtKind::Negate(_) => vec![ApproximationRecord {
            span: s.span,
            stmt_kind: StmtKindName::Stmt,
            kind: ApproximationKind::UNKNOWN,
        }],
        // All other statements are exact (no entry needed).
        _ => vec![],
    }
}

/// Compute the [`ProcSoundness`] of a procedure declaration.
///
/// Returns `None` if the procedure has no body.
pub fn soundness_blame_of_proc(decl: &ProcDecl, tcx: &mut TyCtx) -> Option<ProcSoundness> {
    let body = decl.body.borrow();
    let block = body.as_ref()?;
    let calculus = get_proc_calculus(decl, tcx).ok().flatten();
    let direction = decl.direction;
    let approx_list = track_approximation_in_block(block, direction, calculus, tcx);
    Some(ProcSoundness::new(direction, approx_list, calculus))
}

/// Compute the [`ProcSoundness`] of a raw block (without a procedure declaration).
///
/// This assumes no calculus annotation and uses the default fixpoint semantics for loops based on the direction and the encoding used.
pub fn soundness_blame_of_raw(block: &Block, tcx: &mut TyCtx) -> ProcSoundness {
    let approx_list = track_approximation_in_block(block, Direction::Down, None, tcx);
    ProcSoundness::new(Direction::Down, approx_list, None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Span;

    fn r(kind: ApproximationKind) -> ApproximationRecord {
        ApproximationRecord {
            span: Span::dummy_span(),
            stmt_kind: StmtKindName::Loop,
            kind,
        }
    }

    #[test]
    fn test_infimum() {
        use ApproximationKind as A;
        assert_eq!(A::infimum(&[]), A::EXACT);
        assert_eq!(A::infimum(&[r(A::OVER)]), A::OVER);
        assert_eq!(A::infimum(&[r(A::OVER), r(A::UNDER)]), A::UNKNOWN);
        assert_eq!(A::infimum(&[r(A::EXACT), r(A::OVER)]), A::OVER);
    }
}
