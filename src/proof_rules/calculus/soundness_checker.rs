use std::{
    collections::HashMap,
    fmt,
    ops::{BitAnd, BitOr, DerefMut},
    vec,
};

use itertools::Itertools;

use crate::{
    ast::{Block, DeclKind, Direction, Label, ProcDecl, Span, Stmt, StmtKind},
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

/// Compute the infimum of approximation kinds in the given approximation list.
///
/// This is done by folding the list with the `BitAnd` operation defined for `ApproximationKind`.
///
/// ---
///
/// Examples:
///
/// If `approximations` is empty, the default value is `ApproximationKind::EXACT` as an empty list means no approximations were made.
/// ```
/// let approximations = vec![];
/// assert_eq!(infimum_of_approximation_list(&approximations), ApproximationKind::EXACT);
/// ```
///
///
/// If it contains only one entry, that entry's kind is returned.
///
/// ```
/// let approximations = vec![
///     ApproximationRecord { span: Span::dummy_span(), stmt_kind: StmtKindName::Stmt, kind: ApproximationKind::OVER },
/// ];
/// assert_eq!(infimum_of_approximation_list(&approximations), ApproximationKind::OVER);
/// ```
///
/// If it contains two or more entries, the infimum of all their kinds is returned.
///
/// ```
/// let approximations = vec![
///     ApproximationRecord { span: Span::dummy_span(), stmt_kind: StmtKindName::Stmt, kind: ApproximationKind::OVER },
///     ApproximationRecord { span: Span::dummy_span(), stmt_kind: StmtKindName::Loop, kind: ApproximationKind::UNDER },
/// ];
/// assert_eq!(infimum_of_approximation_list(&approximations), ApproximationKind::UNKNOWN);
pub fn infimum_of_approximation_list(approximations: &ApproximationList) -> ApproximationKind {
    approximations
        .iter()
        .fold(ApproximationKind::EXACT, |acc, approx_entry| {
            acc & approx_entry.kind
        })
}

#[derive(Debug, Clone, Default)]
pub struct ProcSoundness {
    sound_proofs: bool,
    sound_refutations: bool,
    approximations: ApproximationList,
    calculus: Option<Calculus>,
}

impl ProcSoundness {
    /// Create a new ProcSoundness instance by analyzing the given approximations and calculus in the given direction.
    pub fn new(
        direction: Direction,
        approximations: ApproximationList,
        calculus: Option<Calculus>,
    ) -> Self {
        // If the approximation list is empty, it means no approximations were made, therefore the infimum is EXACT
        let approx = infimum_of_approximation_list(&approximations);
        let (sound_proofs, sound_refutations) = match direction {
            Direction::Down => match approx {
                ApproximationKind::EXACT => (true, true), // Both proofs and refutations are sound
                ApproximationKind::UNDER => (true, false), // Only proofs are guaranteed to be sound
                ApproximationKind::OVER => (false, true), // Only refutations are guaranteed to be sound
                ApproximationKind::UNKNOWN => (false, false), // Neither proofs nor refutations are sound
            },
            Direction::Up => match approx {
                ApproximationKind::EXACT => (true, true), // Both proofs and refutations are sound
                ApproximationKind::UNDER => (false, true), // Only refutations are guaranteed to be sound
                ApproximationKind::OVER => (true, false),  // Only proofs are guaranteed to be sound
                ApproximationKind::UNKNOWN => (false, false), // Neither proofs nor refutations are sound
            },
        };
        Self {
            sound_proofs,
            sound_refutations,
            approximations,
            calculus,
        }
    }

    /// Get whether proofs for this procedure are sound.
    pub fn sound_proofs(&self) -> bool {
        self.sound_proofs
    }

    /// Get whether refutations for this procedure are sound.
    pub fn sound_refutations(&self) -> bool {
        self.sound_refutations
    }

    /// Generate diagnostic labels for all approximating statements in the procedure.
    pub fn diagnostic_labels(&self) -> Vec<Label> {
        self.approximations
            .iter()
            .map(|approx| {
                let mut label = Label::new(approx.span).with_message(format!(
                    "This statement is an {} of the real program behavior",
                    approx.kind
                ));

                if let Some(calculus) = self.calculus {
                    match approx.kind {
                        ApproximationKind::OVER => {
                            label = label.with_message(format!(
                                "For this {} S, {} is over-approximated i.e., vc[S] ≥ {}[S]",
                                approx.stmt_kind, calculus, calculus
                            ))
                        }
                        ApproximationKind::UNDER => {
                            label = label.with_message(format!(
                                "For this {} S, {} is under-approximated i.e., vc[S] ≤ {}[S]",
                                approx.stmt_kind, calculus, calculus
                            ));
                        }
                        _ => {}
                    }
                }
                label
            })
            .collect_vec()
    }

    /// Generate a diagnostic note explaining the overall approximation of the procedure.
    pub fn diagnostic_note(&self) -> Option<String> {
        let is_both_over_and_under = self
            .approximations
            .iter()
            .any(|approx| approx.kind == ApproximationKind::OVER)
            && self
                .approximations
                .iter()
                .any(|approx| approx.kind == ApproximationKind::UNDER);

        if let Some(calculus) = self.calculus {
            match self.overall_approximation() {
                ApproximationKind::OVER => Some(format!(
                    "the {} of the program is over-approximated, i.e., vc[program] ≥ {}[program]",
                    calculus, calculus
                )),
                ApproximationKind::UNDER => Some(format!(
                    "the {} of the program is under-approximated, i.e., vc[program] ≤ {}[program]",
                    calculus, calculus
                )),
                ApproximationKind::UNKNOWN => {
                    if is_both_over_and_under {
                        Some(format!(
                            "the {} of the program is both over- and under-approximated in different parts of the program, therefore the approximation relationship for the whole program is unknown.",
                            calculus,
                        ))
                    } else {
                        Some(format!(
                            "the approximation relationship of the vc and the {} of the program is unknown.",
                            calculus,
                        ))
                    }
                }
                _ => None,
            }
        } else {
            None
        }
    }

    fn overall_approximation(&self) -> ApproximationKind {
        infimum_of_approximation_list(&self.approximations)
    }
}

/// Represents the kind of approximation that the vc semantics introduce for the original program semantics.
///
/// Approximations can be introduced by encoding annotations on loops or by negations in the program.
///
/// - If the the field `under` is true, it means that the vc semantics under-approximates the original program semantics, i.e. vc\[S\] ≤ semantics\[S\].
/// - If the field `over` is true, it means that the vc semantics over-approximates the original program semantics, i.e. vc\[S\] ≥ semantics\[S\].
/// - If both fields are true, it means that the vc semantics both under- and over-approximates the original program semantics, therefore it exactly matches the original program semantics, i.e. (vc\[S\] ≤ semantics\[S\]) and (vc\[S\] ≥ semantics\[S\]) hence (vc\[S\] = semantics\[S\]).
/// - If both fields are false, it means that the vc semantics neither under- nor over-approximates the original program semantics, therefore the approximation is unknown. i.e. !(vc\[S\] ≤ semantics\[S\]) and !(vc\[S\] ≥ semantics\[S\]).
///
/// The original program semantics is based on the calculus annotation or the default fixpoint semantics for loops based on the direction and the encoding used.
///
/// See also [`infer_fixpoint_semantics_kind`] for more details on how the semantics kind is inferred.
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

impl BitOr for ApproximationKind {
    type Output = ApproximationKind;

    // This corresponds to supremum in the lattice of approximations
    fn bitor(self, rhs: Self) -> Self::Output {
        ApproximationKind {
            under: self.under || rhs.under,
            over: self.over || rhs.over,
        }
    }
}

impl ApproximationKind {
    /// vc is both under- and over-approximating the original program semantics.
    pub const EXACT: Self = Self {
        under: true,
        over: true,
    };
    /// vc under-approximates the original program semantics.
    pub const UNDER: Self = Self {
        under: true,
        over: false,
    };
    /// vc over-approximates the original program semantics.
    pub const OVER: Self = Self {
        under: false,
        over: true,
    };
    /// vc neither under- nor over-approximates the original program semantics.
    ///
    /// This means !(vc[S] ≤ semantics[S]) and !(vc[S] ≥ semantics[S]).
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
        // Composite statements are handled recursively to collect approximations from sub-statements
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
        // A loop itself do not introduce an approximation, but an encoding annotation on top of it may do so.
        // Therefore, we only track the approximation inside the loop body recursively in this case.
        // This means that the approximation kind of a while loop is the approximation kind of the loop body.
        // While loops can not be used without an encoding annotation therefore this inner approximation is never directly recorded.
        // Instead this will be used by the annotation case below.
        StmtKind::While(_, ref block) => {
            track_approximation_in_block(block, direction, calculus, tcx)
        }
        // Encoding annotations may cause approximations
        // This approximation is based on the direction, calculus and the approximation in the loop body
        StmtKind::Annotation(_, ident, _, inner_stmt) => {
            // This inner statement is the While case above
            let mut inner_approximation_list =
                track_approximation_in_statement(inner_stmt, direction, calculus, tcx);

            // If the annotation is an encoding annotation
            if let DeclKind::AnnotationDecl(AnnotationKind::Encoding(anno_ref)) =
                tcx.get(*ident).unwrap().as_ref()
            {
                let semantics_type = infer_fixpoint_semantics_kind(
                    // Qualified because of the RefCell::borrow naming clash
                    std::borrow::Borrow::borrow(anno_ref),
                    calculus,
                    direction,
                );

                let inner_approximation = infimum_of_approximation_list(&inner_approximation_list);

                // Ask the respective annotation what the resulting approximation(s) will be
                let approximation = anno_ref.get_approximation(semantics_type, inner_approximation);
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
        // All other statements do not change the approximation kind, which means they have the EXACT approximation kind
        _ => vec![],
    }
}

/// Compute the [`ProcSoundness`] of a procedure declaration.
///
/// Returns `None` if the procedure has no body.
pub fn soundness_blame_of_proc(decl: &ProcDecl, tcx: &mut TyCtx) -> Option<ProcSoundness> {
    if let Some(block) = decl.body.borrow_mut().as_mut() {
        // Get the calculus of the procedure
        let calculus = get_proc_calculus(decl, tcx).ok().flatten();
        let direction = decl.direction;

        let approx_list = track_approximation_in_block(block, direction, calculus, tcx);

        return Some(ProcSoundness::new(direction, approx_list, calculus));
    }
    None
}

/// Compute the [`ProcSoundness`] of a raw block (without a procedure declaration).
///
/// This assumes no calculus annotation and uses the default fixpoint semantics for loops based on the direction and the encoding used.
pub fn soundness_blame_of_raw(block: &Block, tcx: &mut TyCtx) -> ProcSoundness {
    let approx_list = track_approximation_in_block(block, Direction::Down, None, tcx);
    // Insert the soundness into the map
    ProcSoundness::new(Direction::Down, approx_list, None)
}
