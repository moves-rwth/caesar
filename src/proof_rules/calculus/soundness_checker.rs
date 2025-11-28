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
#[derive(Debug, Clone, Default)]
pub struct ApproximationList(pub Vec<ApproximationRecord>);

impl IntoIterator for ApproximationList {
    type Item = ApproximationRecord;
    type IntoIter = std::vec::IntoIter<ApproximationRecord>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a ApproximationList {
    type Item = &'a ApproximationRecord;
    type IntoIter = std::slice::Iter<'a, ApproximationRecord>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a> IntoIterator for &'a mut ApproximationList {
    type Item = &'a mut ApproximationRecord;
    type IntoIter = std::slice::IterMut<'a, ApproximationRecord>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl ApproximationList {
    pub fn infimum(&self) -> ApproximationKind {
        self.0
            .iter()
            .fold(ApproximationKind::EXACT, |acc, approx_entry| {
                acc & approx_entry.kind
            })
    }

    // convenience helpers
    pub fn push(&mut self, rec: ApproximationRecord) {
        self.0.push(rec)
    }

    pub fn iter(&self) -> std::slice::Iter<'_, ApproximationRecord> {
        self.0.iter()
    }
}

impl From<Vec<ApproximationRecord>> for ApproximationList {
    fn from(v: Vec<ApproximationRecord>) -> Self {
        ApproximationList(v)
    }
}

impl std::ops::Deref for ApproximationList {
    type Target = Vec<ApproximationRecord>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::DerefMut for ApproximationList {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
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
        let approx = approximations.infimum();
        // The mapping between approximation kinds and soundness is as follows:
        // (approximation.under, approximation.over) -> (sound_proofs, sound_refutations)
        // Direction::Down:
        //                  exact = (false,false) -> (true, true)
        //                          (true,false)  -> (true, false)
        //                          (false,true)  -> (false, true)
        //                unknown = (true,true)  -> (false, false)
        // Direction::Up :
        //                  exact = (false,false) -> (true, true)
        //                          (true,false)  -> (false, true)
        //                          (false,true)  -> (true, false)
        //                unknown = (true,true)  -> (false, false)

        // XOR with "approx.over == approx.under" to only flip (false,false) and (true,true) (see mapping above).
        let over_approx = approx.over ^ (approx.over == approx.under);
        let under_approx = approx.under ^ (approx.over == approx.under);
        let (sound_proofs, sound_refutations) = match direction {
            Direction::Down => (under_approx, over_approx),
            Direction::Up => (over_approx, under_approx),
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
        self.approximations.infimum()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ApproximationKind {
    under: bool,
    over: bool,
}

// Note that the operations are reversed because the exact approximation should be the top element in the lattice but we want it to be (false,false).
// This is because if there isn't any approximations, i.e., "(false, false)", we consider it as exact.
// On the other hand "&" should correspond to infimum and "|" to supremum in the lattice of approximations.
// In that sense the lattice of approximations is the "flipped" lattice of a boolean pair.
impl BitAnd for ApproximationKind {
    type Output = ApproximationKind;

    // This corresponds to infimum in the lattice of approximations
    fn bitand(self, rhs: Self) -> Self::Output {
        ApproximationKind {
            under: self.under || rhs.under,
            over: self.over || rhs.over,
        }
    }
}

impl BitOr for ApproximationKind {
    type Output = ApproximationKind;

    // This corresponds to supremum in the lattice of approximations
    fn bitor(self, rhs: Self) -> Self::Output {
        ApproximationKind {
            under: self.under && rhs.under,
            over: self.over && rhs.over,
        }
    }
}

impl ApproximationKind {
    pub const EXACT: Self = Self {
        under: false,
        over: false,
    };
    pub const UNDER: Self = Self {
        under: true,
        over: false,
    };
    pub const OVER: Self = Self {
        under: false,
        over: true,
    };
    pub const UNKNOWN: Self = Self {
        under: true,
        over: true,
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
        .fold(ApproximationList::default(), |mut acc, stmt| {
            acc.extend(track_approximation_in_statement(
                stmt, direction, calculus, tcx,
            ));
            acc
        })
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
            .fold(ApproximationList::default(), |mut acc, stmt| {
                let stmt_approx_kind =
                    track_approximation_in_statement(stmt, direction, calculus, tcx);
                acc.extend(stmt_approx_kind);
                acc
            }),

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
        StmtKind::While(_, ref block) => {
            track_approximation_in_block(block, direction, calculus, tcx)
        }
        // Encoding annotations may cause approximations
        // This approximation is based on the direction, calculus and the approximation in the loop body
        StmtKind::Annotation(_, ident, _, inner_stmt) => {
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

                let inner_approximation = inner_approximation_list.infimum();

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
        StmtKind::Negate(_) => ApproximationList(vec![ApproximationRecord {
            span: s.span,
            stmt_kind: StmtKindName::Stmt,
            kind: ApproximationKind::UNKNOWN,
        }]),
        // All other statements do not change the approximation kind
        _ => ApproximationList::default(),
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
        let infimum_approx = approx_list.infimum();

        return Some(ProcSoundness {
            sound_proofs: match direction {
                Direction::Down => infimum_approx == ApproximationKind::UNDER,
                Direction::Up => infimum_approx == ApproximationKind::OVER,
            },
            sound_refutations: match direction {
                Direction::Down => infimum_approx == ApproximationKind::OVER,
                Direction::Up => infimum_approx == ApproximationKind::UNDER,
            },
            approximations: approx_list,
            calculus,
        });
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
