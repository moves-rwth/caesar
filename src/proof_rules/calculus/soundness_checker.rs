use std::{collections::HashMap, fmt, ops::DerefMut, vec};

use crate::{
    ast::{Block, DeclKind, Direction, ProcDecl, Span, Stmt, StmtKind},
    driver::{
        front::{Module, SourceUnit},
        item::SourceUnitName,
    },
    intrinsic::annotations::{AnnotationKind, Calculus},
    proof_rules::{get_calculus, infer_fixpoint_semantics_kind},
    tyctx::TyCtx,
};

#[derive(Debug, Clone)]
pub struct ApproximationListEntry {
    pub span: Span,
    pub is_loop: bool,
    pub kind: ApproximationKind,
}
pub type ApproximationList = Vec<ApproximationListEntry>;

// pub type SoundnessBlame = (Soundness, ApproximationList);

#[derive(Debug, Clone, Default)]
pub struct SoundnessBlame {
    pub soundness: Soundness,
    pub approximations: ApproximationList,
    pub calculus: Option<Calculus>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ApproximationKind {
    #[default]
    Exact,
    Under,
    Over,
    Unknown,
}

impl ApproximationKind {
    pub fn supremum(self, other: ApproximationKind) -> ApproximationKind {
        match self.partial_cmp(&other) {
            Some(std::cmp::Ordering::Equal) => self,
            Some(std::cmp::Ordering::Less) => other,
            Some(std::cmp::Ordering::Greater) => self,
            None => ApproximationKind::Exact, // If they are incomparable, return Exact (which is the top element)
        }
    }
    pub fn infimum(self, other: ApproximationKind) -> ApproximationKind {
        match self.partial_cmp(&other) {
            Some(std::cmp::Ordering::Equal) => self,
            Some(std::cmp::Ordering::Less) => self,
            Some(std::cmp::Ordering::Greater) => other,
            None => ApproximationKind::Unknown, // If they are incomparable, return Unknown (which is the bottom element)
        }
    }
}

impl PartialOrd for ApproximationKind {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (ApproximationKind::Exact, ApproximationKind::Exact) => Some(std::cmp::Ordering::Equal),
            (ApproximationKind::Under, ApproximationKind::Under) => Some(std::cmp::Ordering::Equal),
            (ApproximationKind::Over, ApproximationKind::Over) => Some(std::cmp::Ordering::Equal),
            (ApproximationKind::Unknown, ApproximationKind::Unknown) => {
                Some(std::cmp::Ordering::Equal)
            }
            (_, ApproximationKind::Exact) => Some(std::cmp::Ordering::Less),
            (ApproximationKind::Exact, _) => Some(std::cmp::Ordering::Greater),
            (ApproximationKind::Unknown, _) => Some(std::cmp::Ordering::Less),
            (_, ApproximationKind::Unknown) => Some(std::cmp::Ordering::Greater),
            (ApproximationKind::Under, ApproximationKind::Over)
            | (ApproximationKind::Over, ApproximationKind::Under) => None,
        }
    }
}

impl fmt::Display for ApproximationKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ApproximationKind::Exact => write!(f, "exact approximation"),
            ApproximationKind::Under => write!(f, "under-approximation"),
            ApproximationKind::Over => write!(f, "over-approximation"),
            ApproximationKind::Unknown => write!(f, "unknown approximation"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Soundness {
    #[default]
    Exact,
    Proof,
    Refutation,
    Unknown,
}

impl Soundness {
    pub fn from_approximation(approx: ApproximationKind, direction: Direction) -> Self {
        match approx {
            ApproximationKind::Exact => Soundness::Exact,
            ApproximationKind::Under => match direction {
                Direction::Down => Soundness::Proof,
                Direction::Up => Soundness::Refutation,
            },
            ApproximationKind::Over => match direction {
                Direction::Down => Soundness::Refutation,
                Direction::Up => Soundness::Proof,
            },
            ApproximationKind::Unknown => Soundness::Unknown,
        }
    }
}

pub fn get_soundness_map(
    module: &mut Module,
    tcx: &mut TyCtx,
) -> HashMap<SourceUnitName, SoundnessBlame> {
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

/// Track under-, over- and unknown approximating statements in a block
///
/// Returns a list of spans and their corresponding approximation kinds of non-exact approximating statements
fn track_approximation_in_block(
    block: &Block,
    direction: Direction,
    calculus: Option<Calculus>,
    tcx: &mut TyCtx,
) -> ApproximationList {
    block.node.iter().fold(Vec::new(), |mut acc, stmt| {
        acc.extend(track_approximation_in_statement(
            stmt, direction, calculus, tcx,
        ));
        acc
    })
}

/// Determine the approximation kind of a statement and track approximation in its sub-statements
fn track_approximation_in_statement(
    s: &Stmt,
    direction: Direction,
    calculus: Option<Calculus>,
    tcx: &mut TyCtx,
) -> ApproximationList {
    match &s.node {
        // First handle the composite statements for recursion
        StmtKind::Seq(stmts) => stmts.iter().fold(Vec::new(), |mut acc, stmt| {
            let stmt_approx_kind = track_approximation_in_statement(stmt, direction, calculus, tcx);
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
        StmtKind::While(_, ref block) => {
            track_approximation_in_block(block, direction, calculus, tcx)
        }
        // Under-and over-approximations from annotations
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

                let inner_approximation = infimum_approximation_list(&inner_approximation_list);

                // Handle the inner approximation kind according to the encoding annotation and get the overall approximation
                let approximation = anno_ref.get_approximation(semantics_type, inner_approximation);
                inner_approximation_list.push(ApproximationListEntry {
                    span: s.span,
                    is_loop: true,
                    kind: approximation,
                });
            }
            inner_approximation_list
        }
        // Negations lead to unknown approximations
        StmtKind::Negate(_) => vec![ApproximationListEntry {
            span: s.span,
            is_loop: false,
            kind: ApproximationKind::Unknown,
        }],
        // All other statements do not change the approximation kind
        _ => Vec::new(),
    }
}

pub fn soundness_blame_of_proc(decl: &ProcDecl, tcx: &mut TyCtx) -> Option<SoundnessBlame> {
    if let Some(block) = decl.body.borrow_mut().as_mut() {
        // Get the calculus of the procedure
        let calculus = get_calculus(decl, tcx).ok().flatten();
        let direction = decl.direction;

        let approx_list = track_approximation_in_block(block, direction, calculus, tcx);
        let infimum_approx = infimum_approximation_list(&approx_list);

        return Some(SoundnessBlame {
            soundness: Soundness::from_approximation(infimum_approx, direction),
            approximations: approx_list,
            calculus,
        });
    }
    None
}

pub fn soundness_blame_of_raw(block: &Block, tcx: &mut TyCtx) -> SoundnessBlame {
    let approx_list = track_approximation_in_block(block, Direction::Down, None, tcx);
    let meet_approx = infimum_approximation_list(&approx_list);
    // Insert the soundness into the map
    SoundnessBlame {
        soundness: Soundness::from_approximation(meet_approx, Direction::Down),
        approximations: approx_list,
        calculus: None,
    }
}

pub fn _supremum_approximation_list(list: &ApproximationList) -> ApproximationKind {
    list.iter()
        .fold(ApproximationKind::Unknown, |acc, approx_entry| {
            acc.supremum(approx_entry.kind)
        })
}

pub fn infimum_approximation_list(list: &ApproximationList) -> ApproximationKind {
    list.iter()
        .fold(ApproximationKind::Exact, |acc, approx_entry| {
            acc.infimum(approx_entry.kind)
        })
}
