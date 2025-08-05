//! This module contains code to select statements for slicing.
//!
//! The basic notion is the [`SliceEffect`], which relates a statements' removal
//! to its effect on verification or counter-examples of a program.
//!
//! A [`SliceSelection`] filters which kinds of statements to slice (e.g. by
//! their [`SliceEffect`]), and also might include messages to print when a
//! statement is sliced. The selection and associated messages can be given by
//! [`SliceAnnotation`]s, which are available to the user as well.
//!
//!  The [`SelectionBuilder`] can be used to build selections during an AST
//! traversal.

use std::ops::{BitOr, BitOrAssign};

use crate::{
    ast::{Expr, ExprKind, Ident, LitKind, Param, Span, Spanned, Symbol, TyKind},
    front::tycheck::{Tycheck, TycheckError},
    intrinsic::annotations::{tycheck_annotation_call, AnnotationDecl},
};

/// The effect of slicing a certain program statement in its context. Depending
/// on whether the context is down or up (proc or coproc) and whether disabling
/// the statement would increase or decrease the verification conditions (vc), the
/// effect is either concordant (consistent with the proc direction), or
/// discordant (opposite the proc direction). There are also ambiguous
/// statements such as assignments, whose effect is unclear.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SliceEffect {
    /// Statements with a concordant slice effect (e.g. assume in a down
    /// context) can be removed from a program to change the vc in the context
    /// direction (in this example, down.) When concordant statements are
    /// re-introduced, they will only make the program *verify more*, so they're
    /// the ones we'll try to remove while slicing a program where we want to
    /// maintain correctness. If we can't remove it, then it's important for
    /// correctness.
    ///
    /// More formally, in a down context concordant statements S are those which
    /// satisfy `post = vc[skip](post) <= vc[S](post)` (and vice-versa for up
    /// context).
    ///
    /// In a down context, concordant statements are: assume, coassert, angelic
    /// nondeterminism. In an up context, concordant statements are: coassume,
    /// assert, demonic nondeterminism.
    Concordant,
    /// Discordant effect statements can be removed to change the vc in the
    /// opposite of the context direction (e.g. assert in a down context). When
    /// we remove it, the vc will increase (or stay the same). On the other
    /// hand, when we re-introduce it, the vc can only *decrease*. Thus,
    /// re-introducing discordant statements can only *break verification more*.
    /// Discordant statements are the ones we'll try to remove while slicing a
    /// program where we want to maintain incorrectness. If we can't remove it,
    /// then it's important for incorrectness.
    ///
    /// More formally, in a down context discordant statements S are those which
    /// satisfy `vc[S](post) <= vc[skip](post) = post` (and vice-versa for up
    /// context).
    ///
    /// In a down context, discordant statements are: assert, coassume, demonic
    /// nondeterminism. In an up context, discordant statements are: coassert,
    /// assume, angelic nondeterminism.
    Discordant,
    /// Statements with an ambiguous slice effect may have any effect on the vc
    /// when they're removed. This means that re-introducing them may also have
    /// any kind of effect and therefore we cannot conclude that they would
    /// maintain correctness or incorrectness. An example is the assignment,
    /// which can have arbitrary effects due to the assigned variables being
    /// used in arbitrary places.
    ///
    /// However, slicing them might still be useful! For example, if we remove a
    /// statement with an ambiguous slice effect and the program verifies, we
    /// simply have a new program that satisfies the specification. We just
    /// don't learn anything about the original program only from the fact that
    /// the sliced program verifies.
    ///
    /// Caution is necessary, though. Don't slice away statements that are
    /// important for verification, for example. You might get a false
    /// verification result.
    Ambiguous,
}

/// All of our kinds of annotations for slicing.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SliceAnnotationKind {
    SliceVerify,
    SliceError,
    SuccessMessage,
    ErrorMessage,
}

impl SliceAnnotationKind {
    pub fn name(&self) -> Ident {
        let name = match self {
            SliceAnnotationKind::SliceVerify => "slice_verify",
            SliceAnnotationKind::SliceError => "slice_error",
            SliceAnnotationKind::SuccessMessage => "success_msg",
            SliceAnnotationKind::ErrorMessage => "error_msg",
        };
        Ident::with_dummy_span(Symbol::intern(name))
    }
}

/// A slice annotation has a name (an [`Ident`]) and a [`SliceAnnotationKind`].
#[derive(Debug)]
pub struct SliceAnnotation {
    pub ident: Ident,
    pub kind: SliceAnnotationKind,
}

impl SliceAnnotation {
    pub fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), TycheckError> {
        let annotation = match self.kind {
            SliceAnnotationKind::SliceVerify | SliceAnnotationKind::SliceError => AnnotationDecl {
                name: self.kind.name(),
                inputs: Spanned::with_dummy_span(vec![]),
                span: Span::dummy_span(),
            },
            SliceAnnotationKind::SuccessMessage | SliceAnnotationKind::ErrorMessage => {
                AnnotationDecl {
                    name: self.kind.name(),
                    inputs: Spanned::with_dummy_span(vec![Param {
                        name: Ident::with_dummy_span(Symbol::intern("message")),
                        ty: Box::new(TyKind::String),
                        literal_only: true,
                        span: Span::dummy_span(),
                    }]),
                    span: Span::dummy_span(),
                }
            }
        };
        tycheck_annotation_call(tycheck, call_span, &annotation, args)
    }
}

/// A slice selection contains information to filter which kinds of statements
/// to slice and which messages to emit when statements are sliced.
///
/// There is a [`BitOr`] implementation to create a selection that combines two
/// by a logical or.
#[derive(Debug, Clone, Default)]
pub struct SliceSelection {
    pub(super) concordant: bool,
    pub(super) discordant: bool,
    pub in_slice_verify_annotation: bool,
    pub in_slice_error_annotation: bool,
    pub slice_ticks: bool,
    /// Whether we should slice probabilistic sampling. This can be expensive
    /// and is disabled by default.
    pub slice_sampling: bool,
    /// A success message is printed for a statement if it can be removed while
    /// the program still verifies.
    pub(super) success_message: Option<Symbol>,
    /// A failure message is printed for a statement if it cannot be removed
    /// while still obtaining a counterexample.
    pub(super) failure_message: Option<Symbol>,
}

impl SliceSelection {
    /// The usual selection of statements to slice when the program verifies and
    /// we want to obtain a smaller verifying program whose verification entails
    /// the original program's verification.
    ///
    /// This means we slice concordant statements and those with an explicit
    /// annotation.
    pub const VERIFIED_SELECTION: Self = SliceSelection {
        concordant: true,
        discordant: false,
        in_slice_verify_annotation: true,
        in_slice_error_annotation: false,
        slice_ticks: false,
        slice_sampling: false,
        success_message: None,
        failure_message: None,
    };

    /// The usual selection of statements to slice when the program's
    /// verification fails with a counter-example and we want to obtain a
    /// smaller program which still fails with a counter-example and whose
    /// failure to verify implies the original program's failure to verify.
    ///
    /// This means we slice discordant statements and those with an explicit
    /// annotation.
    pub const FAILURE_SELECTION: Self = SliceSelection {
        concordant: false,
        discordant: true,
        in_slice_verify_annotation: false,
        in_slice_error_annotation: true,
        slice_ticks: false,
        slice_sampling: false,
        success_message: None,
        failure_message: None,
    };

    /// Slice everything. This is only used in our tests, as it is generally
    /// unsound in every other use case.
    pub const EVERYTHING: Self = SliceSelection {
        concordant: true,
        discordant: true,
        in_slice_verify_annotation: true,
        in_slice_error_annotation: true,
        slice_ticks: true,
        slice_sampling: true,
        success_message: None,
        failure_message: None,
    };

    /// Does a selection enable another selection, i.e. is there a part of the
    /// selection enabled in both selections?
    pub fn enables(&self, other: &Self) -> bool {
        (self.concordant && other.concordant)
            || (self.discordant && other.discordant)
            || (self.in_slice_verify_annotation && other.in_slice_verify_annotation)
            || (self.in_slice_error_annotation && other.in_slice_error_annotation)
    }
}

impl BitOr for SliceSelection {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        SliceSelection {
            concordant: self.concordant || rhs.concordant,
            discordant: self.discordant || rhs.discordant,
            in_slice_verify_annotation: self.in_slice_verify_annotation
                || rhs.in_slice_verify_annotation,
            in_slice_error_annotation: self.in_slice_error_annotation
                || rhs.in_slice_error_annotation,
            slice_ticks: self.slice_ticks || rhs.slice_ticks,
            slice_sampling: self.slice_sampling || rhs.slice_sampling,
            success_message: self.success_message.or(rhs.success_message),
            failure_message: self.failure_message.or(rhs.failure_message),
        }
    }
}

impl BitOrAssign for SliceSelection {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = self.clone() | rhs
    }
}

/// Helper to build a selection while traversing a program with slice
/// annotations. We have a filter selection to decide whether to slice the
/// statement, and then a stack of slice selections to build a slice selection
/// which is annotated to the slice statement.
#[derive(Debug)]
pub struct SelectionBuilder {
    filter: SliceSelection,
    stack: Vec<SliceSelection>,
}

impl SelectionBuilder {
    /// Create a new selection builder with a filter selection for the
    /// [`Self::should_slice()`] method.
    pub fn new(filter: SliceSelection) -> Self {
        SelectionBuilder {
            filter,
            stack: vec![SliceSelection::default()],
        }
    }

    fn state(&self) -> &SliceSelection {
        self.stack.last().unwrap()
    }

    fn state_mut(&mut self) -> &mut SliceSelection {
        self.stack.last_mut().unwrap()
    }

    /// Push a slice annotation to the stack.
    pub fn push_annotation(&mut self, kind: SliceAnnotationKind, args: &[Expr]) {
        self.stack.push(self.state().clone());
        let state = self.state_mut();
        match kind {
            SliceAnnotationKind::SliceVerify => {
                assert_eq!(args.len(), 0);
                state.in_slice_verify_annotation = true
            }
            SliceAnnotationKind::SliceError => {
                assert_eq!(args.len(), 0);
                state.in_slice_error_annotation = true
            }
            SliceAnnotationKind::SuccessMessage => {
                assert_eq!(args.len(), 1);
                state.success_message = Some(lit_expr_to_symbol(&args[0]));
            }
            SliceAnnotationKind::ErrorMessage => {
                assert_eq!(args.len(), 1);
                state.failure_message = Some(lit_expr_to_symbol(&args[0]))
            }
        }
    }

    /// Based on the filter and the active annotations, should we try to slice
    /// this statement with the given [`SliceEffect`]?
    pub fn should_slice(&self, effect: SliceEffect) -> bool {
        self.filter.enables(&self.make_selection(effect))
    }

    /// Whether we want to slice tick statements.
    pub fn should_slice_ticks(&self) -> bool {
        self.filter.slice_ticks
    }

    /// Whether we want to slice probabilistic sampling statements.
    pub fn should_slice_sampling(&self) -> bool {
        self.filter.slice_sampling
    }

    /// Create a new slice selection from the current state and the given slice
    /// effect.
    pub fn make_selection(&self, effect: SliceEffect) -> SliceSelection {
        let mut selection = self.state().clone();
        selection.concordant = false;
        selection.discordant = false;
        match effect {
            SliceEffect::Concordant => {
                selection.concordant = true;
                selection
                    .success_message
                    .get_or_insert_with(|| Symbol::intern("assumption is not necessary"));
            }
            SliceEffect::Discordant => {
                selection.discordant = true;
                selection
                    .failure_message
                    .get_or_insert_with(|| Symbol::intern("assertion might not hold"));
            }
            SliceEffect::Ambiguous => {}
        }
        selection
    }

    /// Pop the last annotation.
    pub fn pop_annotation(&mut self) {
        self.stack.pop();
    }
}

/// Extract a [`Symbol`] from a literal string expression. Panics if not a
/// string literal expression.
fn lit_expr_to_symbol(expr: &Expr) -> Symbol {
    match &expr.kind {
        ExprKind::Lit(lit) => match lit.node {
            LitKind::Str(symbol) => symbol,
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }
}
