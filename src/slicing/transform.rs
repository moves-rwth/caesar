//! Transformation of programs into versions which have variables to enable or
//! disable statements.
//!
//! After transformation, we can generate verification conditions as normal, but
//! then afterwards we can try to minimize the number of enabled statements via
//! the Boolean variables we created.
//!
//! The transformations happen in [`StmtSliceVisitor`] which implements
//! [`VisitorMut`]. Using the [`StmtSliceVisitor::finish()`] method, we obtain
//! the [`SliceStmts`], which contain the information for each statement to
//! slice it, such as the Boolean variable to slice it or the
//! [`super::selection::SliceSelection`] for this statement.

use std::rc::Rc;

use ariadne::ReportKind;
use replace_with::replace_with_or_abort;
use tracing::{instrument, Level};

use crate::{
    ast::{
        visit::{walk_proc, walk_stmt, VisitorMut},
        BinOpKind, DeclKind, DeclRef, Diagnostic, Direction, Expr, ExprBuilder, ExprKind, Ident,
        Label, ProcDecl, Span, SpanVariant, Spanned, Stmt, StmtKind, Symbol, TyKind, VarDecl,
        VarKind,
    },
    intrinsic::annotations::AnnotationKind,
    tyctx::TyCtx,
};

use super::selection::{SelectionBuilder, SliceEffect, SliceSelection};

/// Structure to keep the Boolean variables that toggle statements. It contains
/// a list of all [`SliceStmt`]s, as well as a list of constraints. The latter
/// come from binary nondeterministic choices, which must always have one of the
/// branches enabled to maintain a slice effect.
#[derive(Debug, Default, Clone)]
pub struct SliceStmts {
    pub stmts: Vec<SliceStmt>,
    pub constraints: Vec<Expr>,
}

/// A slice variable created to enable or disable a statement. We maintain the
/// identifier, the selection, and the span of the statement in this struct.
#[derive(Debug, Clone)]
pub struct SliceStmt {
    pub ident: Ident,
    pub selection: SliceSelection,
    pub statement: Span,
}

impl SliceStmt {
    /// See [`SliceSelection::success_message`].
    pub fn success_message(&self) -> Option<Symbol> {
        self.selection.success_message
    }

    /// See [`SliceSelection::failure_message`].
    pub fn failure_message(&self) -> Option<Symbol> {
        self.selection.failure_message
    }
}

/// [`VisitorMut`] that modifies HeyVL statements so that each gets their own
/// new Boolean variable that enables or disables it. We can then ask the SMT
/// solver to optimize for the *least* enabled statements.
#[derive(Debug)]
pub struct StmtSliceVisitor<'tcx> {
    tcx: &'tcx mut TyCtx,
    selector: SelectionBuilder,
    direction: Direction,
    slice_stmts: SliceStmts,
}

impl<'tcx> StmtSliceVisitor<'tcx> {
    /// Create a new statement slice visitor with a default direction and a
    /// slice selection.
    pub fn new(tcx: &'tcx mut TyCtx, direction: Direction, selection: SliceSelection) -> Self {
        StmtSliceVisitor {
            tcx,
            selector: SelectionBuilder::new(selection),
            direction,
            slice_stmts: SliceStmts::default(),
        }
    }

    /// Add a new [`SliceStmt`] with a new variable with the given
    /// [`SliceEffect`]. Returns the expression with the new slice variable.
    #[instrument(level = Level::TRACE, skip(self))]
    fn add_slice_stmt(&mut self, span: Span, effect: SliceEffect) -> Expr {
        // create the new ident
        let ident = Ident::with_dummy_span(Symbol::intern("slice_toggle"));
        let ident = self
            .tcx
            .fresh_ident(ident, span.variant(SpanVariant::Slicing));

        let selection = self.selector.make_selection(effect);
        self.slice_stmts.stmts.push(SliceStmt {
            ident,
            selection,
            statement: span,
        });

        // create the declaration
        let span = span.variant(SpanVariant::Slicing);
        self.tcx.declare(DeclKind::VarDecl(DeclRef::new(VarDecl {
            name: ident,
            ty: TyKind::Bool,
            kind: VarKind::Slice,
            init: None,
            span,
            created_from: None,
        })));

        // return a variable expression with that new ident
        let builder = ExprBuilder::new(span);
        builder.var(ident, self.tcx)
    }

    /// Wrap the given expression `expr` for the statement at `span` with
    /// direction `dir` in a conditional that returns the top element of the
    /// respective down/up lattice if the slice var is set to false.
    ///
    /// This is the operation done for both assume and assert statements.
    fn mk_top_toggle(&mut self, expr: &mut Expr, dir: Direction, toggle_var: Expr) {
        let builder = ExprBuilder::new(expr.span.variant(SpanVariant::Slicing));
        let ty = expr.ty.clone();
        let ty_ref = ty.as_ref().unwrap();
        let id_element = if dir == Direction::Down {
            builder.top_lit(ty_ref)
        } else {
            builder.bot_lit(ty_ref)
        };
        let cond_asgn = builder.ite(ty, toggle_var, expr.clone(), id_element);
        *expr = cond_asgn;
    }

    /// After the transformation, destroy this visitor and extract the
    /// [`SliceStmts`] to be used with the slice solver.
    pub fn finish(self) -> SliceStmts {
        let mut slice_vars = self.slice_stmts;
        slice_vars.stmts.sort_by_key(|s| s.ident.span.start);
        slice_vars
    }
}

/// Errors during the slicing transformation. When an error occurred, the
/// program may still be (partially) modified. The modified program is however
/// still valid for further use in slicing!
#[derive(Debug)]
pub enum StmtSliceError {
    /// When negation statements are used in an unsupported way. This should not
    /// ever occur from Caesar's internal encodings.
    UnsupportedNegation(Span),
}

impl StmtSliceError {
    pub fn to_diagnostic(&self) -> Diagnostic {
        match self {
            StmtSliceError::UnsupportedNegation(span) => Diagnostic::new(ReportKind::Advice, *span)
                .with_message("unsupported negation for slicing")
                .with_label(
                    Label::new(*span).with_message("after this statement, slicing is disabled"),
                ),
        }
    }
}

impl<'tcx> VisitorMut for StmtSliceVisitor<'tcx> {
    type Err = StmtSliceError;

    fn visit_proc(&mut self, proc_ref: &mut DeclRef<ProcDecl>) -> Result<(), Self::Err> {
        let decl = proc_ref.borrow();
        let prev_dir = self.direction;
        self.direction = decl.direction;
        drop(decl);
        walk_proc(self, proc_ref)?;
        self.direction = prev_dir;
        Ok(())
    }

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        // first, we handle the recursive cases. for annotations, we need to
        // push and pop the annotations to the [`Selector`] which tracks the
        // selection.
        match &mut s.node {
            StmtKind::Annotation(_, ident, args, _) => {
                if let DeclKind::AnnotationDecl(AnnotationKind::Slicing(annotation)) =
                    self.tcx.get(*ident).unwrap().as_ref()
                {
                    self.selector.push_annotation(annotation.kind, args);
                    replace_with_or_abort(s, |s| match s.node {
                        StmtKind::Annotation(_, _, _, body) => *body,
                        _ => unreachable!(),
                    });
                    let res = self.visit_stmt(s);
                    self.selector.pop_annotation();
                    return res;
                } else {
                    walk_stmt(self, s)?
                }
            }
            _ => walk_stmt(self, s)?,
        }

        // now handle the individual statements which we transform.
        match &mut s.node {
            StmtKind::Assign(lhs, rhs) if lhs.len() == 1 && is_pure_expr(self.tcx, rhs) => {
                let effect = SliceEffect::Ambiguous;
                if !self.selector.should_slice(effect) {
                    return Ok(());
                }

                let slice_var = self.add_slice_stmt(s.span, effect);
                let builder = ExprBuilder::new(rhs.span.variant(SpanVariant::Slicing));
                let ty = rhs.ty.clone();
                rhs.replace_with(|rhs| {
                    builder.ite(ty, slice_var, rhs.clone(), builder.var(lhs[0], self.tcx))
                });
            }
            StmtKind::Assume(dir, expr) => {
                let effect = if self.direction == *dir {
                    SliceEffect::Concordant
                } else {
                    SliceEffect::Discordant
                };
                if !self.selector.should_slice(effect) {
                    return Ok(());
                }
                let slice_var = self.add_slice_stmt(s.span, effect);
                self.mk_top_toggle(expr, *dir, slice_var)
            }
            StmtKind::Assert(dir, expr) => {
                let effect = if self.direction == *dir {
                    SliceEffect::Discordant
                } else {
                    SliceEffect::Concordant
                };
                if !self.selector.should_slice(effect) {
                    return Ok(());
                }
                let slice_stmt = self.add_slice_stmt(s.span, effect);
                self.mk_top_toggle(expr, *dir, slice_stmt)
            }
            StmtKind::Tick(expr) => {
                let effect = match self.direction {
                    Direction::Down => SliceEffect::Concordant,
                    Direction::Up => SliceEffect::Discordant,
                };
                if !self.selector.should_slice(effect) {
                    return Ok(());
                }
                let slice_var = self.add_slice_stmt(s.span, effect);
                // this will create a toggle with value 0 if disabled
                self.mk_top_toggle(expr, Direction::Up, slice_var)
            }
            StmtKind::Demonic(lhs, rhs) => {
                let dir = self.direction;
                let effect = match dir {
                    Direction::Down => SliceEffect::Discordant,
                    Direction::Up => SliceEffect::Concordant,
                };
                if !self.selector.should_slice(effect) {
                    return Ok(());
                }

                let span = s.span.variant(SpanVariant::Slicing);
                let builder = ExprBuilder::new(span);
                let spec_ty = self.tcx.spec_ty().clone();

                let generate_slice_stmt = |slice_var: Expr| match dir {
                    Direction::Down => {
                        // assume ite(slice_var, top, bot)
                        let assume_expr = builder.ite(
                            Some(spec_ty.clone()),
                            slice_var.clone(),
                            builder.top_lit(&spec_ty),
                            builder.bot_lit(&spec_ty),
                        );
                        Spanned::new(span, StmtKind::Assume(Direction::Down, assume_expr))
                    }
                    Direction::Up => {
                        // coassert ite(slice_var, top, bot)
                        let assert_expr = builder.ite(
                            Some(spec_ty.clone()),
                            slice_var.clone(),
                            builder.top_lit(&spec_ty),
                            builder.bot_lit(&spec_ty),
                        );
                        Spanned::new(span, StmtKind::Assert(Direction::Up, assert_expr))
                    }
                };

                // create the slice statements
                let lhs_slice_var = self.add_slice_stmt(s.span, effect);
                let rhs_slice_var = self.add_slice_stmt(s.span, effect);

                // at least one of the two statements must always be enabled
                self.slice_stmts.constraints.push(builder.binary(
                    BinOpKind::Or,
                    Some(TyKind::Bool),
                    lhs_slice_var.clone(),
                    rhs_slice_var.clone(),
                ));

                lhs.node.insert(0, generate_slice_stmt(lhs_slice_var));
                rhs.node.insert(0, generate_slice_stmt(rhs_slice_var));
            }
            StmtKind::Angelic(lhs, rhs) => {
                let dir = self.direction;
                let effect = match self.direction {
                    Direction::Down => SliceEffect::Concordant,
                    Direction::Up => SliceEffect::Discordant,
                };
                if !self.selector.should_slice(effect) {
                    return Ok(());
                }

                let span = s.span.variant(SpanVariant::Slicing);
                let builder = ExprBuilder::new(span);
                let spec_ty = self.tcx.spec_ty().clone();

                let generate_slice_stmt = |slice_var: Expr| match dir {
                    Direction::Down => {
                        // assert ite(slice_var, bot, top)
                        let assume_expr = builder.ite(
                            Some(spec_ty.clone()),
                            slice_var.clone(),
                            builder.top_lit(&spec_ty),
                            builder.bot_lit(&spec_ty),
                        );
                        Spanned::new(span, StmtKind::Assert(Direction::Down, assume_expr))
                    }
                    Direction::Up => {
                        // coassume ite(slice_var, top, bot)
                        let assert_expr = builder.ite(
                            Some(spec_ty.clone()),
                            slice_var.clone(),
                            builder.top_lit(&spec_ty),
                            builder.bot_lit(&spec_ty),
                        );
                        Spanned::new(span, StmtKind::Assume(Direction::Up, assert_expr))
                    }
                };

                // create the slice statements
                let lhs_slice_var = self.add_slice_stmt(s.span, effect);
                let rhs_slice_var = self.add_slice_stmt(s.span, effect);

                // at least one of the two statements must always be enabled
                self.slice_stmts.constraints.push(builder.binary(
                    BinOpKind::Or,
                    Some(TyKind::Bool),
                    lhs_slice_var.clone(),
                    rhs_slice_var.clone(),
                ));

                lhs.node.insert(0, generate_slice_stmt(lhs_slice_var));
                rhs.node.insert(0, generate_slice_stmt(rhs_slice_var));
            }
            StmtKind::Negate(dir) => match (self.direction, dir) {
                (Direction::Down, Direction::Down) => self.direction = Direction::Up,
                (Direction::Up, Direction::Up) => self.direction = Direction::Down,
                _ => return Err(StmtSliceError::UnsupportedNegation(s.span)),
            },
            _ => {}
        }

        Ok(())
    }
}

/// Whether this expression is pure, i.e. has no side-effects. For example,
/// distribution calls and procedure calls have side-effects. Calls to
/// uninterpreted functions do not have side-effects.
fn is_pure_expr(tcx: &TyCtx, expr: &Expr) -> bool {
    // calls only show up on the topmost level of the expression, so we do not
    // need to recurse on expr.
    match &expr.kind {
        ExprKind::Call(ident, _) => {
            let decl: Rc<DeclKind> = tcx.get(*ident).unwrap();
            !decl.kind_name().is_proc()
        }
        _ => true,
    }
}
