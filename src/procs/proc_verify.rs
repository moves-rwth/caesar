use crate::{
    ast::{
        self, BinOpKind, Block, Direction, ExprData, ExprKind, ProcDecl, Shared, Span, SpanVariant,
        Spanned, StmtKind, TyKind, UnOpKind,
    },
    driver::core_verify::CoreVerifyTask,
    slicing::{wrap_with_error_message, wrap_with_success_message},
};

/// Encode the preexpectations as a formula for which counterexamples are satisfying valuations
/// of the preexpectations.
/// For proc:
///     goal: Find a model such that (pre1 ⊓ pre2 ⊓...) > 0
///     (pre1 ⊓ pre2 ⊓...) = 0 iff !(pre1 ⊓ pre2 ⊓...) = top
///     (pre1 ⊓ pre2 ⊓...) > 0 iff !(pre1 ⊓ pre2 ⊓...) = 0
///     find cex for: !(pre1 ⊓ pre2 ⊓...)
/// For coproc:
///     goal: Find a model such that (pre1 ⊔ pre2 ⊔...) < top
///     (pre1 ⊔ pre2 ⊔...) = top iff ~(pre1 ⊔ pre2 ⊔...) = 0
///     (pre1 ⊔ pre2 ⊔...) < top iff ~(pre1 ⊔ pre2 ⊔...) = top
///     find cex for: ~(pre1 ⊔ pre2 ⊔...)
pub fn encode_pre_get_model(proc: &ProcDecl) -> Option<(Direction, Block)> {
    let direction = proc.direction;

    let body_ref = proc.body.borrow();
    let body = match &*body_ref {
        Some(body) => body,
        None => return None,
    };
    let mut block = Spanned::new(body.span, vec![]);

    fn get_combination(direction: Direction) -> ast::expr::BinOpKind {
        let combination = match direction {
            Direction::Down => BinOpKind::Inf,
            Direction::Up => BinOpKind::Sup,
        };
        combination
    }

    fn get_negation_type(direction: Direction) -> ast::expr::UnOpKind {
        let negation_type = match direction {
            Direction::Down => UnOpKind::Not,
            Direction::Up => UnOpKind::Non,
        };
        negation_type
    }

    // push the assume statement for each requires
    let mut build_expr = proc
        .requires()
        .next()
        .expect("No preconditions to check")
        .clone();
    for expr in proc.requires().skip(1) {
        build_expr = Shared::new(ExprData {
            kind: ExprKind::Binary(
                Spanned::with_dummy_span(get_combination(direction)),
                build_expr,
                expr.clone(),
            ),
            ty: Some(TyKind::EUReal),
            span: Span::dummy_span(),
        });
    }

    build_expr = Shared::new(ExprData {
        kind: ExprKind::Unary(
            Spanned::with_dummy_span(get_negation_type(direction)),
            build_expr,
        ),
        ty: Some(TyKind::EUReal),
        span: Span::dummy_span(),
    });
    block.node.push(Spanned::new(
        Span::dummy_span(),
        StmtKind::Assert(direction, build_expr),
    ));
    Some((direction, block))
}
/// Generates the HeyVL code to verify a procedure implementation. Returns
/// `None` if the proc has no body does not need verification.
///
/// ## The Encoding
/// A procedure
/// ```
/// proc myproc(param1: typ1) -> (ret2: typ2)
///     pre e1
///     pre e2
///     post e3
///     post e4
///     { body }
/// ```
/// is translated for verification into a HeyVL program of the form
/// ```
/// assume e1;
/// assume e2;
/// body;
/// assert e3;
/// assert e4;
/// ```
pub fn encode_proc_verify(proc: &ProcDecl) -> Option<(Direction, Block)> {
    let direction = proc.direction;

    let body_ref = proc.body.borrow();
    let body = match &*body_ref {
        Some(body) => body,
        None => return None,
    };

    let proc_kind = match direction {
        Direction::Down => "proc",
        Direction::Up => "coproc",
    };

    let mut block = Spanned::new(body.span, vec![]);

    // 1. push the assume statement for each requires
    for (i, expr) in proc.requires().enumerate() {
        let span = expr.span.variant(SpanVariant::ProcVerify);
        block.node.push(wrap_with_success_message(
            Spanned::new(span, StmtKind::Assume(direction, expr.clone())),
            &format!("{proc_kind} pre #{i} is not necessary"),
        ));
    }

    // 2. append the procedure body's statements
    block.node.extend(body.node.iter().cloned());

    // 3. push the assert statements for each ensures
    for (i, expr) in proc.ensures().enumerate() {
        let span = expr.span.variant(SpanVariant::ProcVerify);
        block.node.push(wrap_with_error_message(
            Spanned::new(span, StmtKind::Assert(direction, expr.clone())),
            &format!("{proc_kind} post #{i} is part of the error"),
        ));
    }

    Some((direction, block))
}

/// Turn the direction of this verification unit to lower bounds by adding
/// negations if the direction was up.
///
/// This is currently not used in the code anymore as we want to track the
/// direction explicitly to have better error messages, but exists for the sake
/// of completeness.
pub fn to_direction_lower_bounds(mut verify_unit: CoreVerifyTask) -> CoreVerifyTask {
    if verify_unit.direction == Direction::Up {
        verify_unit.direction = Direction::Down;
        verify_unit.block.node.insert(
            0,
            Spanned::with_dummy_span(StmtKind::Negate(Direction::Down)),
        );
        verify_unit
            .block
            .node
            .push(Spanned::with_dummy_span(StmtKind::Negate(Direction::Up)));
    }
    verify_unit
}
