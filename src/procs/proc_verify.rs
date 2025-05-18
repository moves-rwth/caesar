//! Generates the HeyVL code to verify a procedure implementation.
//!
//! A procedure
//! ```
//! proc myproc(param1: typ1) -> (ret2: typ2)
//!     pre e1
//!     pre e2
//!     post e3
//!     post e4
//!     { body }
//! ```
//! is translated for verification into a HeyVL program of the form
//! ```
//! assume e1;
//! assume e2;
//! body;
//! assert e3;
//! assert e4;
//! ```

use crate::{
    ast::{Direction, ProcDecl, SpanVariant, Spanned, StmtKind},
    driver::VerifyUnit,
    slicing::{wrap_with_error_message, wrap_with_success_message},
};

/// Returns `None` if the proc has no body does not need verification.
pub fn verify_proc(proc: &ProcDecl) -> Option<VerifyUnit> {
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
            &format!("{} pre #{} is not necessary", proc_kind, i),
        ));
    }

    // 2. append the procedure body's statements
    block.node.extend(body.node.iter().cloned());

    // 3. push the assert statements for each ensures
    for (i, expr) in proc.ensures().enumerate() {
        let span = expr.span.variant(SpanVariant::ProcVerify);
        block.node.push(wrap_with_error_message(
            Spanned::new(span, StmtKind::Assert(direction, expr.clone())),
            &format!("{} post #{} is part of the error", proc_kind, i),
        ));
    }

    Some(VerifyUnit {
        span: proc.name.span,
        direction,
        block,
    })
}

/// Turn the direction of this verification unit to lower bounds by adding
/// negations if the direction was up.
///
/// This is currently not used in the code anymore as we want to track the
/// direction explicitly to have better error messages, but exists for the sake
/// of completeness.
pub fn to_direction_lower_bounds(mut verify_unit: VerifyUnit) -> VerifyUnit {
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
