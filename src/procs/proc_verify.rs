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
};

/// Returns `None` if the proc has no body does not need verification.
pub fn verify_proc(proc: &ProcDecl) -> Option<VerifyUnit> {
    let direction = proc.direction;

    let body_ref = proc.body.borrow();
    let body = match &*body_ref {
        Some(body) => body,
        None => return None,
    };

    let mut stmts = Vec::new();

    // 1. push the assume statement for each requires
    for expr in proc.requires() {
        let span = expr.span.variant(SpanVariant::ProcVerify);
        stmts.push(Spanned::new(
            span,
            StmtKind::Assume(direction, expr.clone()),
        ));
    }
    // 2. append the procedure body's statements
    stmts.extend(body.iter().cloned());
    // 3. push the assert statements for each ensures
    for expr in proc.ensures() {
        let span = expr.span.variant(SpanVariant::ProcVerify);
        stmts.push(Spanned::new(
            span,
            StmtKind::Assert(direction, expr.clone()),
        ));
    }

    Some(VerifyUnit {
        direction,
        block: stmts,
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
        verify_unit.block.insert(
            0,
            Spanned::with_dummy_span(StmtKind::Negate(Direction::Down)),
        );
        verify_unit
            .block
            .push(Spanned::with_dummy_span(StmtKind::Negate(Direction::Up)));
    }
    verify_unit
}
