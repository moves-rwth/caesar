//! Generates the HeyVL code to verify a procedure implementation.
//!
//! A procedure
//! ```
//! proc myproc(param1: typ1) -> (ret2: typ2)
//!     down requires e1
//!     down requires e2
//!     down ensures e3
//!     down ensures e4
//!     { body }
//! ```
//! is translated for verification into a HeyVL program of the form
//! ```
//! down assume e1;
//! down assume e2;
//! body;
//! down assert e3;
//! down assert e4;
//! ```
//!
//! If the direction is `up`, corresponding negations are generated as well.

use crate::ast::{Block, Direction, ProcDecl, SpanVariant, Spanned, StmtKind};

/// Returns `None` if the proc has no body does not need verification.
pub fn verify_proc(proc: &ProcDecl) -> Option<Block> {
    let dir = proc.direction;

    let body_ref = proc.body.borrow();
    let body = match &*body_ref {
        Some(body) => body,
        None => return None,
    };

    let mut stmts = Vec::new();

    // 1. push the assume statement for each requires
    for expr in proc.requires() {
        let span = expr.span.variant(SpanVariant::ProcVerify);
        stmts.push(Spanned::new(span, StmtKind::Assume(dir, expr.clone())));
    }
    // 2. append the procedure body's statements
    stmts.extend(body.iter().cloned());
    // 3. push the assert statements for each ensures
    for expr in proc.ensures() {
        let span = expr.span.variant(SpanVariant::ProcVerify);
        stmts.push(Spanned::new(span, StmtKind::Assert(dir, expr.clone())));
    }
    // 4. wrap with negations if direction is up
    if dir == Direction::Up {
        stmts.insert(
            0,
            Spanned::with_dummy_span(StmtKind::Negate(Direction::Down)),
        );
        stmts.push(Spanned::with_dummy_span(StmtKind::Negate(Direction::Up)));
    }

    Some(stmts)
}
