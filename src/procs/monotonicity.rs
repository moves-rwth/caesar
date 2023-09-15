//! Monotonicity proofs for HeyVL programs. These are needed to ensure the
//! specification call encoding is sound.
//!
//! Formally, we'd like to check `forall f, g: \Expectations. f <= g ==>
//! vc[S](f) <= vc[S](g)`. Here, we only implement a syntactic check that
//! basically just requires that the program starts with a `down negate` and
//! that each `down negate` is followed by an `up negate`. There are monotone
//! programs that do not conform to this, so this check here is only a simple
//! approximation.

use ariadne::ReportKind;

use crate::ast::{
    visit::{walk_stmt, VisitorMut},
    DeclRef, Diagnostic, Direction, Label, ProcDecl, Span, Stmt, StmtKind,
};

pub struct MonotonicityVisitor {
    proc: DeclRef<ProcDecl>,
    current_dir: Direction,
    prev_negate: Option<Span>,
}

impl MonotonicityVisitor {
    pub fn new(proc_ref: DeclRef<ProcDecl>) -> Self {
        let current_dir = {
            let decl = proc_ref.borrow();
            decl.direction
        };
        MonotonicityVisitor {
            proc: proc_ref,
            current_dir,
            prev_negate: None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct MonotonicityError {
    proc: DeclRef<ProcDecl>,
    negate_span: Span,
    negate_dir: Direction,
    prev_negate: Option<Span>,
}

impl MonotonicityError {
    pub fn diagnostic(&self) -> Diagnostic {
        let proc = self.proc.borrow();
        const NOTE: &str = "Usually, in monotone programs, the first `negate` is a `negate` and each negation statement is followed by one of the opposite direction. However, this check is merely a heuristic. If you truly know what you are doing, then this might be fine.";
        let mut diag = Diagnostic::new(ReportKind::Warning, self.negate_span)
            .with_message(format!(
                "Procedure `{}` might not be monotone and calls to it might be unsound",
                proc.name
            ))
            .with_label(Label::new(self.negate_span).with_message(format!(
                "unexpected `{}` here",
                self.negate_dir.prefix("negate")
            )))
            .with_note(NOTE);
        if let Some(prev_negate) = self.prev_negate {
            diag = diag.with_label(Label::new(prev_negate).with_message(format!(
                "previous `{}` here",
                self.negate_dir.toggle().prefix("negate")
            )));
        }
        diag
    }
}

impl VisitorMut for MonotonicityVisitor {
    type Err = MonotonicityError;

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        match s.node {
            StmtKind::Negate(dir) => {
                if self.current_dir != dir {
                    return Err(MonotonicityError {
                        proc: self.proc.clone(),
                        negate_span: s.span,
                        negate_dir: dir,
                        prev_negate: None,
                    });
                }
                self.prev_negate = Some(s.span);
                self.current_dir = self.current_dir.toggle();
                Ok(())
            }
            _ => walk_stmt(self, s),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::verify_test;

    #[test]
    fn test_monotonicity_check() {
        for error_case in [
            "proc test() -> () { conegate }",
            "proc test() -> () { negate; negate }",
            "coproc test() -> () { negate; conegate }",
        ] {
            let err = verify_test(error_case).0.unwrap_err();
            assert_eq!(
                err.to_string(),
                "Warning: Procedure `test` might not be monotone and calls to it might be unsound"
            );
        }

        for good_case in [
            "proc test() -> () { }",
            "proc test() -> () { negate; conegate; negate; conegate }",
            "coproc test() -> () { conegate; negate }",
        ] {
            verify_test(good_case).0.unwrap();
        }
    }
}
