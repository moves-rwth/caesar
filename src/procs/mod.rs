//! The verification of procedures and their use in procedure calls is rewritten using pure HeyVL encodings.
//! This module provides these transformations.

pub mod monotonicity;
mod proc_verify;
mod spec_call;

pub use proc_verify::verify_proc;
pub use spec_call::SpecCall;

use crate::{
    ast::{DeclKind, Direction, ExprBuilder, ProcSpec, TyKind},
    tyctx::TyCtx,
};

/// If a procedure declaration has no spec at all, add the default one.
///
/// For procs, that is `pre ?(true)` and `post ?(true)`.
/// For coprocs, that is `pre ?(false)` and `post ?(false)`.
pub fn add_default_specs(tcx: &mut TyCtx) {
    for decl in tcx.declarations_mut() {
        if let DeclKind::ProcDecl(proc_ref) = decl {
            let mut proc = proc_ref.borrow_mut();
            if proc.spec.is_empty() {
                let builder = ExprBuilder::new(proc.span);
                let value = match proc.direction {
                    Direction::Down => builder.top_lit(&TyKind::EUReal),
                    Direction::Up => builder.bot_lit(&TyKind::EUReal),
                };
                proc.spec.push(ProcSpec::Requires(value.clone()));
                proc.spec.push(ProcSpec::Ensures(value));
            }
        }
    }
}
