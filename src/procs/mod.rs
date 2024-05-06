//! The verification of procedures and their use in procedure calls is rewritten using pure HeyVL encodings.
//! This module provides these transformations.

pub mod monotonicity;
pub mod proc_verify;
mod spec_call;

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
            let builder = ExprBuilder::new(proc.span);
            let value = match proc.direction {
                Direction::Down => builder.top_lit(&TyKind::EUReal),
                Direction::Up => builder.bot_lit(&TyKind::EUReal),
            };
            if proc.requires().next().is_none() {
                proc.spec.push(ProcSpec::Requires(value.clone()));
            }
            if proc.ensures().next().is_none() {
                proc.spec.push(ProcSpec::Ensures(value));
            }
        }
    }
}
