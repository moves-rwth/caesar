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

