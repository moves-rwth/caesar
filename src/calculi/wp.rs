use std::fmt;

use crate::{
    ast::{Direction, FileId, Ident, Symbol},
    proof_rules::EncodingKind,
};

use super::Calculus;

pub struct WpCalculus(Ident);

impl WpCalculus {
    pub fn new(file: FileId) -> Self {
        WpCalculus(Ident::with_dummy_file_span(Symbol::intern("wp"), file))
    }
}

impl fmt::Debug for WpCalculus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("wp").finish()
    }
}

impl Calculus for WpCalculus {
    fn name(&self) -> Ident {
        self.0
    }

    fn check_encoding(&self, encoding: EncodingKind, direction: Direction) -> Result<(), ()> {
        match encoding {
            EncodingKind::Invariant(_)
            | EncodingKind::KInduction(_)
            | EncodingKind::Unroll(_)
            | EncodingKind::Ast(_)
            | EncodingKind::Past(_) => match direction {
                Direction::Down => Err(()),
                Direction::Up => Ok(()),
            },
            EncodingKind::Omega(_) | EncodingKind::Ost(_) => match direction {
                Direction::Down => Ok(()),
                Direction::Up => Err(()),
            },
        }
    }
}
