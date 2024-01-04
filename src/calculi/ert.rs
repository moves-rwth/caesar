use std::fmt;

use crate::{
    ast::{Direction, FileId, Ident, Symbol},
    proof_rules::EncodingKind,
};

use super::Calculus;

pub struct ErtCalculus(Ident);

impl ErtCalculus {
    pub fn new(file: FileId) -> Self {
        ErtCalculus(Ident::with_dummy_file_span(Symbol::intern("ert"), file))
    }
}

impl fmt::Debug for ErtCalculus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ert").finish()
    }
}

impl Calculus for ErtCalculus {
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
