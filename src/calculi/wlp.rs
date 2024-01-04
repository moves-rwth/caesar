use std::fmt;

use crate::{
    ast::{Direction, FileId, Ident, Symbol},
    proof_rules::EncodingKind,
};

use super::Calculus;

pub struct WlpCalculus(Ident);

impl WlpCalculus {
    pub fn new(file: FileId) -> Self {
        WlpCalculus(Ident::with_dummy_file_span(Symbol::intern("wlp"), file))
    }
}

impl fmt::Debug for WlpCalculus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("wlp").finish()
    }
}

impl Calculus for WlpCalculus {
    fn name(&self) -> Ident {
        self.0
    }

    fn check_encoding(&self, encoding: EncodingKind, direction: Direction) -> Result<(), ()> {
        match encoding {
            EncodingKind::Invariant(_) | EncodingKind::KInduction(_) | EncodingKind::Unroll(_) => {
                match direction {
                    Direction::Down => Ok(()),
                    Direction::Up => Err(()),
                }
            }
            EncodingKind::Omega(_) => match direction {
                Direction::Down => Err(()),
                Direction::Up => Ok(()),
            },
            EncodingKind::Ast(_) | EncodingKind::Past(_) | EncodingKind::Ost(_) => Err(()),
        }
    }
}
