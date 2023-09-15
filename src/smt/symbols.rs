//! Assignment of Caesar idents to Z3 symbols.

use std::collections::{hash_map::Entry, HashMap};

use crate::ast::{Ident, Symbol};

/// Translates Caesar idents to Z3 symbols.
#[derive(Debug, Default)]
pub struct Symbolizer {
    /// How many times have we seen distinct idents with this name?
    counter: HashMap<Symbol, usize>,
    /// The assignment of idents to symbols. If an ident cannot be
    /// found in this map, it is created using the counter map.
    symbols: HashMap<Ident, z3::Symbol>,
}

impl Symbolizer {
    pub fn get(&mut self, ident: Ident) -> z3::Symbol {
        if let Some(symbol) = self.symbols.get(&ident) {
            return symbol.clone();
        }
        // If we need to create a new symbol, then retrieve an index from the
        // counter map. But since a user might also create a symbol that
        // conflicts with the new name combined with the counter's index, we
        // need to run a loop that searches for the next unused name. Usually
        // however, this loop should only be executed (at most) once.
        let counter_entry = self.counter.entry(ident.name).or_insert(0);
        loop {
            let mut name = ident.name.to_owned();
            let counter = *counter_entry;
            *counter_entry += 1;
            let prev = self.symbols.entry(ident);
            if let Entry::Vacant(entry) = prev {
                if counter > 0 {
                    name = format!("{}_{}", name, counter);
                }
                let symbol = z3::Symbol::String(name);
                entry.insert(symbol.clone());
                return symbol;
            }
        }
    }
}
