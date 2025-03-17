use super::Span;
use crate::ast::FileId;
use std::fmt;
use std::sync::{LazyLock, Mutex};
use string_interner::{DefaultStringInterner, DefaultSymbol, StringInterner};

static INTERNED_STRINGS: LazyLock<Mutex<DefaultStringInterner>> =
    LazyLock::new(|| Mutex::new(StringInterner::default()));

/// An interned string.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(DefaultSymbol);

impl Symbol {
    pub fn intern(string: &str) -> Self {
        let mut interned = INTERNED_STRINGS.lock().unwrap();
        Symbol(interned.get_or_intern(string))
    }

    pub fn to_owned(self) -> String {
        let interned = INTERNED_STRINGS.lock().unwrap();
        interned.resolve(self.0).unwrap().to_owned()
    }
}

impl PartialEq<str> for Symbol {
    fn eq(&self, other: &str) -> bool {
        let interned = INTERNED_STRINGS.lock().unwrap();
        interned.resolve(self.0).unwrap() == other
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let interned = INTERNED_STRINGS.lock().unwrap();
        fmt::Debug::fmt(interned.resolve(self.0).unwrap(), f)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let interned = INTERNED_STRINGS.lock().unwrap();
        fmt::Display::fmt(interned.resolve(self.0).unwrap(), f)
    }
}

/// An identifier consists of a name and a span.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Ident {
    pub name: Symbol,
    pub span: Span,
}

impl Ident {
    pub fn with_dummy_span(name: Symbol) -> Ident {
        Ident {
            name,
            span: Span::dummy_span(),
        }
    }

    pub fn with_dummy_file_span(name: Symbol, file: FileId) -> Ident {
        Ident {
            name,
            span: Span::dummy_file_span(file),
        }
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.name.fmt(f)
    }
}

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO
        f.write_fmt(format_args!("{:?}_{:?}", self.name, self.span))
        // f.write_fmt(format_args!("{:?}", self.name))
    }
}
