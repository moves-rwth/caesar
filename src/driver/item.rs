use std::{
    fmt,
    ops::{Deref, DerefMut},
    path::PathBuf,
};

use tracing::info_span;

use crate::ast::{SourceFilePath, Span};

/// Human-readable name for a source unit consisting of a file path, an
/// optionally qualified name, and a span for reporting.
#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct SourceUnitName {
    short_path: String,
    decl_name: Option<String>,
    /// The span used for reporting, such as the name of the procedure. We use
    /// this span position e.g. the gutter icons in the IDE.
    span: Span,
}

impl SourceUnitName {
    pub fn new(
        source_file_path: &SourceFilePath,
        decl_name: Option<String>,
        span: Span,
    ) -> SourceUnitName {
        let short_path = source_file_path
            .relative_to_cwd()
            .unwrap()
            .to_string_lossy()
            .to_string();
        SourceUnitName {
            short_path,
            decl_name,
            span,
        }
    }

    /// Create a file name for this source unit with the given file extension.
    ///
    /// This is used to create e.g. SMT-LIB output files for debugging. It is
    /// not necessarily related to the actual file name of the source unit.
    pub fn to_file_name(&self, extension: &str) -> PathBuf {
        let file_name = match &self.decl_name {
            Some(decl_name) => {
                // On Windows, `:` is not allowed in paths. Use `__` instead.
                let sep = if cfg!(windows) { "__" } else { "::" };
                format!("{}{}{}.{}", &self.short_path, sep, decl_name, extension)
            }
            None => format!("{}.{}", &self.short_path, extension),
        };
        let buf = PathBuf::from(file_name);
        // remove `..` parts from the path to avoid path traversal
        buf.components()
            .filter(|comp| !matches!(comp, std::path::Component::ParentDir))
            .collect::<PathBuf>()
    }

    pub fn span(&self) -> Span {
        self.span
    }
}

impl fmt::Display for SourceUnitName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(decl_name) = &self.decl_name {
            write!(f, "{}::{}", &self.short_path, decl_name)
        } else {
            write!(f, "{}", &self.short_path)
        }
    }
}

/// An _item_ is a piece of input. An item can be a procedure, a function, or a domain declaration.
pub struct Item<T> {
    name: SourceUnitName,
    span: tracing::Span,
    item: T,
}

impl<T> Item<T> {
    pub fn new(name: SourceUnitName, item: T) -> Self {
        let span = info_span!("item", name=%name);
        Item { name, span, item }
    }

    pub fn name(&self) -> &SourceUnitName {
        &self.name
    }

    pub fn enter_mut(&mut self) -> ItemEntered<'_, T> {
        ItemEntered {
            item: &mut self.item,
            _entered: self.span.enter(),
        }
    }

    pub fn enter_with_name(&mut self) -> (&SourceUnitName, ItemEntered<'_, T>) {
        let name = &self.name;
        let entered = ItemEntered {
            item: &mut self.item,
            _entered: self.span.enter(),
        };
        (name, entered)
    }

    pub fn flat_map<S>(self, f: impl FnOnce(T) -> Option<S>) -> Option<Item<S>> {
        let name = self.name;
        let span = self.span;
        let item = self.item;
        span.in_scope(|| f(item))
            .map(|item| Item { name, span, item })
    }
}

impl<T> fmt::Debug for Item<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.item, f)
    }
}

impl<T> fmt::Display for Item<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.item, f)
    }
}

/// An item implements [`Deref`] to enable filtering or reading the item.
///
/// Importantly, it does *not* implement [`DerefMut`] - use [`Item::enter`] to
/// obtain a mutable reference to the item. In contrast to this [`Deref`] impl,
/// [`Item::enter`] will also enter the span of the item.
impl<T> Deref for Item<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.item
    }
}

pub struct ItemEntered<'a, T> {
    item: &'a mut T,
    _entered: tracing::span::Entered<'a>,
}

impl<'a, T> fmt::Debug for ItemEntered<'a, T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.item, f)
    }
}

impl<'a, T> Deref for ItemEntered<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.item
    }
}

impl<'a, T> DerefMut for ItemEntered<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        self.item
    }
}
