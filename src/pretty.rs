//! Pretty-printing infrastructure.

use ::pretty::RcDoc;

/// The main type for pretty-printed text.
pub type Doc = RcDoc<'static, ()>;

/// A value that can be pretty-printed.
pub trait SimplePretty {
    fn pretty(&self) -> Doc;
}

impl<'a, T: SimplePretty> SimplePretty for &'a T {
    fn pretty(&self) -> Doc {
        T::pretty(self)
    }
}

/// Wrap a document with parentheses and a group.
pub fn parens_group(doc: Doc) -> Doc {
    Doc::text("(")
        .append(Doc::group(
            Doc::line_().append(doc).nest(4).append(Doc::line_()),
        ))
        .append(Doc::text(")"))
}

/// Wrap the document in braces and indent it by four characters.
pub fn pretty_block(stmts: Doc) -> Doc {
    Doc::text("{")
        .append(Doc::line().append(stmts).nest(4))
        .append(Doc::line())
        .append(Doc::text("}"))
}

/// Render a list, separated by commas.
pub fn pretty_list<I>(iter: I) -> Doc
where
    I: IntoIterator,
    I::Item: SimplePretty,
{
    Doc::intersperse(
        iter.into_iter().map(|arg| arg.pretty()),
        Doc::text(",").append(Doc::line()),
    )
    .group()
}

/// Render a document to a String.
pub fn pretty_string<T: SimplePretty>(value: &T) -> String {
    let mut buf = String::new();
    value.pretty().render_fmt(80, &mut buf).unwrap();
    buf
}

/// Join normal (non-pretty) Strings with commas.
pub fn join_commas(iter: impl IntoIterator<Item = String>) -> String {
    let mut iter = iter.into_iter().peekable();
    let mut buf = String::new();
    while let Some(next) = iter.next() {
        buf.push_str(&next);
        if iter.peek().is_some() {
            buf.push_str(", ");
        }
    }
    buf
}
