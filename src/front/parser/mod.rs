//! The parser takes a string and creates an AST from it.

pub(crate) mod parser_util;

use std::mem;

use ariadne::ReportKind;
use tracing::instrument;

use crate::ast::{
    Block, DeclKind, Diagnostic, Expr, FileId, Label, LitKind, Span, SpanVariant, StoredFile,
};

lalrpop_util::lalrpop_mod!(
    #[cfg_attr(rustfmt, rustfmt_skip)]
    #[allow(clippy::all, unused_parens)]
    grammar,
    "/src/front/parser/grammar.rs"
);

type GrammarParseError<'input> =
    lalrpop_util::ParseError<usize, grammar::Token<'input>, &'static str>;

#[derive(Debug)]
pub enum ParseError {
    InvalidToken { span: Span },
    UnrecognizedEOF { span: Span, expected: Vec<String> },
    UnrecognizedToken { span: Span, expected: Vec<String> },
    ExtraToken { span: Span },
}

impl ParseError {
    fn from_grammar_parse_error(file_id: FileId, err: GrammarParseError<'_>) -> ParseError {
        match err {
            GrammarParseError::InvalidToken { location } => ParseError::InvalidToken {
                span: Span::new(
                    file_id,
                    location,
                    location + 1,
                    crate::ast::SpanVariant::Parser,
                ),
            },
            GrammarParseError::UnrecognizedEOF { location, expected } => {
                ParseError::UnrecognizedEOF {
                    span: Span::new(
                        file_id,
                        location,
                        location + 1,
                        crate::ast::SpanVariant::Parser,
                    ),
                    expected,
                }
            }
            GrammarParseError::UnrecognizedToken { token, expected } => {
                ParseError::UnrecognizedToken {
                    span: Span::new(file_id, token.0, token.2, SpanVariant::Parser),
                    expected,
                }
            }
            GrammarParseError::ExtraToken { token } => ParseError::ExtraToken {
                span: Span::new(file_id, token.0, token.2, SpanVariant::Parser),
            },
            GrammarParseError::User { error: _ } => unreachable!(),
        }
    }

    pub fn diagnostic(&self) -> Diagnostic {
        match self {
            ParseError::InvalidToken { span } => Diagnostic::new(ReportKind::Error, *span)
                .with_message("Invalid token")
                .with_label(Label::new(*span).with_message("here")),
            ParseError::UnrecognizedEOF { span, expected } => {
                Diagnostic::new(ReportKind::Error, *span)
                    .with_message("Unrecognized end of file")
                    .with_label(Label::new(*span).with_message("here"))
                    .with_note(fmt_expected(expected))
            }
            ParseError::UnrecognizedToken { span, expected } => {
                Diagnostic::new(ReportKind::Error, *span)
                    .with_message("Unexpected token")
                    .with_label(Label::new(*span).with_message("here"))
                    .with_note(fmt_expected(expected))
            }
            ParseError::ExtraToken { span } => Diagnostic::new(ReportKind::Error, *span)
                .with_message("Extra token")
                .with_label(Label::new(*span).with_message("here")),
        }
    }
}

/// Parse a source code file into a list of declarations.
#[instrument]
pub fn parse_decls(file_id: FileId, source: &str) -> Result<Vec<DeclKind>, ParseError> {
    let clean_source = remove_comments(source).unwrap();
    let parser = grammar::DeclsParser::new();
    parser
        .parse(file_id, &clean_source)
        .map_err(|err| ParseError::from_grammar_parse_error(file_id, err))
}

/// Parse a source code file into a block of HeyVL statements.
#[instrument]
pub fn parse_raw(file_id: FileId, source: &str) -> Result<Block, ParseError> {
    let clean_source = remove_comments(source).unwrap();
    let parser = grammar::StmtsParser::new();
    parser
        .parse(file_id, &clean_source)
        .map_err(|err| ParseError::from_grammar_parse_error(file_id, err))
}

/// Parse an expression. This function DOES NOT handle comments!
pub fn parse_expr(file_id: FileId, source: &str) -> Result<Expr, ParseError> {
    let parser = grammar::ExprParser::new();
    parser
        .parse(file_id, source)
        .map_err(|err| ParseError::from_grammar_parse_error(file_id, err))
}

/// Parse a single literal. This function DOES NOT handle comments!
#[instrument]
pub fn parse_bare_decl(file: &StoredFile) -> Result<DeclKind, ParseError> {
    let parser = grammar::DeclParser::new();
    parser
        .parse(file.id, &file.source)
        .map_err(|err| ParseError::from_grammar_parse_error(file.id, err))
}

/// Parse a literal. Used for the [`std::str::FromStr`] implementation of
/// [`LitKind`].
pub(crate) fn parse_lit(source: &str) -> Result<LitKind, ()> {
    let parser = grammar::LitKindParser::new();
    parser.parse(FileId::DUMMY, source).map_err(|_| ())
}

#[derive(Debug)]
struct UnclosedCommentError;

/// Return a string where all comments are replaced by whitespace. The result
/// can be fed into our parser, and all non-whitespace locations will be the
/// same as in the original string.
fn remove_comments(source: &str) -> Result<String, UnclosedCommentError> {
    let mut res = source.as_bytes().to_owned();
    let mut iter = res.iter_mut();
    // iterate over all comment candidates
    while let Some(ch1) = iter.find(|ch| **ch == b'/') {
        match iter.next() {
            // single line comments
            Some(ch2 @ b'/') => {
                *ch1 = b' ';
                *ch2 = b' ';
                for ch3 in iter.by_ref().take_while(|ch| **ch != b'\n') {
                    *ch3 = b' ';
                }
            }
            // block comments
            Some(ch2 @ b'*') => {
                *ch1 = b' ';
                *ch2 = b' ';

                let mut comment_depth = 1;
                // the peekable iterator will consume one character after the
                // block comment. this effect is desirable: we require a space
                // before a new comment can begin again.
                let mut iter = iter.by_ref().peekable();
                while let Some(ch1) = iter.next() {
                    let ch1 = mem::replace(ch1, b' ');
                    match (ch1, iter.peek()) {
                        // block comment end
                        (b'*', Some(b'/')) => {
                            *iter.next().unwrap() = b' ';
                            comment_depth -= 1;
                            if comment_depth == 0 {
                                break;
                            }
                        }
                        // nested block comment start
                        (b'/', Some(b'*')) => {
                            *iter.next().unwrap() = b' ';
                            comment_depth += 1;
                        }
                        _ => {}
                    }
                }
                if comment_depth > 0 {
                    return Err(UnclosedCommentError);
                }
            }
            _ => {}
        }
    }

    let res = String::from_utf8(res).unwrap();
    assert_eq!(res.len(), source.len());
    Ok(res)
}

fn fmt_expected(expected: &[String]) -> String {
    if expected.len() == 1 {
        return format!("Expected {}", expected[0]);
    }

    let mut buf = String::new();
    for (i, e) in expected.iter().enumerate() {
        let sep = match i {
            0 => "Expected one of",
            _ if i < expected.len() - 1 => ",",
            _ if expected.len() >= 3 => ", or",
            _ => " or",
        };
        buf.push_str(sep);
        buf.push(' ');
        buf.push_str(e);
    }
    buf
}

#[cfg(test)]
mod test {
    use ariadne::Config;

    use crate::{
        ast::{Files, SourceFilePath},
        front::parser::ParseError,
    };

    use super::{parse_raw, remove_comments};

    #[test]
    fn test_remove_comments() {
        assert_eq!(remove_comments("/* /* */ */").unwrap(), "           ");
        assert_eq!(remove_comments("// /* */ */").unwrap(), "           ");
        assert_eq!(remove_comments("/* */ //").unwrap(), "        ");

        assert_eq!(
            remove_comments("test //   \ntest").unwrap(),
            "test      \ntest"
        );
    }

    #[test]
    fn test_parse_error() {
        let mut files = Files::new();
        let source = "if ⊓!";
        let file = files.add(SourceFilePath::Builtin, source.to_string());

        match parse_raw(file.id, &file.source) {
            Err(ref e @ ParseError::UnrecognizedToken { span, expected: _ }) => {
                assert_eq!(span.start, 6);
                assert_eq!(span.end, 7);

                let mut buf = Vec::new();
                e.diagnostic()
                    .into_ariadne(&files)
                    .with_config(Config::default().with_color(false))
                    .finish()
                    .write(&mut &files, &mut buf)
                    .unwrap();
                let buf = String::from_utf8(buf).unwrap();
                assert_eq!(
                    buf.lines()
                        .map(str::trim_end)
                        .map(|s| s.to_owned() + "\n")
                        .collect::<String>(),
                    r#"Error: Unexpected token
   ╭─[<builtin>:1:5]
   │
 1 │ if ⊓!
   ·     ┬
   ·     ╰── here
   ·
   · Note: Expected "{"
───╯
"#
                );
            }
            res => panic!("unexpected {:?}", res),
        }
    }
}
