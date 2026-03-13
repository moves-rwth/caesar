//! The parser takes a string and creates an AST from it.

pub(crate) mod parser_util;
mod precedence_update;

use std::mem;

use ariadne::ReportKind;
use clap::ValueEnum;
use tracing::instrument;

use crate::ast::{
    Block, DeclKind, Diagnostic, FileId, Label, LitKind, Span, SpanVariant, StoredFile,
};

lalrpop_util::lalrpop_mod!(
    #[cfg_attr(rustfmt, rustfmt_skip)]
    grammar,
    "/src/front/parser/grammar.rs"
);

type GrammarParseError<'input> =
    lalrpop_util::ParseError<usize, grammar::Token<'input>, &'static str>;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum ParserMode {
    New,
    Old,
    #[default]
    Both,
}

#[derive(Debug)]
pub enum ParseError {
    InvalidToken { span: Span },
    UnrecognizedEof { span: Span, expected: Vec<String> },
    UnrecognizedToken { span: Span, expected: Vec<String> },
    ExtraToken { span: Span },
    ChangedPrecedence(Box<precedence_update::ExprMismatch>),
}

impl ParseError {
    fn from_grammar_parse_error(file_id: FileId, err: GrammarParseError<'_>) -> ParseError {
        Self::from_lalrpop_parse_error(file_id, err)
    }

    pub(crate) fn from_lalrpop_parse_error<Token>(
        file_id: FileId,
        err: lalrpop_util::ParseError<usize, Token, &'static str>,
    ) -> ParseError {
        match err {
            lalrpop_util::ParseError::InvalidToken { location } => ParseError::InvalidToken {
                span: Span::new(
                    file_id,
                    location,
                    location + 1,
                    crate::ast::SpanVariant::Parser,
                ),
            },
            lalrpop_util::ParseError::UnrecognizedEof { location, expected } => {
                ParseError::UnrecognizedEof {
                    span: Span::new(
                        file_id,
                        location,
                        location + 1,
                        crate::ast::SpanVariant::Parser,
                    ),
                    expected,
                }
            }
            lalrpop_util::ParseError::UnrecognizedToken { token, expected } => {
                ParseError::UnrecognizedToken {
                    span: Span::new(file_id, token.0, token.2, SpanVariant::Parser),
                    expected,
                }
            }
            lalrpop_util::ParseError::ExtraToken { token } => ParseError::ExtraToken {
                span: Span::new(file_id, token.0, token.2, SpanVariant::Parser),
            },
            lalrpop_util::ParseError::User { error: _ } => unreachable!(),
        }
    }

    pub fn diagnostic(&self) -> Diagnostic {
        match self {
            ParseError::InvalidToken { span } => Diagnostic::new(ReportKind::Error, *span)
                .with_message("Invalid token")
                .with_label(Label::new(*span).with_message("here")),
            ParseError::UnrecognizedEof { span, expected } => {
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
            ParseError::ChangedPrecedence(data) => {
                Diagnostic::new(ReportKind::Error, data.subexpr.span)
                    .with_message("Expression is ambiguous after Caesar's parser changes")
                    .with_label(
                        Label::new(data.subexpr.span)
                            .with_message("add explicit parentheses to disambiguate"),
                    )
                    .with_note(format!(
                "Old parser: {}\nNew parser: {}\nAdd parentheses to keep the intended meaning.",
                strip_outer_parens_once(&data.subexpr.old_expr),
                strip_outer_parens_once(&data.subexpr.new_expr)
            ))
            }
        }
    }
}

/// Parse a source code file into a list of declarations.
#[instrument(skip(source))]
pub fn parse_decls(file_id: FileId, source: &str) -> Result<Vec<DeclKind>, ParseError> {
    parse_decls_with_mode(file_id, source, ParserMode::Both)
}

pub fn parse_decls_with_mode(
    file_id: FileId,
    source: &str,
    parser_mode: ParserMode,
) -> Result<Vec<DeclKind>, ParseError> {
    let clean_source = remove_comments(source);
    parse_by_mode(
        parser_mode,
        || parse_new_decls(file_id, &clean_source),
        || precedence_update::parse_old_decls(file_id, &clean_source),
        |decls| precedence_update::decls_mismatch(file_id, &clean_source, decls),
    )
}

/// Parse a source code file into a block of HeyVL statements.
#[instrument]
pub fn parse_raw(file_id: FileId, source: &str) -> Result<Block, ParseError> {
    parse_raw_with_mode(file_id, source, ParserMode::Both)
}

pub fn parse_raw_with_mode(
    file_id: FileId,
    source: &str,
    parser_mode: ParserMode,
) -> Result<Block, ParseError> {
    let clean_source = remove_comments(source);
    parse_by_mode(
        parser_mode,
        || parse_new_raw(file_id, &clean_source),
        || precedence_update::parse_old_block(file_id, &clean_source),
        |block| precedence_update::block_mismatch(file_id, &clean_source, block),
    )
}

/// Parse an expression. This function DOES NOT handle comments!
#[cfg(test)]
pub fn parse_expr(file_id: FileId, source: &str) -> Result<crate::ast::Expr, ParseError> {
    parse_expr_with_mode(file_id, source, ParserMode::Both)
}

/// Parse an expression with a specific parser mode. This function DOES NOT
/// handle comments!
#[cfg(test)]
pub fn parse_expr_with_mode(
    file_id: FileId,
    source: &str,
    parser_mode: ParserMode,
) -> Result<crate::ast::Expr, ParseError> {
    parse_by_mode(
        parser_mode,
        || parse_new_expr(file_id, source),
        || precedence_update::parse_old_expr(file_id, source),
        |expr| precedence_update::expr_mismatch(file_id, source, expr),
    )
}

/// Parse a single literal. This function DOES NOT handle comments!
#[instrument]
pub fn parse_bare_decl(file: &StoredFile) -> Result<DeclKind, ParseError> {
    parse_bare_decl_with_mode(file, ParserMode::Both)
}

/// Parse a single declaration with a specific parser mode. This function DOES
/// NOT handle comments!
#[instrument]
pub fn parse_bare_decl_with_mode(
    file: &StoredFile,
    parser_mode: ParserMode,
) -> Result<DeclKind, ParseError> {
    parse_by_mode(
        parser_mode,
        || parse_new_decl(file.id, &file.source),
        || precedence_update::parse_old_decl(file.id, &file.source),
        |decl| precedence_update::decl_mismatch(file.id, &file.source, decl),
    )
}

fn parse_by_mode<T>(
    parser_mode: ParserMode,
    parse_new: impl FnOnce() -> Result<T, ParseError>,
    parse_old: impl FnOnce() -> Result<T, ParseError>,
    changed_precedence: impl FnOnce(&T) -> Option<precedence_update::ExprMismatch>,
) -> Result<T, ParseError> {
    match parser_mode {
        ParserMode::New => parse_new(),
        ParserMode::Old => parse_old(),
        ParserMode::Both => {
            let parsed = parse_new()?;
            if let Some(mismatch) = changed_precedence(&parsed) {
                return Err(ParseError::ChangedPrecedence(Box::new(mismatch)));
            }
            Ok(parsed)
        }
    }
}

fn parse_new_decls(file_id: FileId, source: &str) -> Result<Vec<DeclKind>, ParseError> {
    grammar::DeclsParser::new()
        .parse(file_id, source)
        .map_err(|err| ParseError::from_grammar_parse_error(file_id, err))
}

fn parse_new_raw(file_id: FileId, source: &str) -> Result<Block, ParseError> {
    grammar::SpannedStmtsParser::new()
        .parse(file_id, source)
        .map_err(|err| ParseError::from_grammar_parse_error(file_id, err))
}

#[cfg(test)]
fn parse_new_expr(file_id: FileId, source: &str) -> Result<crate::ast::Expr, ParseError> {
    grammar::ExprParser::new()
        .parse(file_id, source)
        .map_err(|err| ParseError::from_grammar_parse_error(file_id, err))
}

fn parse_new_decl(file_id: FileId, source: &str) -> Result<DeclKind, ParseError> {
    grammar::DeclParser::new()
        .parse(file_id, source)
        .map_err(|err| ParseError::from_grammar_parse_error(file_id, err))
}

/// Parse a literal. Used for the [`std::str::FromStr`] implementation of
/// [`LitKind`].
pub(crate) fn parse_lit(source: &str) -> Result<LitKind, ()> {
    let parser = grammar::LitKindParser::new();
    parser.parse(FileId::DUMMY, source).map_err(|_| ())
}

/// Return a string where all comments are replaced by whitespace. The result
/// can be fed into our parser, and all non-whitespace locations will be the
/// same as in the original string.
///
/// If a block comment is not closed, then there will be no error, and instead
/// the rest of the file will be treated as whitespace.
fn remove_comments(source: &str) -> String {
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
            }
            _ => {}
        }
    }

    let res = String::from_utf8(res).unwrap();
    assert_eq!(res.len(), source.len());
    res
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

/// Formatting hack for precedence diagnostics: drop one outer `( … )` pair
/// if present, to reduce visual noise in the note output.
fn strip_outer_parens_once(expr: &str) -> &str {
    if expr.len() >= 2 && expr.starts_with('(') && expr.ends_with(')') {
        &expr[1..expr.len() - 1]
    } else {
        expr
    }
}

#[cfg(test)]
mod test {
    use ariadne::Config;

    use crate::{
        ast::{FileId, Files, SourceFilePath},
        front::parser::ParseError,
        pretty::pretty_string,
    };

    use super::{parse_expr_with_mode, parse_raw, remove_comments, ParserMode};

    #[test]
    fn test_remove_comments() {
        assert_eq!(remove_comments("/* /* */ */"), "           ");
        assert_eq!(remove_comments("// /* */ */"), "           ");
        assert_eq!(remove_comments("/* */ //"), "        ");

        assert_eq!(remove_comments("test //   \ntest"), "test      \ntest");
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
   ╭─[ <builtin>:1:5 ]
   │
 1 │ if ⊓!
   │     ┬
   │     ╰── here
   │
   │ Note: Expected "{"
───╯
"#
                );
            }
            res => panic!("unexpected {res:?}"),
        }
    }

    #[test]
    fn test_parser_mode_switching() {
        let source = "n - i + x";
        let old_expr = parse_expr_with_mode(FileId::DUMMY, source, ParserMode::Old).unwrap();
        let new_expr = parse_expr_with_mode(FileId::DUMMY, source, ParserMode::New).unwrap();

        assert_eq!(pretty_string(&old_expr), "(n - (i + x))");
        assert_eq!(pretty_string(&new_expr), "((n - i) + x)");

        match parse_expr_with_mode(FileId::DUMMY, source, ParserMode::Both) {
            Err(ParseError::ChangedPrecedence(_)) => {}
            res => panic!("expected changed-precedence error, got {res:?}"),
        }
    }
}
