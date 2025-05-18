//! Data structures for output of diagnostic information to the user about a program, e.g. type errors.

use std::{
    borrow::Cow,
    convert::TryFrom,
    error::Error,
    fmt::{self, Display, Formatter},
    path::PathBuf,
    sync::Arc,
};

use ariadne::{Cache, Report, ReportBuilder, ReportKind, Source};
use lsp_types::{
    DiagnosticTag, NumberOrString, TextDocumentIdentifier, VersionedTextDocumentIdentifier,
};
use pathdiff::diff_paths;

use crate::pretty::{Doc, SimplePretty};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileId(u16);

impl FileId {
    pub const DUMMY: FileId = FileId(0);
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceFilePath {
    Path(PathBuf),
    Lsp(VersionedTextDocumentIdentifier),
    Builtin,
    Generated,
}

impl SourceFilePath {
    /// Rewrites a [`SourceFilePath::Path`] to be relative to the process
    /// working directory.
    pub fn relative_to_cwd(&self) -> std::io::Result<Self> {
        match self {
            SourceFilePath::Path(path) => {
                let current_dir = std::env::current_dir()?;
                #[allow(clippy::or_fun_call)]
                // clippy doesn't realize we need the call for the borrow checker
                let path_buf = diff_paths(path, current_dir).unwrap_or(path.to_path_buf());
                Ok(SourceFilePath::Path(path_buf))
            }
            _ => Ok(self.clone()),
        }
    }

    pub fn to_string_lossy(&self) -> Cow<'_, str> {
        match self {
            SourceFilePath::Path(path) => path.to_string_lossy(),
            SourceFilePath::Lsp(ident) => Cow::Owned(format!(
                "{} (version {})",
                ident.uri.as_str(),
                ident.version
            )),
            SourceFilePath::Builtin => Cow::from("<builtin>"),
            SourceFilePath::Generated => Cow::from("<generated>"),
        }
    }

    pub fn to_lsp_identifier(&self) -> Option<VersionedTextDocumentIdentifier> {
        match self {
            SourceFilePath::Lsp(ident) => Some(ident.clone()),
            _ => None,
        }
    }
}

impl fmt::Display for SourceFilePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_string_lossy())
    }
}

pub struct StoredFile {
    pub id: FileId,
    pub path: SourceFilePath,
    pub source: String,
    lines: Source,
}

impl StoredFile {
    pub(self) fn new(id: FileId, path: SourceFilePath, source: String) -> Self {
        let lines = Source::from(source.clone());
        StoredFile {
            id,
            path,
            source,
            lines,
        }
    }

    pub fn char_span(&self, span: Span) -> CharSpan {
        assert!(span.start <= span.end);
        let source = &self.source;
        let start = (0..span.start)
            .filter(|i| source.is_char_boundary(*i))
            .count();
        let end = start
            + (span.start..span.end)
                .filter(|i| source.is_char_boundary(*i))
                .count();
        CharSpan {
            file: span.file,
            start,
            end,
        }
    }
}

impl fmt::Debug for StoredFile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.path)
    }
}

#[derive(Debug, Default)]
pub struct Files {
    files: Vec<Arc<StoredFile>>,
}

impl Files {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn add(&mut self, path: SourceFilePath, source: String) -> &Arc<StoredFile> {
        let id = FileId(u16::try_from(self.files.len() + 1).unwrap());
        self.files.push(Arc::new(StoredFile::new(id, path, source)));
        self.get(id).unwrap()
    }

    pub fn add_or_update_uri(
        &mut self,
        document_id: VersionedTextDocumentIdentifier,
        source: String,
    ) -> &StoredFile {
        let file = self.files.iter_mut().find(|file| match &file.path {
            SourceFilePath::Lsp(ident) => ident.uri == document_id.uri,
            _ => false,
        });
        let path = SourceFilePath::Lsp(document_id);
        if let Some(file) = file {
            let file_id = file.id;
            *file = Arc::new(StoredFile::new(file_id, path, source));
            self.get(file_id).unwrap()
        } else {
            self.add(path, source)
        }
    }

    pub fn get(&self, file_id: FileId) -> Option<&Arc<StoredFile>> {
        assert_ne!(file_id, FileId::DUMMY);
        self.files.get((file_id.0 - 1) as usize)
    }

    pub fn find(&self, path: &SourceFilePath) -> Option<&Arc<StoredFile>> {
        self.files.iter().find(|file| &file.path == path)
    }

    pub fn find_uri(&self, document_id: TextDocumentIdentifier) -> Option<&Arc<StoredFile>> {
        self.files.iter().find(|file| match &file.path {
            SourceFilePath::Lsp(ident) => ident.uri == document_id.uri,
            _ => false,
        })
    }

    pub fn char_span(&self, span: Span) -> CharSpan {
        self.get(span.file).unwrap().char_span(span)
    }

    pub fn get_human_span_start(&self, span: Span) -> Option<(&StoredFile, usize, usize)> {
        if span.file == FileId::DUMMY {
            None
        } else {
            let file = self.get(span.file).unwrap();
            let char_span = file.char_span(span);
            let (_line, line_number, col_number) =
                file.lines.get_offset_line(char_span.start).unwrap();
            Some((file, line_number + 1, col_number + 1))
        }
    }

    /// Formats the start of the span as a human-readable string. The format is
    /// `FILE:LINE:COL`, where `LINE` and `COL` are 1-indexed character offsets
    /// into the file.
    ///
    /// This is the format accepted by e.g. VSCode's terminal to click and jump
    /// directly to the location in the file.
    ///
    /// Returns `None` if the span's file id is [`FileId::DUMMY`].
    pub fn format_span_start(&self, span: Span) -> Option<String> {
        let (file, line_number, col_number) = self.get_human_span_start(span)?;
        Some(format!("{}:{}:{}", file.path, line_number, col_number))
    }
}

/// Hacky impl of `Cache` for `Files` so that it only requires a shared reference.
impl<'a> Cache<FileId> for &'a Files {
    type Storage = String;

    fn fetch(&mut self, id: &FileId) -> Result<&Source<Self::Storage>, impl fmt::Debug> {
        let stored_file = self.get(*id).unwrap();
        Ok::<&ariadne::Source, ()>(&stored_file.lines)
    }

    fn display<'b>(&self, id: &'b FileId) -> Option<impl fmt::Display + 'b> {
        let stored_file = self.get(*id).unwrap();
        Some(Box::new(format!("{}", stored_file.path)))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum SpanVariant {
    Parser,
    VC,
    ImplicitCast,
    ProcVerify,
    SpecCall,
    Encoding,
    Qelim,
    Boolify,
    Subst,
    Slicing,
}

/// A region of source code in some file.
///
/// Positions are located by bytes (not characters!).
/// See [`CharSpan`] for the version which represents character offsets.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub file: FileId,
    pub start: usize,
    pub end: usize,
    pub variant: SpanVariant,
}

impl Span {
    pub fn new(file: FileId, start: usize, end: usize, origin: SpanVariant) -> Self {
        Span {
            file,
            start,
            end,
            variant: origin,
        }
    }

    pub fn dummy_span() -> Self {
        Span {
            file: FileId::DUMMY,
            start: 0,
            end: 0,
            variant: SpanVariant::Parser,
        }
    }

    pub fn dummy_file_span(file: FileId) -> Self {
        Span {
            file,
            start: 0,
            end: 0,
            variant: SpanVariant::Parser,
        }
    }

    pub fn variant(self, variant: SpanVariant) -> Self {
        Span {
            file: self.file,
            start: self.start,
            end: self.end,
            variant,
        }
    }

    pub fn to_lsp(
        self,
        files: &Files,
    ) -> Option<(VersionedTextDocumentIdentifier, lsp_types::Range)> {
        let file = files.get(self.file).unwrap();
        let char_span = file.char_span(self);

        let mut start_line = 0;
        let mut start_offset = 0;
        let mut end_line = 0;
        let mut end_offset = 0;

        for (i, c) in file.source.chars().enumerate() {
            if i == char_span.end {
                break;
            }
            if i == char_span.start {
                (start_line, start_offset) = (end_line, end_offset);
            }

            if c == '\n' {
                end_line += 1;
                end_offset = 0;
            } else {
                end_offset += 1;
            }
        }

        let range = lsp_types::Range {
            start: lsp_types::Position {
                line: start_line,
                character: start_offset,
            },
            end: lsp_types::Position {
                line: end_line,
                character: end_offset,
            },
        };
        Some((file.path.to_lsp_identifier()?, range))
    }
}

// TODO: this debug impl isn't great
impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prefix = match self.variant {
            SpanVariant::Parser => "",
            SpanVariant::VC => "vc/",
            SpanVariant::ImplicitCast => "cast/",
            SpanVariant::ProcVerify => "verify/",
            SpanVariant::SpecCall => "spec-call/",
            SpanVariant::Encoding => "encoding/",
            SpanVariant::Qelim => "qelim/",
            SpanVariant::Boolify => "boolify/",
            SpanVariant::Subst => "subst/",
            SpanVariant::Slicing => "slicing/",
        };
        f.write_fmt(format_args!("{}{}-{}", prefix, self.start, self.end))
    }
}

#[derive(Clone, Copy)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(span: Span, node: T) -> Self {
        Spanned { node, span }
    }

    pub fn with_dummy_span(node: T) -> Self {
        Spanned {
            node,
            span: Span::dummy_span(),
        }
    }

    pub fn with_dummy_file_span(node: T, file: FileId) -> Self {
        Spanned {
            node,
            span: Span::dummy_file_span(file),
        }
    }

    pub fn variant(span: Span, variant: SpanVariant, node: T) -> Self {
        Spanned {
            node,
            span: span.variant(variant),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{:?}", self.node))
    }
}

impl<T: PartialEq> PartialEq for Spanned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.node == other.node
    }
}

impl<T: Eq> Eq for Spanned<T> {}

impl<T: SimplePretty> SimplePretty for Spanned<T> {
    fn pretty(&self) -> Doc {
        self.node.pretty()
    }
}

/// Like [`Span`], but with character offsets. Needed to interface with ariadne.
pub struct CharSpan {
    pub file: FileId,
    pub start: usize,
    pub end: usize,
}

impl ariadne::Span for CharSpan {
    type SourceId = FileId;

    fn source(&self) -> &FileId {
        &self.file
    }

    fn start(&self) -> usize {
        self.start
    }

    fn end(&self) -> usize {
        self.end
    }
}

/// Similar to [`ariadne::ReportBuilder`], but it accepts our [`Span`] that is based on bytes.
#[derive(Debug)]
pub struct Diagnostic(Box<DiagnosticInner>);

/// We put all the [`Diagnostic`]'s data in an inner structure in a [`Box`] so
/// the [`Diagnostic`] type is small and can be used e.g. in the `Err` variant
/// of a [`Result`] without clippy complaining because of a big object.
#[derive(Debug)]
struct DiagnosticInner {
    kind: ReportKind<'static>,
    code: Option<NumberOrString>,
    msg: Option<String>,
    note: Option<String>,
    location: Span,
    labels: Vec<Label>,
    tags: Option<Vec<DiagnosticTag>>,
}

impl Diagnostic {
    pub fn new(kind: ReportKind<'static>, span: Span) -> Self {
        let inner = DiagnosticInner {
            kind,
            code: None,
            msg: None,
            note: None,
            location: span,
            labels: vec![],
            tags: None,
        };
        Diagnostic(Box::new(inner))
    }

    /// Overwrite the [`ReportKind`].
    pub fn with_kind(mut self, kind: ReportKind<'static>) -> Self {
        self.0.kind = kind;
        self
    }

    /// Give this diagnostic a code.
    pub fn with_code(mut self, code: NumberOrString) -> Self {
        self.0.code = Some(code);
        self
    }

    /// Give this diagnostic a message.
    pub fn with_message<M: ToString>(mut self, msg: M) -> Self {
        self.0.msg = Some(msg.to_string());
        self
    }

    /// Give the diagnostic a final note.
    pub fn with_note<N: ToString>(mut self, note: N) -> Self {
        self.0.note = Some(note.to_string());
        self
    }

    /// Add a new label to the diagnostic.
    pub fn with_label(mut self, label: Label) -> Self {
        self.0.labels.push(label);
        self
    }

    /// Add new labels to the diagnostic.
    pub fn with_labels(mut self, labels: impl IntoIterator<Item = Label>) -> Self {
        self.0.labels.extend(labels);
        self
    }

    /// Add a new [`DiagnosticTag`] (relevant for LSP only).
    pub fn with_tag(mut self, tag: DiagnosticTag) -> Self {
        self.0.tags.get_or_insert(vec![]).push(tag);
        self
    }

    pub fn kind(&self) -> ReportKind {
        self.0.kind
    }

    pub fn span(&self) -> Span {
        self.0.location
    }

    /// Generate the [`ariadne::ReportBuilder`].
    pub fn into_ariadne(self, files: &Files) -> ReportBuilder<CharSpan> {
        // note that ariadne's report doesn't use the span end
        let span = files.char_span(self.0.location);
        let mut builder = Report::build(self.0.kind, span);
        if let Some(code) = self.0.code {
            let code = match code {
                NumberOrString::Number(code) => code.to_string(),
                NumberOrString::String(code) => code,
            };
            builder = builder.with_code(code);
        }
        if let Some(msg) = self.0.msg {
            builder = builder.with_message(msg);
        }
        if let Some(note) = self.0.note {
            builder = builder.with_note(note);
        }
        for label in self.0.labels {
            builder = builder.with_label(label.into_ariadne(files));
        }
        builder
    }

    pub fn into_lsp_diagnostic(
        &self,
        files: &Files,
    ) -> Option<(VersionedTextDocumentIdentifier, lsp_types::Diagnostic)> {
        let (document_id, range) = self.0.location.to_lsp(files)?;

        let severity = match self.0.kind {
            ReportKind::Error => lsp_types::DiagnosticSeverity::ERROR,
            ReportKind::Warning => lsp_types::DiagnosticSeverity::WARNING,
            ReportKind::Advice => lsp_types::DiagnosticSeverity::INFORMATION,
            _ => lsp_types::DiagnosticSeverity::ERROR,
        };
        let code = self.0.code.clone();
        let message = self
            .0
            .msg
            .clone()
            .unwrap_or_else(|| "(no message)".to_string());
        let mut related_information = self
            .0
            .labels
            .iter()
            .flat_map(|label| {
                let (uri, range) = if let Some(res) = label.span.to_lsp(files) {
                    res
                } else {
                    tracing::error!("{:?} is not an LSP path, skipping label", label.span);
                    return None;
                };
                Some(lsp_types::DiagnosticRelatedInformation {
                    location: lsp_types::Location {
                        uri: uri.uri,
                        range,
                    },
                    message: label.msg.clone()?,
                })
            })
            .collect::<Vec<_>>();
        if let Some(note) = &self.0.note {
            related_information.push(lsp_types::DiagnosticRelatedInformation {
                location: lsp_types::Location {
                    uri: document_id.uri.clone(),
                    range,
                },
                message: format!("Note: {}", note),
            })
        }
        let diagnostic = lsp_types::Diagnostic {
            range,
            severity: Some(severity),
            code,
            code_description: None,
            source: Some("caesar".to_owned()),
            message,
            related_information: Some(related_information),
            tags: self.0.tags.clone(),
            data: None,
        };
        Some((document_id, diagnostic))
    }

    /// Write the diagnostic to a simple [`String`] without ANSI colors.
    ///
    /// This is useful for testing.
    pub fn into_string(self, files: &Files) -> String {
        let config = ariadne::Config::default().with_color(false);
        let mut buf = Vec::new();
        self.into_ariadne(files)
            .with_config(config)
            .finish()
            .write(files, &mut buf)
            .unwrap();
        String::from_utf8(buf).unwrap()
    }
}

/// The Display instance should be avoided in favor of properly using ariadne's
/// printing facilities through [`Diagnostic::into_ariadne`]. This instance only
/// exists to make debugging easier.
impl Display for Diagnostic {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(code) = &self.0.code {
            let code = match code {
                NumberOrString::Number(code) => &code.to_string(),
                NumberOrString::String(code) => code,
            };
            write!(f, "[{}] ", code)?;
        }
        write!(f, "{}: ", self.0.kind)?;
        if let Some(msg) = &self.0.msg {
            f.write_str(msg)?;
        } else {
            f.write_str("(no message)")?;
        }
        // TODO: somehow print some info about the location?
        Ok(())
    }
}

impl Error for Diagnostic {}

/// Similar to [`ariadne::Label`], but using our [`Span`].
#[derive(Debug)]
pub struct Label {
    span: Span,
    msg: Option<String>,
}

impl Label {
    pub fn new(span: Span) -> Self {
        Self { span, msg: None }
    }

    pub fn with_message<M: ToString>(mut self, msg: M) -> Self {
        self.msg = Some(msg.to_string());
        self
    }

    fn into_ariadne(self, files: &Files) -> ariadne::Label<CharSpan> {
        let mut label = ariadne::Label::new(files.char_span(self.span));
        if let Some(msg) = self.msg {
            label = label.with_message(msg);
        }
        label
    }
}
