//! This module glues all components of Caesar together.

use std::{
    fmt,
    ops::{Deref, DerefMut},
};

use crate::{
    ast::{
        visit::VisitorMut, Block, DeclKind, Expr, ExprData, ExprKind, LitKind, Shared,
        SourceFilePath, Span, Spanned, StoredFile, TyKind,
    },
    front::parser,
    front::resolve::{Resolve, ResolveError},
    front::{
        parser::ParseError,
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::AnnotationError,
    pretty::{Doc, SimplePretty},
    procs::{
        monotonicity::{MonotonicityError, MonotonicityVisitor},
        verify_proc, SpecCall,
    },
    proof_rules::EncCall,
    tyctx::TyCtx,
    vc::vcgen::Vcgen,
};
use tracing::{info_span, instrument, trace};

/// Human-readable name for a source unit. Used for debugging and error messages.
#[derive(Debug)]
pub struct SourceUnitName(String);

impl SourceUnitName {
    fn new_raw(source_file_path: &SourceFilePath) -> SourceUnitName {
        let short_path = source_file_path
            .relative_to_cwd()
            .unwrap()
            .to_string_lossy()
            .to_string();
        SourceUnitName(short_path)
    }

    fn new_decl(source_file_path: &SourceFilePath, decl: &DeclKind) -> SourceUnitName {
        let short_path = source_file_path
            .relative_to_cwd()
            .unwrap()
            .to_string_lossy()
            .to_string();
        SourceUnitName(format!("{}::{}", short_path, decl.name().name))
    }
}

impl fmt::Display for SourceUnitName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
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

    pub fn init(name: SourceUnitName, init: impl FnOnce() -> T) -> Self {
        Item::new(name, ()).map(|()| init())
    }

    pub fn try_init<E>(
        name: SourceUnitName,
        init: impl FnOnce() -> Result<T, E>,
    ) -> Result<Item<T>, E> {
        let res = Item::init(name, init);
        Ok(Item {
            name: res.name,
            span: res.span,
            item: res.item?,
        })
    }

    pub fn enter(&mut self) -> ItemEntered<'_, T> {
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

    pub fn map<S>(self, f: impl FnOnce(T) -> S) -> Item<S> {
        let name = self.name;
        let span = self.span;
        let item = self.item;
        let item = span.in_scope(|| f(item));
        Item { name, span, item }
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

/// A unit of source code that can be independently type-checked and verified.
/// It is either a declaration or just a series of raw HeyVL statements.
#[derive(Debug)]
pub enum SourceUnit {
    Decl(DeclKind),
    Raw(Block),
}

impl SourceUnit {
    #[instrument(skip(self, tcx))]
    pub fn desugar(
        &mut self,
        tcx: &mut TyCtx,
        source_units_buf: &mut Vec<Item<SourceUnit>>,
    ) -> Result<(), AnnotationError> {
        let mut enc_call = EncCall::new(tcx, source_units_buf);

        match self {
            SourceUnit::Decl(decl) => enc_call.visit_decl(decl),
            SourceUnit::Raw(block) => enc_call.visit_stmts(block),
        }
    }

    /// Return a new [`Item`] by wrapping it around the [`SourceUnit`]
    /// and set the file path of the new [`SourceUnitName`] to the given file_path argument
    /// This function is used to generate [`Item`]s from generated [`SourceUnit`] objects (through AST transformations)
    pub fn wrap_item(self, file_path: &SourceFilePath) -> Item<SourceUnit> {
        match self {
            SourceUnit::Decl(decl) => Item::new(
                SourceUnitName::new_decl(file_path, &decl),
                SourceUnit::Decl(decl),
            ),
            SourceUnit::Raw(block) => {
                Item::new(SourceUnitName::new_raw(file_path), SourceUnit::Raw(block))
            }
        }
    }

    pub fn parse(file: &StoredFile, raw: bool) -> Result<Vec<Item<Self>>, ParseError> {
        if raw {
            let name = SourceUnitName::new_raw(&file.path);
            let item = Item::try_init(name, || {
                let block = parser::parse_raw(file.id, &file.source)?;
                Ok(SourceUnit::Raw(block))
            })?;
            Ok(vec![item])
        } else {
            let decls =
                info_span!("parse", path=%file.path.to_string_lossy(), raw=raw).in_scope(|| {
                    let decls = parser::parse_decls(file.id, &file.source)?;
                    trace!(n = decls.len(), "source units parsed");
                    Ok(decls)
                })?;

            Ok(decls
                .into_iter()
                .map(|decl| {
                    Item::new(
                        SourceUnitName::new_decl(&file.path, &decl),
                        SourceUnit::Decl(decl),
                    )
                })
                .collect())
        }
    }

    fn visit_mut<V: VisitorMut>(&mut self, visitor: &mut V) -> Result<(), V::Err> {
        match self {
            SourceUnit::Decl(decl) => visitor.visit_decl(decl),
            SourceUnit::Raw(block) => visitor.visit_stmts(block),
        }
    }

    /// Forward declare top-level declarations.
    #[instrument(skip(self, resolve))]
    pub fn forward_declare(&self, resolve: &mut Resolve) -> Result<(), ResolveError> {
        if let SourceUnit::Decl(decl) = self {
            resolve.declare(decl.clone())?;
        }
        Ok(())
    }

    /// Resolve all identifiers.
    #[instrument(skip(self, resolve))]
    pub fn resolve(&mut self, resolve: &mut Resolve) -> Result<(), ResolveError> {
        // Raw source units get their own subscope
        match self {
            SourceUnit::Decl(decl) => resolve.visit_decl(decl),
            SourceUnit::Raw(block) => resolve.with_subscope(|resolve| resolve.visit_stmts(block)),
        }
    }

    /// Type-check the resolved unit.
    #[instrument(skip(self, tycheck))]
    pub fn tycheck(&mut self, tycheck: &mut Tycheck) -> Result<(), TycheckError> {
        self.visit_mut(tycheck)
    }

    /// Check procedures for monotonicity
    #[instrument(skip(self))]
    pub fn check_monotonicity(&mut self) -> Result<(), MonotonicityError> {
        if let SourceUnit::Decl(decl_kind) = self {
            if let DeclKind::ProcDecl(decl_ref) = decl_kind {
                let mut visitor = MonotonicityVisitor::new(decl_ref.clone());
                visitor.visit_decl(decl_kind)?;
            }
        }
        Ok(())
    }

    /// Convert this source unit into a [`VerifyUnit`].
    /// Some declarations, such as domains or functions, do not generate any verify units.
    /// In these cases, `None` is returned.
    pub fn into_verify_unit(self) -> Option<VerifyUnit> {
        match self {
            SourceUnit::Decl(decl) => {
                match decl {
                    DeclKind::ProcDecl(proc_decl) => {
                        verify_proc(&proc_decl.borrow()).map(VerifyUnit)
                    }
                    DeclKind::DomainDecl(_domain_decl) => None, // TODO: check that the axioms are not contradictions
                    DeclKind::FuncDecl(_func_decl) => None,
                    _ => unreachable!(), // axioms and variable declarations are not allowed on the top level
                }
            }
            SourceUnit::Raw(block) => Some(VerifyUnit(block)),
        }
    }
}

impl SimplePretty for SourceUnit {
    fn pretty(&self) -> Doc {
        match self {
            SourceUnit::Raw(block) => block.pretty(),
            SourceUnit::Decl(decl) => decl.pretty(),
        }
    }
}

impl fmt::Display for SourceUnit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.pretty().render_fmt(80, f)
    }
}

/// A series of HeyVL statements to be verified.
#[derive(Debug)]

pub struct VerifyUnit(Block);

impl VerifyUnit {
    /// Desugar some statements, such as assignments with procedure calls.
    #[instrument(skip(self, tcx))]
    pub fn desugar(&mut self, tcx: &mut TyCtx) -> Result<(), ()> {
        let mut spec_call = SpecCall::new(tcx);
        spec_call.visit_stmts(&mut self.0)
    }

    /// Generate the verification conditions with post-expectation `∞`.
    /// The desugaring must have already taken place.
    #[instrument(skip(self, vcgen))]
    pub fn vcgen(&self, vcgen: &Vcgen) -> Result<Expr, ()> {
        let infinity = Shared::new(ExprData {
            kind: ExprKind::Lit(Spanned::with_dummy_span(LitKind::Infinity)),
            ty: Some(TyKind::EUReal),
            span: Span::dummy_span(),
        });
        Ok(vcgen.vcgen_stmts(&self.0, infinity))
    }
}

impl SimplePretty for VerifyUnit {
    fn pretty(&self) -> Doc {
        self.0.pretty()
    }
}

impl fmt::Display for VerifyUnit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.pretty().render_fmt(80, f)
    }
}
