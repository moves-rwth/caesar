//! The part of the driver that runs the frontend of Caesar: parsing, resolving,
//! type checking, and desugaring.

use std::{
    fmt::{self, Display, Formatter},
    fs::create_dir_all,
    ops::DerefMut,
    path::PathBuf,
};

use ariadne::ReportKind;
use regex::Regex;
use tracing::{info_span, instrument, trace};

use crate::{
    ast::{
        visit::VisitorMut, Block, DeclKind, Diagnostic, Direction, ExprBuilder, FileId, Files,
        SourceFilePath, Span, StoredFile, TyKind,
    },
    depgraph::DepGraph,
    driver::{
        commands::options::{
            DebugOptions, FunctionEncodingOption, InputOptions, ModelCheckingOptions,
        },
        error::CaesarError,
        item::{Item, SourceUnitName},
    },
    front::{
        parser::{self, ParseError},
        resolve::Resolve,
        tycheck::Tycheck,
    },
    intrinsic::{annotations::init_calculi, distributions::init_distributions, list::init_lists},
    mc,
    pretty::{Doc, SimplePretty},
    procs::monotonicity::MonotonicityVisitor,
    proof_rules::{
        calculus::{find_recursive_procs, CalculusVisitor},
        init_encodings, EncodingVisitor,
    },
    resource_limits::LimitsRef,
    servers::Server,
    slicing::init_slicing,
    tyctx::TyCtx,
    vc::explain::{explain_decl_vc, explain_raw_vc},
};

/// The first steps of running Caesar: parsing and type checking. This will
/// create a new [`TyCtx`] (using [`init_tcx`] with all default built-in
/// declarations) and will populate a new module with the parsed items.
///
/// If provided, the `--filter` option will be applied and the module's items
/// will be filtered based on it.
pub fn parse_and_tycheck(
    input_options: &InputOptions,
    debug_options: &DebugOptions,
    server: &mut dyn Server,
    user_files: &[FileId],
) -> Result<(Module, TyCtx), CaesarError> {
    let mut module = Module::new();
    for file_id in user_files {
        let file = server.get_file(*file_id).unwrap();
        let new_units = module
            .parse(&file, input_options.raw)
            .map_err(|parse_err| parse_err.diagnostic())?;

        // Print the result of parsing if requested
        if debug_options.print_parsed {
            println!("{}: Parsed file:\n", file.path);
            for unit in new_units {
                println!("{unit}");
            }
        }
    }

    let mut files = server.get_files_internal().lock().unwrap();
    let mut tcx = init_tcx(&mut files);
    drop(files);

    let mut resolve = Resolve::new(&mut tcx);
    module.resolve(&mut resolve)?;
    let mut tycheck = Tycheck::new(&mut tcx);
    module.tycheck(&mut tycheck, server)?;

    // filter if requested
    if let Some(filter) = &input_options.filter {
        module.filter(filter)?;
    };

    Ok((module, tcx))
}

/// A module is a list of [`SourceUnit`]s, usually coming from one input file.
#[derive(Debug)]
pub struct Module {
    pub items: Vec<Item<SourceUnit>>,
}

impl Module {
    pub fn new() -> Self {
        Module { items: vec![] }
    }

    /// Add new source units, and return a mutable reference to the added items.
    fn extend(
        &mut self,
        iter: impl IntoIterator<Item = Item<SourceUnit>>,
    ) -> &mut [Item<SourceUnit>] {
        let old_items_len = self.items.len();
        self.items.extend(iter);
        if self.items.len() > old_items_len {
            &mut self.items[old_items_len + 1..]
        } else {
            &mut []
        }
    }

    /// Parse a file and add the contents to this module.
    pub fn parse(
        &mut self,
        file: &StoredFile,
        raw: bool,
    ) -> Result<&mut [Item<SourceUnit>], ParseError> {
        if raw {
            let block = info_span!("parse", path=%file.path.to_string_lossy(), raw=raw)
                .in_scope(|| parser::parse_raw(file.id, &file.source))?;
            let name = SourceUnitName::new(&file.path, None, block.span);
            let item = Item::new(name, SourceUnit::Raw(block));
            Ok(self.extend(std::iter::once(item)))
        } else {
            let decls =
                info_span!("parse", path=%file.path.to_string_lossy(), raw=raw).in_scope(|| {
                    let decls = parser::parse_decls(file.id, &file.source)?;
                    trace!(n = decls.len(), "source units parsed");
                    Ok(decls)
                })?;
            let items = decls.into_iter().map(|decl| {
                Item::new(
                    SourceUnitName::new(
                        &file.path,
                        Some(decl.name().name.to_owned()),
                        decl.name().span,
                    ),
                    SourceUnit::Decl(decl),
                )
            });
            Ok(self.extend(items))
        }
    }

    /// Run forward resolution, then resolution on all source units.
    pub fn resolve(&mut self, resolve: &mut Resolve) -> Result<(), CaesarError> {
        for source_unit in &mut self.items {
            source_unit.enter_mut().forward_declare(resolve)?;
        }
        for source_unit in &mut self.items {
            source_unit.enter_mut().resolve(resolve)?;
        }
        Ok(())
    }

    /// Type check and monotonictiy check all source units.
    pub fn tycheck(
        &mut self,
        tycheck: &mut Tycheck,
        server: &mut dyn Server,
    ) -> Result<(), CaesarError> {
        for source_unit in &mut self.items {
            let mut source_unit = source_unit.enter_mut();
            source_unit.tycheck(tycheck)?;

            let monotonicity_res = source_unit.check_monotonicity();
            if let Err(err) = monotonicity_res {
                server.add_or_throw_diagnostic(err)?;
            }
        }
        Ok(())
    }

    /// Filter the set of source units based on a regular expression.
    ///
    /// Returns an error if the filter is not a valid regular expression.
    pub fn filter(&mut self, filter: &str) -> Result<(), CaesarError> {
        let filter = Regex::new(filter)
            .map_err(|err| CaesarError::UserError(format!("Invalid filter regex: {err}").into()))?;
        self.items
            .retain(|source_unit| filter.is_match(&source_unit.name().to_string()));
        Ok(())
    }

    pub fn register_with_server(&mut self, server: &mut dyn Server) -> Result<(), CaesarError> {
        for source_unit in &mut self.items {
            server.register_source_unit(source_unit)?;
        }
        Ok(())
    }

    /// Apply encodings to each source unit. Returns a reference to newly
    /// generated source units, if there were any.
    ///
    /// This might generate new source units, which will be added to this
    /// module and registered with the server.
    pub fn apply_encodings(
        &mut self,
        tcx: &mut TyCtx,
        server: &mut dyn Server,
    ) -> Result<&mut [Item<SourceUnit>], CaesarError> {
        let mut new_units = vec![];
        for source_unit in &mut self.items {
            let unit_extras = source_unit.enter_mut().apply_encodings(tcx)?;
            new_units.extend(unit_extras);
        }
        for source_unit in &mut new_units {
            server.register_source_unit(source_unit)?;
        }
        Ok(self.extend(new_units))
    }

    /// Explain high-level verification conditions.
    pub fn explain_high_level_vc(
        &mut self,
        tcx: &TyCtx,
        limits_ref: &LimitsRef,
        server: &mut dyn Server,
    ) -> Result<(), CaesarError> {
        for source_unit in &mut self.items {
            source_unit
                .enter_mut()
                .explain_vc(tcx, server, limits_ref)?;
        }
        Ok(())
    }

    /// Check the calculus rules: whether correct proof rules are compatible
    /// with the calculus annotation if provided.
    pub fn check_calculus_rules(&mut self, tcx: &mut TyCtx) -> Result<(), CaesarError> {
        // Find potentially 'recursive' (co)procs i.e. (co)procs that contain a proc call which might result in a recursive loop.
        let recursive_procs = find_recursive_procs(tcx, self);

        let mut visitor = CalculusVisitor::new(tcx, recursive_procs);
        for source_unit in &mut self.items {
            match source_unit.enter_mut().deref_mut() {
                SourceUnit::Decl(decl) => visitor.visit_decl(decl),
                SourceUnit::Raw(block) => visitor.visit_block(block),
            }
            .map_err(|ann_err| ann_err.diagnostic())?;
        }
        Ok(())
    }

    /// Generate a dependency graph for this module. This is used to determine
    /// which declarations are needed for the SMT translation later.
    ///
    /// TODO: This partially overlaps with the analysis done for checking
    /// calculus rules, and one should really refactor that :)
    pub fn generate_depgraph(
        &mut self,
        opt_options: &FunctionEncodingOption,
    ) -> Result<DepGraph, CaesarError> {
        let mut depgraph = DepGraph::new(opt_options.axiom_instantiation());
        for source_unit in &mut self.items {
            source_unit.enter_mut().populate_depgraph(&mut depgraph)?;
        }
        Ok(depgraph)
    }
}

impl Display for Module {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        writeln!(
            f,
            "{}",
            self.items
                .iter()
                .map(|item| item.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

/// Create a new [`TyCtx`] initialized with all of the built-ins that we usually
/// have. Will create new internal files for some stuff.
pub fn init_tcx(files: &mut Files) -> TyCtx {
    let mut tcx = TyCtx::new(TyKind::EUReal);
    init_calculi(files, &mut tcx);
    init_encodings(files, &mut tcx);
    init_distributions(files, &mut tcx);
    init_lists(files, &mut tcx);
    init_slicing(&mut tcx);
    tcx
}

/// A unit of source code that can be independently type-checked and verified.
/// It is either a declaration or just a series of raw HeyVL statements.
#[derive(Debug)]
pub enum SourceUnit {
    Decl(DeclKind),
    Raw(Block),
}

impl SourceUnit {
    /// Return a new generated source unit (with [`SourceFilePath::Generated`])
    /// for the given declaration and span in an [`Item`].
    pub fn from_generated_decl(decl: DeclKind, span: Span) -> Item<SourceUnit> {
        Item::new(
            SourceUnitName::new(
                &SourceFilePath::Generated,
                Some(decl.name().name.to_owned()),
                span,
            ),
            SourceUnit::Decl(decl),
        )
    }

    /// The span where to report diagnostics.
    pub fn diagnostic_span(&self) -> Span {
        match self {
            SourceUnit::Decl(decl) => decl.name().span,
            SourceUnit::Raw(block) => block.span,
        }
    }

    fn visit_mut<V: VisitorMut>(&mut self, visitor: &mut V) -> Result<(), V::Err> {
        match self {
            SourceUnit::Decl(decl) => visitor.visit_decl(decl),
            SourceUnit::Raw(block) => visitor.visit_block(block),
        }
    }

    /// Forward declare top-level declarations.
    #[instrument(skip(self, resolve))]
    fn forward_declare(&self, resolve: &mut Resolve) -> Result<(), CaesarError> {
        if let SourceUnit::Decl(decl) = self {
            resolve
                .declare(decl.clone())
                .map_err(|resolve_err| resolve_err.diagnostic())?;
        }
        Ok(())
    }

    /// Resolve all identifiers.
    #[instrument(skip(self, resolve))]
    fn resolve(&mut self, resolve: &mut Resolve) -> Result<(), CaesarError> {
        // Raw source units get their own subscope
        let res = match self {
            SourceUnit::Decl(decl) => resolve.visit_decl(decl),
            SourceUnit::Raw(block) => resolve.with_subscope(|resolve| resolve.visit_block(block)),
        };
        Ok(res.map_err(|resolve_err| resolve_err.diagnostic())?)
    }

    /// Type-check the resolved unit.
    #[instrument(skip(self, tycheck))]
    fn tycheck(&mut self, tycheck: &mut Tycheck) -> Result<(), CaesarError> {
        Ok(self
            .visit_mut(tycheck)
            .map_err(|ty_err| ty_err.diagnostic())?)
    }

    /// Check procedures for monotonicity.
    #[instrument(skip(self))]
    fn check_monotonicity(&mut self) -> Result<(), Diagnostic> {
        if let SourceUnit::Decl(decl_kind) = self {
            if let DeclKind::ProcDecl(decl_ref) = decl_kind {
                let mut visitor = MonotonicityVisitor::new(decl_ref.clone());
                visitor
                    .visit_decl(decl_kind)
                    .map_err(|err| err.diagnostic())?;
            }
        }
        Ok(())
    }

    /// Explain high-level verification conditions.
    pub fn explain_vc(
        &self,
        tcx: &TyCtx,
        server: &mut dyn Server,
        limits_ref: &LimitsRef,
    ) -> Result<(), CaesarError> {
        let explanation = match self {
            SourceUnit::Decl(decl) => explain_decl_vc(tcx, decl, limits_ref),
            SourceUnit::Raw(block) => {
                let builder = ExprBuilder::new(Span::dummy_span());
                let post = builder.top_lit(tcx.spec_ty());
                explain_raw_vc(tcx, block, post, Direction::Down, limits_ref).map(Some)
            }
        };
        match explanation {
            Ok(Some(explanation)) => server.add_vc_explanation(explanation),
            Ok(None) => Ok(()),
            Err(CaesarError::Diagnostic(diagnostic)) => {
                server.add_diagnostic(diagnostic.with_kind(ReportKind::Warning))
            }
            Err(err) => Err(err),
        }
    }

    /// Encode the source unit as a JANI file if requested.
    pub fn write_to_jani_if_requested(
        &self,
        options: &ModelCheckingOptions,
        tcx: &TyCtx,
    ) -> Result<Option<PathBuf>, CaesarError> {
        if let Some(jani_dir) = &options.jani_dir {
            match self {
                SourceUnit::Decl(decl) => {
                    if let DeclKind::ProcDecl(decl_ref) = decl {
                        let jani_model = mc::proc_to_model(options, tcx, &decl_ref.borrow())
                            .map_err(|err| CaesarError::Diagnostic(err.diagnostic()))?;
                        let file_path = jani_dir.join(format!("{}.jani", decl.name()));
                        create_dir_all(file_path.parent().unwrap())?;
                        std::fs::write(&file_path, jani::to_string(&jani_model))?;
                        Ok(Some(file_path))
                    } else {
                        Ok(None)
                    }
                }
                SourceUnit::Raw(_) => panic!("raw code not supported with --jani-dir"),
            }
        } else {
            Ok(None)
        }
    }

    /// Apply encodings given by annotations. This might generate new source
    /// units for side conditions.
    pub fn apply_encodings(
        &mut self,
        tcx: &mut TyCtx,
    ) -> Result<Vec<Item<SourceUnit>>, CaesarError> {
        let mut encoding_visitor = EncodingVisitor::new(tcx);
        match self {
            SourceUnit::Decl(decl) => encoding_visitor.visit_decl(decl),
            SourceUnit::Raw(block) => encoding_visitor.visit_block(block),
        }
        .map_err(|ann_err| ann_err.diagnostic())?;
        Ok(encoding_visitor.finish())
    }

    /// If this is a declaration, add the dependencies to the [DepGraph].
    pub fn populate_depgraph(&mut self, depgraph: &mut DepGraph) -> Result<(), CaesarError> {
        assert!(depgraph.current_deps.is_empty());
        match self {
            SourceUnit::Decl(decl) => depgraph
                .visit_decl(decl)
                .map_err(|e| CaesarError::Diagnostic(e.diagnostic())),
            SourceUnit::Raw(_block) => Ok(()),
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
