//! This module glues all components of Caesar together.

use std::{
    fmt,
    fs::{create_dir_all, File},
    io::Write,
    ops::{Deref, DerefMut},
    path::PathBuf,
};

use crate::{
    ast::{
        stats::StatsVisitor, visit::VisitorMut, BinOpKind, Block, DeclKind, DeclKindName,
        Diagnostic, Direction, Expr, ExprBuilder, Label, SourceFilePath, Span, StoredFile, TyKind,
        UnOpKind, VarKind,
    },
    front::{
        parser::{self, ParseError},
        resolve::Resolve,
        tycheck::Tycheck,
    },
    mc::{self, JaniOptions},
    opt::{
        boolify::Boolify, egraph, qelim::Qelim, relational::Relational, unfolder::Unfolder,
        RemoveParens,
    },
    pretty::{Doc, SimplePretty},
    procs::{
        monotonicity::MonotonicityVisitor,
        proc_verify::{to_direction_lower_bounds, verify_proc},
        SpecCall,
    },
    proof_rules::EncodingVisitor,
    resource_limits::{LimitError, LimitsRef},
    servers::Server,
    slicing::{
        model::SliceModel,
        selection::SliceSelection,
        solver::{SliceSolveOptions, SliceSolver},
        transform::{SliceStmts, StmtSliceVisitor},
    },
    smt::{
        pretty_model::{
            pretty_model, pretty_slice, pretty_unaccessed, pretty_var_value, pretty_vc_value,
        },
        translate_exprs::TranslateExprs,
        SmtCtx,
    },
    tyctx::TyCtx,
    vc::{
        explain::{explain_decl_vc, explain_raw_vc},
        subst::apply_subst,
        vcgen::Vcgen,
    },
    version::write_detailed_version_info,
    Options, SliceOptions, SliceVerifyMethod, VerifyError,
};

use ariadne::ReportKind;
use itertools::Itertools;
use z3::{
    ast::{Ast, Bool},
    Config, Context,
};
use z3rro::{
    prover::{ProveResult, Prover},
    smtlib::Smtlib,
    util::PrefixWriter,
};

use tracing::{info_span, instrument, trace};

/// Human-readable name for a source unit. Used for debugging and error messages.
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct SourceUnitName {
    short_path: String,
    decl_name: Option<String>,
}

impl SourceUnitName {
    fn new_raw(source_file_path: &SourceFilePath) -> SourceUnitName {
        let short_path = source_file_path
            .relative_to_cwd()
            .unwrap()
            .to_string_lossy()
            .to_string();
        SourceUnitName {
            short_path,
            decl_name: None,
        }
    }

    fn new_decl(source_file_path: &SourceFilePath, decl: &DeclKind) -> SourceUnitName {
        let mut res = Self::new_raw(source_file_path);
        res.decl_name = Some(decl.name().name.to_string());
        res
    }

    /// Create a filne name for this source unit with the given file extension.
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
        PathBuf::from(file_name)
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
            SourceUnit::Raw(block) => visitor.visit_block(block),
        }
    }

    /// Forward declare top-level declarations.
    #[instrument(skip(self, resolve))]
    pub fn forward_declare(&self, resolve: &mut Resolve) -> Result<(), VerifyError> {
        if let SourceUnit::Decl(decl) = self {
            resolve
                .declare(decl.clone())
                .map_err(|resolve_err| resolve_err.diagnostic())?;
        }
        Ok(())
    }

    /// Resolve all identifiers.
    #[instrument(skip(self, resolve))]
    pub fn resolve(&mut self, resolve: &mut Resolve) -> Result<(), VerifyError> {
        // Raw source units get their own subscope
        let res = match self {
            SourceUnit::Decl(decl) => resolve.visit_decl(decl),
            SourceUnit::Raw(block) => resolve.with_subscope(|resolve| resolve.visit_block(block)),
        };
        Ok(res.map_err(|resolve_err| resolve_err.diagnostic())?)
    }

    /// Type-check the resolved unit.
    #[instrument(skip(self, tycheck))]
    pub fn tycheck(&mut self, tycheck: &mut Tycheck) -> Result<(), VerifyError> {
        Ok(self
            .visit_mut(tycheck)
            .map_err(|ty_err| ty_err.diagnostic())?)
    }

    /// Check procedures for monotonicity
    #[instrument(skip(self))]
    pub fn check_monotonicity(&mut self) -> Result<(), Diagnostic> {
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
    pub fn explain_vc(&self, tcx: &TyCtx, server: &mut dyn Server) -> Result<(), VerifyError> {
        let explanation = match self {
            SourceUnit::Decl(decl) => explain_decl_vc(tcx, decl),
            SourceUnit::Raw(block) => {
                let builder = ExprBuilder::new(Span::dummy_span());
                let post = builder.top_lit(tcx.spec_ty());
                explain_raw_vc(tcx, block, post).map(Some)
            }
        };
        match explanation {
            Ok(Some(explanation)) => server.add_vc_explanation(explanation),
            Ok(None) => Ok(()),
            Err(diagnostic) => server.add_diagnostic(diagnostic.with_kind(ReportKind::Warning)),
        }
    }

    /// Encode the source unit as a JANI file if requested.
    pub fn write_to_jani_if_requested(
        &self,
        options: &Options,
        tcx: &TyCtx,
    ) -> Result<(), VerifyError> {
        if let Some(jani_dir) = &options.jani_dir {
            match self {
                SourceUnit::Decl(decl) => {
                    if let DeclKind::ProcDecl(decl_ref) = decl {
                        let jani_options = JaniOptions {
                            skip_quant_pre: options.jani_skip_quant_pre,
                        };
                        let jani_model = mc::proc_to_model(&jani_options, tcx, &decl_ref.borrow())
                            .map_err(|err| VerifyError::Diagnostic(err.diagnostic()))?;
                        let file_path = jani_dir.join(format!("{}.jani", decl.name()));
                        create_dir_all(file_path.parent().unwrap())?;
                        std::fs::write(file_path, jani::to_string(&jani_model))?;
                    }
                }
                SourceUnit::Raw(_) => panic!("raw code not supported with --jani-dir"),
            }
        }
        Ok(())
    }

    /// Apply encodings from annotations.
    #[instrument(skip(self, tcx, source_units_buf))]
    pub fn apply_encodings(
        &mut self,
        tcx: &mut TyCtx,
        source_units_buf: &mut Vec<Item<SourceUnit>>,
    ) -> Result<(), VerifyError> {
        let mut encoding_visitor = EncodingVisitor::new(tcx, source_units_buf);
        let res = match self {
            SourceUnit::Decl(decl) => encoding_visitor.visit_decl(decl),
            SourceUnit::Raw(block) => encoding_visitor.visit_block(block),
        };
        Ok(res.map_err(|ann_err| ann_err.diagnostic())?)
    }

    /// Convert this source unit into a [`VerifyUnit`].
    /// Some declarations, such as domains or functions, do not generate any verify units.
    /// In these cases, `None` is returned.
    pub fn into_verify_unit(self) -> Option<VerifyUnit> {
        match self {
            SourceUnit::Decl(decl) => {
                match decl {
                    DeclKind::ProcDecl(proc_decl) => verify_proc(&proc_decl.borrow()),
                    DeclKind::DomainDecl(_domain_decl) => None, // TODO: check that the axioms are not contradictions
                    DeclKind::FuncDecl(_func_decl) => None,
                    _ => unreachable!(), // axioms and variable declarations are not allowed on the top level
                }
            }
            SourceUnit::Raw(block) => Some(VerifyUnit {
                span: block.span,
                direction: Direction::Down,
                block,
            }),
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

/// A block of HeyVL statements to be verified with a certain [`Direction`].
#[derive(Debug, Clone)]
pub struct VerifyUnit {
    pub span: Span,
    pub direction: Direction,
    pub block: Block,
}

impl VerifyUnit {
    /// Desugar assignments with procedure calls.
    #[instrument(skip(self, tcx))]
    pub fn desugar_spec_calls(&mut self, tcx: &mut TyCtx, name: String) -> Result<(), VerifyError> {
        // Pass the context direction to the SpecCall so that it can check direction compatibility with called procedures
        let mut spec_call = SpecCall::new(tcx, self.direction, name);
        let res = spec_call.visit_block(&mut self.block);

        Ok(res.map_err(|ann_err| ann_err.diagnostic())?)
    }

    /// Prepare the code for slicing.
    #[instrument(skip_all)]
    pub fn prepare_slicing(
        &mut self,
        options: &SliceOptions,
        tcx: &mut TyCtx,
        server: &mut dyn Server,
    ) -> Result<SliceStmts, VerifyError> {
        let mut selection = SliceSelection::default();
        if !options.no_slice_error {
            selection |= SliceSelection::FAILURE_SELECTION;
        }
        selection.slice_ticks = options.slice_ticks;
        selection.slice_sampling = options.slice_sampling;
        if options.slice_verify {
            selection |= SliceSelection::VERIFIED_SELECTION;
        }
        let mut stmt_slicer = StmtSliceVisitor::new(tcx, self.direction, selection);
        let res = stmt_slicer.visit_block(&mut self.block);
        if let Err(err) = res {
            server.add_or_throw_diagnostic(err.to_diagnostic())?;
        }
        Ok(stmt_slicer.finish())
    }

    /// Generate the verification conditions with post-expectation `∞` or `0`
    /// depending on the direction (down or up, respectively).
    ///
    /// The desugaring must have already taken place.
    #[instrument(skip(self, vcgen))]
    pub fn vcgen(&self, vcgen: &mut Vcgen) -> Result<QuantVcUnit, VerifyError> {
        let terminal = top_lit_in_lattice(self.direction, &TyKind::EUReal);
        Ok(QuantVcUnit {
            direction: self.direction,
            expr: vcgen.vcgen_block(&self.block, terminal)?,
        })
    }
}

fn top_lit_in_lattice(dir: Direction, ty: &TyKind) -> Expr {
    let builder = ExprBuilder::new(Span::dummy_span());
    match dir {
        Direction::Down => builder.top_lit(ty),
        Direction::Up => {
            // this should just be builder.bot_lit(ty), but unfortunately this
            // introduces some regressions and Z3 suddenly won't terminate on
            // some examples.
            //
            // TODO: change this back and debug why it couldn't be just bot.
            builder.unary(UnOpKind::Non, Some(TyKind::EUReal), builder.top_lit(ty))
        }
    }
}

impl SimplePretty for VerifyUnit {
    fn pretty(&self) -> Doc {
        let lower_bounds = to_direction_lower_bounds(self.clone());
        assert_eq!(lower_bounds.direction, Direction::Down);
        lower_bounds.block.pretty()
    }
}

impl fmt::Display for VerifyUnit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.pretty().render_fmt(80, f)
    }
}

/// Quantitative verification conditions that are to be checked.
pub struct QuantVcUnit {
    pub direction: Direction,
    pub expr: Expr,
}

impl QuantVcUnit {
    /// Apply unfolding to this verification conditon. If enabled, do lazy
    /// unfolding. Otherwise, eager.
    pub fn unfold(
        &mut self,
        options: &Options,
        limits_ref: &LimitsRef,
        tcx: &TyCtx,
    ) -> Result<(), LimitError> {
        let span = info_span!("unfolding");
        let _entered = span.enter();
        if !options.strict {
            let ctx = Context::new(&Config::default());
            let smt_ctx = SmtCtx::new(&ctx, tcx);
            let mut unfolder = Unfolder::new(limits_ref.clone(), &smt_ctx);
            unfolder.visit_expr(&mut self.expr)
        } else {
            apply_subst(tcx, &mut self.expr);
            Ok(())
        }
    }

    /// Apply quantitative quantifier elimination.
    pub fn qelim(&mut self, tcx: &mut TyCtx) {
        let mut qelim = Qelim::new(tcx);
        qelim.qelim(self);
        // Apply/eliminate substitutions again
        apply_subst(tcx, &mut self.expr);
    }

    /// Trace some statistics about this vc expression.
    pub fn trace_expr_stats(&mut self) {
        let mut stats = StatsVisitor::default();
        stats.visit_expr(&mut self.expr).unwrap();
        let stats = stats.stats;
        tracing::info!(
            num_exprs = stats.num_exprs,
            num_quants = stats.num_quants,
            depths = %stats.depths_summary(),
            "Verification condition stats"
        );
        if stats.num_quants > 0 {
            tracing::warn!(
                num_quants=stats.num_quants, "Quantifiers are present in the generated verification conditions. It is possible that quantifier elimination failed. If Z3 can't decide the problem, this may be the reason."
            );
        }
    }

    /// Convert his verification condition into a Boolean query of the form `top
    /// == expr`.
    pub fn into_bool_vc(self) -> BoolVcUnit {
        let builder = ExprBuilder::new(Span::dummy_span());
        let terminal = builder.top_lit(self.expr.ty.as_ref().unwrap());
        let mut expr = self.expr.clone();

        // Instead of comparing the negated expr to infinity, we should just
        // compare expr to zero for upper bounds. Unfortunately this introduces
        // regressions that I don't know how to debug right now.
        //
        // TODO: figure out what's happening
        if self.direction == Direction::Up {
            expr = builder.unary(UnOpKind::Not, Some(expr.ty.clone().unwrap()), expr);
        }
        let res = builder.binary(BinOpKind::Eq, Some(TyKind::Bool), terminal, expr);
        BoolVcUnit {
            quant_vc: self,
            vc: res,
        }
    }
}

/// The next step is a Boolean verification condition - it represents that the
/// quantative verification conditions are true/false depending on the direction.
pub struct BoolVcUnit {
    quant_vc: QuantVcUnit,
    vc: Expr,
}

impl BoolVcUnit {
    /// E-Graph simplifications. They're not being used at the moment and are
    /// very limited.
    pub fn egraph_simplify(&self) {
        egraph::simplify(&self.vc);
    }

    /// Removing parentheses before optimizations.
    pub fn remove_parens(&mut self) {
        RemoveParens.visit_expr(&mut self.vc).unwrap();
    }

    /// Apply the "boolify" optimization.
    pub fn opt_boolify(&mut self) {
        let span = info_span!("boolify");
        let _entered = span.enter();
        (Boolify {}).visit_expr(&mut self.vc).unwrap();
    }

    /// Apply the "relational" optimization.
    pub fn opt_relational(&mut self) {
        let span = info_span!("relationalize");
        let _entered = span.enter();
        (Relational {}).visit_expr(&mut self.vc).unwrap();
    }

    /// Print the theorem to prove.
    pub fn print_theorem(&self, name: &SourceUnitName) {
        println!("{}: Theorem to prove:\n{}\n", name, &self.vc);
    }

    /// Translate to SMT.
    pub fn into_smt_vc<'smt, 'ctx>(
        self,
        translate: &mut TranslateExprs<'smt, 'ctx>,
    ) -> SmtVcUnit<'ctx> {
        let span = info_span!("translation to Z3");
        let _entered = span.enter();
        SmtVcUnit {
            quant_vc: self.quant_vc,
            vc: translate.t_bool(&self.vc),
        }
    }
}

/// The verification condition validitiy formula as a Z3 formula.
pub struct SmtVcUnit<'ctx> {
    quant_vc: QuantVcUnit,
    vc: Bool<'ctx>,
}

impl<'ctx> SmtVcUnit<'ctx> {
    /// Simplify the SMT formula using Z3's simplifier.
    pub fn simplify(&mut self) {
        let span = info_span!("simplify query");
        let _entered = span.enter();
        self.vc = self.vc.simplify();
    }

    /// Run the solver(s) on this SMT formula.
    pub fn run_solver<'smt>(
        self,
        options: &Options,
        limits_ref: &LimitsRef,
        ctx: &'ctx Context,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        slice_vars: &SliceStmts,
    ) -> Result<SmtVcCheckResult<'ctx>, VerifyError> {
        let span = info_span!("SAT check");
        let _entered = span.enter();

        let prover = mk_valid_query_prover(limits_ref, ctx, translate, &self.vc);
        let smtlib = get_smtlib(options, &prover);

        let mut slice_solver = SliceSolver::new(slice_vars.clone(), translate, prover);
        let failing_slice_options = SliceSolveOptions {
            globally_optimal: true,
            continue_on_unknown: false,
        };
        let (result, mut slice_model) =
            slice_solver.slice_while_failing(&failing_slice_options, limits_ref)?;
        if matches!(result, ProveResult::Proof) && options.slice_options.slice_verify {
            match options.slice_options.slice_verify_via {
                SliceVerifyMethod::UnsatCore => {
                    slice_model = slice_solver.verified_slice_unsat_core(limits_ref)?;
                }
                SliceVerifyMethod::MinimalUnsatSubset => {
                    let slice_options = SliceSolveOptions {
                        globally_optimal: false,
                        continue_on_unknown: true,
                    };
                    slice_model = slice_solver.verified_slice_mus(&slice_options, limits_ref)?;
                }
                SliceVerifyMethod::SmallestUnsatSubset => {
                    let slice_options = SliceSolveOptions {
                        globally_optimal: true,
                        continue_on_unknown: true,
                    };
                    slice_model = slice_solver.verified_slice_mus(&slice_options, limits_ref)?;
                }
                SliceVerifyMethod::ExistsForall => {
                    let slice_options = SliceSolveOptions {
                        globally_optimal: false,
                        continue_on_unknown: false,
                    };
                    if translate.ctx.uninterpreteds().is_empty() {
                        slice_model =
                            slice_solver.exists_verified_slice(&slice_options, limits_ref)?;
                    } else {
                        tracing::warn!("There are uninterpreted sorts, functions, or axioms present. Slicing for correctness is disabled because it does not support them.");
                    }
                }
            }
        }

        Ok(SmtVcCheckResult {
            prove_result: result,
            quant_vc: self.quant_vc,
            slice_model,
            smtlib,
        })
    }
}

pub fn mk_z3_ctx(options: &Options) -> Context {
    let mut config = Config::default();
    if options.z3_trace {
        config.set_bool_param_value("trace", true);
        config.set_bool_param_value("proof", true);
    }
    Context::new(&config)
}

fn mk_valid_query_prover<'smt, 'ctx>(
    limits_ref: &LimitsRef,
    ctx: &'ctx Context,
    smt_translate: &TranslateExprs<'smt, 'ctx>,
    valid_query: &Bool<'ctx>,
) -> Prover<'ctx> {
    // create the prover and set the params
    let mut prover = Prover::new(ctx);
    if let Some(remaining) = limits_ref.time_left() {
        prover.set_timeout(remaining);
    }

    // add assumptions (from axioms and locals) to the prover
    smt_translate
        .ctx
        .uninterpreteds()
        .add_axioms_to_prover(&mut prover);
    smt_translate
        .local_scope()
        .add_assumptions_to_prover(&mut prover);
    // add the provable: is this Boolean true?
    prover.add_provable(valid_query);
    prover
}

fn get_smtlib(options: &Options, prover: &Prover) -> Option<Smtlib> {
    if options.print_smt || options.smt_dir.is_some() {
        let mut smtlib = prover.get_smtlib();
        if !options.no_pretty_smtlib {
            let res = smtlib.pretty_raco_read();
            if let Err(err) = res {
                tracing::warn!("error pretty-printing SMT-LIB: {}", err);
            }
        }
        Some(smtlib)
    } else {
        None
    }
}

/// The result of an SMT solver call for a [`SmtVcUnit`].
pub struct SmtVcCheckResult<'ctx> {
    pub prove_result: ProveResult<'ctx>,
    slice_model: Option<SliceModel>,
    quant_vc: QuantVcUnit,
    smtlib: Option<Smtlib>,
}

impl<'ctx> SmtVcCheckResult<'ctx> {
    /// Print the result of the query to stdout.
    pub fn print_prove_result<'smt>(
        &mut self,
        server: &mut dyn Server,
        translate: &mut TranslateExprs<'smt, 'ctx>,
        name: &SourceUnitName,
    ) {
        let files = server.get_files_internal().lock().unwrap();
        match &mut self.prove_result {
            ProveResult::Proof => {
                println!("{}: Verified.", name);
                if let Some(slice_model) = &self.slice_model {
                    let mut w = Vec::new();
                    let doc = pretty_slice(&files, slice_model);
                    if let Some(doc) = doc {
                        let doc = doc.nest(4).append(Doc::line_());
                        doc.render(120, &mut w).unwrap();
                        println!("    {}", String::from_utf8(w).unwrap());
                    }
                }
            }
            ProveResult::Counterexample(model) => {
                println!("{}: Counter-example to verification found!", name);
                let mut w = Vec::new();
                let doc = pretty_model(
                    &files,
                    self.slice_model.as_ref().unwrap(),
                    &self.quant_vc,
                    translate,
                    model,
                );
                doc.nest(4).render(120, &mut w).unwrap();
                println!("    {}", String::from_utf8(w).unwrap());
            }
            ProveResult::Unknown(reason) => {
                println!("{}: Unknown result! (reason: {})", name, reason)
            }
        }
    }

    /// Emit diagnostics for this check result.
    ///
    /// The provided span is for the location to attach the counterexample to.
    pub fn emit_diagnostics<'smt>(
        &mut self,
        span: Span,
        server: &mut dyn Server,
        translate: &mut TranslateExprs<'smt, 'ctx>,
    ) -> Result<(), VerifyError> {
        // TODO: batch all those messages

        if let Some(slice_model) = &self.slice_model {
            for diagnostic in slice_model.to_diagnostics() {
                server.add_diagnostic(diagnostic)?;
            }
        }

        match &mut self.prove_result {
            ProveResult::Proof => {}
            ProveResult::Counterexample(model) => {
                let mut labels = vec![];
                let files = server.get_files_internal().lock().unwrap();
                // Print the values of the global variables in the model.
                let global_decls = translate
                    .local_idents()
                    .sorted_by_key(|ident| ident.span.start)
                    .map(|ident| translate.ctx.tcx().get(ident).unwrap())
                    .filter(|decl| decl.kind_name() != DeclKindName::Var(VarKind::Slice))
                    .collect_vec();
                for decl_kind in global_decls {
                    if let DeclKind::VarDecl(decl_ref) = &*decl_kind {
                        let var_decl = decl_ref.borrow();
                        let ident = var_decl.name;
                        let value = pretty_var_value(translate, ident, model);
                        labels.push(Label::new(ident.span).with_message(format!(
                            "in the cex, {} variable {} is {}",
                            var_decl.kind,
                            var_decl.original_name(),
                            value
                        )));
                    }
                }
                drop(files);

                let mut res: Vec<Doc> = vec![Doc::text("Counter-example to verification found!")];

                // Print the unaccessed definitions.
                if let Some(unaccessed) = pretty_unaccessed(model) {
                    res.push(unaccessed);
                }

                res.push(pretty_vc_value(
                    &self.quant_vc,
                    translate,
                    model,
                    self.slice_model.as_ref().unwrap(),
                ));

                let mut w = Vec::new();
                Doc::intersperse(res, Doc::line_().append(Doc::line_()))
                    .render(120, &mut w)
                    .unwrap();
                let text = String::from_utf8(w).unwrap();

                let diagnostic = Diagnostic::new(ReportKind::Error, span)
                    .with_message(text)
                    .with_labels(labels);
                server.add_diagnostic(diagnostic)?;
            }
            ProveResult::Unknown(reason) => {
                server.add_diagnostic(
                    Diagnostic::new(ReportKind::Error, span)
                        .with_message(format!("Unknown result: {}", reason)),
                )?;
            }
        }

        Ok(())
    }

    /// Write the SMT-LIB dump to a file if requested.
    pub fn write_smtlib(
        &self,
        options: &Options,
        name: &SourceUnitName,
    ) -> Result<(), VerifyError> {
        if options.print_smt || options.smt_dir.is_some() {
            let mut smtlib = self.smtlib.clone().unwrap();
            smtlib.add_check_sat();
            smtlib.add_details_query(&self.prove_result);
            let smtlib = smtlib.into_string();
            if options.print_smt {
                println!("\n; --- Solver SMT-LIB ---\n{}\n", smtlib);
            }
            if let Some(smt_dir) = &options.smt_dir {
                let file_path = smt_dir.join(name.to_file_name("smt2"));
                create_dir_all(file_path.parent().unwrap())?;
                let mut file = File::create(&file_path)?;
                let mut comment_writer = PrefixWriter::new("; ".as_bytes(), &mut file);
                write_detailed_version_info(&mut comment_writer)?;
                writeln!(comment_writer, "Source unit: {}", name)?;
                writeln!(comment_writer, "Prove result: {}", self.prove_result)?;
                file.write_all(smtlib.as_bytes())?;
                tracing::info!(?file_path, "SMT-LIB query written to file");
            }
        }
        Ok(())
    }
}
