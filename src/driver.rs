//! This module glues all components of Caesar together.

use std::{
    fmt,
    fs::{create_dir_all, File},
    io::{self, Write},
    ops::{Deref, DerefMut},
};

use crate::{
    ast::{
        stats::StatsVisitor, visit::VisitorMut, BinOpKind, Block, DeclKind, Expr, ExprData,
        ExprKind, LitKind, Shared, SourceFilePath, Span, Spanned, StoredFile, TyKind,
    },
    front::{
        parser::{self, ParseError},
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::AnnotationError,
    opt::{
        boolify::Boolify, egraph, qelim::Qelim, relational::Relational, unfolder::Unfolder,
        RemoveParens,
    },
    pretty::{Doc, SimplePretty},
    procs::{
        monotonicity::{MonotonicityError, MonotonicityVisitor},
        verify_proc, SpecCall,
    },
    proof_rules::EncCall,
    smt::{translate_exprs::TranslateExprs, SmtCtx},
    tyctx::TyCtx,
    vc::{subst::apply_subst, vcgen::Vcgen},
    version::write_detailed_version_info,
    Options, VerifyError,
};

use z3::{
    ast::{Ast, Bool},
    Config, Context,
};
use z3rro::{
    pretty::{get_pretty_solver_smtlib, get_solver_smtlib},
    prover::{ProveResult, Prover},
    util::{PrefixWriter, ReasonUnknown},
};

use tracing::{info, info_span, instrument, trace};

/// Human-readable name for a source unit. Used for debugging and error messages.
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
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

    pub fn verify(
        &mut self,
        name: &SourceUnitName,
        tcx: &mut TyCtx,
        options: &Options,
    ) -> Result<bool, VerifyError> {
        // 4. Desugaring: transforming spec calls to procs
        self.desugar(tcx).unwrap();

        // print HeyVL core after desugaring if requested
        if options.print_core {
            println!("{}: HeyVL core query:\n{}\n", name, *self);
        }

        // 5. Generating verification conditions
        let vcgen = Vcgen::new(tcx, options.print_label_vc);
        let mut vc_expr = self.vcgen(&vcgen).unwrap();

        // 6. Unfolding
        unfold_expr(options, tcx, &mut vc_expr);

        // 7. Quantifier elimination
        if !options.no_qelim {
            apply_qelim(tcx, &mut vc_expr);
        }

        // In-between, gather some stats about the vc expression
        trace_expr_stats(&mut vc_expr);

        // 8. Create the "vc[S] is valid" expression
        let mut vc_expr_eq_infinity = expr_eq_infty(vc_expr);

        if options.egraph {
            egraph::simplify(&vc_expr_eq_infinity);
        }

        // 9. Optimizations
        if !options.no_boolify || options.opt_rel {
            RemoveParens.visit_expr(&mut vc_expr_eq_infinity).unwrap();
        }
        if !options.no_boolify {
            apply_boolify_opt(&mut vc_expr_eq_infinity);
        }
        if options.opt_rel {
            apply_relational_opt(&mut vc_expr_eq_infinity);
        }

        // print theorem to prove if requested
        if options.print_theorem {
            println!("{}: Theorem to prove:\n{}\n", name, &vc_expr_eq_infinity);
        }

        // 10. Translate to Z3
        let translate_span = info_span!("translation to Z3");
        let translate_entered = translate_span.enter();

        let ctx = mk_z3_ctx(options);
        let smt_ctx = SmtCtx::new(&ctx, tcx);
        let mut smt_translate = TranslateExprs::new(&smt_ctx);
        let mut valid_query = smt_translate.t_bool(&vc_expr_eq_infinity);

        drop(translate_entered);
        drop(translate_span);

        if !options.no_simplify {
            info_span!("simplify query").in_scope(|| valid_query = valid_query.simplify());
        }

        // 11. Create Z3 solver with axioms, solve
        let sat_span = info_span!("SAT check");
        let sat_entered = sat_span.enter();

        let mut prover = mk_valid_query_prover(&ctx, &smt_translate, &valid_query);
        let smtlib = get_smtlib(options, &prover);

        let result = prover.check_proof();

        drop(sat_entered);
        drop(sat_span);

        if !options.language_server {
            // Now let's examine the result.
            print_prove_result(result, name, &prover);
        }

        write_smtlib(options, smtlib, name, result).unwrap();

        if options.z3_trace {
            info!("Z3 tracing output will be written to `z3.log`.");
        }

        // If the solver was interrupted from the keyboard, exit now.
        if prover.get_reason_unknown() == Some(ReasonUnknown::Interrupted) {
            return Err(VerifyError::Interrupted);
        }

        Ok(result == ProveResult::Proof)
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

fn apply_qelim(tcx: &mut TyCtx, vc_expr: &mut Expr) {
    let mut qelim = Qelim::new(tcx);
    qelim.qelim_inf(vc_expr);
    // Apply/eliminate substitutions again
    apply_subst(tcx, vc_expr);
}

fn apply_relational_opt(vc_expr_eq_infinity: &mut Expr) {
    let span = info_span!("relationalize");
    let _entered = span.enter();
    (Relational {}).visit_expr(vc_expr_eq_infinity).unwrap();
}

fn apply_boolify_opt(vc_expr_eq_infinity: &mut Expr) {
    let span = info_span!("boolify");
    let _entered = span.enter();
    (Boolify {}).visit_expr(vc_expr_eq_infinity).unwrap();
}

fn unfold_expr(options: &Options, tcx: &TyCtx, vc_expr: &mut Expr) {
    let span = info_span!("unfolding");
    let _entered = span.enter();
    if !options.strict {
        let ctx = Context::new(&Config::default());
        let smt_ctx = SmtCtx::new(&ctx, tcx);
        let mut unfolder = Unfolder::new(&smt_ctx);
        unfolder.visit_expr(vc_expr).unwrap();
    } else {
        apply_subst(tcx, vc_expr);
    }
}

fn mk_z3_ctx(options: &Options) -> Context {
    let mut config = Config::default();
    if options.z3_trace {
        config.set_bool_param_value("trace", true);
        config.set_bool_param_value("proof", true);
    }
    Context::new(&config)
}

fn mk_valid_query_prover<'smt, 'ctx>(
    ctx: &'ctx Context,
    smt_translate: &TranslateExprs<'smt, 'ctx>,
    valid_query: &Bool<'ctx>,
) -> Prover<'ctx> {
    // create the prover and set the params
    let mut prover = Prover::new(ctx);
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

fn trace_expr_stats(vc_expr: &mut Expr) {
    let mut stats = StatsVisitor::default();
    stats.visit_expr(vc_expr).unwrap();
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

fn expr_eq_infty(vc_expr: Expr) -> Expr {
    let infinity = Shared::new(ExprData {
        kind: ExprKind::Lit(Spanned::with_dummy_span(LitKind::Infinity)),
        ty: Some(TyKind::EUReal),
        span: Span::dummy_span(),
    });
    Shared::new(ExprData {
        kind: ExprKind::Binary(Spanned::with_dummy_span(BinOpKind::Eq), infinity, vc_expr),
        ty: Some(TyKind::Bool),
        span: Span::dummy_span(),
    })
}

fn print_prove_result(result: ProveResult, name: &SourceUnitName, prover: &Prover) {
    match result {
        ProveResult::Proof => println!("{}: Verified.", name),
        ProveResult::Counterexample => {
            println!("{}: Counter-example to verification found!", name);
            if let Some(model) = prover.get_model() {
                println!("{:?}", model);
            };
        }
        ProveResult::Unknown => {
            if let Some(reason) = prover.get_reason_unknown() {
                println!("{}: Unknown result! (reason: {})", name, reason)
            } else {
                println!("{}: Unknown result!", name)
            }
        }
    }
}

fn get_smtlib(options: &Options, prover: &Prover) -> Option<String> {
    if options.print_smt || options.smt_dir.is_some() {
        let smtlib = if !options.no_pretty_smtlib {
            get_pretty_solver_smtlib(prover.solver())
        } else {
            get_solver_smtlib(prover.solver())
        };
        Some(smtlib)
    } else {
        None
    }
}

fn write_smtlib(
    options: &Options,
    smtlib: Option<String>,
    name: &SourceUnitName,
    result: ProveResult,
) -> io::Result<()> {
    if options.print_smt || options.smt_dir.is_some() {
        let mut smtlib = smtlib.unwrap();
        if result == ProveResult::Counterexample {
            smtlib.push_str("\n(get-model)\n");
        } else if result == ProveResult::Unknown {
            smtlib.push_str("\n(get-info :reason-unknown)\n");
        }
        if options.print_smt {
            println!("\n; --- Solver SMT-LIB ---\n{}\n", smtlib);
        }
        if let Some(smt_dir) = &options.smt_dir {
            let file_path = smt_dir.join(format!("{}.smt2", name));
            create_dir_all(file_path.parent().unwrap())?;
            let mut file = File::create(&file_path)?;
            let mut comment_writer = PrefixWriter::new("; ".as_bytes(), &mut file);
            write_detailed_version_info(&mut comment_writer)?;
            writeln!(comment_writer, "Source unit: {}", name)?;
            writeln!(comment_writer, "Prove result: {:?}", result)?;
            file.write_all(smtlib.as_bytes())?;
            info!(?file_path, "SMT-LIB query written to file");
        }
    }
    Ok(())
}
