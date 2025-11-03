//! Verification of "core" HeyVL, i.e. HeyVL with desugared proof rule
//! encodings. This code does the lowering of core HeyVL to a (quantitative)
//! proof obligation.

use std::fmt;

use crate::{
    ast::{
        visit::VisitorMut, Block, DeclKind, Direction, Expr, ExprBuilder, Span, TyKind, UnOpKind,
    },
    depgraph::{DepGraph, Dependencies},
    driver::{
        commands::{
            options::{LanguageServerOptions, SliceOptions},
            verify::VerifyCommand,
        },
        error::CaesarError,
        front::SourceUnit,
        item::SourceUnitName,
        quant_proof::QuantVcProveTask,
    },
    pretty::{Doc, SimplePretty},
    procs::{
        proc_verify::{encode_preexpectation, encode_proc_verify, to_direction_lower_bounds},
        SpecCall,
    },
    resource_limits::LimitsRef,
    servers::Server,
    slicing::{
        selection::SliceSelection,
        transform::{SliceStmts, StmtSliceVisitor},
    },
    tyctx::TyCtx,
    vc::{explain::VcExplanation, vcgen::Vcgen},
};

use tracing::instrument;

/// Lower a core verification task into a quantitative vc prove task: apply
/// desugaring for spec calls, preparing slicing, and verification condition
/// generation.
pub fn lower_core_heyvl_task(
    tcx: &mut TyCtx,
    name: &SourceUnitName,
    options: &VerifyCommand,
    limits_ref: &LimitsRef,
    server: &mut dyn Server,
    task: &mut CoreHeyVLTask,
) -> Result<(QuantVcProveTask, SliceStmts), CaesarError> {
    // 1. Desugaring
    task.desugar_spec_calls(tcx, name.to_string())?;

    // 2. Preparing slicing
    let slice_stmts = task.prepare_slicing(&options.slice_options, tcx, server)?;

    // print HeyVL core after desugaring if requested
    if options.debug_options.print_core {
        println!("{}: HeyVL core query:\n{}\n", name, *task);
    }

    // 3. Verification condition generation
    let vc = task.vcgen(limits_ref, tcx, &options.lsp_options, server)?;

    Ok((vc, slice_stmts))
}

/// A block of HeyVL statements to be verified with a certain [`Direction`].
#[derive(Debug, Clone)]
pub struct CoreHeyVLTask {
    pub deps: Dependencies,
    pub direction: Direction,
    pub block: Block,
}

impl CoreHeyVLTask {
    /// Convert proc_verify into a [`CoreHeyVLTask`]. Some declarations,
    /// such as domains or functions, do not generate any verify units. In these
    /// cases, `None` is returned.
    pub fn from_proc_verify(mut proc_verify: SourceUnit, depgraph: &mut DepGraph) -> Option<Self> {
        let deps = Self::compute_deps(&mut proc_verify, depgraph);

        match proc_verify {
            SourceUnit::Decl(decl) => {
                match decl {
                    DeclKind::ProcDecl(proc_decl) => {
                        let (direction, block) = encode_proc_verify(&proc_decl.borrow())?;
                        Some(CoreHeyVLTask {
                            deps,
                            direction,
                            block,
                        })
                    }
                    DeclKind::DomainDecl(_domain_decl) => None, // TODO: check that the axioms are not contradictions
                    DeclKind::FuncDecl(_func_decl) => None,
                    _ => unreachable!(), // axioms and variable declarations are not allowed on the top level
                }
            }
            SourceUnit::Raw(block) => Some(CoreHeyVLTask {
                deps,
                direction: Direction::Down,
                block,
            }),
        }
    }

    /// Same as [`from_proc_verify`] but translating from proc_pre_model.
    /// For this the preexpectations need to be translated
    pub fn from_proc_pre_model(mut proc_pre_model: SourceUnit, depgraph: &mut DepGraph) -> Option<Self> {
        let deps = Self::compute_deps(&mut proc_pre_model, depgraph);
        match proc_pre_model {
            SourceUnit::Decl(decl) => {
                match decl {
                    DeclKind::ProcDecl(proc_decl) => {
                        let (direction, block) = encode_preexpectation(&proc_decl.borrow())?;
                        Some(CoreHeyVLTask {
                            deps,
                            direction,
                            block,
                        })
                    }
                    DeclKind::DomainDecl(_domain_decl) => None, // TODO: check that the axioms are not contradictions
                    DeclKind::FuncDecl(_func_decl) => None,
                    _ => unreachable!(), // axioms and variable declarations are not allowed on the top level
                }
            }
            SourceUnit::Raw(block) => Some(CoreHeyVLTask {
                deps,
                direction: Direction::Down,
                block,
            }),
        }
    }

    /// Compute the dependency closure for a given source unit.
    fn compute_deps(source_unit: &mut SourceUnit, depgraph: &mut DepGraph) -> Dependencies {
        match source_unit {
            SourceUnit::Decl(decl) => depgraph.get_reachable([decl.name()]),
            SourceUnit::Raw(block) => {
                assert!(depgraph.current_deps.is_empty());
                depgraph.visit_block(block).unwrap();
                let current_deps = std::mem::take(&mut depgraph.current_deps);
                depgraph.get_reachable(current_deps)
            }
        }
    }

    /// Desugar assignments with procedure calls.
    #[instrument(skip_all)]
    pub fn desugar_spec_calls(&mut self, tcx: &mut TyCtx, name: String) -> Result<(), CaesarError> {
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
    ) -> Result<SliceStmts, CaesarError> {
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
    ///
    /// If core explanations are enabled, they will be computed and added to the server.
    #[instrument(skip_all)]
    pub fn vcgen(
        &self,
        limits_ref: &LimitsRef,
        tcx: &TyCtx,
        lsp_options: &LanguageServerOptions,
        server: &mut dyn Server,
    ) -> Result<QuantVcProveTask, CaesarError> {
        let explanations = lsp_options
            .explain_core_vc
            .then(|| VcExplanation::new(self.direction));

        let mut vcgen = Vcgen::new(tcx, limits_ref, explanations);

        let terminal = top_lit_in_lattice(self.direction, &TyKind::EUReal);
        let expr = vcgen.vcgen_block(&self.block, terminal)?;

        if let Some(explanation) = vcgen.explanation {
            server.add_vc_explanation(explanation)?;
        }

        Ok(QuantVcProveTask {
            deps: self.deps.clone(),
            direction: self.direction,
            expr,
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

impl SimplePretty for CoreHeyVLTask {
    fn pretty(&self) -> Doc {
        let lower_bounds = to_direction_lower_bounds(self.clone());
        assert_eq!(lower_bounds.direction, Direction::Down);
        lower_bounds.block.pretty()
    }
}

impl fmt::Display for CoreHeyVLTask {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.pretty().render_fmt(80, f)
    }
}
