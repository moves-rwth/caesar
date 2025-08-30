//! Verification of "core" HeyVL, i.e. HeyVL with desugared proof rule
//! encodings. This code does the lowering of core HeyVL to a (quantitative)
//! proof obligation.

use std::fmt;

use crate::{
    ast::{
        visit::VisitorMut, Block, DeclKind, Direction, Expr, ExprBuilder, Span, TyKind, UnOpKind,
    },
    depgraph::{DepGraph, Dependencies},
    driver::{commands::SliceOptions, front::SourceUnit, quant_proof::QuantVcProveTask},
    pretty::{Doc, SimplePretty},
    procs::{
        proc_verify::{encode_proc_verify, to_direction_lower_bounds},
        SpecCall,
    },
    servers::Server,
    slicing::{
        selection::SliceSelection,
        transform::{SliceStmts, StmtSliceVisitor},
    },
    tyctx::TyCtx,
    vc::vcgen::Vcgen,
    CaesarError,
};

use tracing::instrument;

/// A block of HeyVL statements to be verified with a certain [`Direction`].
#[derive(Debug, Clone)]
pub struct CoreVerifyTask {
    pub deps: Dependencies,
    pub direction: Direction,
    pub block: Block,
}

impl CoreVerifyTask {
    /// Convert this source unit into a [`CoreVerifyTask`]. Some declarations,
    /// such as domains or functions, do not generate any verify units. In these
    /// cases, `None` is returned.
    pub fn from_source_unit(mut source_unit: SourceUnit, depgraph: &mut DepGraph) -> Option<Self> {
        let deps = match &mut source_unit {
            SourceUnit::Decl(decl) => depgraph.get_reachable([decl.name()]),
            SourceUnit::Raw(block) => {
                assert!(depgraph.current_deps.is_empty());
                depgraph.visit_block(block).unwrap();
                let current_deps = std::mem::take(&mut depgraph.current_deps);
                depgraph.get_reachable(current_deps)
            }
        };

        match source_unit {
            SourceUnit::Decl(decl) => {
                match decl {
                    DeclKind::ProcDecl(proc_decl) => {
                        let (direction, block) = encode_proc_verify(&proc_decl.borrow())?;
                        Some(CoreVerifyTask {
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
            SourceUnit::Raw(block) => Some(CoreVerifyTask {
                deps,
                direction: Direction::Down,
                block,
            }),
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
    #[instrument(skip(self, vcgen))]
    pub fn vcgen(&self, vcgen: &mut Vcgen) -> Result<QuantVcProveTask, CaesarError> {
        let terminal = top_lit_in_lattice(self.direction, &TyKind::EUReal);
        Ok(QuantVcProveTask {
            deps: self.deps.clone(),
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

impl SimplePretty for CoreVerifyTask {
    fn pretty(&self) -> Doc {
        let lower_bounds = to_direction_lower_bounds(self.clone());
        assert_eq!(lower_bounds.direction, Direction::Down);
        lower_bounds.block.pretty()
    }
}

impl fmt::Display for CoreVerifyTask {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.pretty().render_fmt(80, f)
    }
}
