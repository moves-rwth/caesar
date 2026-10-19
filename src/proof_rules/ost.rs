//! Encode a lower-bound rule based on case (b) of the optional stopping theorem in Aiming Low Is Harder.
//! Subinvariance supplies the exit condition `I <= post`.
//!
//! @ost takes the arguments:
//!
//! - `inv`: the invariant of the loop
//! - `past_inv`: the invariant for the PAST rule
//! - `c`: the constant c from the theorem, must be a literal
//! - `post`: the postcondition of the loop
//!
use std::{any::Any, fmt};

use crate::{
    ast::{
        util::VariableCollector, visit::VisitorMut, BinOpKind, Block, DeclKind, Direction, Expr,
        ExprBuilder, Files, Ident, ProcSpec, SourceFilePath, Span, Spanned, Stmt, StmtKind, Symbol,
        TyKind, UnOpKind,
    },
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{tycheck_annotation_call, AnnotationDecl, AnnotationError, Calculus},
    proof_rules::calculus::{ApproximationKind, CalculusType, FixpointKind},
    tyctx::TyCtx,
};

use super::{Encoding, EncodingEnvironment, GeneratedEncoding, ProcInfo};

use super::util::*;

pub struct OSTAnnotation(AnnotationDecl);

impl OSTAnnotation {
    pub fn new(_tcx: &mut TyCtx, files: &mut Files) -> Self {
        let file = files.add(SourceFilePath::Builtin, "ost".to_string()).id;
        // TODO: replace the dummy span with a proper span
        let name = Ident::with_dummy_file_span(Symbol::intern("ost"), file);

        let invariant_param = intrinsic_param(file, "inv", TyKind::SpecTy, false);
        let past_invariant_param = intrinsic_param(file, "past_inv", TyKind::SpecTy, false);
        let c_param = intrinsic_param(file, "c", TyKind::UReal, true);
        let post_param = intrinsic_param(file, "post", TyKind::SpecTy, false);

        let anno_decl = AnnotationDecl {
            name,
            inputs: Spanned::with_dummy_file_span(
                vec![invariant_param, past_invariant_param, c_param, post_param],
                file,
            ),
            span: Span::dummy_file_span(file),
        };

        OSTAnnotation(anno_decl)
    }
}

impl fmt::Debug for OSTAnnotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OSTAnnotation")
            .field("annotation", &self.0)
            .finish()
    }
}

impl Encoding for OSTAnnotation {
    fn name(&self) -> Ident {
        self.0.name
    }

    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), TycheckError> {
        tycheck_annotation_call(tycheck, call_span, &self.0, args)?;
        Ok(())
    }

    fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        _call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError> {
        let [inv, past_inv, c, post] = mut_four_args(args);
        resolve.visit_expr(inv)?;
        resolve.visit_expr(past_inv)?;
        resolve.visit_expr(c)?;
        resolve.visit_expr(post)
    }

    fn get_approximation(
        &self,
        fixpoint_kind: FixpointKind,
        inner_approximation_kind: ApproximationKind,
        calculus: Option<Calculus>,
    ) -> ApproximationKind {
        // @ost is only sound with @wp; @ert also uses LFP but is not appropriate here.
        if let Some(c) = calculus {
            if !matches!(c.calculus_type, CalculusType::Wp) {
                return ApproximationKind::UNKNOWN;
            }
        }
        match (fixpoint_kind, inner_approximation_kind) {
            (FixpointKind::Least, ApproximationKind::EXACT) => ApproximationKind::EXACT,
            _ => ApproximationKind::UNKNOWN,
        }
    }

    fn default_fixpoint_kind(&self, _direction: Direction, _args: &[Expr]) -> FixpointKind {
        FixpointKind::Least
    }

    fn transform(
        &self,
        tcx: &TyCtx,
        args: &[Expr],
        inner_stmt: &Stmt,
        enc_env: EncodingEnvironment,
    ) -> Result<GeneratedEncoding, AnnotationError> {
        if !matches!(&inner_stmt.node, StmtKind::While(_, _)) {
            return Err(AnnotationError::NotOnWhile {
                span: enc_env.call_span,
                annotation_name: self.name(),
                annotated: Box::new(inner_stmt.clone()),
            });
        }

        let [invariant, iteration_bound, difference_bound, post] = four_args(args);
        let encoding = OstEncoding::new(tcx, &enc_env, inner_stmt, args);
        let invariant_variables: Vec<Ident> = VariableCollector::from_expr(invariant)
            .used_variables
            .into_iter()
            .collect();
        let iteration_bound_variables: Vec<Ident> = VariableCollector::from_expr(iteration_bound)
            .used_variables
            .into_iter()
            .collect();
        let initial_invariant = encoding.snapshot(invariant, &invariant_variables);
        let initial_iteration_bound =
            encoding.snapshot(iteration_bound, &iteration_bound_variables);

        let iteration_bound_finite =
            encoding.encode_finiteness("lt_infinity", iteration_bound, iteration_bound_variables);
        let expected_iterations =
            encoding.encode_iteration_bound(iteration_bound, initial_iteration_bound);
        let difference_bounded =
            encoding.encode_difference_bound(invariant, &initial_invariant, difference_bound);
        // I < infinity and CDB give Phi_I(I) <= I + c < infinity.
        // Apply OST with postexpectation I, then use I <= post at loop exit.
        let invariant_finite =
            encoding.encode_finiteness("invariant_finite", invariant, invariant_variables);
        let subinvariant = encoding.encode_subinvariant(invariant, initial_invariant, post);
        let block = encoding.encode_call(&subinvariant);

        Ok(GeneratedEncoding {
            block,
            decls: Some(vec![
                iteration_bound_finite,
                expected_iterations,
                difference_bounded,
                invariant_finite,
                subinvariant,
            ]),
            diagnostics: vec![],
        })
    }

    fn is_terminator(&self) -> bool {
        true
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

struct OstEncoding<'a> {
    tcx: &'a TyCtx,
    env: &'a EncodingEnvironment,
    loop_stmt: &'a Stmt,
    modified_variables: Vec<Ident>,
    procedure_inputs: Vec<Ident>,
    call_inputs: Vec<Ident>,
    initialization: Vec<Stmt>,
}

impl<'a> OstEncoding<'a> {
    fn new(
        tcx: &'a TyCtx,
        env: &'a EncodingEnvironment,
        loop_stmt: &'a Stmt,
        args: &[Expr],
    ) -> Self {
        let mut variables = VariableCollector::from_stmt(loop_stmt);
        for arg in args {
            variables.add_expr(arg);
        }
        let modified_variables: Vec<Ident> = variables.free_modified().collect();
        let (mut procedure_inputs, initialization) =
            encode_initial_state(tcx, env.call_span, &modified_variables);
        let mut call_inputs = modified_variables.clone();
        for variable in variables.free_read_only() {
            procedure_inputs.push(variable);
            call_inputs.push(variable);
        }

        Self {
            tcx,
            env,
            loop_stmt,
            modified_variables,
            procedure_inputs,
            call_inputs,
            initialization,
        }
    }

    /// Replace modified free variables with their initial values, in expression order.
    fn snapshot(&self, expression: &Expr, variables: &[Ident]) -> Expr {
        let modified_variables: Vec<Ident> = variables
            .iter()
            .filter(|ident| self.modified_variables.contains(ident))
            .copied()
            .collect();
        to_init_expr(
            self.tcx,
            self.env.call_span,
            expression,
            &modified_variables,
        )
    }

    fn iteration_body(&self, next_iteration: Vec<Stmt>) -> Block {
        let mut body = self.initialization.clone();
        body.push(encode_iter(self.env, self.loop_stmt, next_iteration).unwrap());
        Spanned::new(self.env.call_span, body)
    }

    /// Check that the expectation is finite in every state.
    fn encode_finiteness(&self, name: &str, expression: &Expr, variables: Vec<Ident>) -> DeclKind {
        let span = self.env.call_span;
        let builder = ExprBuilder::new(span);
        let condition = builder.unary(
            UnOpKind::Embed,
            Some(self.tcx.spec_ty().clone()),
            builder.binary(
                BinOpKind::Lt,
                Some(TyKind::Bool),
                expression.clone(),
                builder.top_lit(self.tcx.spec_ty()),
            ),
        );
        generate_proc(
            span,
            ProcInfo {
                name: name.to_owned(),
                inputs: params_from_idents(variables, self.tcx),
                outputs: vec![],
                spec: vec![],
                body: Spanned::new(
                    span,
                    vec![Spanned::new(
                        span,
                        StmtKind::Assert(Direction::Down, condition),
                    )],
                ),
                direction: Direction::Down,
            },
            self.env.base_proc_ident,
            self.tcx,
        )
    }

    /// Check the upper bound on the expected number of iterations.
    fn encode_iteration_bound(&self, invariant: &Expr, initial_invariant: Expr) -> DeclKind {
        let span = self.env.call_span;
        let builder = ExprBuilder::new(span);
        let mut next_iteration = vec![Spanned::new(
            span,
            StmtKind::Tick(builder.cast(TyKind::EUReal, builder.uint(1))),
        )];
        next_iteration.extend(hey_const(span, invariant, Direction::Up, self.tcx));
        generate_proc(
            span,
            ProcInfo {
                name: "past".to_owned(),
                inputs: params_from_idents(self.procedure_inputs.clone(), self.tcx),
                outputs: params_from_idents(self.modified_variables.clone(), self.tcx),
                spec: vec![
                    ProcSpec::Requires(initial_invariant),
                    ProcSpec::Ensures(builder.cast(TyKind::EUReal, builder.uint(0))),
                ],
                body: self.iteration_body(next_iteration),
                direction: Direction::Up,
            },
            self.env.base_proc_ident,
            self.tcx,
        )
    }

    /// Bound the expected absolute change of I over one iteration, including exit.
    fn encode_difference_bound(
        &self,
        invariant: &Expr,
        initial_invariant: &Expr,
        bound: &Expr,
    ) -> DeclKind {
        let span = self.env.call_span;
        let builder = ExprBuilder::new(span);
        let difference = builder.ite(
            Some(TyKind::EUReal),
            builder.binary(
                BinOpKind::Le,
                Some(TyKind::Bool),
                initial_invariant.clone(),
                invariant.clone(),
            ),
            builder.binary(
                BinOpKind::Sub,
                Some(TyKind::EUReal),
                invariant.clone(),
                initial_invariant.clone(),
            ),
            builder.binary(
                BinOpKind::Sub,
                Some(TyKind::EUReal),
                initial_invariant.clone(),
                invariant.clone(),
            ),
        );
        generate_proc(
            span,
            ProcInfo {
                name: "conditional_difference_bounded".to_owned(),
                inputs: params_from_idents(self.procedure_inputs.clone(), self.tcx),
                outputs: params_from_idents(self.modified_variables.clone(), self.tcx),
                spec: vec![
                    ProcSpec::Requires(builder.cast(TyKind::EUReal, bound.clone())),
                    ProcSpec::Ensures(difference),
                ],
                body: self.iteration_body(vec![]),
                direction: Direction::Up,
            },
            self.env.base_proc_ident,
            self.tcx,
        )
    }

    /// Check `I <= Phi_post(I)`, including `I <= post` at loop exit.
    fn encode_subinvariant(
        &self,
        invariant: &Expr,
        initial_invariant: Expr,
        post: &Expr,
    ) -> DeclKind {
        let span = self.env.call_span;
        generate_proc(
            span,
            ProcInfo {
                name: "lower_bound".to_owned(),
                inputs: params_from_idents(self.procedure_inputs.clone(), self.tcx),
                outputs: params_from_idents(self.modified_variables.clone(), self.tcx),
                spec: vec![
                    ProcSpec::Requires(initial_invariant),
                    ProcSpec::Ensures(post.clone()),
                ],
                body: self
                    .iteration_body(hey_const(span, invariant, Direction::Down, self.tcx).into()),
                direction: Direction::Down,
            },
            self.env.base_proc_ident,
            self.tcx,
        )
    }

    fn encode_call(&self, subinvariant: &DeclKind) -> Block {
        let span = self.env.call_span;
        let builder = ExprBuilder::new(span);
        let call = builder.call(
            subinvariant.name(),
            self.call_inputs
                .iter()
                .map(|ident| ident_to_expr(self.tcx, span, *ident)),
            self.tcx,
        );
        Spanned::new(
            span,
            vec![Spanned::new(
                span,
                StmtKind::Assign(self.modified_variables.clone(), call),
            )],
        )
    }
}
