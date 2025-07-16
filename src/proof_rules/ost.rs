//! Encode the proof for a lower bound to the wp of a program using the optional stopping theorem from Aiming Low is Harder paper.
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
        util::{FreeVariableCollector, ModifiedVariableCollector},
        visit::VisitorMut,
        BinOpKind, Direction, Expr, ExprBuilder, Files, Ident, ProcSpec, SourceFilePath, Span,
        Spanned, Stmt, StmtKind, Symbol, TyKind, UnOpKind,
    },
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{
        tycheck_annotation_call, AnnotationDecl, AnnotationError, Calculus, CalculusType,
    },
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

    fn is_calculus_allowed(&self, calculus: Calculus, direction: Direction) -> bool {
        matches!(calculus.calculus_type, CalculusType::Wp) && direction == Direction::Down
    }

    fn transform(
        &self,
        tcx: &TyCtx,
        args: &[Expr],
        inner_stmt: &Stmt,
        enc_env: EncodingEnvironment,
    ) -> Result<GeneratedEncoding, AnnotationError> {
        // Unpack values from struct
        let annotation_span = enc_env.call_span;
        let base_proc_ident = enc_env.base_proc_ident;

        let [inv, past_inv, c, post] = four_args(args);

        let builder = ExprBuilder::new(annotation_span);
        let mut free_var_collector = FreeVariableCollector::new();

        // Collect and store the variables from the invariant
        let inv_variables: Vec<Ident> = free_var_collector
            .collect_and_clear(&mut inv.clone())
            .into_iter()
            .collect();

        // Collect and store the variables from the past_invariant
        let past_inv_variables: Vec<Ident> = free_var_collector
            .collect_and_clear(&mut past_inv.clone())
            .into_iter()
            .collect();

        // Collect modified variables for havoc (exclude the variables that are declared in the loop)
        let mut visitor = ModifiedVariableCollector::new();
        visitor.visit_stmt(&mut inner_stmt.clone()).unwrap();
        let modified_vars: Vec<Ident> = (&visitor.modified_variables - &visitor.declared_variables)
            .into_iter()
            .collect();

        let (loop_guard, loop_body) = if let StmtKind::While(guard, body) = &inner_stmt.node {
            (guard, body)
        } else {
            return Err(AnnotationError::NotOnWhile {
                span: annotation_span,
                annotation_name: self.name(),
                annotated: Box::new(inner_stmt.clone()),
            });
        };

        // Get the "init_{}" versions of the variable identifiers and declare them
        let init_idents = get_init_idents(tcx, annotation_span, &modified_vars);

        // Transform the [`Ident`]s into [`Expr`]s for assignments.
        let init_exprs = init_idents
            .iter()
            .map(|ident| ident_to_expr(tcx, annotation_span, *ident))
            .collect();

        let init_assigns = multiple_assign(annotation_span, modified_vars.clone(), init_exprs);

        // Replace all variables with the init versions in the invariant
        let init_inv = to_init_expr(tcx, annotation_span, inv, &inv_variables);

        // Replace all variables with the init versions in the past-invariant
        let init_past_inv = to_init_expr(tcx, annotation_span, past_inv, &past_inv_variables);

        // Construct ?(past_I < ∞)
        let cond1_assert = builder.unary(
            UnOpKind::Embed,
            Some(TyKind::EUReal),
            builder.binary(
                BinOpKind::Lt,
                Some(TyKind::Bool),
                past_inv.clone(),
                builder.top_lit(&tcx.spec_ty().clone()),
            ),
        );

        // ?(!guard ==> (I=f))
        let harmonize_expr = builder.unary(
            UnOpKind::Embed,
            Some(tcx.spec_ty().clone()),
            builder.binary(
                BinOpKind::Impl,
                Some(TyKind::Bool),
                builder.unary(UnOpKind::Not, Some(TyKind::Bool), loop_guard.clone()),
                builder.binary(BinOpKind::Eq, Some(TyKind::Bool), inv.clone(), post.clone()),
            ),
        );

        // Collect variables used in the harmonization condition
        let harmonize_expr_vars: Vec<Ident> = free_var_collector
            .collect_and_clear(&mut harmonize_expr.clone())
            .into_iter()
            .collect();

        // Condition 1: past_I < ∞
        let cond1_proc_info = ProcInfo {
            name: "lt_infinity".to_string(),
            inputs: params_from_idents(past_inv_variables, tcx),
            outputs: vec![],
            spec: vec![],
            body: Spanned::new(
                annotation_span,
                vec![Spanned::new(
                    annotation_span,
                    StmtKind::Assert(Direction::Down, cond1_assert),
                )],
            ),
            direction: Direction::Down,
        };
        let cond1_proc = generate_proc(annotation_span, cond1_proc_info, base_proc_ident, tcx);

        let mut cond2_next_iter = vec![Spanned::new(
            annotation_span,
            StmtKind::Tick(builder.cast(TyKind::EUReal, builder.uint(1))),
        )];
        cond2_next_iter.extend(hey_const(&enc_env, past_inv, Direction::Up, tcx));
        // Condition 2 : \Phi_{0}(past_I) <= past_I, so ert[P](0) <= past_I
        let mut cond2_body = init_assigns.clone();
        cond2_body.push(encode_iter(&enc_env, inner_stmt, cond2_next_iter).unwrap());

        let cond2_proc_info = ProcInfo {
            name: "past".to_string(),
            inputs: params_from_idents(init_idents.clone(), tcx),
            outputs: params_from_idents(modified_vars.clone(), tcx),
            spec: vec![
                ProcSpec::Requires(init_past_inv),
                ProcSpec::Ensures(builder.cast(TyKind::EUReal, builder.uint(0))),
            ],
            body: Spanned::new(annotation_span, cond2_body),
            direction: Direction::Up,
        };
        let cond2_proc = generate_proc(annotation_span, cond2_proc_info, base_proc_ident, tcx);

        // Init assigns followed by the loop body
        let mut cond3_body = init_assigns.clone();
        cond3_body.extend(loop_body.node.clone());

        // Encode |I(s)-I| as ite(I(s) <= I, I - I(s), I(s) - I)
        let cond3_post = builder.ite(
            Some(TyKind::EUReal),
            builder.binary(
                BinOpKind::Le,
                Some(TyKind::Bool),
                init_inv.clone(),
                inv.clone(),
            ),
            builder.binary(
                BinOpKind::Sub,
                Some(TyKind::EUReal),
                inv.clone(),
                init_inv.clone(),
            ),
            builder.binary(
                BinOpKind::Sub,
                Some(TyKind::EUReal),
                init_inv.clone(),
                inv.clone(),
            ),
        );
        let cond3_proc_info = ProcInfo {
            name: "conditional_difference_bounded".to_string(),
            inputs: params_from_idents(init_idents.clone(), tcx),
            outputs: params_from_idents(modified_vars.clone(), tcx),
            spec: vec![
                // Cast c to EUReal otherwise the type is not a complete lattice
                ProcSpec::Requires(builder.cast(TyKind::EUReal, c.clone())),
                ProcSpec::Ensures(cond3_post),
            ],
            body: Spanned::new(annotation_span, cond3_body),
            direction: Direction::Up,
        };

        let cond3_proc = generate_proc(annotation_span, cond3_proc_info, base_proc_ident, tcx);

        // Condition 4: !guard ==> (I = f)
        let cond4_proc_info = ProcInfo {
            name: "harmonize_I_f".to_string(),
            inputs: params_from_idents(harmonize_expr_vars, tcx),
            outputs: vec![],
            spec: vec![],
            body: Spanned::new(
                annotation_span,
                vec![Spanned::new(
                    annotation_span,
                    StmtKind::Assert(Direction::Down, harmonize_expr),
                )],
            ),
            direction: Direction::Down,
        };

        let cond4_proc = generate_proc(annotation_span, cond4_proc_info, base_proc_ident, tcx);

        // Condition 5: \Phi_f(I) < ∞
        // The following block should be inserted before the iter encoding to check Phi < ∞
        // instead of Phi <= ∞ which we normally achieve with just the coassume:
        // coassume 0
        // validate
        // assume ∞

        // Insert init assignments at the beginning
        let mut cond5_body = init_assigns.clone();
        cond5_body.extend(vec![
            Spanned::new(annotation_span, StmtKind::Validate(Direction::Down)),
            Spanned::new(
                annotation_span,
                StmtKind::Assume(Direction::Down, builder.top_lit(&TyKind::EUReal)),
            ),
            encode_iter(
                &enc_env,
                inner_stmt,
                hey_const(&enc_env, inv, Direction::Up, tcx),
            )
            .unwrap(),
        ]);

        let cond5_proc_info = ProcInfo {
            name: "loopiter_lt_infty".to_string(),
            inputs: params_from_idents(init_idents.clone(), tcx),
            outputs: params_from_idents(modified_vars.clone(), tcx),
            spec: vec![
                ProcSpec::Requires(builder.cast(TyKind::EUReal, builder.uint(0))),
                ProcSpec::Ensures(post.clone()),
            ],
            body: Spanned::new(annotation_span, cond5_body),
            direction: Direction::Up,
        };
        let cond5_proc = generate_proc(annotation_span, cond5_proc_info, base_proc_ident, tcx);

        // Condition 6: I <= \Phi_{post}(I)
        let mut cond6_body = init_assigns;
        cond6_body.push(
            encode_iter(
                &enc_env,
                inner_stmt,
                hey_const(&enc_env, inv, Direction::Down, tcx),
            )
            .unwrap(),
        );

        let cond6_proc_info = ProcInfo {
            name: "lower_bound".to_string(),
            inputs: params_from_idents(init_idents, tcx),
            outputs: params_from_idents(modified_vars.clone(), tcx),
            spec: vec![
                ProcSpec::Requires(init_inv),
                ProcSpec::Ensures(post.clone()),
            ],
            body: Spanned::new(annotation_span, cond6_body),
            direction: Direction::Down,
        };
        let cond6_proc = generate_proc(annotation_span, cond6_proc_info, base_proc_ident, tcx);

        // Call to the lower_bound proc from Condition 6
        let proc_call = builder.call(
            cond6_proc.name(),
            modified_vars
                .iter()
                .map(|ident| ident_to_expr(tcx, annotation_span, *ident)),
            tcx,
        );

        // Assign variables to return values of the "lower_bound" proc call
        let buf = vec![Spanned::new(
            annotation_span,
            StmtKind::Assign(modified_vars, proc_call),
        )];

        Ok(GeneratedEncoding {
            block: Spanned::new(annotation_span, buf),
            decls: Some(vec![
                cond1_proc, cond2_proc, cond3_proc, cond4_proc, cond5_proc, cond6_proc,
            ]),
        })
    }

    fn is_terminator(&self) -> bool {
        true
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
