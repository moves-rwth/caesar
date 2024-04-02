//! Encode the proof rule for almost-sure termination of a loop by McIver et al. (2018)
//!
//! @ast takes the arguments:
//!
//! - `invariant`: a boolean-valued invariant
//! - `variant` : a variant function
//! - `free_variable`: the free variable used in prob and decrease
//! - `prob`: a probability function
//! - `decrease`: a decrease function

use std::fmt;

use indexmap::IndexSet;

use crate::{
    ast::{
        util::ModifiedVariableCollector, visit::VisitorMut, BinOpKind, DeclKind, DeclRef,
        Direction, Expr, ExprBuilder, ExprKind, Files, Ident, ProcSpec, SourceFilePath, Span,
        Spanned, Stmt, StmtKind, Symbol, TyKind, UnOpKind, VarDecl, VarKind,
    },
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{check_annotation_call, AnnotationError, AnnotationInfo},
    tyctx::TyCtx,
};

use super::{Encoding, EncodingEnvironment, EncodingGenerated, ProcInfo};

use super::util::*;

pub struct ASTAnnotation(AnnotationInfo);

impl ASTAnnotation {
    pub fn new(_tcx: &mut TyCtx, files: &mut Files) -> Self {
        let file = files.add(SourceFilePath::Builtin, "ast".to_string()).id;
        // TODO: replace the dummy span with a proper span
        let name = Ident::with_dummy_file_span(Symbol::intern("ast"), file);

        let invariant_param = intrinsic_param(file, "invariant", TyKind::Bool, false);
        let variant_param = intrinsic_param(file, "variant", TyKind::SpecTy, false);
        let free_var_param = intrinsic_param(file, "free_variable", TyKind::UInt, false);
        let prob_param = intrinsic_param(file, "prob", TyKind::UReal, false);
        let decr_param = intrinsic_param(file, "decrease", TyKind::UReal, false);

        let anno_info = AnnotationInfo {
            name,
            inputs: Spanned::with_dummy_file_span(
                vec![
                    invariant_param,
                    variant_param,
                    free_var_param,
                    prob_param,
                    decr_param,
                ],
                file,
            ),
            span: Span::dummy_file_span(file),
        };

        ASTAnnotation(anno_info)
    }
}

impl fmt::Debug for ASTAnnotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ASTAnnotation")
            .field("annotation", &self.0)
            .finish()
    }
}

impl Encoding for ASTAnnotation {
    fn name(&self) -> Ident {
        self.0.name
    }

    fn is_terminator(&self) -> bool {
        false
    }

    fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError> {
        let [invariant, variant, free_var, prob, decrease] = mut_five_args(args);
        resolve.visit_expr(invariant)?;
        resolve.visit_expr(variant)?;

        if let ExprKind::Var(var_ref) = &free_var.kind {
            let var_decl = VarDecl {
                name: *var_ref,
                ty: TyKind::UInt,
                kind: VarKind::Mut,
                init: None,
                span: call_span,
                created_from: None,
            };
            // Declare the free variable to be used in the omega invariant
            resolve.declare(DeclKind::VarDecl(DeclRef::new(var_decl)))?;
        }

        resolve.visit_expr(prob)?;
        resolve.visit_expr(decrease)
    }

    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), TycheckError> {
        check_annotation_call(tycheck, call_span, &self.0, args)?;
        Ok(())
    }

    fn transform(
        &self,
        tcx: &TyCtx,
        args: &[Expr],
        inner_stmt: &Stmt,
        enc_env: EncodingEnvironment,
    ) -> Result<EncodingGenerated, AnnotationError> {
        // Unpack values from struct
        let annotation_span = enc_env.annotation_span;
        let base_proc_ident = enc_env.base_proc_ident;

        let [invariant, variant, free_var, prob, decrease] = five_args(args);
        let builder = ExprBuilder::new(annotation_span);

        // Unpack the loop guard and body from the [`Stmt`]
        let (loop_guard, loop_body) = if let StmtKind::While(guard, body) = &inner_stmt.node {
            (guard, body)
        } else {
            return Err(AnnotationError::NotOnWhile(
                annotation_span,
                self.name(),
                inner_stmt.clone(),
            ));
        };

        let free_var = if let ExprKind::Var(var_ref) = &free_var.kind {
            *var_ref
        } else {
            return Err(AnnotationError::WrongArgument(
                annotation_span,
                free_var.clone(),
                String::from("This argument must be a single variable expression."),
            ));
        };

        // Collect modified variables (exclude the variables that are declared in the loop)
        let mut visitor = ModifiedVariableCollector::new();
        visitor.visit_stmt(&mut inner_stmt.clone()).unwrap();
        let modified_vars: Vec<Ident> = (&visitor.modified_variables - &visitor.declared_variables)
            .into_iter()
            .collect();

        let modified_or_used: IndexSet<Ident> = visitor
            .modified_variables
            .union(&visitor.used_variables)
            .cloned()
            .collect();

        // Get the "init_{}" versions of the variable identifiers and declare them
        let init_idents = get_init_idents(tcx, annotation_span, &modified_vars);

        // Variables that are used but not modified or declared in the loop (These won't be transformed into an init version)
        let only_used_idents: Vec<Ident> = (&visitor.used_variables
            - &visitor
                .declared_variables
                .union(&visitor.modified_variables)
                .cloned()
                .collect::<IndexSet<Ident>>())
            .into_iter()
            .collect();

        // init version of variables and only-used variables without "init_"
        let mut input_init_vars = init_idents.clone();
        input_init_vars.extend(only_used_idents);

        // Transform the [`Ident`]s into [`Expr`]s for assignments.
        let init_exprs = init_idents
            .iter()
            .map(|ident| ident_to_expr(tcx, annotation_span, *ident))
            .collect();

        let init_assigns = multiple_assign(annotation_span, modified_vars.clone(), init_exprs);

        // That is modified variables AND variables used in an expression (exclude the variables that are declared in the loop)
        // ((Modified ∪ Used) - Declared)
        // This is used in procs that do not modify any variables in their body
        let input_vars: Vec<Ident> = (&modified_or_used - &visitor.declared_variables)
            .into_iter()
            .collect();

        // Replace all variables with the init versions in the past-invariant
        let init_variant = to_init_expr(tcx, annotation_span, variant, &modified_vars);

        let a_ident = new_ident_with_name(tcx, &TyKind::UReal, annotation_span, "a");
        let a_expr = ident_to_expr(tcx, annotation_span, a_ident);

        let b_ident = new_ident_with_name(tcx, &TyKind::UReal, annotation_span, "b");
        let b_expr = ident_to_expr(tcx, annotation_span, b_ident);

        let cond1_2_pre = builder.unary(
            UnOpKind::Embed,
            Some(TyKind::EUReal),
            builder.binary(
                BinOpKind::Le,
                Some(TyKind::Bool),
                a_expr.clone(),
                b_expr.clone(),
            ),
        );

        let cond1_post = builder.unary(
            UnOpKind::Embed,
            Some(TyKind::EUReal),
            builder.binary(
                BinOpKind::Ge,
                Some(TyKind::Bool),
                builder.subst(prob.clone(), [(free_var, a_expr.clone())]),
                builder.subst(prob.clone(), [(free_var, b_expr.clone())]),
            ),
        );

        let cond2_post = builder.unary(
            UnOpKind::Embed,
            Some(TyKind::EUReal),
            builder.binary(
                BinOpKind::Ge,
                Some(TyKind::Bool),
                builder.subst(decrease.clone(), [(free_var, a_expr)]),
                builder.subst(decrease.clone(), [(free_var, b_expr)]),
            ),
        );

        // prob antitone
        let cond1_proc_info = ProcInfo {
            name: "prob_antitone".to_string(),
            inputs: params_from_idents(vec![a_ident, b_ident], tcx),
            outputs: vec![],
            spec: vec![
                ProcSpec::Requires(cond1_2_pre.clone()),
                ProcSpec::Ensures(cond1_post),
            ],
            body: vec![],
            direction: Direction::Down,
        };

        let cond1_proc = generate_proc(annotation_span, cond1_proc_info, base_proc_ident, tcx);

        let cond2_proc_info = ProcInfo {
            name: "decrease_antitone".to_string(),
            inputs: params_from_idents(vec![a_ident, b_ident], tcx),
            outputs: vec![],
            spec: vec![
                ProcSpec::Requires(cond1_2_pre),
                ProcSpec::Ensures(cond2_post),
            ],
            body: vec![],
            direction: Direction::Down,
        };

        // decrease antitone
        let cond2_proc = generate_proc(annotation_span, cond2_proc_info, base_proc_ident, tcx);

        let cond3_expr = builder.unary(UnOpKind::Iverson, Some(TyKind::EUReal), invariant.clone());

        let mut cond3_body = init_assigns.clone();
        cond3_body.push(
            encode_iter(
                annotation_span,
                inner_stmt,
                // hey_const(annotation_span, &cond3_expr, tcx),
                vec![],
            )
            .unwrap(),
        );

        // [I] <= Phi_{[I]}([I])
        let cond3_proc_info = ProcInfo {
            name: "I_wp_subinvariant".to_string(),
            inputs: params_from_idents(input_init_vars.clone(), tcx),
            outputs: params_from_idents(modified_vars.clone(), tcx),
            spec: vec![
                ProcSpec::Requires(to_init_expr(
                    tcx,
                    annotation_span,
                    &cond3_expr,
                    &modified_vars,
                )),
                ProcSpec::Ensures(cond3_expr.clone()),
            ],
            body: cond3_body,
            direction: Direction::Down,
        };

        let cond3_proc = generate_proc(annotation_span, cond3_proc_info, base_proc_ident, tcx);

        // ?((~loop_guard) == (variant = 0))
        let cond4_expr = builder.unary(
            UnOpKind::Embed,
            Some(TyKind::EUReal),
            builder.binary(
                BinOpKind::Eq,
                Some(TyKind::Bool),
                builder.unary(UnOpKind::Not, Some(TyKind::Bool), loop_guard.clone()),
                builder.binary(
                    BinOpKind::Eq,
                    Some(TyKind::Bool),
                    variant.clone(),
                    builder.cast(TyKind::EUReal, builder.uint(0)),
                ),
            ),
        );

        // !G iff V = 0
        let cond4_proc_info = ProcInfo {
            // create the ProcInfo according to the generate_proc function below
            name: "termination_condition".to_string(),
            inputs: params_from_idents(input_vars, tcx),
            outputs: vec![],
            spec: vec![],
            body: vec![Spanned::new(
                annotation_span,
                StmtKind::Assert(Direction::Down, cond4_expr),
            )],
            direction: Direction::Down,
        };
        let cond4_proc = generate_proc(annotation_span, cond4_proc_info, base_proc_ident, tcx);
        let mut cond5_body = init_assigns.clone();
        cond5_body.push(
            encode_iter(
                annotation_span,
                inner_stmt,
                // hey_const(annotation_span, &variant, tcx),
                vec![],
            )
            .unwrap(),
        );

        // Phi_{V}(V) <= V
        let cond5_proc_info = ProcInfo {
            name: "V_wp_superinvariant".to_string(),
            inputs: params_from_idents(input_init_vars.clone(), tcx),
            outputs: params_from_idents(modified_vars.clone(), tcx),
            spec: vec![
                ProcSpec::Requires(to_init_expr(tcx, annotation_span, variant, &modified_vars)),
                ProcSpec::Ensures(variant.clone()),
            ],
            body: cond5_body,
            direction: Direction::Up,
        };

        let cond5_proc = generate_proc(annotation_span, cond5_proc_info, base_proc_ident, tcx);

        let cond6_pre = builder.binary(
            BinOpKind::Mul,
            Some(TyKind::EUReal),
            builder.unary(
                UnOpKind::Iverson,
                Some(TyKind::EUReal),
                invariant.to_owned(),
            ),
            builder.binary(
                BinOpKind::Mul,
                Some(TyKind::EUReal),
                builder.unary(
                    UnOpKind::Iverson,
                    Some(TyKind::EUReal),
                    loop_guard.to_owned(),
                ),
                builder.subst(prob.clone(), [(free_var, variant.clone())]),
            ),
        );

        let cond6_post = builder.unary(
            UnOpKind::Iverson,
            Some(TyKind::EUReal),
            builder.binary(
                BinOpKind::Le,
                Some(TyKind::Bool),
                variant.clone(),
                builder.binary(
                    BinOpKind::Sub,
                    Some(TyKind::EUReal),
                    init_variant.clone(),
                    builder.subst(decrease.clone(), [(free_var, init_variant)]),
                ),
            ),
        );

        let mut cond6_body = init_assigns;
        cond6_body.extend(loop_body.clone());

        //[I] * [G] * (p o V) <= \\s. wp[P]([V < V(s) - d(V(s))])(s)
        let cond6_proc_info = ProcInfo {
            name: "progress_condition".to_string(),
            inputs: params_from_idents(input_init_vars, tcx),
            outputs: params_from_idents(modified_vars.clone(), tcx),
            spec: vec![
                ProcSpec::Requires(to_init_expr(
                    tcx,
                    annotation_span,
                    &cond6_pre,
                    &modified_vars,
                )),
                ProcSpec::Ensures(cond6_post),
            ],
            body: cond6_body,
            direction: Direction::Down,
        };

        let cond6_proc = generate_proc(annotation_span, cond6_proc_info, base_proc_ident, tcx);

        Ok(EncodingGenerated {
            span: annotation_span,
            stmts: vec![],
            decls: Some(vec![
                cond1_proc, cond2_proc, cond3_proc, cond4_proc, cond5_proc, cond6_proc,
            ]),
        })
    }
}
