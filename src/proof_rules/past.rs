use std::fmt;

use crate::{
    ast::{
        util::{FreeVariableCollector, ModifiedVariableCollector},
        visit::VisitorMut,
        BinOpKind, DeclKind, Direction, Expr, ExprBuilder, Files, Ident, ProcSpec, SourceFilePath,
        Span, Spanned, Stmt, StmtKind, Symbol, TyKind, UnOpKind,
    },
    front::{
        resolve::{Resolve, ResolveError},
        tycheck::{Tycheck, TycheckError},
    },
    intrinsic::annotations::{check_annotation_call, AnnotationError, AnnotationInfo},
    tyctx::TyCtx,
};

use super::Encoding;

use super::util::*;

pub struct PASTAnnotation(AnnotationInfo);

impl PASTAnnotation {
    pub fn new(_tcx: &mut TyCtx, files: &mut Files) -> Self {
        let file = files.add(SourceFilePath::Builtin, "past".to_string()).id;

        let name = Ident::with_dummy_file_span(Symbol::intern("past"), file);

        let invariant_param = intrinsic_param(file, "inv", TyKind::SpecTy, false);
        let eps_param = intrinsic_param(file, "eps", TyKind::UReal, true);
        let k_param = intrinsic_param(file, "k", TyKind::UReal, true);

        let anno_info = AnnotationInfo {
            name,
            inputs: Spanned::with_dummy_file_span(vec![invariant_param, eps_param, k_param], file),
            span: Span::dummy_file_span(file),
        };

        PASTAnnotation(anno_info)
    }
}

impl fmt::Debug for PASTAnnotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PASTAnnotation")
            .field("annotation", &self.0)
            .finish()
    }
}

impl Encoding for PASTAnnotation {
    fn name(&self) -> Ident {
        self.0.name
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
    fn resolve(
        &self,
        resolve: &mut Resolve<'_>,
        _call_span: Span,
        args: &mut [Expr],
    ) -> Result<(), ResolveError> {
        let [inv, eps, k] = mut_three_args(args);
        resolve.visit_expr(inv)?;
        resolve.visit_expr(eps)?;
        resolve.visit_expr(k)
    }

    fn transform(
        &self,
        tcx: &TyCtx,
        annotation_span: Span,
        args: &[Expr],
        inner_stmt: &Stmt,
        _direction: Direction,
    ) -> Result<(Span, Vec<Stmt>, Option<Vec<DeclKind>>), AnnotationError> {
        let [inv, eps, k] = three_args(args);
        let builder = ExprBuilder::new(annotation_span);

        let eps_val = lit_f64(eps);
        let k_val = lit_f64(k);

        if eps_val >= k_val {
            return Err(AnnotationError::WrongArgument(
                annotation_span,
                eps.clone(),
                String::from("eps must be smaller than k."),
            ));
        }

        // Collect modified variables for havoc (exclude the variables that are declared in the loop)
        let mut visitor = ModifiedVariableCollector::new();
        visitor.visit_stmt(&mut inner_stmt.clone()).unwrap();
        let modified_vars: Vec<Ident> = (&visitor.modified_variables - &visitor.declared_variables)
            .into_iter()
            .collect();

        let mut free_var_collector = FreeVariableCollector::new();

        // Collect and store the variables from the invariant
        let inv_variables: Vec<Ident> = free_var_collector
            .collect_and_clear(&mut inv.clone())
            .into_iter()
            .collect();

        let (loop_guard, _) = if let StmtKind::While(guard, body) = &inner_stmt.node {
            (guard, body)
        } else {
            return Err(AnnotationError::NotOnWhile(
                annotation_span,
                self.name(),
                inner_stmt.clone(),
            ));
        };

        // Get the "init_{}" versions of the variable identifiers and declare them
        let init_idents = get_init_idents(tcx, annotation_span, &modified_vars);

        // Transform the [`Ident`]s into [`Expr`]s for assignments.
        let init_exprs = init_idents
            .iter()
            .map(|ident| ident_to_expr(tcx, annotation_span, *ident))
            .collect();

        let init_assigns = multiple_assign(annotation_span, modified_vars.clone(), init_exprs);

        // Replace all variables with the init versions in the past-invariant
        let init_inv = to_init_expr(tcx, annotation_span, inv, &inv_variables);

        // ?([!guard] * inv <= k)
        let cond1_expr = builder.unary(
            UnOpKind::Embed,
            Some(tcx.spec_ty().clone()),
            builder.binary(
                BinOpKind::Le,
                Some(TyKind::Bool),
                builder.binary(
                    BinOpKind::Mul,
                    Some(TyKind::EUReal),
                    builder.unary(
                        UnOpKind::Iverson,
                        Some(TyKind::EUReal),
                        builder.unary(UnOpKind::Not, Some(TyKind::Bool), loop_guard.clone()),
                    ),
                    inv.clone(),
                ),
                k.clone(),
            ),
        );

        // Collect variables used in the first condition
        let cond1_expr_vars: Vec<Ident> = free_var_collector
            .collect_and_clear(&mut cond1_expr.clone())
            .into_iter()
            .collect();

        let cond1_proc = generate_proc(
            annotation_span,
            "condition_1",
            params_from_idents(cond1_expr_vars, tcx),
            vec![],
            vec![],
            vec![Spanned::new(
                annotation_span,
                StmtKind::Assert(Direction::Down, cond1_expr),
            )],
            Direction::Down,
            tcx,
        );

        // [guard] * k <= (([guard] * invariant) + [!guard])
        let cond2_expr = builder.binary(
            BinOpKind::Le,
            Some(TyKind::Bool),
            // [guard] * k
            builder.binary(
                BinOpKind::Mul,
                Some(TyKind::EUReal),
                // [guard]
                builder.unary(UnOpKind::Iverson, Some(TyKind::EUReal), loop_guard.clone()),
                k.clone(),
            ),
            // (([guard] * invariant) + [!guard])
            builder.binary(
                BinOpKind::Add,
                Some(TyKind::EUReal),
                // ([guard] * invariant)
                builder.binary(
                    BinOpKind::Mul,
                    Some(TyKind::EUReal),
                    builder.unary(UnOpKind::Iverson, Some(TyKind::EUReal), loop_guard.clone()),
                    inv.clone(),
                ),
                // [!guard]
                builder.unary(
                    UnOpKind::Iverson,
                    Some(TyKind::EUReal),
                    builder.unary(UnOpKind::Not, Some(TyKind::Bool), loop_guard.clone()),
                ),
            ),
        );

        // Collect variables used in the second condition
        let cond2_expr_vars: Vec<Ident> = free_var_collector
            .collect_and_clear(&mut cond2_expr.clone())
            .into_iter()
            .collect();

        let cond2_proc = generate_proc(
            annotation_span,
            "condition_2",
            params_from_idents(cond2_expr_vars, tcx),
            vec![],
            vec![],
            vec![Spanned::new(
                annotation_span,
                StmtKind::Assert(Direction::Down, cond2_expr),
            )],
            Direction::Down,
            tcx,
        );

        // Condition 3: \Phi_0(I) <= [G] * (I - eps)
        let mut cond3_body = init_assigns;
        cond3_body.push(
            encode_iter(
                annotation_span,
                inner_stmt,
                hey_const(annotation_span, inv, tcx),
            )
            .unwrap(),
        );

        let cond3_pre = builder.binary(
            BinOpKind::Mul,
            Some(TyKind::EUReal),
            builder.unary(UnOpKind::Iverson, Some(TyKind::EUReal), loop_guard.clone()),
            builder.binary(BinOpKind::Sub, Some(TyKind::EUReal), init_inv, eps.clone()),
        );

        let cond3_proc = generate_proc(
            annotation_span,
            "past",
            params_from_idents(init_idents, tcx),
            params_from_idents(modified_vars, tcx),
            vec![
                ProcSpec::Requires(cond3_pre),
                ProcSpec::Ensures(builder.cast(TyKind::EUReal, builder.uint(0))),
            ],
            cond3_body,
            Direction::Up,
            tcx,
        );

        Ok((
            annotation_span,
            vec![],
            Some(vec![cond1_proc, cond2_proc, cond3_proc]),
        ))
    }

    fn is_one_loop(&self) -> bool {
        true
    }
}
