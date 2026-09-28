//! Encode an almost-sure termination rule based on McIver et al. (2018).
//!
//! @ast takes the arguments:
//!
//! - `invariant`: a boolean-valued invariant
//! - `variant` : a variant function
//! - `free_variable`: the free variable used in prob and decrease
//! - `prob`: a probability function
//! - `decrease`: a decrease function

use std::{any::Any, fmt};

use ariadne::ReportKind;
use indexmap::IndexSet;

use crate::{
    ast::{
        util::{FreeVariableCollector, ModifiedVariableCollector},
        visit::{walk_expr, walk_stmt, VisitorMut},
        BinOpKind, Block, DeclKind, DeclRef, Diagnostic, Direction, Expr, ExprBuilder, ExprKind,
        Files, Ident, Label, ProcSpec, SourceFilePath, Span, Spanned, Stmt, StmtKind, Symbol,
        TyKind, UnOpKind, VarDecl, VarKind,
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

pub struct ASTAnnotation(AnnotationDecl);

impl ASTAnnotation {
    pub fn new(_tcx: &mut TyCtx, files: &mut Files) -> Self {
        let file = files.add(SourceFilePath::Builtin, "ast".to_string()).id;
        // TODO: replace the dummy span with a proper span
        let name = Ident::with_dummy_file_span(Symbol::intern("ast"), file);

        let invariant_param = intrinsic_param(file, "invariant", TyKind::Bool, false);
        let variant_param = intrinsic_param(file, "variant", TyKind::UReal, false);
        let free_var_param = intrinsic_param(file, "free_variable", TyKind::UReal, false);
        let prob_param = intrinsic_param(file, "prob", TyKind::UReal, false);
        let decr_param = intrinsic_param(file, "decrease", TyKind::UReal, false);

        let anno_decl = AnnotationDecl {
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

        ASTAnnotation(anno_decl)
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

        resolve.with_subscope(|resolve| {
            if let ExprKind::Var(var_ref) = &free_var.kind {
                let var_decl = VarDecl {
                    name: *var_ref,
                    ty: TyKind::UReal,
                    kind: VarKind::Mut,
                    init: None,
                    span: call_span,
                    created_from: None,
                };
                resolve.declare(DeclKind::VarDecl(DeclRef::new(var_decl)))?;
            } else {
                return Err(ResolveError::NotIdent(free_var.span));
            }

            resolve.visit_expr(prob)?;
            resolve.visit_expr(decrease)
        })
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

    fn validate(
        &self,
        tcx: &TyCtx,
        call_span: Span,
        args: &[Expr],
        inner_stmt: &Stmt,
    ) -> Result<Vec<Diagnostic>, AnnotationError> {
        let mut validator = AstBodyValidator {
            tcx,
            annotation_name: self.name(),
            call_span,
            diagnostics: vec![],
        };
        if matches!(inner_stmt.node, StmtKind::While(_, _)) {
            validator.visit_stmt(&mut inner_stmt.clone())?;
            let [_, _, free_var, prob, decrease] = five_args(args);
            let ExprKind::Var(free_var) = &free_var.kind else {
                unreachable!("free variable has been resolved");
            };
            let modified = ModifiedVariableCollector::from_stmt(inner_stmt);
            let mut free_variables = FreeVariableCollector::new();
            for (name, expr) in [("prob", prob), ("decrease", decrease)] {
                for variable in free_variables.collect_and_clear(&mut expr.clone()) {
                    if variable != *free_var && modified.modified_variables.contains(&variable) {
                        return Err(AnnotationError::WrongArgument {
                            span: call_span,
                            arg: expr.clone(),
                            message: format!(
                                "`{name}` must not depend on loop-modified variable `{variable}`."
                            ),
                        });
                    }
                }
            }
        }
        Ok(validator.diagnostics)
    }

    fn get_approximation(
        &self,
        fixpoint_kind: FixpointKind,
        inner_approximation_kind: ApproximationKind,
        calculus: Option<Calculus>,
    ) -> ApproximationKind {
        // @ast is only sound with @wp; @ert also uses LFP but is not appropriate here.
        if let Some(c) = calculus {
            if !matches!(c.calculus_type, CalculusType::Wp) {
                return ApproximationKind::UNKNOWN;
            }
        }
        match (fixpoint_kind, inner_approximation_kind) {
            (FixpointKind::Least, ApproximationKind::EXACT) => ApproximationKind::UNDER,
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
        let annotation_span = enc_env.call_span;

        let [invariant, variant, free_var, prob, decrease] = five_args(args);
        let builder = ExprBuilder::new(annotation_span);

        // Unpack the loop guard and body from the [`Stmt`]
        let (loop_guard, loop_body) = if let StmtKind::While(guard, body) = &inner_stmt.node {
            (guard, body)
        } else {
            return Err(AnnotationError::NotOnWhile {
                span: annotation_span,
                annotation_name: self.name(),
                annotated: Box::new(inner_stmt.clone()),
            });
        };

        let free_var = if let ExprKind::Var(var_ref) = &free_var.kind {
            *var_ref
        } else {
            unreachable!("error should have been caught during resolve")
        };

        // Collect modified variables (exclude the variables that are declared in the loop)
        let visitor = ModifiedVariableCollector::from_stmt(inner_stmt);
        let modified_vars = visitor.modified_outside_declarations();

        let mut free_variables = FreeVariableCollector::new();
        free_variables.visit_stmt(&mut inner_stmt.clone()).unwrap();
        for expr in [invariant, variant, prob, decrease] {
            free_variables.visit_expr(&mut expr.clone()).unwrap();
        }
        free_variables.variables.shift_remove(&free_var);

        // Get the "init_{}" versions of the variable identifiers and declare them
        let init_idents = get_init_idents(tcx, annotation_span, &modified_vars);

        // Variables that are used but not modified or declared in the loop (These won't be transformed into an init version)
        let only_used_idents: Vec<Ident> = (&free_variables.variables
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

        let encoding = AstEncoding {
            tcx,
            env: &enc_env,
            loop_stmt: inner_stmt,
            invariant,
            variant,
            free_var,
            prob,
            decrease,
            modified_vars,
            input_init_vars,
            init_assigns,
        };
        let [prob_conditions, decrease_conditions] = encoding.encode_function_conditions();
        let invariant_condition = encoding.encode_invariant();
        let variant_bound = encoding.encode_variant_bound(loop_guard);
        let progress_condition = encoding.encode_progress(loop_guard, loop_body);
        let invariant_expr =
            builder.unary(UnOpKind::Iverson, Some(TyKind::EUReal), invariant.clone());

        Ok(GeneratedEncoding {
            block: Spanned::new(
                annotation_span,
                encode_loop_spec(
                    annotation_span,
                    &invariant_expr,
                    encoding.modified_vars,
                    Direction::Down,
                )
                .into(),
            ),
            decls: Some(vec![
                prob_conditions,
                decrease_conditions,
                invariant_condition,
                variant_bound,
                progress_condition,
            ]),
            diagnostics: vec![],
        })
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

struct AstEncoding<'a> {
    tcx: &'a TyCtx,
    env: &'a EncodingEnvironment,
    loop_stmt: &'a Stmt,
    invariant: &'a Expr,
    variant: &'a Expr,
    free_var: Ident,
    prob: &'a Expr,
    decrease: &'a Expr,
    modified_vars: Vec<Ident>,
    input_init_vars: Vec<Ident>,
    init_assigns: Vec<Stmt>,
}

impl AstEncoding<'_> {
    fn encode_function_conditions(&self) -> [DeclKind; 2] {
        let span = self.env.call_span;
        let builder = ExprBuilder::new(span);

        let a_ident = self.tcx.clone_var(self.free_var, span, VarKind::Input);
        let a_expr = ident_to_expr(self.tcx, span, a_ident);

        let b_ident = self.tcx.clone_var(self.free_var, span, VarKind::Input);
        let b_expr = ident_to_expr(self.tcx, span, b_ident);

        let mut function_variables = FreeVariableCollector::new();
        for expr in [self.invariant, self.prob, self.decrease] {
            function_variables.visit_expr(&mut expr.clone()).unwrap();
        }
        function_variables.variables.shift_remove(&self.free_var);
        let mut function_inputs = vec![a_ident, b_ident];
        function_inputs.extend(function_variables.variables);

        // ?(I && a <= b)
        let pre = builder.unary(
            UnOpKind::Embed,
            Some(TyKind::EUReal),
            builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                self.invariant.clone(),
                builder.binary(
                    BinOpKind::Le,
                    Some(TyKind::Bool),
                    a_expr.clone(),
                    b_expr.clone(),
                ),
            ),
        );

        let prob_a = builder.subst(self.prob.clone(), [(self.free_var, a_expr.clone())]);
        let prob_b = builder.subst(self.prob.clone(), [(self.free_var, b_expr.clone())]);
        let decrease_a = builder.subst(self.decrease.clone(), [(self.free_var, a_expr)]);
        let decrease_b = builder.subst(self.decrease.clone(), [(self.free_var, b_expr)]);

        let prob_proc_info = ProcInfo {
            name: "prob_conditions".to_string(),
            inputs: params_from_idents(function_inputs.clone(), self.tcx),
            outputs: vec![],
            spec: vec![
                ProcSpec::Requires(pre.clone()),
                ProcSpec::Ensures(builder.unary(
                    UnOpKind::Embed,
                    Some(TyKind::EUReal),
                    builder.binary(
                        BinOpKind::Gt,
                        Some(TyKind::Bool),
                        prob_b.clone(),
                        builder.cast(TyKind::UReal, builder.uint(0)),
                    ),
                )),
                ProcSpec::Ensures(builder.unary(
                    UnOpKind::Embed,
                    Some(TyKind::EUReal),
                    builder.binary(BinOpKind::Le, Some(TyKind::Bool), prob_b, prob_a.clone()),
                )),
                ProcSpec::Ensures(builder.unary(
                    UnOpKind::Embed,
                    Some(TyKind::EUReal),
                    builder.binary(
                        BinOpKind::Le,
                        Some(TyKind::Bool),
                        prob_a,
                        builder.cast(TyKind::UReal, builder.uint(1)),
                    ),
                )),
            ],
            body: Spanned::new(span, vec![]),
            direction: Direction::Down,
        };

        let prob_proc = generate_proc(span, prob_proc_info, self.env.base_proc_ident, self.tcx);

        let decrease_proc_info = ProcInfo {
            name: "decrease_conditions".to_string(),
            inputs: params_from_idents(function_inputs, self.tcx),
            outputs: vec![],
            spec: vec![
                ProcSpec::Requires(pre),
                ProcSpec::Ensures(builder.unary(
                    UnOpKind::Embed,
                    Some(TyKind::EUReal),
                    builder.binary(
                        BinOpKind::Gt,
                        Some(TyKind::Bool),
                        decrease_b.clone(),
                        builder.cast(TyKind::UReal, builder.uint(0)),
                    ),
                )),
                ProcSpec::Ensures(builder.unary(
                    UnOpKind::Embed,
                    Some(TyKind::EUReal),
                    builder.binary(BinOpKind::Le, Some(TyKind::Bool), decrease_b, decrease_a),
                )),
            ],
            body: Spanned::new(span, vec![]),
            direction: Direction::Down,
        };

        let decrease_proc =
            generate_proc(span, decrease_proc_info, self.env.base_proc_ident, self.tcx);

        [prob_proc, decrease_proc]
    }

    fn encode_invariant(&self) -> DeclKind {
        let span = self.env.call_span;
        let builder = ExprBuilder::new(span);

        let invariant_expr = builder.unary(
            UnOpKind::Iverson,
            Some(TyKind::EUReal),
            self.invariant.clone(),
        );

        let mut body = self.init_assigns.clone();
        body.push(encode_iter(self.env, self.loop_stmt, vec![]).unwrap());

        // [I] <= Phi_{[I]}([I])
        let proc_info = ProcInfo {
            name: "I_wp_subinvariant".to_string(),
            inputs: params_from_idents(self.input_init_vars.clone(), self.tcx),
            outputs: params_from_idents(self.modified_vars.clone(), self.tcx),
            spec: vec![
                ProcSpec::Requires(to_init_expr(
                    self.tcx,
                    span,
                    &invariant_expr,
                    &self.modified_vars,
                )),
                ProcSpec::Ensures(invariant_expr),
            ],
            body: Spanned::new(span, body),
            direction: Direction::Down,
        };

        generate_proc(span, proc_info, self.env.base_proc_ident, self.tcx)
    }

    fn encode_variant_bound(&self, loop_guard: &Expr) -> DeclKind {
        let span = self.env.call_span;
        let builder = ExprBuilder::new(span);

        let init_variant = to_init_expr(self.tcx, span, self.variant, &self.modified_vars);
        let init_invariant = to_init_expr(self.tcx, span, self.invariant, &self.modified_vars);

        let mut body = self.init_assigns.clone();
        let mut variant_iteration = encode_iter(self.env, self.loop_stmt, vec![]).unwrap();
        AwpEncoder.visit_stmt(&mut variant_iteration).unwrap();
        body.push(variant_iteration);

        let proc_info = ProcInfo {
            name: "V_awp_superinvariant".to_string(),
            inputs: params_from_idents(self.input_init_vars.clone(), self.tcx),
            outputs: params_from_idents(self.modified_vars.clone(), self.tcx),
            spec: vec![
                ProcSpec::Requires(builder.unary(
                    UnOpKind::Not,
                    Some(TyKind::EUReal),
                    builder.unary(UnOpKind::Embed, Some(TyKind::EUReal), init_invariant),
                )),
                ProcSpec::Requires(builder.cast(TyKind::EUReal, init_variant)),
                ProcSpec::Ensures(builder.binary(
                    BinOpKind::Mul,
                    Some(TyKind::EUReal),
                    builder.unary(UnOpKind::Iverson, Some(TyKind::EUReal), loop_guard.clone()),
                    builder.cast(TyKind::EUReal, self.variant.clone()),
                )),
            ],
            body: Spanned::new(span, body),
            direction: Direction::Up,
        };

        generate_proc(span, proc_info, self.env.base_proc_ident, self.tcx)
    }

    fn encode_progress(&self, loop_guard: &Expr, loop_body: &Block) -> DeclKind {
        let span = self.env.call_span;
        let builder = ExprBuilder::new(span);

        let init_variant = to_init_expr(self.tcx, span, self.variant, &self.modified_vars);
        let init_invariant = to_init_expr(self.tcx, span, self.invariant, &self.modified_vars);
        let init_guard = to_init_expr(self.tcx, span, loop_guard, &self.modified_vars);
        let init_prob = builder.subst(self.prob.clone(), [(self.free_var, init_variant.clone())]);
        let invariant_pre = builder.unary(UnOpKind::Embed, Some(TyKind::EUReal), init_invariant);
        let guard_pre = builder.unary(UnOpKind::Embed, Some(TyKind::EUReal), init_guard);

        // [!G || V + d(V(init)) <= V(init)]
        let post = builder.unary(
            UnOpKind::Iverson,
            Some(TyKind::EUReal),
            builder.binary(
                BinOpKind::Or,
                Some(TyKind::Bool),
                builder.unary(UnOpKind::Not, Some(TyKind::Bool), loop_guard.clone()),
                builder.binary(
                    BinOpKind::Le,
                    Some(TyKind::Bool),
                    builder.binary(
                        BinOpKind::Add,
                        Some(TyKind::UReal),
                        self.variant.clone(),
                        builder.subst(
                            self.decrease.clone(),
                            [(self.free_var, init_variant.clone())],
                        ),
                    ),
                    init_variant,
                ),
            ),
        );

        let mut body = self.init_assigns.clone();
        body.extend(loop_body.node.clone());

        let proc_info = ProcInfo {
            name: "progress_condition".to_string(),
            inputs: params_from_idents(self.input_init_vars.clone(), self.tcx),
            outputs: params_from_idents(self.modified_vars.clone(), self.tcx),
            spec: vec![
                ProcSpec::Requires(invariant_pre),
                ProcSpec::Requires(guard_pre),
                ProcSpec::Requires(builder.cast(TyKind::EUReal, init_prob)),
                ProcSpec::Ensures(post),
            ],
            body: Spanned::new(span, body),
            direction: Direction::Down,
        };

        generate_proc(span, proc_info, self.env.base_proc_ident, self.tcx)
    }
}

/// Check that loop bodies use only demonic nondeterminism.
struct AstBodyValidator<'tcx> {
    tcx: &'tcx TyCtx,
    annotation_name: Ident,
    call_span: Span,
    diagnostics: Vec<Diagnostic>,
}

impl AstBodyValidator<'_> {
    fn unsupported(
        &self,
        statement_span: Span,
        message: &str,
        note: Option<&'static str>,
    ) -> AnnotationError {
        AnnotationError::UnsupportedStatement {
            span: self.call_span,
            annotation_name: self.annotation_name,
            statement_span,
            message: message.to_owned(),
            note,
        }
    }
}

impl VisitorMut for AstBodyValidator<'_> {
    type Err = AnnotationError;

    fn visit_stmt(&mut self, stmt: &mut Stmt) -> Result<(), Self::Err> {
        let choice_note = Some("Only probabilistic or demonic choices are allowed.");
        let error = match &stmt.node {
            StmtKind::Angelic(_, _) => Some(("Angelic choice is not allowed.", choice_note)),
            StmtKind::Additive(_, _) => Some(("Additive choice is not allowed.", choice_note)),
            StmtKind::Havoc(Direction::Up, _) => {
                Some(("Angelic havoc is not allowed.", choice_note))
            }
            StmtKind::Havoc(Direction::Down, variables) => {
                let labels: Vec<_> = variables
                    .iter()
                    .filter_map(|ident| {
                        let decl = self.tcx.get(*ident).unwrap();
                        let DeclKind::VarDecl(var) = decl.as_ref() else {
                            unreachable!("havoc variables have been typechecked")
                        };
                        let ty = &var.borrow().ty;
                        (*ty != TyKind::Bool).then(|| {
                            Label::new(stmt.span).with_message(format!(
                                "`{ident}` has type `{ty}`, which is not known to be finite."
                            ))
                        })
                    })
                    .collect();
                if !labels.is_empty() {
                    self.diagnostics.push(
                        Diagnostic::new(ReportKind::Warning, stmt.span)
                            .with_message("Havoc domain may be infinite")
                            .with_labels(labels)
                            .with_note("`@ast` requires finite nondeterminism."),
                    );
                }
                None
            }
            StmtKind::Var(var) if var.borrow().init.is_none() => Some((
                "Loop-local variables must be initialized.",
                Some("`@ast` requires explicit `havoc` for demonic nondeterminism."),
            )),
            _ => None,
        };
        if let Some((message, note)) = error {
            return Err(self.unsupported(stmt.span, message, note));
        }
        walk_stmt(self, stmt)
    }

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        if let ExprKind::Call(ident, _) = &expr.kind {
            if matches!(
                self.tcx.get(*ident).unwrap().as_ref(),
                DeclKind::ProcDecl(_)
            ) {
                return Err(self.unsupported(expr.span, "Procedure calls are not allowed.", None));
            }
        }
        walk_expr(self, expr)
    }
}

/// Switch demonic choices to angelic choices for `awp`.
struct AwpEncoder;

impl VisitorMut for AwpEncoder {
    type Err = ();

    fn visit_stmt(&mut self, stmt: &mut Stmt) -> Result<(), Self::Err> {
        walk_stmt(self, stmt)?;
        match &mut stmt.node {
            StmtKind::Demonic(lhs, rhs) => {
                stmt.node = StmtKind::Angelic(lhs.clone(), rhs.clone());
            }
            StmtKind::Havoc(direction @ Direction::Down, _) => *direction = Direction::Up,
            _ => {}
        }
        Ok(())
    }
}
