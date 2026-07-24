use crate::{
    ast::{
        visit::{walk_expr, walk_stmt, VisitorMut},
        BinOpKind, DeclKind, Direction, Expr, ExprBuilder, ExprData, ExprKind, Ident, Shared, Span,
        Spanned, Stmt, StmtKind, TyKind, UnOpKind,
    },
    tyctx::TyCtx,
};

// Collects every call expression `f(args)` where `f` is one of the target
// functions, anywhere inside a walked expression.
struct CallCollector<'a> {
    funcs: &'a [Ident],
    tcx: &'a TyCtx,
    calls: Vec<Expr>,
}

impl<'a> CallCollector<'a> {
    fn new(funcs: &'a [Ident], tcx: &'a TyCtx) -> Self {
        Self {
            funcs,
            tcx,
            calls: Vec::new(),
        }
    }

    /// Returns true if `func` is a `FuncDecl` with a defining body (as opposed to uninterpreted).
    fn has_body(&self, func: &Ident) -> bool {
        self.tcx
            .get(*func)
            .and_then(|decl| {
                if let DeclKind::FuncDecl(func_ref) = decl.as_ref() {
                    Some(func_ref.borrow().body.borrow().is_some())
                } else {
                    None
                }
            })
            .unwrap_or(false)
    }
}

impl<'a> VisitorMut for CallCollector<'a> {
    type Err = ();

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        if let ExprKind::Call(ref func, _) = e.kind {
            if self.funcs.contains(func) && self.has_body(func) {
                self.calls.push(e.clone());
                // Don't recurse: this call's definedness guard already covers
                // any nested calls by inlining the body.
                return Ok(());
            }
        }
        walk_expr(self, e)
    }
}

// Substitutes every free occurrence of `var` with `val` in an expression,
// stopping at binders that shadow `var` (capture-avoiding).
struct SubstVisitor<'a> {
    var: Ident,
    val: &'a Expr,
}

impl<'a> VisitorMut for SubstVisitor<'a> {
    type Err = ();

    fn visit_expr(&mut self, e: &mut Expr) -> Result<(), Self::Err> {
        enum Action {
            Replace,
            SubstValOnly,
            BodyOnly,
            Skip,
            Walk,
        }
        let action = match &e.kind {
            ExprKind::Var(v) if *v == self.var => Action::Replace,
            ExprKind::Subst(bound, _, _) if *bound == self.var => Action::SubstValOnly,
            ExprKind::Quant(_, qvars, _, _) if qvars.iter().any(|qv| qv.name() == self.var) => {
                Action::Skip
            }
            ExprKind::Quant(..) => Action::BodyOnly,
            _ => Action::Walk,
        };
        match action {
            Action::Replace => *e = self.val.clone(),
            Action::SubstValOnly => {
                if let ExprKind::Subst(_, by, _) = &mut e.kind {
                    self.visit_expr(by)?;
                }
            }
            Action::BodyOnly => {
                if let ExprKind::Quant(_, _, _, body) = &mut e.kind {
                    self.visit_expr(body)?;
                }
            }
            Action::Skip => {}
            Action::Walk => walk_expr(self, e)?,
        }
        Ok(())
    }
}

fn subst_var(expr: &Expr, var: &Ident, val: &Expr) -> Expr {
    let mut result = expr.clone();
    SubstVisitor { var: *var, val }
        .visit_expr(&mut result)
        .unwrap();
    result
}

// Returns the body (if any) and formal parameter names of `func` from `tcx`.
fn get_func_body_params(func: &Ident, tcx: &TyCtx) -> Option<(Option<Expr>, Vec<Ident>)> {
    tcx.get(*func).and_then(|decl| {
        if let DeclKind::FuncDecl(func_ref) = decl.as_ref() {
            let func_decl = func_ref.borrow();
            let body = func_decl.body.borrow().clone();
            let params = func_decl.inputs.node.iter().map(|p| p.name).collect();
            Some((body, params))
        } else {
            None
        }
    })
}

// Compute the fuel-limited approximant e^fuel of `expr` (def:approxexpr):
// replace each call to a target function with its inlined body, recursing at
// fuel-1, and leave the call node as-is when fuel is exhausted (f^0).
fn approx_expr(expr: &Expr, fuel: usize, func_idents: &[Ident], tcx: &TyCtx) -> Expr {
    let builder = ExprBuilder::new(expr.span);

    match &expr.kind {
        ExprKind::Call(func, args) if func_idents.contains(func) => {
            let body_params = get_func_body_params(func, tcx);

            match body_params {
                Some((Some(body), params)) if fuel > 0 => {
                    let mut inst_body = body;
                    for (param, arg) in params.iter().zip(args.iter()) {
                        inst_body = subst_var(&inst_body, param, arg);
                    }
                    approx_expr(&inst_body, fuel - 1, func_idents, tcx)
                }
                // Fuel exhausted or no body: return the call node unchanged (f^0).
                _ => expr.clone(),
            }
        }

        ExprKind::Var(_) | ExprKind::Call(_, _) | ExprKind::Lit(_) => expr.clone(),

        ExprKind::Ite(cond, then_, else_) => {
            let then_approx = approx_expr(then_, fuel, func_idents, tcx);
            let else_approx = approx_expr(else_, fuel, func_idents, tcx);
            builder.ite(expr.ty.clone(), cond.clone(), then_approx, else_approx)
        }

        ExprKind::Binary(bin_op, lhs, rhs) => {
            let lhs_approx = approx_expr(lhs, fuel, func_idents, tcx);
            let rhs_approx = approx_expr(rhs, fuel, func_idents, tcx);
            builder.binary(bin_op.node, expr.ty.clone(), lhs_approx, rhs_approx)
        }

        ExprKind::Unary(un_op, inner) => {
            let inner_approx = approx_expr(inner, fuel, func_idents, tcx);
            builder.unary(un_op.node, expr.ty.clone(), inner_approx)
        }

        ExprKind::Cast(inner) => {
            let inner_approx = approx_expr(inner, fuel, func_idents, tcx);
            Shared::new(ExprData {
                kind: ExprKind::Cast(inner_approx),
                ty: expr.ty.clone(),
                span: expr.span,
            })
        }

        ExprKind::Subst(bound, subst_val, body) => {
            let subst_body = subst_var(body, bound, subst_val);
            approx_expr(&subst_body, fuel, func_idents, tcx)
        }

        ExprKind::Quant(quant, vars, triggers, body) => {
            let body_approx = approx_expr(body, fuel, func_idents, tcx);
            Shared::new(ExprData {
                kind: ExprKind::Quant(*quant, vars.clone(), triggers.clone(), body_approx),
                ty: expr.ty.clone(),
                span: expr.span,
            })
        }
    }
}

fn cast_to_eureal(expr: Expr) -> Expr {
    if expr.ty.as_ref() == Some(&TyKind::EUReal) {
        return expr;
    }
    let span = expr.span;
    Shared::new(ExprData {
        kind: ExprKind::Cast(expr),
        ty: Some(TyKind::EUReal),
        span,
    })
}

// Compute the Boolean guard B_k(b) for a Boolean sub-expression b.
// B_k(b) is true iff the fuel-k approximant of b does not bottom out (\bot).
// Mirrors the short-circuit semantics of Boolean operators:
//   - && has absorber false: one false operand makes the conjunction defined.
//   - || has absorber true:  one true  operand makes the disjunction defined.
fn bool_definedness_guard(expr: &Expr, fuel: usize, func_idents: &[Ident], tcx: &TyCtx) -> Expr {
    let builder = ExprBuilder::new(expr.span);

    match &expr.kind {
        // Literals and variables are always defined.
        ExprKind::Lit(_) | ExprKind::Var(_) => builder.bool_lit(true),

        // Comparison (a1 op a2): both quantitative operands must be defined.
        ExprKind::Binary(bin_op, lhs, rhs)
            if matches!(
                bin_op.node,
                BinOpKind::Eq
                    | BinOpKind::Ne
                    | BinOpKind::Lt
                    | BinOpKind::Le
                    | BinOpKind::Ge
                    | BinOpKind::Gt
            ) =>
        {
            let lhs_def = definedness_guard(lhs, fuel, func_idents, tcx);
            let rhs_def = definedness_guard(rhs, fuel, func_idents, tcx);
            builder.binary(BinOpKind::And, Some(TyKind::Bool), lhs_def, rhs_def)
        }

        // Boolean conjunction (b1 && b2): absorber is false.
        // B_k(b1 && b2) = (B_k(b1) && b1_approx=false)
        //                || (B_k(b2) && b2_approx=false)
        //                || (B_k(b1) && B_k(b2))
        ExprKind::Binary(bin_op, lhs, rhs) if bin_op.node == BinOpKind::And => {
            let lhs_approx = approx_expr(lhs, fuel, func_idents, tcx);
            let rhs_approx = approx_expr(rhs, fuel, func_idents, tcx);
            let lhs_def = bool_definedness_guard(lhs, fuel, func_idents, tcx);
            let rhs_def = bool_definedness_guard(rhs, fuel, func_idents, tcx);
            let false_lit = builder.bool_lit(false);
            let lhs_is_false = builder.binary(
                BinOpKind::Eq,
                Some(TyKind::Bool),
                lhs_approx,
                false_lit.clone(),
            );
            let rhs_is_false =
                builder.binary(BinOpKind::Eq, Some(TyKind::Bool), rhs_approx, false_lit);
            let lhs_absorbed = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                lhs_def.clone(),
                lhs_is_false,
            );
            let rhs_absorbed = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                rhs_def.clone(),
                rhs_is_false,
            );
            let both_def = builder.binary(BinOpKind::And, Some(TyKind::Bool), lhs_def, rhs_def);
            let one_absorbed = builder.binary(
                BinOpKind::Or,
                Some(TyKind::Bool),
                lhs_absorbed,
                rhs_absorbed,
            );
            builder.binary(BinOpKind::Or, Some(TyKind::Bool), one_absorbed, both_def)
        }

        // Boolean disjunction (b1 || b2): absorber is true.
        // B_k(b1 || b2) = (B_k(b1) && b1_approx=true)
        //                || (B_k(b2) && b2_approx=true)
        //                || (B_k(b1) && B_k(b2))
        ExprKind::Binary(bin_op, lhs, rhs) if bin_op.node == BinOpKind::Or => {
            let lhs_approx = approx_expr(lhs, fuel, func_idents, tcx);
            let rhs_approx = approx_expr(rhs, fuel, func_idents, tcx);
            let lhs_def = bool_definedness_guard(lhs, fuel, func_idents, tcx);
            let rhs_def = bool_definedness_guard(rhs, fuel, func_idents, tcx);
            let true_lit = builder.bool_lit(true);
            let lhs_is_true = builder.binary(
                BinOpKind::Eq,
                Some(TyKind::Bool),
                lhs_approx,
                true_lit.clone(),
            );
            let rhs_is_true =
                builder.binary(BinOpKind::Eq, Some(TyKind::Bool), rhs_approx, true_lit);
            let lhs_absorbed = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                lhs_def.clone(),
                lhs_is_true,
            );
            let rhs_absorbed = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                rhs_def.clone(),
                rhs_is_true,
            );
            let both_def = builder.binary(BinOpKind::And, Some(TyKind::Bool), lhs_def, rhs_def);
            let one_absorbed = builder.binary(
                BinOpKind::Or,
                Some(TyKind::Bool),
                lhs_absorbed,
                rhs_absorbed,
            );
            builder.binary(BinOpKind::Or, Some(TyKind::Bool), one_absorbed, both_def)
        }

        // Boolean negation (!b): propagate through.
        ExprKind::Unary(un_op, inner) if un_op.node == UnOpKind::Not => {
            bool_definedness_guard(inner, fuel, func_idents, tcx)
        }

        // Subst: apply substitution and recurse.
        ExprKind::Subst(bound, subst_val, body) => {
            let subst_body = subst_var(body, bound, subst_val);
            bool_definedness_guard(&subst_body, fuel, func_idents, tcx)
        }

        // Anything else (calls, other unary, quantifiers): delegate to G_k.
        _ => definedness_guard(expr, fuel, func_idents, tcx),
    }
}

// Compute the quantitative definedness guard G_k(e) for expression e (def:defguard).
// G_k(e) is true iff the fuel-k approximant e^k does not bottom out (\bot).
// Mirrors the \bot-extended semantics of quantitative operators (def:botabsorption):
//   - * and \sqcap have absorber 0:    one zero operand makes the result defined.
//   - \sqcup has absorber \infty:      one infinite operand makes the result defined.
//   - -> has absorbers 0 (left) and \infty (right).
//   - <-  has absorbers \infty (left) and 0 (right).
// ITE additionally requires B_k on the condition, then guards only the selected branch.
// Target function calls recurse at fuel-1; at fuel 0 the call returns \bot, so G_0 = false.
fn definedness_guard(expr: &Expr, fuel: usize, func_idents: &[Ident], tcx: &TyCtx) -> Expr {
    let builder = ExprBuilder::new(expr.span);

    match &expr.kind {
        // Target function call: inline (if body exists) or mark as \bot.
        // Functions without a body (synthesis constants) are always defined.
        ExprKind::Call(func, args) if func_idents.contains(func) => {
            let body_params = get_func_body_params(func, tcx);

            match body_params {
                Some((Some(body), params)) => {
                    if fuel == 0 {
                        builder.bool_lit(false) // \bot: fuel exhausted
                    } else {
                        let mut inst_body = body;
                        for (param, arg) in params.iter().zip(args.iter()) {
                            inst_body = subst_var(&inst_body, param, arg);
                        }
                        definedness_guard(&inst_body, fuel - 1, func_idents, tcx)
                    }
                }
                // No body (synthesis constant) or not found: always defined.
                _ => builder.bool_lit(true),
            }
        }

        // Variables, non-target calls, and literals (including infinity) are always defined.
        ExprKind::Var(_) | ExprKind::Call(_, _) | ExprKind::Lit(_) => builder.bool_lit(true),

        // ITE: condition must be defined (B_k), and the selected branch must be defined (G_k).
        ExprKind::Ite(cond, then_, else_) => {
            let cond_def = bool_definedness_guard(cond, fuel, func_idents, tcx);
            let then_def = definedness_guard(then_, fuel, func_idents, tcx);
            let else_def = definedness_guard(else_, fuel, func_idents, tcx);
            let branch_def = builder.ite(Some(TyKind::Bool), cond.clone(), then_def, else_def);
            builder.binary(BinOpKind::And, Some(TyKind::Bool), cond_def, branch_def)
        }

        // Multiplication and infimum (\cap): absorber is 0.
        // Defined if: (G_k(lhs) && lhs_approx=0) || (G_k(rhs) && rhs_approx=0)
        //             || (G_k(lhs) && G_k(rhs))
        ExprKind::Binary(bin_op, lhs, rhs)
            if matches!(bin_op.node, BinOpKind::Mul | BinOpKind::Inf) =>
        {
            let lhs_approx = approx_expr(lhs, fuel, func_idents, tcx);
            let rhs_approx = approx_expr(rhs, fuel, func_idents, tcx);
            let lhs_def = definedness_guard(lhs, fuel, func_idents, tcx);
            let rhs_def = definedness_guard(rhs, fuel, func_idents, tcx);
            let ty = lhs
                .ty
                .as_ref()
                .or(rhs.ty.as_ref())
                .unwrap_or(&TyKind::EUReal);
            let zero = builder.zero_lit(ty);
            let lhs_is_zero =
                builder.binary(BinOpKind::Eq, Some(TyKind::Bool), lhs_approx, zero.clone());
            let rhs_is_zero = builder.binary(BinOpKind::Eq, Some(TyKind::Bool), rhs_approx, zero);
            let lhs_absorbed = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                lhs_def.clone(),
                lhs_is_zero,
            );
            let rhs_absorbed = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                rhs_def.clone(),
                rhs_is_zero,
            );
            let both_def = builder.binary(BinOpKind::And, Some(TyKind::Bool), lhs_def, rhs_def);
            let one_absorbed = builder.binary(
                BinOpKind::Or,
                Some(TyKind::Bool),
                lhs_absorbed,
                rhs_absorbed,
            );
            builder.binary(BinOpKind::Or, Some(TyKind::Bool), one_absorbed, both_def)
        }

        // Supremum (\cup): absorber is infinity.
        // Defined if: (G_k(lhs) && lhs_approx=infinity) || (G_k(rhs) && rhs_approx=infinity)
        //             || (G_k(lhs) && G_k(rhs))
        ExprKind::Binary(bin_op, lhs, rhs) if bin_op.node == BinOpKind::Sup => {
            let lhs_approx = cast_to_eureal(approx_expr(lhs, fuel, func_idents, tcx));
            let rhs_approx = cast_to_eureal(approx_expr(rhs, fuel, func_idents, tcx));
            let lhs_def = definedness_guard(lhs, fuel, func_idents, tcx);
            let rhs_def = definedness_guard(rhs, fuel, func_idents, tcx);
            let inf = builder.infinity_lit();
            let lhs_is_inf =
                builder.binary(BinOpKind::Eq, Some(TyKind::Bool), lhs_approx, inf.clone());
            let rhs_is_inf = builder.binary(BinOpKind::Eq, Some(TyKind::Bool), rhs_approx, inf);
            let lhs_absorbed = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                lhs_def.clone(),
                lhs_is_inf,
            );
            let rhs_absorbed = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                rhs_def.clone(),
                rhs_is_inf,
            );
            let both_def = builder.binary(BinOpKind::And, Some(TyKind::Bool), lhs_def, rhs_def);
            let one_absorbed = builder.binary(
                BinOpKind::Or,
                Some(TyKind::Bool),
                lhs_absorbed,
                rhs_absorbed,
            );
            builder.binary(BinOpKind::Or, Some(TyKind::Bool), one_absorbed, both_def)
        }

        // Implication (->): left absorber is 0, right absorber is infinity.
        // Defined if: (G_k(lhs) && lhs_approx=0) || (G_k(rhs) && rhs_approx=infinity)
        //             || (G_k(lhs) && G_k(rhs))
        ExprKind::Binary(bin_op, lhs, rhs) if bin_op.node == BinOpKind::Impl => {
            let lhs_approx = approx_expr(lhs, fuel, func_idents, tcx);
            let rhs_approx = cast_to_eureal(approx_expr(rhs, fuel, func_idents, tcx));
            let lhs_def = definedness_guard(lhs, fuel, func_idents, tcx);
            let rhs_def = definedness_guard(rhs, fuel, func_idents, tcx);
            let ty = lhs
                .ty
                .as_ref()
                .or(rhs.ty.as_ref())
                .unwrap_or(&TyKind::EUReal);
            let zero = builder.zero_lit(ty);
            let inf = builder.infinity_lit();
            let lhs_is_zero = builder.binary(BinOpKind::Eq, Some(TyKind::Bool), lhs_approx, zero);
            let rhs_is_inf = builder.binary(BinOpKind::Eq, Some(TyKind::Bool), rhs_approx, inf);
            let lhs_absorbed = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                lhs_def.clone(),
                lhs_is_zero,
            );
            let rhs_absorbed = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                rhs_def.clone(),
                rhs_is_inf,
            );
            let both_def = builder.binary(BinOpKind::And, Some(TyKind::Bool), lhs_def, rhs_def);
            let one_absorbed = builder.binary(
                BinOpKind::Or,
                Some(TyKind::Bool),
                lhs_absorbed,
                rhs_absorbed,
            );
            builder.binary(BinOpKind::Or, Some(TyKind::Bool), one_absorbed, both_def)
        }

        // Co-implication (<-): left absorber is infinity, right absorber is 0.
        // Defined if: (G_k(lhs) && lhs_approx=infinity) || (G_k(rhs) && rhs_approx=0)
        //             || (G_k(lhs) && G_k(rhs))
        ExprKind::Binary(bin_op, lhs, rhs) if bin_op.node == BinOpKind::CoImpl => {
            let lhs_approx = cast_to_eureal(approx_expr(lhs, fuel, func_idents, tcx));
            let rhs_approx = approx_expr(rhs, fuel, func_idents, tcx);
            let lhs_def = definedness_guard(lhs, fuel, func_idents, tcx);
            let rhs_def = definedness_guard(rhs, fuel, func_idents, tcx);
            let ty = lhs
                .ty
                .as_ref()
                .or(rhs.ty.as_ref())
                .unwrap_or(&TyKind::EUReal);
            let zero = builder.zero_lit(ty);
            let inf = builder.infinity_lit();
            let lhs_is_inf = builder.binary(BinOpKind::Eq, Some(TyKind::Bool), lhs_approx, inf);
            let rhs_is_zero = builder.binary(BinOpKind::Eq, Some(TyKind::Bool), rhs_approx, zero);
            let lhs_absorbed = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                lhs_def.clone(),
                lhs_is_inf,
            );
            let rhs_absorbed = builder.binary(
                BinOpKind::And,
                Some(TyKind::Bool),
                rhs_def.clone(),
                rhs_is_zero,
            );
            let both_def = builder.binary(BinOpKind::And, Some(TyKind::Bool), lhs_def, rhs_def);
            let one_absorbed = builder.binary(
                BinOpKind::Or,
                Some(TyKind::Bool),
                lhs_absorbed,
                rhs_absorbed,
            );
            builder.binary(BinOpKind::Or, Some(TyKind::Bool), one_absorbed, both_def)
        }

        // All other binary operators: defined iff both operands are defined.
        ExprKind::Binary(_, lhs, rhs) => {
            let lhs_def = definedness_guard(lhs, fuel, func_idents, tcx);
            let rhs_def = definedness_guard(rhs, fuel, func_idents, tcx);
            builder.binary(BinOpKind::And, Some(TyKind::Bool), lhs_def, rhs_def)
        }

        // Boolean embedding ?(b), Iverson [b], and negation !b: delegate to B_k.
        ExprKind::Unary(un_op, inner)
            if matches!(
                un_op.node,
                UnOpKind::Embed | UnOpKind::Iverson | UnOpKind::Not
            ) =>
        {
            bool_definedness_guard(inner, fuel, func_idents, tcx)
        }

        // Other unary (Non, Parens, etc.): propagate through G_k.
        ExprKind::Unary(_, inner) => definedness_guard(inner, fuel, func_idents, tcx),

        // Cast: propagate through.
        ExprKind::Cast(inner) => definedness_guard(inner, fuel, func_idents, tcx),

        // Subst: substitute the value into the body, then check definedness.
        ExprKind::Subst(bound, subst_val, body) => {
            let subst_body = subst_var(body, bound, subst_val);
            definedness_guard(&subst_body, fuel, func_idents, tcx)
        }

        // Quant: propagate through the body.
        ExprKind::Quant(_, _, _, body) => definedness_guard(body, fuel, func_idents, tcx),
    }
}

/// Visitor that inserts `assume(embed(is_defined(call)))` statements before each recursive call,
/// guarding the CEGIS verification condition against fuel exhaustion.
pub struct InsertAssumeBeforeCalls<'a> {
    pub(crate) func_idents: &'a [Ident],
    pub(crate) direction: Direction,
    pub(crate) tcx: &'a TyCtx,
    /// How many recursive unrolling steps to perform when building the
    /// well-definedness guard.  Matches `--max-fuel` from the CLI options.
    pub(crate) max_fuel: usize,
}

impl<'a> InsertAssumeBeforeCalls<'a> {
    /// Collect every call to a target (recursive) function inside `e`.
    fn guarded_calls(&self, e: &Expr) -> Vec<Expr> {
        let mut collector = CallCollector::new(self.func_idents, self.tcx);
        let mut e_clone = e.clone();
        collector.visit_expr(&mut e_clone).unwrap();
        collector.calls
    }

    /// Emit `assume(embed(def_guard))` for each call, prepended before `original`.
    fn make_definedness_assumes(
        &self,
        span: Span,
        calls: Vec<Expr>,
        original: StmtKind,
    ) -> StmtKind {
        let builder = ExprBuilder::new(Span::dummy_span());
        let mut stmts = Vec::new();

        for call_expr in calls {
            // def_guard: the call is defined (does not bottom out due to fuel exhaustion).
            // definedness_guard returns false only when a recursive call exhausts
            // fuel, never when the function legitimately returns infinity.
            let mut def_guard =
                definedness_guard(&call_expr, self.max_fuel, self.func_idents, self.tcx);
            // In the coproc (Up) direction, assume uses dual semantics, so we negate.
            if self.direction == Direction::Up {
                def_guard = builder.unary(UnOpKind::Not, Some(TyKind::Bool), def_guard);
            }
            let assume_expr = builder.unary(UnOpKind::Embed, Some(TyKind::EUReal), def_guard);
            stmts.push(Spanned {
                span,
                node: StmtKind::Assume(self.direction, assume_expr),
            });
        }

        stmts.push(Spanned {
            span,
            node: original,
        });

        StmtKind::Seq(stmts)
    }
}

impl<'a> VisitorMut for InsertAssumeBeforeCalls<'a> {
    type Err = ();

    fn visit_stmt(&mut self, s: &mut Stmt) -> Result<(), Self::Err> {
        let span = s.span;

        // If/While: recurse into bodies first, then wrap calls from the condition.
        // The early return below would skip the body walk, so we handle these separately.
        if matches!(s.node, StmtKind::If(..) | StmtKind::While(..)) {
            let calls = match &s.node {
                StmtKind::If(cond, _, _) | StmtKind::While(cond, _) => self.guarded_calls(cond),
                _ => unreachable!(),
            };
            walk_stmt(self, s)?;
            if !calls.is_empty() {
                let original = std::mem::replace(&mut s.node, StmtKind::Seq(vec![]));
                s.node = self.make_definedness_assumes(span, calls, original);
            }
            return Ok(());
        }

        let calls: Vec<Expr> = match &s.node {
            StmtKind::Var(decl) => decl
                .borrow()
                .init
                .as_ref()
                .map(|e| self.guarded_calls(e))
                .unwrap_or_default(),

            StmtKind::Assign(_, e)
            | StmtKind::Assert(_, e)
            | StmtKind::Assume(_, e)
            | StmtKind::Compare(_, e)
            | StmtKind::Tick(e) => self.guarded_calls(e),

            _ => Vec::new(),
        };

        if !calls.is_empty() {
            let original = std::mem::replace(&mut s.node, StmtKind::Seq(vec![]));
            s.node = self.make_definedness_assumes(span, calls, original);
            return Ok(());
        }

        walk_stmt(self, s)
    }
}
