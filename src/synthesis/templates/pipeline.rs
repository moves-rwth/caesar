use crate::{
    ast::{
        util::remove_casts,
        visit::{walk_expr, VisitorMut},
        BinOpKind, DeclKind, Expr, ExprBuilder, ExprData, ExprKind, Ident, Shared, Span, TyKind,
    },
    driver::{
        error::CaesarError,
        item::SourceUnitName,
        quant_proof::{lower_quant_prove_task, BoolVcProveTask, QuantVcProveTask},
    },
    opt::unfolder::Unfolder,
    smt::{
        funcs::axiomatic::AxiomaticFunctionEncoder, translate_exprs::TranslateExprs,
        uninterpreted::FuncEntry, DepConfig, SmtCtx,
    },
    synthesis::{cegis::get_synth_functions, report::SynthStats},
    tyctx::TyCtx,
};

fn wrap_with_subst(body: Expr, parameters: &[Ident], args: &[Expr], span: Span) -> Expr {
    let mut wrapped = body;
    for (parameter, actual_expr) in parameters.iter().zip(args.iter()) {
        let ty = wrapped.ty.clone();
        let inner = wrapped;
        wrapped = Shared::new(ExprData {
            kind: ExprKind::Subst(*parameter, actual_expr.clone(), inner),
            ty,
            span,
        });
    }
    wrapped
}

pub struct FunctionInliner<'smt, 'ctx> {
    pub target: Ident,
    pub entry: &'ctx FuncEntry<'ctx>,
    pub body: &'ctx Expr,
    pub tcx: &'smt TyCtx,
    inlining_stack: Vec<Ident>,
}

impl<'smt, 'ctx> FunctionInliner<'smt, 'ctx> {
    pub fn new(
        target: Ident,
        entry: &'ctx FuncEntry<'ctx>,
        body: &'ctx Expr,
        tcx: &'smt TyCtx,
    ) -> Self {
        Self {
            target,
            entry,
            body,
            tcx,
            inlining_stack: Vec::new(),
        }
    }
}

impl<'smt, 'ctx> VisitorMut for FunctionInliner<'smt, 'ctx> {
    type Err = ();

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        let span = expr.span;
        match &mut expr.kind {
            ExprKind::Call(func_ident, args) if *func_ident == self.target => {
                let param_idents: Vec<Ident> =
                    self.entry.inputs.node.iter().map(|p| p.name).collect();
                *expr = wrap_with_subst(self.body.clone(), &param_idents, args, span);
                Ok(())
            }
            ExprKind::Call(func_ident, args) => {
                if self.inlining_stack.contains(func_ident) {
                    return walk_expr(self, expr);
                }
                if let Some(DeclKind::FuncDecl(func_ref)) = self.tcx.get(*func_ident).as_deref() {
                    let func = func_ref.borrow();
                    let body_opt = func.body.borrow();
                    let param_idents: Vec<Ident> =
                        func.inputs.node.iter().map(|p| p.name).collect();
                    if let Some(body_expr) = body_opt.clone() {
                        self.inlining_stack.push(*func_ident);
                        let mut wrapped = wrap_with_subst(body_expr, &param_idents, args, span);
                        let result = self.visit_expr(&mut wrapped);
                        self.inlining_stack.pop();
                        result?;
                        *expr = wrapped;
                        return Ok(());
                    }
                    return walk_expr(self, expr);
                }
                walk_expr(self, expr)
            }
            _ => walk_expr(self, expr),
        }
    }
}
use super::{build_template_expression, TemplateConfig, TemplateEntry, TemplateResult};
use std::time::Instant;

type TemplatesResult = Result<(Vec<TemplateEntry>, Vec<(Ident, TyKind)>), CaesarError>;

/// Build a template for every synth function, cross-inline them into each other,
/// inline the results into the VC, and conjoin nonnegativity constraints.
/// Modifies `vc_expr` and `vc_is_valid` in place; returns the template list and
/// collected template variable bindings.
pub fn build_and_inline_templates<'smt, 'ctx>(
    translate: &mut TranslateExprs<'smt, 'ctx>,
    vc_expr: &mut QuantVcProveTask,
    vc_is_valid: &mut BoolVcProveTask,
    config: &TemplateConfig<'_>,
    name: &SourceUnitName,
    stats: &mut SynthStats,
) -> TemplatesResult {
    let smt_ctx = translate.ctx;
    let synth_funcs = get_synth_functions(smt_ctx.uninterpreteds());
    if synth_funcs.is_empty() {
        return Ok((Vec::new(), Vec::new()));
    }

    let mut builder = ExprBuilder::new(Span::dummy_span());
    let mut templates: Vec<TemplateEntry> = Vec::new();
    let mut tvars: Vec<(Ident, TyKind)> = Vec::new();

    let tcx = translate.ctx.tcx();

    // Build a template for each synthesised function.
    for (synth_name, synth_val) in synth_funcs.iter() {
        let start_template = Instant::now();

        let mut vc_unfolded = vc_expr.expr.clone();
        Unfolder::new(config.limits_ref.clone(), smt_ctx).visit_expr(&mut vc_unfolded)?;

        let TemplateResult {
            expr: template,
            template_idents: tvar_idents,
            guards_before_pruning,
            guards_after_pruning,
            num_sat_checks,
            loop_mode,
        } = build_template_expression(
            config,
            synth_name,
            synth_val,
            &vc_expr.expr,
            &mut builder,
            translate,
            &vc_unfolded,
        );

        stats.template_sat_checks += num_sat_checks;
        let elapsed_template = start_template.elapsed();
        stats.duration_template_build += elapsed_template;
        tvars.extend(tvar_idents);

        // Unfold the template before storing it.
        let ctx_local = z3::Context::new(&z3::Config::default());
        let smt_ctx_local = SmtCtx::new(
            &ctx_local,
            tcx,
            Box::new(AxiomaticFunctionEncoder::default()),
            DepConfig::SpecsOnly,
        );
        let mut template_expr = template;
        Unfolder::new(config.limits_ref.clone(), &smt_ctx_local).visit_expr(&mut template_expr)?;

        if config.options.synth_options.syn_benchmarks {
            println!(
                "Template building for `{}` took: {:.2}s",
                synth_name,
                elapsed_template.as_secs_f64()
            );
        }
        if config.options.synth_options.print_template {
            println!(
                "template for `{}`: {}",
                synth_name,
                remove_casts(&template_expr)
            );
        }
        templates.push(TemplateEntry {
            synth_name: *synth_name,
            expr: template_expr,
            guards_before_pruning,
            guards_after_pruning,
            loop_mode,
        });
    }

    // Cross-inline templates into one another (single pass; synth functions are non-recursive).
    let ctx_local = z3::Context::new(&z3::Config::default());
    let smt_ctx_local = SmtCtx::new(
        &ctx_local,
        tcx,
        Box::new(AxiomaticFunctionEncoder::default()),
        DepConfig::SpecsOnly,
    );
    for i in 0..templates.len() {
        let other_templates: Vec<(Ident, Expr)> = templates
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != i)
            .map(|(_, t)| (t.synth_name, t.expr.clone()))
            .collect();
        for (func_ident, other_template) in &other_templates {
            let func_entry = synth_funcs
                .get(func_ident)
                .expect("synth function disappeared during cross-inlining");
            FunctionInliner::new(*func_ident, func_entry, other_template, tcx)
                .visit_expr(&mut templates[i].expr)
                .unwrap();
        }
        Unfolder::new(config.limits_ref.clone(), &smt_ctx_local)
            .visit_expr(&mut templates[i].expr)?;
    }

    // Inline all templates into the main VC.
    for t in templates.iter() {
        let func_entry = synth_funcs
            .get(&t.synth_name)
            .expect("synth function disappeared before VC inlining");
        FunctionInliner::new(t.synth_name, func_entry, &t.expr, tcx)
            .visit_expr(&mut vc_expr.expr)
            .unwrap();
    }

    *vc_is_valid = lower_quant_prove_task(
        config.options,
        config.limits_ref,
        tcx,
        name,
        vc_expr.clone(),
    )?;

    // Conjoin template >= 0 for each synthesised function.
    for t in &templates {
        let template_expr = &t.expr;
        let Some(ty) = template_expr.ty.clone() else {
            continue;
        };
        let zero = builder.zero_lit(&ty);
        let constraint = builder.binary(
            BinOpKind::Ge,
            Some(TyKind::Bool),
            template_expr.clone(),
            zero,
        );
        vc_is_valid.vc = builder.binary(
            BinOpKind::And,
            Some(TyKind::Bool),
            vc_is_valid.vc.clone(),
            constraint,
        );
    }

    Ok((templates, tvars))
}
