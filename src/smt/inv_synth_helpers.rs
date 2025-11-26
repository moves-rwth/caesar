use num::{BigInt, BigRational};
use z3rro::{
    eureal::ConcreteEUReal,
    model::{InstrumentedModel, SmtEval},
};

use crate::{
    ast::{
        self, BinOpKind, DeclRef, Direction, Expr, ExprBuilder, ExprData, ExprKind, Ident, Shared, Span, Symbol, TyKind, UnOpKind, VarDecl, VarKind, util::FreeVariableCollector, visit::{VisitorMut, walk_expr}
    }, depgraph::Dependencies, driver::quant_proof::{BoolVcProveTask, QuantVcProveTask}, smt::{
        symbolic::Symbolic,
        uninterpreted::{self, FuncEntry, Uninterpreteds},
    }, tyctx::TyCtx
};
use std::collections::{HashMap, HashSet};

// Takes a function and substitutes calls to that function with the functions body,
// substituting function parameters with the caller arguments
pub struct FunctionInliner<'ctx> {
    pub target: Ident,                // the function ident
    pub entry: &'ctx FuncEntry<'ctx>, // contains input params
    pub body: &'ctx Expr,             // the function body expression
}

impl<'a> VisitorMut for FunctionInliner<'a> {
    type Err = ();

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<(), Self::Err> {
        let span = expr.span;

        match &mut expr.kind {
            ExprKind::Call(func_ident, args) if *func_ident == self.target => {
                let parameters: Vec<Ident> =
                    self.entry.inputs.node.iter().map(|p| p.name).collect();

                let mut wrapped = self.body.clone();

                // Substitute arguments with which the function is called into the body
                for (parameter, actual_expr) in parameters.iter().zip(args.iter()) {
                    wrapped = Shared::new(ExprData {
                        kind: ExprKind::Subst(*parameter, actual_expr.clone(), wrapped.clone()),
                        ty: wrapped.ty.clone(),
                        span,
                    });
                }

                // Replace the call with the body wrapped in substitutions
                *expr = wrapped.clone();

                Ok(())
            }

            _ => walk_expr(self, expr),
        }
    }
}

// Translates a model into a map Ident -> Expression
pub fn create_subst_mapping<'ctx>(
    model: &InstrumentedModel<'ctx>,
    translate: &mut crate::smt::translate_exprs::TranslateExprs<'_, 'ctx>,
) -> HashMap<ast::symbol::Ident, Expr> {
    let builder = ExprBuilder::new(Span::dummy_span());
    let mut mapping = HashMap::new();

    let idents: Vec<_> = translate.local_idents().collect();

    for ident in idents {
        // Build a variable expression to feed into t_symbolic
        let var_expr = builder.var(ident.clone(), translate.ctx.tcx);
        let symbolic = translate.t_symbolic(&var_expr);

        let lit_opt = match &symbolic {
            Symbolic::Bool(v) => v.eval(model).ok().map(|b| builder.bool_lit(b)),

            Symbolic::Int(v) => v
                .eval(model)
                .ok()
                .map(|i: BigInt| builder.frac_lit(BigRational::from_integer(i))),

            Symbolic::UInt(v) => v.eval(model).ok().map(|i: BigInt| {
                if i >= BigInt::from(0) {
                    match u128::try_from(i.clone()) {
                        Ok(u) => builder.uint(u),
                        Err(_) => builder.frac_lit(BigRational::from_integer(i)),
                    }
                } else {
                    builder.frac_lit(BigRational::from_integer(i))
                }
            }),

            Symbolic::Real(v) => {
                let eval = v.eval(model);
                eval.ok().map(|r: BigRational| builder.signed_frac_lit(r))
            }

            Symbolic::UReal(v) => {
                let eval = v.eval(model);
                eval.ok().map(|r: BigRational| builder.frac_lit_not_extended(r))
            }

            Symbolic::EUReal(v) => v.eval(model).ok().map(|r| match r {
                ConcreteEUReal::Real(rat) => builder.frac_lit(rat),
                ConcreteEUReal::Infinity => builder.infinity_lit(),
            }),

            _ => None,
        };

        if let Some(ref lit) = lit_opt {
            mapping.insert(ident.clone(), lit.clone());
        }
    }

    mapping
}

/// "Instantiate" an expression with concrete values from a mapping.
/// To do this, wrap the expression in nested `Subst` expressions.
/// Then later tunfolding can take care of the actual substitutions.
pub fn subst_from_mapping<'ctx>(mapping: HashMap<ast::symbol::Ident, Expr>, vc: &Expr) -> Expr {
    let mut wrapped = vc.clone();
    for (ident, expr) in mapping {
        wrapped = Shared::new(ExprData {
            kind: ExprKind::Subst(ident, expr, wrapped.clone()),
            ty: wrapped.ty.clone(),
            span: vc.span,
        });
    }
    wrapped
}

// A helper function to build the templates
// returns (sum_(param_vars)( templ_var * param_var )) + templ_last
fn build_linear_combination(
    bool_idx: usize,
    synth_entry: &uninterpreted::FuncEntry,
    builder: &ExprBuilder,
    tcx: &TyCtx,
    declare_template_var: &mut dyn FnMut(String) -> Expr,
) -> Expr {
    let mut lin_comb: Option<Expr> = None; // used to accumulate the lin comb
                                           // TODO: currently this assumes that synth has only one entry
    for param in &synth_entry.inputs.node {
        let vardecl = VarDecl::from_param(param, VarKind::Input)
            .try_unwrap()
            .unwrap();

        // Create variable for parameter (and cast to Real)
        let mut variable = builder.var(vardecl.name, tcx);

        if vardecl.ty == TyKind::Bool {
            continue;
            // variable = builder.unary(UnOpKind::Iverson, Some(TyKind::Real), variable.clone());
        }

        variable = builder.cast(TyKind::Real, variable.clone());

        // Create template variable
        // Template var name
        let name = format!(
            "tvar{}_{}",
            bool_idx, vardecl.name.name
        );

        let templ = declare_template_var(name);

        // Parenthesize template var
        // TODO: this is only needed because fractions get parsed incorrectly:
        // a/b *c gets parsed as a/(b*c)
        let templ_paren = builder.unary(UnOpKind::Parens, Some(TyKind::Real), templ);

        // Multiply: templ * variable
        let prod = builder.binary(BinOpKind::Mul, Some(TyKind::Real), templ_paren, variable);

        // Accumulate sum
        lin_comb = Some(lin_comb.map_or(prod.clone(), |acc| {
            builder.binary(BinOpKind::Add, Some(TyKind::Real), acc, prod)
        }));
    }

    // Add the "last" summand
    let last = declare_template_var(format!(
        "tvar_{}_last",
        bool_idx
    ));

    let lin_comb_with_last = lin_comb.map_or(last.clone(), |acc| {
        builder.binary(BinOpKind::Add, Some(TyKind::Real), acc, last)
    });

    let clamp_with_zero_name = Ident::with_dummy_span(Symbol::intern("clamp_with_zero"));

    lin_comb = Some(Shared::new(ExprData {
        kind: ExprKind::Call(clamp_with_zero_name, vec![lin_comb_with_last.clone()]),
        ty: Some(TyKind::EUReal),

        span: Span::dummy_span(),
    }));
    lin_comb.unwrap()
}

fn all_assignments(n: usize) -> Vec<Vec<bool>> {
    let mut result = Vec::new();
    for mask in 0..(1 << n) {
        let mut v = Vec::with_capacity(n);
        for i in 0..n {
            v.push((mask & (1 << i)) != 0);
        }
        result.push(v);
    }
    result
}

// TODO: Currently this requires the variables to be named the same in both the function and the code
// Build a template by collecting boolean conditions that are "relevant", calcu
// and
pub fn build_template_expression(
    synth_val: &uninterpreted::FuncEntry,
    vc_expr: &Expr,
    builder: &ExprBuilder,
    tcx: &TyCtx,
) -> (Expr, Vec<Ident>) {
    let mut allowed_vars = HashSet::new();
    let mut template_idents = Vec::new();

    for param in &synth_val.inputs.node {
        let vardecl = VarDecl::from_param(param, VarKind::Input)
            .try_unwrap()
            .unwrap();
        allowed_vars.insert(vardecl.name.name);
    }

    // Get the conditions, filtered to those variables that appear as inputs of the function
    // TODO: this should be changed
    // But how?
    let bool_exprs: Vec<_> = vc_expr
        .collect_bool_conditions()
        .into_iter()
        .filter(|b| {
            let mut collector = FreeVariableCollector::new();
            let mut cloned = b.clone();
            let vars = collector.collect_and_clear(&mut cloned);
            vars.iter().all(|id| allowed_vars.contains(&id.name))
        })
        .collect();

    assert!(
        !bool_exprs.is_empty(),
        "No boolean expressions remain after filtering."
    );

    // Helper to declare a template variable and return its Expr
    let mut declare_template_var = |name: String| -> Expr {
        let ident = Ident::with_dummy_span(Symbol::intern(&name));
        let decl = VarDecl {
            name: ident,
            ty: TyKind::Real,
            kind: VarKind::Input,
            init: None,
            span: Span::dummy_span(),
            created_from: None,
        };
        tcx.declare(crate::ast::DeclKind::VarDecl(DeclRef::new(decl.clone())));
        template_idents.push(decl.name);
        builder.var(decl.name, tcx)
    };

    let mut final_expr: Option<Expr> = None;

    for (assign_idx, assignment) in all_assignments(bool_exprs.len()).into_iter().enumerate() {
        // 1. Build Π_j Iverson(b_j or ¬b_j)
        let mut iverson_prod = builder.bool_lit(true);

        for (j, &assign_val) in assignment.iter().enumerate() {
            let b = bool_exprs[j].clone();
            println!("expression: {b}");
            let cond = if assign_val {
                b
            } else {
                let not_b = builder.unary(UnOpKind::Not, Some(TyKind::Bool), b);
                not_b
            };

            iverson_prod = builder.binary(BinOpKind::And, Some(TyKind::Bool), iverson_prod, cond);
        }

//Direkt filtern

        iverson_prod = builder.unary(UnOpKind::Iverson, Some(TyKind::EUReal), iverson_prod);

        println!("iverson: {iverson_prod}");



        //  let refined_vc =
        //                 lower_quant_prove_task(options, &limits_ref, &tcx, name, refined_vc)?;

        //             // Translate again to SMT form
        //             vc_pvars = SmtVcProveTask::translate(refined_vc, &mut translate);



        // 2. Build a linear combination for this assignment
        let lc = build_linear_combination(
            assign_idx,
            synth_val,
            builder,
            tcx,
            &mut declare_template_var,
        );

        // 3. Multiply and accumulate
        let term = builder.binary(BinOpKind::Mul, Some(TyKind::EUReal), iverson_prod, lc);

        final_expr = Some(final_expr.map_or(term.clone(), |acc| {
            builder.binary(BinOpKind::Add, Some(TyKind::EUReal), acc, term)
        }));
    }

    (final_expr.unwrap(), template_idents)
}

pub fn get_synth_functions<'ctx>(
    un: &'ctx Uninterpreteds<'ctx>,
) -> HashMap<Ident, &'ctx uninterpreted::FuncEntry<'ctx>> {
    un.functions()
        .iter()
        .filter_map(|(id, f)| if f.syn { Some((id.clone(), f)) } else { None })
        .collect()
}
