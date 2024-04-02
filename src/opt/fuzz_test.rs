use proptest::{
    prelude::*,
    test_runner::{TestCaseResult, TestRunner},
};
use z3rro::prover::{ProveResult, Prover};

use crate::{
    ast::{
        BinOpKind, DeclKind, DeclRef, Expr, ExprBuilder, ExprData, ExprKind, Ident, LitKind,
        Shared, Span, Spanned, Symbol, TyKind, UnOpKind, VarDecl, VarKind,
    },
    smt::{translate_exprs::TranslateExprs, SmtCtx},
    tyctx::TyCtx,
};

/// Expression generator for Boolean and EUReal expressions.
struct ExprGen {
    bool_names: Vec<Ident>,
    eureal_names: Vec<Ident>,
    bool_exprs: Vec<Expr>,
    eureal_exprs: Vec<Expr>,
}

impl ExprGen {
    fn new() -> Self {
        let bool_names: Vec<Ident> = ["a", "b", "c", "d"]
            .iter()
            .map(|n| Ident::with_dummy_span(Symbol::intern(n)))
            .collect();
        let eureal_names: Vec<Ident> = ["f", "g", "h", "i", "j"]
            .iter()
            .map(|n| Ident::with_dummy_span(Symbol::intern(n)))
            .collect();
        let bool_exprs = bool_names
            .iter()
            .map(|name| ident_to_expr(*name, TyKind::Bool))
            .collect();
        let eureal_exprs = eureal_names
            .iter()
            .map(|name| ident_to_expr(*name, TyKind::EUReal))
            .collect();
        ExprGen {
            bool_names,
            eureal_names,
            bool_exprs,
            eureal_exprs,
        }
    }

    fn declare(&self, tcx: &mut TyCtx) {
        self.bool_names
            .iter()
            .zip(std::iter::repeat_with(|| TyKind::Bool))
            .chain(
                self.eureal_names
                    .iter()
                    .zip(std::iter::repeat_with(|| TyKind::EUReal)),
            )
            .for_each(|(name, ty)| {
                tcx.declare(DeclKind::VarDecl(DeclRef::new(VarDecl {
                    name: *name,
                    ty,
                    kind: VarKind::Input,
                    init: None,
                    span: Span::dummy_span(),
                    created_from: None,
                })))
            });
    }

    fn mk_strategy(&self) -> impl Strategy<Value = (Expr, Expr)> {
        let bool_leafs = prop_oneof![
            3 => lit_strategy(prop::bool::ANY.prop_map(|lit| LitKind::Bool(lit)), TyKind::Bool),
            1 => prop::sample::select(self.bool_exprs.clone()),
        ];
        let eureal_variables = prop::sample::select(self.eureal_exprs.clone());
        (bool_leafs, eureal_variables).prop_recursive(15, 20, 2, |inner| {
            let bool_element = inner.clone().prop_map(|(bool_expr, _)| bool_expr);
            let eureal_element = inner.prop_map(|(_, eureal_element)| eureal_element);
            let bool_strategy = prop_oneof![
                // negations
                unary_strategy(vec![UnOpKind::Not], TyKind::Bool, bool_element.clone()),
                // ite
                ite_strategy(bool_element.clone(), TyKind::Bool, bool_element.clone()),
                // and, or, impl
                binary_strategy(
                    vec![BinOpKind::And, BinOpKind::Or, BinOpKind::Impl],
                    TyKind::Bool,
                    bool_element.clone()
                ),
                // le, ge, lt, gt, eq between eureals
                binary_strategy(
                    vec![
                        BinOpKind::Le,
                        BinOpKind::Ge,
                        BinOpKind::Lt,
                        BinOpKind::Gt,
                        BinOpKind::Eq,
                    ],
                    TyKind::EUReal,
                    eureal_element.clone()
                )
            ];
            let eureal_strategy = prop_oneof![
                // embed
                unary_strategy(vec![UnOpKind::Embed], TyKind::EUReal, bool_element.clone()),
                // ite
                ite_strategy(bool_element.clone(), TyKind::EUReal, eureal_element.clone()),
                // not or non on eureals
                unary_strategy(
                    vec![UnOpKind::Not, UnOpKind::Non],
                    TyKind::EUReal,
                    eureal_element.clone()
                ),
                // inf or sup or mul
                binary_strategy(
                    vec![BinOpKind::Sup, BinOpKind::Inf, BinOpKind::Mul],
                    TyKind::EUReal,
                    eureal_element.clone()
                ),
                // implications
                binary_strategy(
                    vec![
                        BinOpKind::Impl,
                        BinOpKind::CoImpl,
                        BinOpKind::Compare,
                        BinOpKind::CoCompare,
                    ],
                    TyKind::EUReal,
                    eureal_element
                ),
            ];
            (bool_strategy, eureal_strategy)
        })
    }

    fn mk_eureal_strategy(&self) -> impl Strategy<Value = Expr> {
        self.mk_strategy().prop_map(|(_, eureal_expr)| eureal_expr)
    }
}

fn lit_strategy(lit: impl Strategy<Value = LitKind>, ty: TyKind) -> impl Strategy<Value = Expr> {
    lit.prop_map(move |lit| {
        Shared::new(ExprData {
            kind: ExprKind::Lit(Spanned::new(Span::dummy_span(), lit)),
            ty: Some(ty.clone()),
            span: Span::dummy_span(),
        })
    })
}

fn unary_strategy(
    un_op: Vec<UnOpKind>,
    ty: TyKind,
    element: impl Strategy<Value = Expr>,
) -> impl Strategy<Value = Expr> {
    let un_op = prop::sample::select(un_op);
    (un_op, element).prop_map(move |(un_op, expr)| {
        ExprBuilder::new(Span::dummy_span()).unary(un_op, Some(ty.clone()), expr)
    })
}

fn binary_strategy(
    bin_op: Vec<BinOpKind>,
    ty: TyKind,
    element: impl Strategy<Value = Expr> + Clone,
) -> impl Strategy<Value = Expr> {
    let bin_op = prop::sample::select(bin_op);
    (bin_op, element.clone(), element).prop_map(move |(bin_op, lhs, rhs)| {
        ExprBuilder::new(Span::dummy_span()).binary(bin_op, Some(ty.clone()), lhs, rhs)
    })
}

fn ite_strategy(
    cond: impl Strategy<Value = Expr>,
    ty: TyKind,
    element: impl Strategy<Value = Expr> + Clone,
) -> impl Strategy<Value = Expr> {
    (cond, element.clone(), element).prop_map(move |(cond, lhs, rhs)| {
        ExprBuilder::new(Span::dummy_span()).ite(Some(ty.clone()), cond, lhs, rhs)
    })
}

fn ident_to_expr(ident: Ident, ty: TyKind) -> Expr {
    Shared::new(ExprData {
        kind: ExprKind::Var(ident),
        ty: Some(ty),
        span: Span::dummy_span(),
    })
}

fn prove_equiv(expr: Expr, optimized: Expr, tcx: &TyCtx) -> TestCaseResult {
    let builder = ExprBuilder::new(Span::dummy_span());
    let eq_expr = builder.binary(
        BinOpKind::Eq,
        Some(TyKind::Bool),
        expr.clone(),
        optimized.clone(),
    );
    let ctx = z3::Context::new(&z3::Config::new());
    let smt_ctx = SmtCtx::new(&ctx, tcx);
    let mut translate = TranslateExprs::new(&smt_ctx);
    let eq_expr_z3 = translate.t_bool(&eq_expr);
    let mut prover = Prover::new(&ctx);
    translate
        .local_scope()
        .add_assumptions_to_prover(&mut prover);
    prover.add_provable(&eq_expr_z3);
    match prover.check_proof() {
        ProveResult::Proof => Ok(()),
        ProveResult::Counterexample => Err(TestCaseError::fail(format!(
            "rewrote {} ...into... {}, but those are not equivalent:\n{}",
            expr,
            optimized,
            prover.get_model().unwrap()
        ))),
        ProveResult::Unknown => Err(TestCaseError::fail("unknown result")),
    }
}

pub fn mk_tcx() -> TyCtx {
    let expr_gen = ExprGen::new();
    let mut tcx = TyCtx::new(TyKind::EUReal);
    expr_gen.declare(&mut tcx);
    tcx
}

/// Run the expression fuzz tester on the given expression optimizing function.
#[doc(hidden)]
pub fn fuzz_expr_opt_internal(
    config: proptest::test_runner::Config,
    optimize_fn: impl Fn(Expr) -> Expr,
) {
    let expr_gen = ExprGen::new();
    let mut tcx = TyCtx::new(TyKind::EUReal);
    expr_gen.declare(&mut tcx);
    let mut test_runner = TestRunner::new(config);
    let res = test_runner.run(&expr_gen.mk_eureal_strategy(), |expr| {
        let optimized = optimize_fn(expr.clone());
        prove_equiv(expr, optimized, &tcx)
    });
    match res {
        Ok(_) => (),
        Err(e) => panic!("{}\n{}", e, test_runner),
    }
}

#[macro_export]
macro_rules! fuzz_expr_opt_test {
    ($optimize_fn:expr) => {{
        let mut config = ::proptest::test_runner::Config::default();
        config.test_name = Some(concat!(module_path!(), "::", stringify!($test_name)));
        config.source_file = Some(file!());
        config.cases = 1000;
        crate::opt::fuzz_test::fuzz_expr_opt_internal(config, $optimize_fn);
    }};
}
