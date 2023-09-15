//! Representation of expressions as e-graphs using `egg`.
//! With e-graphs, we can easily specify a bunch of rewrite rules for expressions and automatically apply simplifications.

use crate::ast::{BinOpKind, Expr, ExprKind, Ident, LitKind, UnOpKind};
use egg::{define_language, CostFunction, Id, RecExpr};
use egg::{rewrite, Rewrite};
use egg::{AstSize, Extractor, Runner};
use tracing::instrument;

define_language! {
    pub enum ExprLanguage {
        // Calls
        "call" = Call(Box<[Id]>),
        // Binops
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "%" = Mod([Id; 2]),
        "&&" = And([Id; 2]),
        "||" = Or([Id; 2]),
        "==" = Eq([Id; 2]),
        "<" = Lt([Id;2]),
        "<=" = Le([Id; 2]),
        "⊓" = Inf([Id; 2]),
        "⊔" = Sup([Id; 2]),
        "→" = Impl([Id; 2]),
        "←" = CoImpl([Id; 2]),
        "↘" = Compare([Id; 2]),
        "↖" = CoCompare([Id; 2]),
        // Unops
        "!" = Not(Id),
        "~" = Non(Id),
        "embed" = Embed(Id),
        "iverson" = Iverson(Id),
        // If-then-else
        "ite" = Ite([Id; 3]),
        // Casts
        "to-realplus" = ToRealPlus(Id),
        // TODO: Quantifiers, Substs
        // Literals
        Lit(LitKind),
        // Variables
        Var(egg::Symbol),
    }
}

pub fn expr_to_egg(expr: &Expr) -> RecExpr<ExprLanguage> {
    fn recurse(graph: &mut RecExpr<ExprLanguage>, expr: &Expr) -> Id {
        let mk_var = |graph: &mut RecExpr<ExprLanguage>, ident: Ident| -> Id {
            graph.add(ExprLanguage::Var(egg::Symbol::from(ident.name.to_owned())))
        };

        match &expr.kind {
            ExprKind::Var(ident) => mk_var(graph, *ident),
            ExprKind::Call(ident, args) => {
                let callable = mk_var(graph, *ident);
                let mut children: Vec<Id> = args.iter().map(|arg| recurse(graph, arg)).collect();
                children.insert(0, callable);
                graph.add(ExprLanguage::Call(children.into_boxed_slice()))
            }
            ExprKind::Ite(cond, arg1, arg2) => {
                let cond = recurse(graph, cond);
                let arg1 = recurse(graph, arg1);
                let arg2 = recurse(graph, arg2);
                graph.add(ExprLanguage::Ite([cond, arg1, arg2]))
            }
            ExprKind::Binary(bin_op, arg1, arg2) => {
                let arg1 = recurse(graph, arg1);
                let arg2 = recurse(graph, arg2);
                match bin_op.node {
                    BinOpKind::Add => graph.add(ExprLanguage::Add([arg1, arg2])),
                    BinOpKind::Sub => graph.add(ExprLanguage::Sub([arg1, arg2])),
                    BinOpKind::Mul => graph.add(ExprLanguage::Mul([arg1, arg2])),
                    BinOpKind::Div => graph.add(ExprLanguage::Div([arg1, arg2])),
                    BinOpKind::Mod => graph.add(ExprLanguage::Mod([arg1, arg2])),
                    BinOpKind::And => graph.add(ExprLanguage::And([arg1, arg2])),
                    BinOpKind::Or => graph.add(ExprLanguage::Or([arg1, arg2])),
                    BinOpKind::Eq => graph.add(ExprLanguage::Eq([arg1, arg2])),
                    BinOpKind::Lt => graph.add(ExprLanguage::Lt([arg1, arg2])),
                    BinOpKind::Le => graph.add(ExprLanguage::Le([arg1, arg2])),
                    BinOpKind::Ne => {
                        let eq = graph.add(ExprLanguage::Eq([arg1, arg2]));
                        graph.add(ExprLanguage::Not(eq))
                    }
                    BinOpKind::Ge => graph.add(ExprLanguage::Le([arg2, arg1])),
                    BinOpKind::Gt => graph.add(ExprLanguage::Lt([arg2, arg1])),
                    BinOpKind::Inf => graph.add(ExprLanguage::Inf([arg1, arg2])),
                    BinOpKind::Sup => graph.add(ExprLanguage::Sup([arg1, arg2])),
                    BinOpKind::Impl => graph.add(ExprLanguage::Impl([arg1, arg2])),
                    BinOpKind::CoImpl => graph.add(ExprLanguage::CoImpl([arg1, arg2])),
                    BinOpKind::Compare => graph.add(ExprLanguage::Compare([arg1, arg2])),
                    BinOpKind::CoCompare => graph.add(ExprLanguage::CoCompare([arg1, arg2])),
                }
            }
            ExprKind::Unary(un_op, arg) => {
                let arg = recurse(graph, arg);
                match un_op.node {
                    UnOpKind::Not => graph.add(ExprLanguage::Not(arg)),
                    UnOpKind::Non => graph.add(ExprLanguage::Non(arg)),
                    UnOpKind::Embed => graph.add(ExprLanguage::Embed(arg)),
                    UnOpKind::Iverson => graph.add(ExprLanguage::Iverson(arg)),
                    UnOpKind::Parens => arg,
                }
            }
            ExprKind::Cast(arg) => {
                #[allow(clippy::let_and_return)]
                let arg = recurse(graph, arg);
                // TODO: for the moment, we don't generate ToRealPlus
                // assert!(matches!(expr.ty.as_ref().unwrap().node, TyKind::RealPlus));
                // graph.add(ExprLanguage::ToRealPlus(arg))
                arg
            }
            ExprKind::Quant(_, _, _) => todo!(),
            ExprKind::Subst(_, _, _) => todo!(),
            ExprKind::Lit(lit) => graph.add(ExprLanguage::Lit(lit.node.clone())),
        }
    }

    let mut graph = RecExpr::default();
    recurse(&mut graph, expr);
    graph
}

fn make_rewrites() -> Vec<Rewrite<ExprLanguage, ()>> {
    let rules: Vec<Rewrite<_, _>> = vec![
        // addition
        // rewrite!("comm-add";  "(+ ?a ?b)" => "(+ ?b ?a)"),
        // rewrite!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        // rewrite!("zero-add"; "(+ ?a 0)" => "?a"),
        // multiplication
        // rewrite!("comm-mul";  "(* ?a ?b)" => "(* ?b ?a)"),
        // rewrite!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        // rewrite!("zero-mul"; "(* ?a 0)" => "0"),
        // rewrite!("one-mul";  "(* ?a 1)" => "?a"),
        // addition + multiplication
        // rewrite!("distribute"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        // rewrite!("factor"; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        // Boolean and
        // rewrite!("comm-and";  "(&& ?a ?b)" => "(&& ?b ?a)"),
        // rewrite!("true-and"; "(&& ?a true)" => "?a"),
        // rewrite!("false-and"; "(&& ?a false)" => "false"),
        // Boolean or
        // rewrite!("comm-or";  "(|| ?a ?b)" => "(|| ?b ?a)"),
        // rewrite!("true-or"; "(|| ?a true)" => "true"),
        // rewrite!("false-or"; "(|| ?a false)" => "?a"),
        // Binary infimum
        // rewrite!("leq-inf"; "(<= ?a (⊓ ?b ?c))" => "(&& (<= ?a ?b) (<= ?a ?c))"),
        // rewrite!("geq-inf"; "(<= (⊓ ?a ?b) ?c)" => "(|| (<= ?a ?c) (<= ?b ?c))"),
        // Binary supremum
        // rewrite!("leq-sup"; "(<= ?a (⊔ ?b ?c))" => "(|| (<= ?a ?b) (<= ?a ?c))"),
        // rewrite!("geq-sup"; "(<= (⊔ ?a ?b) ?c)" => "(&& (<= ?a ?c) (<= ?b ?c))"),
        // ==
        // rewrite!("true-eq"; "(== ?a ?a)" => "true"),
        // <=
        // rewrite!("leq-zero"; "(<= 0 ?a)" => "true"),
        // rewrite!("leq-infty"; "(<= ?a ∞)" => "true"),
        // Implication
        // rewrite!("zero-impl"; "(→ 0 ?a)" => "∞"),
        // rewrite!("inf-impl"; "(→ ?a ∞)" => "∞"),
        // rewrite!("impl-ite"; "(→ ?a ?b)" => "(ite (<= ?a ?b) ∞ ?b)"),
        // rewrite!("valid-impl"; "(== (→ ?a ?b) ∞)" => "(<= ?a ?b)"),
        // rewrite!("leq-impl"; "(<= ?a (→ ?b ?c))" => "(|| (<= ?a ?b) (<= ?a ?c))"),
        // Embed
        // rewrite!("embed-ite"; "(embed ?a)" => "(ite ?a ∞ 0)"),
        // rewrite!("intro-impl-ite"; "(⊓ (→ (embed ?a) ?b) (→ (embed (! ?a)) ?c))" => "(ite ?a ?b ?c)"),
        // Ite
        // rewrite!("true-ite"; "(ite true ?a ?b)" => "?a"),
        // rewrite!("false-ite"; "(ite false ?a ?b)" => "?b"),
        // rewrite!("ite-eq"; "(== (ite ?a ?b ?c) ?d)" => "(ite ?a (== ?b ?d) (== ?c ?d))"),

        // Arithmetic
        // rewrite!("factor"; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        // rewrite!("distribute"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        // rewrite!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        // rewrite!("two-add"; "(+ ?a ?a)" => "(* 2 ?a)"),
        // rewrite!("half-mul-two"; "(* 1/2 (* 2 ?a))" => "?a"),
        // rewrite!("one-mul";  "(* ?a 1)" => "?a"),
        // rewrite!("intro-one-mul"; "?a" => "(* ?a 1)"),
        // rewrite!("comm-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        // rewrite!("comm-add";  "(+ ?a ?b)" => "(+ ?b ?a)"),

        // Ite
        rewrite!("true-ite"; "(ite true ?a ?b)" => "?a"),
        rewrite!("false-ite"; "(ite false ?a ?b)" => "?b"),
        rewrite!("const-ite"; "(ite ?a ?b ?b)" => "?b"),
        // rewrite!("case1-ite"; "(ite ?a (ite ?a ?b ?c) ?d)" => "(ite ?a ?b ?d)"),
        // rewrite!("case2-ite"; "(ite ?a ?b (ite ?a ?c ?d))" => "(ite ?a ?b ?d)"),
        // rewrite!("add-ite"; "(+ ?a (ite ?b ?c ?d))" => "(ite ?b (+ ?a ?c) (+ ?a ?d))"),
        // rewrite!("mul-ite"; "(* ?a (ite ?b ?c ?d))" => "(ite ?b (* ?a ?c) (* ?a ?d))"),
        // rewrite!("leq-ite1"; "(<= (ite ?a ?b ?c) ?d)" => "(ite ?a (<= ?b ?d) (<= ?c ?d))"),
        // rewrite!("leq-ite2"; "(<= ?a (ite ?b ?c ?d))" => "(ite ?b (<= ?a ?c) (<= ?a ?d))"),

        // Boolean and
        rewrite!("comm-and";  "(&& ?a ?b)" => "(&& ?b ?a)"),
        rewrite!("true-and"; "(&& ?a true)" => "?a"),
        rewrite!("false-and"; "(&& ?a false)" => "false"),
        // Boolean or
        rewrite!("comm-or";  "(|| ?a ?b)" => "(|| ?b ?a)"),
        rewrite!("true-or"; "(|| ?a true)" => "true"),
        rewrite!("false-or"; "(|| ?a false)" => "?a"),
        // ==
        rewrite!("comm-eq"; "(== ?a ?b)" => "(== ?b ?a)"),
        // <=
        rewrite!("leq-true"; "(<= ?a ?a)" => "true"),
        // Binary infimum ⊓
        rewrite!("comm-inf"; "(⊓ ?a ?b)" => "(⊓ ?b ?a)"),
        rewrite!("id-inf"; "(⊓ ?a ∞)" => "?a"),
        rewrite!("leq-inf"; "(<= ?a (⊓ ?b ?c))" => "(&& (<= ?a ?b) (<= ?a ?c))"),
        rewrite!("geq-inf"; "(<= (⊓ ?a ?b) ?c)" => "(|| (<= ?a ?c) (<= ?b ?c))"),
        // Binary supremum ⊔
        rewrite!("comm-sup"; "(⊔ ?a ?b)" => "(⊔ ?b ?a)"),
        rewrite!("id-sup"; "(⊔ ?a 0)" => "?a"),
        rewrite!("leq-sup"; "(<= ?a (⊔ ?b ?c))" => "(|| (<= ?a ?b) (<= ?a ?c))"),
        rewrite!("geq-sup"; "(<= (⊔ ?a ?b) ?c)" => "(&& (<= ?a ?c) (<= ?b ?c))"),
        // Implication
        rewrite!("zero-impl"; "(→ 0 ?a)" => "∞"),
        rewrite!("inf-impl"; "(→ ∞ ?a)" => "?a"),
        rewrite!("impl-inf"; "(→ ?a ∞)" => "∞"),
        // Compare
        rewrite!("infty-compare"; "(== (↘ ?a ?b) ∞)" => "(<= ?a ?b)"),
        rewrite!("compare-hey1"; "(↘ ?a ?a)" => "∞"),
        rewrite!("compare-hey4"; "(↘ ?a (⊓ ?b ?c))" => "(⊓ (↘ ?a ?b) (↘ ?a ?c))"),
        // Co-compare
        rewrite!("zero-cocompare"; "(== (↖ ?a ?b) 0)" => "(<= ?b ?a)"),
        rewrite!("cocompare-hey1"; "(↖ ?a ?a)" => "0"),
        rewrite!("cocompare-hey4"; "(↖ ?a (⊔ ?b ?c))" => "(⊔ (↖ ?a ?b) (↖ ?a ?c))"),
        // Negation
        rewrite!("not-true"; "(! true)" => "false"),
        rewrite!("not-false"; "(! false)" => "true"),
        rewrite!("infty-not"; "(== (! ?a) ∞)" => "(== ?a 0)"),
        // Co-negation
        rewrite!("non-infty"; "(~ ∞)" => "0"),
        // Embed
        rewrite!("embed-true"; "(embed true)" => "∞"),
        rewrite!("embed-false"; "(embed false)" => "0"),
        rewrite!("impl-intro-ite"; "(⊓ (→ (embed ?a) ?b) (→ (embed (! ?a)) ?c))" => "(ite ?a ?b ?c)"), // Embed
        // Iverson
        rewrite!("iverson-true"; "(iverson true)" => "1"),
        rewrite!("iverson-false"; "(iverson false)" => "0"),
        rewrite!("iverson-intro-ite"; "(+ (* (iverson ?a) ?b) (* (iverson (! ?a)) ?c))" => "(ite ?a ?b ?c)"),
        // Arithmetic
        // addition
        rewrite!("zero-add"; "(+ ?a 0)" => "?a"),
        rewrite!("add-sub"; "(+ (- ?a ?b) ?b)" => "?a"),
        // subtraction
        rewrite!("zero-sub"; "(- ?a 0)" => "?a"),
        rewrite!("sub-add"; "(- (+ ?a ?b) ?b)" => "?a"),
        // multiplication
        rewrite!("zero-mul"; "(* ?a 0)" => "0"),
        rewrite!("one-mul";  "(* ?a 1)" => "?a"),
    ];
    rules
}

#[instrument(skip(expr))]
pub fn simplify(expr: &Expr) {
    let start = expr_to_egg(expr);
    // TODO: have a better CostFn than AstSize that penalizes our implications according to encoding size
    let start_cost = AstSize.cost_rec(&start);
    tracing::info!(
        start = %start,
        cost = start_cost,
        "simplifying egraph",
    );
    let runner = Runner::default().with_expr(&start).run(&make_rewrites());
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);
    tracing::info!(
        best_expr = %best_expr,
        best_cost = best_cost,
        cost_delta = (best_cost as isize) - (start_cost as isize),
        stop_reason = ?runner.stop_reason.unwrap(),
        "simplified egraph"
    );
}
