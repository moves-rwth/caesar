//! Built-in procedures for probability distributions.

use std::{fmt, rc::Rc};

use num::{integer::binomial, rational::Ratio};
use tracing::instrument;

use crate::{
    ast::{
        visit::VisitorMut, BinOpKind, DeclKind, Expr, ExprBuilder, ExprKind, Files, Ident, LitKind,
        ProcDecl, SourceFilePath, Span, TyKind,
    },
    front::parser,
    front::resolve::Resolve,
    front::tycheck::{Tycheck, TycheckError},
    tyctx::TyCtx,
};

use super::ProcIntrin;

type DistFn = Box<dyn Fn(&[Expr], ExprBuilder) -> Dist>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum DistProcKind {
    /// Only accepting constant parameters.
    ConstantOnly,
    /// Accepting symbolic parameters (like any other procedure).
    Symbolic,
}

struct DistProc {
    decl: ProcDecl,
    dist_fn: DistFn,
}

impl DistProc {
    fn new(
        kind: DistProcKind,
        files: &mut Files,
        tcx: &mut TyCtx,
        decl: &str,
        dist_fn: DistFn,
    ) -> Self {
        // create the file
        let file = files.add(SourceFilePath::Builtin, decl.to_string());

        // parse the declaration
        let mut decl = parser::parse_bare_decl(file).unwrap();

        // resolve all identifiers
        let mut resolve = Resolve::new(tcx);
        // we need to declare this ProcDecl temporarily (to replace TyKind::Unresolved by the resolved type)
        resolve.declare(decl.clone()).unwrap();
        resolve.visit_decl(&mut decl).unwrap();
        // now remove the ProcDecl
        tcx.undeclare(decl.name());

        // extract the ProcDecl from the Decl. We do `try_unwrap` because we're
        // now the only owner of the ProcDecl.
        let mut proc_decl = if let DeclKind::ProcDecl(proc_decl) = decl {
            proc_decl.try_unwrap().unwrap()
        } else {
            unreachable!()
        };

        if kind == DistProcKind::ConstantOnly {
            for param in proc_decl.params_iter_mut() {
                param.literal_only = true;
            }
        }

        DistProc {
            decl: proc_decl,
            dist_fn,
        }
    }
}

impl fmt::Debug for DistProc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DistProc")
            .field("decl", &self.decl)
            .field("vcgen_fn", &"<omitted>")
            .finish()
    }
}

impl ProcIntrin for DistProc {
    fn name(&self) -> Ident {
        self.decl.name
    }

    fn tycheck(
        &self,
        tycheck: &mut Tycheck<'_>,
        call_span: Span,
        args: &mut [Expr],
    ) -> Result<TyKind, TycheckError> {
        let ty = tycheck.check_proc_call(call_span, &self.decl, args)?;
        Ok(ty)
    }

    fn vcgen(&self, builder: ExprBuilder, args: &[Expr], lhses: &[Ident], post: Expr) -> Expr {
        let lhs = if let [lhs] = lhses {
            *lhs
        } else {
            panic!("unexpected number of lhses")
        };
        let dist = (self.dist_fn)(args, builder);
        dist.expectation(lhs, &post, builder)
    }
}

/// Add all built-in distributions as globals into the [`TyCtx`].
#[instrument(skip(files, tcx))]
pub fn init_distributions(files: &mut Files, tcx: &mut TyCtx) {
    let ber = DistProc::new(
        DistProcKind::ConstantOnly,
        files,
        tcx,
        "proc ber(pa: UInt, pb: UInt) -> (r: Bool)",
        Box::new(|args, builder| {
            let [pa, pb] = two_args(args);
            Dist::ber(lit_u128(pa), lit_u128(pb), builder)
        }),
    );
    tcx.add_global(ber.name());
    tcx.declare(DeclKind::ProcIntrin(Rc::new(ber)));

    let flip = DistProc::new(
        DistProcKind::Symbolic,
        files,
        tcx,
        "proc flip(p: UReal) -> (r: Bool)",
        Box::new(|args, builder| {
            let [p] = one_arg(args);
            Dist::flip(p.clone(), builder)
        }),
    );
    tcx.add_global(flip.name());
    tcx.declare(DeclKind::ProcIntrin(Rc::new(flip)));

    let unif = DistProc::new(
        DistProcKind::ConstantOnly,
        files,
        tcx,
        "proc unif(a: UInt, b: UInt) -> (r: UInt)",
        Box::new(|args, builder| {
            let [a, b] = two_args(args);
            Dist::unif(lit_u128(a), lit_u128(b), builder)
        }),
    );
    tcx.add_global(unif.name());
    tcx.declare(DeclKind::ProcIntrin(Rc::new(unif)));

    let binom = DistProc::new(
        DistProcKind::ConstantOnly,
        files,
        tcx,
        "proc binom(n: UInt, pa: UInt, pb: UInt) -> (r: UInt)",
        Box::new(|args, builder| {
            let [a, b, c] = three_args(args);
            Dist::binom(lit_u128(a), lit_u128(b), lit_u128(c), builder)
        }),
    );
    tcx.add_global(binom.name());
    tcx.declare(DeclKind::ProcIntrin(Rc::new(binom)));

    let hyper = DistProc::new(
        DistProcKind::ConstantOnly,
        files,
        tcx,
        "proc hyper(pN: UInt, k: UInt, pn: UInt) -> (r: UInt)",
        Box::new(|args, builder| {
            let [a, b, c] = three_args(args);
            Dist::hyper(lit_u128(a), lit_u128(b), lit_u128(c), builder)
        }),
    );
    tcx.add_global(hyper.name());
    tcx.declare(DeclKind::ProcIntrin(Rc::new(hyper)));
}

fn lit_u128(expr: &Expr) -> u128 {
    if let ExprKind::Lit(lit) = &expr.kind {
        if let LitKind::UInt(value) = &lit.node {
            return *value;
        }
    };
    unreachable!()
}

fn one_arg(args: &[Expr]) -> [&Expr; 1] {
    if let [a] = args {
        [a]
    } else {
        unreachable!()
    }
}

fn two_args(args: &[Expr]) -> [&Expr; 2] {
    if let [a, b] = args {
        [a, b]
    } else {
        unreachable!()
    }
}

fn three_args(args: &[Expr]) -> [&Expr; 3] {
    if let [a, b, c] = args {
        [a, b, c]
    } else {
        unreachable!()
    }
}

/// We represent a distribution as a list of values (expressions) with
/// probabilities.
#[derive(Debug)]
struct Dist(Vec<(Expr, Expr)>);

impl Dist {
    fn from_odds(iter: impl IntoIterator<Item = (u128, Expr)>, builder: ExprBuilder) -> Self {
        let pairs: Vec<_> = iter.into_iter().collect();
        let total: u128 = pairs.iter().map(|pair| pair.0).sum();
        let dist = pairs
            .into_iter()
            .map(|(odds, val)| (builder.frac_lit(Ratio::new(odds.into(), total.into())), val))
            .collect();
        Dist(dist)
    }

    /// Create a new bernoulli distribution given a pair of odds.
    fn ber(pa: u128, pb: u128, builder: ExprBuilder) -> Dist {
        let one = builder.bool_lit(true);
        let zero = builder.bool_lit(false);
        Dist::from_odds(vec![(pa, one), (pb, zero)], builder)
    }

    /// Create a new bernoulli distribution given a probability for choice `true`.
    fn flip(p: Expr, builder: ExprBuilder) -> Dist {
        let pb = builder.binary(
            BinOpKind::Sub,
            Some(TyKind::UReal),
            builder.cast(TyKind::UReal, builder.uint(1)),
            p.clone(),
        );
        let p = builder.cast(TyKind::EUReal, p);
        let pb = builder.cast(TyKind::EUReal, pb);
        let one = builder.bool_lit(true);
        let zero = builder.bool_lit(false);
        Dist(vec![(p, one), (pb, zero)])
    }

    /// Create a new uniform distribution with the given bounds.
    fn unif(a: u128, b: u128, builder: ExprBuilder) -> Dist {
        let dist = (a..=b).map(|val| (1, builder.uint(val)));
        Dist::from_odds(dist, builder)
    }

    /// Create a new binomial distribution with the given parameters.
    fn binom(n: u128, pa: u128, pb: u128, builder: ExprBuilder) -> Dist {
        let dist = (0..=n).map(|k| {
            (
                binomial(n, k) * pa.pow(k as u32) * pb.pow((pb - pa) as u32),
                builder.uint(k),
            )
        });
        Dist::from_odds(dist, builder)
    }

    /// Create a new hypergeometric distribution with the given parameters.
    fn hyper(population: u128, successes: u128, draws: u128, builder: ExprBuilder) -> Dist {
        let k = 0.max(draws + successes - population)..=draws.min(successes);
        let dist = k.map(|k| {
            (
                binomial(successes, k) * binomial(population - successes, draws - k),
                builder.uint(k),
            )
        });
        Dist::from_odds(dist, builder)
    }

    /// Compute the expected value of the given expression `expr` by
    /// substituting `ident` with all possible values in this distribution. Each
    /// expression with the substitution is weighted by its probability and the
    /// result of this function is the sum over all these weighted expressions.
    fn expectation(self, ident: Ident, expr: &Expr, builder: ExprBuilder) -> Expr {
        self.0
            .into_iter()
            .map(|(prob, val)| {
                let subst = builder.subst(expr.clone(), [(ident, val)]);
                let ty = prob.ty.clone();
                builder.binary(BinOpKind::Mul, ty, prob, subst)
            })
            .reduce(|a, b| {
                let ty = a.ty.clone();
                builder.binary(BinOpKind::Add, ty, a, b)
            })
            .unwrap()
    }
}
