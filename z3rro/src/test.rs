//! This module contains utilities to generate tests for the various traits of
//! our SMT framework. The tests usually create proofs of various properties for
//! Z3 to check.

use z3::{ast::Bool, Config, Context, SatResult};

use crate::prover::{IncrementalMode, ProveResult, Prover, SolverType};

use super::scope::SmtScope;

/// Create a new solver and check that the formula returned by `f` is always
/// valid. `f` receives an [`SmtScope`] to create the required variables in.
/// This function also checks that the [`SmtScope`] without the returned formula
/// is not inconsistent, that is, that the constraints of the scope are satisfiable.
pub fn test_prove(f: impl for<'ctx> FnOnce(&'ctx Context, &mut SmtScope<'ctx>) -> Bool<'ctx>) {
    let ctx = Context::new(&Config::default());

    let mut scope = SmtScope::new();
    let theorem = f(&ctx, &mut scope);

    let mut prover = Prover::new(&ctx, IncrementalMode::Native, SolverType::Z3);
    scope.add_assumptions_to_prover(&mut prover);
    assert_eq!(
        prover.check_sat(),
        SatResult::Sat,
        "SmtScope is inconsistent"
    );

    prover.add_provable(&theorem);
    match prover.check_proof() {
        Ok(ProveResult::Counterexample) => panic!(
            "counter-example: {:?}\nassertions:\n{:?}",
            prover.get_model(),
            prover.get_assertions()
        ),
        Ok(ProveResult::Unknown(reason)) => panic!("solver returned unknown ({})", reason),
        Ok(ProveResult::Proof) => {},
        Err(_) => {}
    };
}

/// Generate tests for types that implement [`super::SmtBranch`]. The type needs to
/// implement [`SmtFresh`] and [`SmtAst`].
#[macro_export]
macro_rules! generate_smt_branch_tests {
    ($mk_factory:expr, $ty:ty) => {
        #[test]
        fn test_branch() {
            use crate::test::test_prove;
            use crate::{scope::SmtFresh, SmtBranch, SmtEq};
            use z3::ast::Bool;
            test_prove(|ctx, scope| {
                let factory = $mk_factory(ctx);
                let x = <$ty>::fresh(&factory, scope, "x");
                let y = <$ty>::fresh(&factory, scope, "y");
                let b = Bool::fresh(&ctx, scope, "b");
                let ite = <$ty>::branch(&b, &x, &y);
                z3_and!(b.implies(&ite.smt_eq(&x)), b.not().implies(&ite.smt_eq(&y)))
            });
        }
    };
}

/// Generate tests for types that implement [`super::orders::SmtPartialOrd`].
/// The type needs to implement [`SmtFresh`] and [`SmtEq`].
#[macro_export]
macro_rules! generate_smt_partial_ord_tests {
    ($mk_factory:expr, $ty:ty) => {
        #[test]
        fn test_reflexivity() {
            use crate::test::test_prove;
            use crate::{orders::SmtPartialOrd, scope::SmtFresh};
            test_prove(|ctx, scope| {
                let factory = $mk_factory(ctx);
                let x = <$ty>::fresh(&factory, scope, "x");
                x.smt_le(&x)
            });
        }

        #[test]
        fn test_antisymmetry() {
            use crate::test::test_prove;
            use crate::{orders::SmtPartialOrd, scope::SmtFresh, SmtEq};
            test_prove(|ctx, scope| {
                let factory = $mk_factory(ctx);
                let x = <$ty>::fresh(&factory, scope, "x");
                let y = <$ty>::fresh(&factory, scope, "y");
                z3_and!(x.smt_le(&y), y.smt_le(&x)).implies(&x.smt_eq(&y))
            });
        }

        #[test]
        fn test_transitivity() {
            use crate::test::test_prove;
            use crate::{orders::SmtPartialOrd, scope::SmtFresh};
            test_prove(|ctx, scope| {
                let factory = $mk_factory(ctx);
                let x = <$ty>::fresh(&factory, scope, "x");
                let y = <$ty>::fresh(&factory, scope, "y");
                let z = <$ty>::fresh(&factory, scope, "z");
                z3_and!(x.smt_le(&y), y.smt_le(&z)).implies(&x.smt_le(&z))
            });
        }

        #[test]
        fn test_smt_cmp() {
            use crate::test::test_prove;
            use crate::{
                orders::{SmtOrdering, SmtPartialOrd},
                scope::SmtFresh,
                SmtEq,
            };
            test_prove(|ctx, scope| {
                let factory = $mk_factory(ctx);
                let x = <$ty>::fresh(&factory, scope, "x");
                let y = <$ty>::fresh(&factory, scope, "y");
                x.smt_cmp(&y, SmtOrdering::Equal).iff(&x.smt_eq(&y))
            });
            test_prove(|ctx, scope| {
                let factory = $mk_factory(ctx);
                let x = <$ty>::fresh(&factory, scope, "x");
                let y = <$ty>::fresh(&factory, scope, "y");
                x.smt_cmp(&y, SmtOrdering::LessOrEqual).iff(&x.smt_le(&y))
            });
            test_prove(|ctx, scope| {
                let factory = $mk_factory(ctx);
                let x = <$ty>::fresh(&factory, scope, "x");
                let y = <$ty>::fresh(&factory, scope, "y");
                x.smt_le(&y)
                    .iff(&y.smt_cmp(&x, SmtOrdering::GreaterOrEqual))
            });
            test_prove(|ctx, scope| {
                let factory = $mk_factory(ctx);
                let x = <$ty>::fresh(&factory, scope, "x");
                let y = <$ty>::fresh(&factory, scope, "y");
                x.smt_le(&y).iff(&x.smt_cmp(&y, SmtOrdering::Greater).not())
            });
            test_prove(|ctx, scope| {
                let factory = $mk_factory(ctx);
                let x = <$ty>::fresh(&factory, scope, "x");
                let y = <$ty>::fresh(&factory, scope, "y");
                x.smt_cmp(&y, SmtOrdering::Less)
                    .iff(&x.smt_cmp(&y, SmtOrdering::GreaterOrEqual).not())
            });
        }
    };
}
