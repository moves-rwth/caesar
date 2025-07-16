use std::{
    borrow::Cow,
    fmt::{Display, Formatter},
    ops::{Add, Mul, Sub},
};

use num::{BigRational, Zero};
use z3::{ast::Real, Context};

use crate::{util::PrettyRational, UReal};

use super::{pair::EUReal, pair::EURealFactory};

/// A concrete extended unsigned real. If it's finite, then it's represented as
/// a [`BigRational`]. Thus, this representation cannot represent all reals, but
/// only the rationals.
///
/// These values can be created using [`EUReal`]s implementation of the
/// [`crate::model::SmtEval`] trait.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConcreteEUReal {
    Real(BigRational),
    Infinity,
}

impl ConcreteEUReal {
    pub fn to_symbolic<'ctx>(&self, ctx: &'ctx Context) -> EUReal<'ctx> {
        let factory = EURealFactory::new(ctx);
        match self {
            ConcreteEUReal::Real(rational) => EUReal::from_ureal(
                &factory,
                &UReal::unchecked_from_real(Real::from_big_rational(ctx, rational)),
            ),
            ConcreteEUReal::Infinity => EUReal::infinity(&factory),
        }
    }
}

impl Display for ConcreteEUReal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ConcreteEUReal::Real(rational) => {
                write!(f, "{}", PrettyRational(Cow::Borrowed(rational)))
            }
            ConcreteEUReal::Infinity => f.write_str("∞"),
        }
    }
}

impl Add for ConcreteEUReal {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        match (self, other) {
            (ConcreteEUReal::Infinity, _) | (_, ConcreteEUReal::Infinity) => {
                ConcreteEUReal::Infinity
            }
            (ConcreteEUReal::Real(a), ConcreteEUReal::Real(b)) => ConcreteEUReal::Real(a + b),
        }
    }
}

impl Sub for ConcreteEUReal {
    type Output = Option<Self>;

    fn sub(self, other: Self) -> Self::Output {
        match (self, other) {
            (ConcreteEUReal::Infinity, ConcreteEUReal::Infinity) => None,
            (ConcreteEUReal::Infinity, _) => Some(ConcreteEUReal::Infinity),
            (_, ConcreteEUReal::Infinity) => None,
            (ConcreteEUReal::Real(a), ConcreteEUReal::Real(b)) => {
                if a >= b {
                    Some(ConcreteEUReal::Real(a - b))
                } else {
                    Some(ConcreteEUReal::Real(BigRational::zero()))
                }
            }
        }
    }
}

impl Mul for ConcreteEUReal {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        match (self, other) {
            (ConcreteEUReal::Real(a), _) if a.is_zero() => {
                ConcreteEUReal::Real(BigRational::zero())
            }
            (_, ConcreteEUReal::Real(b)) if b.is_zero() => {
                ConcreteEUReal::Real(BigRational::zero())
            }
            (ConcreteEUReal::Infinity, _) | (_, ConcreteEUReal::Infinity) => {
                ConcreteEUReal::Infinity
            }
            (ConcreteEUReal::Real(a), ConcreteEUReal::Real(b)) => ConcreteEUReal::Real(a * b),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::SmtEq;

    use super::*;
    use num::BigInt;
    use proptest::prelude::*;
    use z3::{Config, SatResult, Solver};

    fn arb_bigrational() -> impl Strategy<Value = BigRational> {
        // Limit numerator and denominator to reasonable size for testing
        (any::<u64>(), 1i64..=1000)
            .prop_map(|(num, denom)| BigRational::new(BigInt::from(num), BigInt::from(denom)))
    }

    fn arb_concrete_eureal() -> impl Strategy<Value = ConcreteEUReal> {
        prop_oneof![
            arb_bigrational().prop_map(ConcreteEUReal::Real),
            Just(ConcreteEUReal::Infinity),
        ]
    }

    fn z3_compare(
        concrete: ConcreteEUReal,
        symbolic: impl for<'ctx> FnOnce(&'ctx Context) -> EUReal<'ctx>,
    ) {
        let ctx = Context::new(&Config::default());
        let solver = Solver::new(&ctx);
        solver.assert(&concrete.to_symbolic(&ctx).smt_eq(&symbolic(&ctx)).not());
        assert_eq!(solver.check(), SatResult::Unsat);
    }

    proptest! {
        #[test]
        fn add(a in arb_concrete_eureal(), b in arb_concrete_eureal()) {
            z3_compare(a.clone() + b.clone(), |ctx| {
                a.to_symbolic(ctx) + b.to_symbolic(ctx)
            });
        }

        #[test]
        fn sub(a in arb_concrete_eureal(), b in arb_concrete_eureal()) {
            if let Some(result) = a.clone() - b.clone() {
                z3_compare(result, |ctx| {
                    a.to_symbolic(ctx) - b.to_symbolic(ctx)
                });
            }
        }

        #[test]
        fn mul(a in arb_concrete_eureal(), b in arb_concrete_eureal()) {
            z3_compare(a.clone() * b.clone(), |ctx| {
                a.to_symbolic(ctx) * b.to_symbolic(ctx)
            });
        }
    }
}
