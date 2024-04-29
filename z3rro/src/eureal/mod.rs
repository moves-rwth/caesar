//! We have two different, but equivalent SMT encodings of the EUReal type
//! (non-negative real numbers with infinity).
//!
//! By default, the [`pair`] representation is exported by this module and used
//! everywhere. However, the [`datatype`] representation can be enabled with the
//! `datatype-eureal` feature.

use std::fmt::{Display, Formatter};

use num::BigRational;
use z3::Context;

use crate::{Factory, SmtBranch};

pub mod datatype;
pub mod pair;

#[cfg(not(feature = "datatype-eureal"))]
pub type EUReal<'ctx> = pair::EUReal<'ctx>;

#[cfg(feature = "datatype-eureal")]
pub type EUReal<'ctx> = datatype::EUReal<'ctx>;

/// A concrete extended unsigned real. If it's finite, then it's represented as
/// a [`BigRational`]. Thus, this representation cannot represent all reals, but
/// only the rationals.
///
/// These values can be created using [`EUReal`]s implementation of the
/// [`z3rro::eval::SmtEval`] trait.
#[derive(Debug)]
pub enum ConcreteEUReal {
    Infinity,
    Real(BigRational),
}

impl Display for ConcreteEUReal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ConcreteEUReal::Infinity => f.write_str("∞"),
            ConcreteEUReal::Real(rational) => write!(f, "{}", rational),
        }
    }
}

/// This is just a factory that supports both EUReal types and supports
/// retrieval of the factory for the default [`EUReal`] type.
pub struct EURealSuperFactory<'ctx> {
    pub datatype_factory: Factory<'ctx, datatype::EUReal<'ctx>>,
    pub pair_factory: Factory<'ctx, pair::EUReal<'ctx>>,
}

impl<'ctx> EURealSuperFactory<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        EURealSuperFactory {
            datatype_factory: datatype::EURealFactory::new(ctx),
            pair_factory: pair::EURealFactory::new(ctx),
        }
    }

    /// Return the factory for the default [`EUReal`] type.
    pub fn default_factory(&self) -> &Factory<'ctx, EUReal<'ctx>> {
        cfg_if::cfg_if! {
            if #[cfg(feature = "datatype-eureal")] {
                &self.datatype_factory
            } else {
                &self.pair_factory
            }
        }
    }

    /// Convert the default [`EUReal`] representation to the [`datatype`] representation.
    ///
    /// If the datatype representation is the default, this is the identity function.
    pub fn to_datatype(&self, value: &EUReal<'ctx>) -> datatype::EUReal<'ctx> {
        cfg_if::cfg_if! {
            if #[cfg(feature = "datatype-eureal")] {
                value.clone()
            } else {
                pair_to_datatype(&self.datatype_factory, value)
            }
        }
    }

    /// Convert the [`datatype`] representation to the default [`EUReal`] representation.
    ///
    /// If the datatype representation is the default, this is the identity function.
    pub fn from_datatype(&self, datatype: &datatype::EUReal<'ctx>) -> EUReal<'ctx> {
        cfg_if::cfg_if! {
            if #[cfg(feature = "datatype-eureal")] {
                datatype.clone()
            } else {
                datatype_to_pair(&self.pair_factory, datatype)
            }
        }
    }
}

/// Go from the [`pair`] representation to the [`datatype`] representation.
pub fn pair_to_datatype<'ctx>(
    factory: &Factory<'ctx, datatype::EUReal<'ctx>>,
    pair: &pair::EUReal<'ctx>,
) -> datatype::EUReal<'ctx> {
    SmtBranch::branch(
        pair.is_infinity(),
        &datatype::EUReal::infinity(factory),
        &datatype::EUReal::from_ureal(factory, pair.get_ureal()),
    )
}

/// Go from the [`datatype`] representation to the [`pair`] representation.
pub fn datatype_to_pair<'ctx>(
    factory: &Factory<'ctx, pair::EUReal<'ctx>>,
    datatype: &datatype::EUReal<'ctx>,
) -> pair::EUReal<'ctx> {
    SmtBranch::branch(
        &datatype.is_infinity(),
        &pair::EUReal::infinity(factory),
        &pair::EUReal::from_ureal(factory, &datatype.get_ureal()),
    )
}

#[cfg(test)]
mod test {
    use std::ops::Add;
    use std::ops::Mul;

    use super::datatype;
    use super::datatype_to_pair;
    use super::pair;
    use super::pair_to_datatype;
    use crate::orders::SmtLattice;
    use crate::orders::SmtPartialOrd;
    use crate::scope::SmtFresh;
    use crate::test::test_prove;
    use crate::SmtEq;

    #[test]
    fn test_impls_iso() {
        test_prove(|ctx, scope| {
            let pair_factory = pair::EURealFactory::new(ctx);
            let datatype_factory = datatype::EURealFactory::new(ctx);
            let pair = pair::EUReal::fresh(&pair_factory, scope, "pair");
            pair.smt_eq(&datatype_to_pair(
                &pair_factory,
                &pair_to_datatype(&datatype_factory, &pair),
            ))
        });
        test_prove(|ctx, scope| {
            let pair_factory = pair::EURealFactory::new(ctx);
            let datatype_factory = datatype::EURealFactory::new(ctx);
            let datatype = datatype::EUReal::fresh(&datatype_factory, scope, "pair");
            datatype.smt_eq(&pair_to_datatype(
                &datatype_factory,
                &datatype_to_pair(&pair_factory, &datatype),
            ))
        });
    }

    macro_rules! test_binop_impls {
        ($operator:path) => {
            test_prove(|ctx, scope| {
                let pair_factory = pair::EURealFactory::new(ctx);
                let datatype_factory = datatype::EURealFactory::new(ctx);
                let x_pair = pair::EUReal::fresh(&pair_factory, scope, "x");
                let y_pair = pair::EUReal::fresh(&pair_factory, scope, "x");
                let x_datatype = pair_to_datatype(&datatype_factory, &x_pair);
                let y_datatype = pair_to_datatype(&datatype_factory, &y_pair);
                let pair_result = $operator(&x_pair, &y_pair);
                let datatype_result = $operator(&x_datatype, &y_datatype);

                let pair_check =
                    pair_result.smt_eq(&datatype_to_pair(&pair_factory, &datatype_result));
                let datatype_check =
                    datatype_result.smt_eq(&pair_to_datatype(&datatype_factory, &pair_result));
                z3_and!(pair_check, datatype_check)
            })
        };
    }

    #[test]
    fn test_impls_mul() {
        test_binop_impls!(Mul::mul);
    }

    #[test]
    fn test_impls_add() {
        test_binop_impls!(Add::add);
    }

    #[test]
    fn test_impls_lattice() {
        // ensure that the ordering is the same
        test_prove(|ctx, scope| {
            let pair_factory = pair::EURealFactory::new(ctx);
            let datatype_factory = datatype::EURealFactory::new(ctx);
            let x_pair = pair::EUReal::fresh(&pair_factory, scope, "x");
            let y_pair = pair::EUReal::fresh(&pair_factory, scope, "x");
            let x_datatype = pair_to_datatype(&datatype_factory, &x_pair);
            let y_datatype = pair_to_datatype(&datatype_factory, &y_pair);
            let pair_result = SmtPartialOrd::smt_le(&x_pair, &y_pair);
            let datatype_result = SmtPartialOrd::smt_le(&x_datatype, &y_datatype);
            pair_result.iff(&datatype_result)
        });
        // test binary inf and sup
        test_binop_impls!(SmtLattice::inf);
        test_binop_impls!(SmtLattice::sup);
    }
}
