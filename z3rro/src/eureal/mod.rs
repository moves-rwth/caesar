//! We have two different, but equivalent SMT encodings of the EUReal type
//! (non-negative real numbers with infinity).
//!
//! By default, the [`pair`] representation is exported by this module and used
//! everywhere. However, the [`datatype`] representation can be enabled with the
//! `datatype-eureal` feature.

use z3::{
    ast::{Ast, Bool, Dynamic, Real},
    Context,
};

use crate::{Factory, SmtBranch};

mod concrete;
pub mod datatype;
pub mod pair;
pub use concrete::ConcreteEUReal;

#[cfg(not(feature = "datatype-eureal"))]
pub type EUReal<'ctx> = pair::EUReal<'ctx>;

#[cfg(feature = "datatype-eureal")]
pub type EUReal<'ctx> = datatype::EUReal<'ctx>;

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
    if let Some(value) = extract_datatype_to_pair(factory, pair) {
        return value;
    }

    SmtBranch::branch(
        pair.is_infinity(),
        &datatype::EUReal::infinity(factory),
        &datatype::EUReal::from_ureal(factory, pair.get_ureal()),
    )
}

/// If the given `pair` is created by a conversion from a datatype, extract the
/// underlying datatype expression.
///
/// This is used to eliminate unnecessary round-trip conversions in the SMT
/// expressions. For the most part, this is a performance optimization, but this
/// also allows more quantifier patterns: when we translate a call to a function
/// that returns an `EUReal`, the translation will indirectly generate such a
/// datatype-to-pair conversion; but when we put that into a pattern, illegal
/// `ite` expressions show up. This simplification removes them by recognizing
/// that we had a datatype expression in the first place.
fn extract_datatype_to_pair<'ctx>(
    factory: &Factory<'ctx, datatype::EUReal<'ctx>>,
    pair: &pair::EUReal<'ctx>,
) -> Option<datatype::EUReal<'ctx>> {
    fn safe_decl_kind(ast: &dyn Ast<'_>) -> Option<z3::DeclKind> {
        ast.safe_decl().ok().map(|decl| decl.kind())
    }

    let ctx = &pair.get_ureal().as_real().get_ctx();
    let is_infty = pair.is_infinity();
    let value = pair.get_ureal();
    if is_infty.safe_decl().is_ok() && value.as_real().safe_decl().is_ok() {
        // whether the is_infinity expression is a conversion from a datatype
        // which looks like `ite(is_infty(inner_expr), true, false)`
        let is_infty_datatype = safe_decl_kind(is_infty) == Some(z3::DeclKind::ITE)
            && safe_decl_kind(&is_infty.nth_child(0).unwrap()) == Some(z3::DeclKind::DT_IS)
            && is_infty.nth_child(0).unwrap().decl().name() == factory.rplus_is_inf.name()
            && is_infty.nth_child(1).unwrap() == Dynamic::from_ast(&Bool::from_bool(ctx, true))
            && is_infty.nth_child(2).unwrap() == Dynamic::from_ast(&Bool::from_bool(ctx, false));
        if is_infty_datatype {
            // extract the inner datatype expression
            let inner_datatype_expr = is_infty.nth_child(0).unwrap().nth_child(0).unwrap();
            assert!(inner_datatype_expr.get_sort() == factory.sort);

            // whether the value expression is a conversion from a datatype which
            // looks like `ite(is_infty(inner_expr), rplus_mk_inf(),
            // rplus_get_real(inner_expr))`
            let is_value_datatype = safe_decl_kind(value.as_real()) == Some(z3::DeclKind::ITE)
                && value.as_real().nth_child(0).unwrap().decl().name()
                    == factory.rplus_is_inf.name()
                && value.as_real().nth_child(1).unwrap()
                    == Dynamic::from_ast(&Real::from_real(ctx, 1, 1))
                && safe_decl_kind(&value.as_real().nth_child(2).unwrap())
                    == Some(z3::DeclKind::DT_ACCESSOR)
                && value.as_real().nth_child(2).unwrap().decl().name()
                    == factory.rplus_get_real.name()
                && value.as_real().nth_child(2).unwrap().nth_child(0).unwrap()
                    == inner_datatype_expr;
            // if pattern matching was successful, we can short-circuit
            if is_value_datatype {
                return Some(datatype::EUReal::from_dynamic(
                    factory,
                    &inner_datatype_expr,
                ));
            }
        }
    };
    None
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
