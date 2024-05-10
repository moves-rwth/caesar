//! JANI types.

use serde::{Deserialize, Serialize};

use crate::exprs::Expression;

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "lowercase")]
pub enum BasicType {
    /// Booleans, assignable from booleans only.
    Bool,
    /// Numeric; assignable from int and bounded int.
    Int,
    /// Numeric; assignable from all numberic types.
    Real,
}

/// Numeric if `base` is numeric; `lower_bound` or `upper_bound` must be
/// present.
#[derive(Serialize, Deserialize, Debug)]
#[serde(tag = "kind", rename = "bounded", rename_all = "kebab-case")]
pub struct BoundedType {
    pub base: BoundedTypeBase,
    /// Smallest value allowed by the type; constant expression of the base type.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lower_bound: Option<Box<Expression>>,
    /// Largest value allowed by the type; constant expression of the base type.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub upper_bound: Option<Box<Expression>>,
}

impl BoundedType {
    /// This object is valid if there's a lower or an upper bound.
    pub fn is_valid(&self) -> bool {
        self.lower_bound.is_some() || self.upper_bound.is_some()
    }
}

/// Subset of [`BasicType`]s for [`BoundedType`]s.
#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "lowercase")]
pub enum BoundedTypeBase {
    Int,
    Real,
}

/// Other types for specific kinds of models.
#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "lowercase")]
pub enum OtherType {
    /// Numeric; only allowed for TA, PTA, STA, HA, PHA and SHA; assignable from int and bounded int.
    Clock,
    /// numeric; continuous variable that changes over time as allowed by the
    /// current location's invariant; only allowed for HA, PHA and SHA;
    /// assignable from all numeric types.
    Continuous,
}

/// JANI only supports basic types at the moment.
///
/// We represent types as an enum of other enums to simplify the serde
/// implementations.
#[derive(Serialize, Deserialize, Debug)]
#[serde(untagged)]
pub enum Type {
    BasicType(BasicType),
    BoundedType(BoundedType),
    OtherType(OtherType),
}
