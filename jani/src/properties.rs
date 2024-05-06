//! Properties to specify about JANI models.

use serde::{Deserialize, Serialize};

use crate::{exprs::Expression, Identifier};

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct PropertyInterval {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lower: Option<Expression>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lower_exclusive: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub upper: Option<Expression>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub upper_exclusive: Option<bool>,
}

pub type RewardAccumulation = Vec<Reward>;

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub enum Reward {
    Steps,
    Time,
    /// Needs [`super::models::ModelFeature::StateExitRewards`].
    Exit,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "lowercase")]
pub enum FilterFun {
    Min,
    Max,
    Sum,
    #[serde(rename = "avg")]
    Average,
    Count,
    #[serde(rename = "∀")]
    Forall,
    #[serde(rename = "∃")]
    Exists,
    Argmin,
    Argmax,
    Values,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(tag = "op", rename = "filter")]
pub struct FilterExpression {
    pub fun: FilterFun,
    pub values: Box<PropertyExpression>,
    pub states: Box<PropertyExpression>,
}

#[derive(Serialize, Deserialize, Debug)]
pub enum Quantifier {
    #[serde(rename = "Pmin")]
    Pmin,
    #[serde(rename = "Pmax")]
    Pmax,
    #[serde(rename = "∀")]
    Forall,
    #[serde(rename = "∃")]
    Exists,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct QuantifiedExpression {
    pub op: Quantifier,
    pub exp: Box<PropertyExpression>,
}

#[derive(Serialize, Deserialize, Debug)]
pub enum UntilExpressionKind {
    #[serde(rename = "U")]
    Until,
    #[serde(rename = "W")]
    WeakUntil,
    #[serde(rename = "R")]
    Release,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct RewardBound {
    pub exp: Expression,
    pub accumulate: RewardAccumulation,
    pub bounds: PropertyInterval,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct UntilExpression {
    pub op: UntilExpressionKind,
    pub left: Box<PropertyExpression>,
    pub right: Box<PropertyExpression>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub step_bounds: Option<PropertyInterval>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub time_bounds: Option<PropertyInterval>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reward_bounds: Option<Vec<RewardBound>>,
}

#[derive(Serialize, Deserialize, Debug)]
pub enum UnaryPathExpressionKind {
    #[serde(rename = "F")]
    Finally,
    #[serde(rename = "G")]
    Globally,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct UnaryPathExpression {
    pub op: UnaryPathExpressionKind,
    pub exp: Box<PropertyExpression>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub step_bounds: Option<PropertyInterval>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub time_bounds: Option<PropertyInterval>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reward_bounds: Option<Vec<RewardBound>>,
}

#[derive(Serialize, Deserialize, Debug)]
pub enum ExpectedValueKind {
    Emin,
    Emax,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct RewardInstant {
    pub exp: Expression,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub accumulate: Option<RewardAccumulation>,
    pub instant: Expression,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct ExpectedValueExpression {
    pub op: ExpectedValueKind,
    pub exp: Expression,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub accumulate: Option<RewardAccumulation>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reach: Option<Box<PropertyExpression>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub step_instant: Option<Expression>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub time_instant: Option<Expression>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reward_instants: Option<Vec<RewardInstant>>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(tag = "op", rename_all = "kebab-case")]
pub enum StatePredicate {
    Initial,
    Deadlock,
    Timelock,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(untagged)]
pub enum PropertyExpression {
    Expression(Expression),
    Filter(FilterExpression),
    Quantified(QuantifiedExpression),
    ExpectedValue(ExpectedValueExpression),
    // TODO: long-run average
    Until(UntilExpression),
    UnaryPath(UnaryPathExpression),
    Predicate(StatePredicate),
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Property {
    pub name: Identifier,
    pub expression: PropertyExpression,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<Box<str>>,
}
