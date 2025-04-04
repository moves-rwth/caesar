//! Expressions in JANI.

use std::{
    fmt::Display,
    ops::{Add, BitAnd, BitOr, Mul, Not, Sub},
};

use serde::{Deserialize, Serialize};

use crate::Identifier;

pub use serde_json::Number;

/// Mathematical constants that cannot be expressed using numeric values and
/// basic jani-model expressions.
#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq)]
pub enum MathConstant {
    /// Euler's number (the base of the natural logarithm); type real.
    #[serde(rename = "e")]
    EulersNumber,
    /// π (the ratio of a circle's circumference to its diameter); type real.
    #[serde(rename = "π")]
    Pi,
}

impl Display for MathConstant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MathConstant::EulersNumber => write!(f, "e"),
            MathConstant::Pi => write!(f, "π"),
        }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(untagged)]
pub enum ConstantValue {
    /// Numeric value; has type int if it is an integer and type real otherwise.
    Number(serde_json::Number),
    /// Boolean value; has type bool.
    Boolean(bool),
    /// Mathematical constants that cannot be expressed using numeric values and
    /// basic jani-model expressions.
    MathConstant(MathConstant),
}

impl From<u64> for ConstantValue {
    fn from(value: u64) -> Self {
        ConstantValue::Number(value.into())
    }
}

/// This error is emitted from the [`TryFrom<f64>`] implementation for
/// [`ConstantValue`] if the value is not finie (e.g. NaN or infinity).
#[derive(Debug)]
pub struct NotFiniteNumberError;

impl TryFrom<f64> for ConstantValue {
    type Error = NotFiniteNumberError;

    fn try_from(value: f64) -> Result<Self, Self::Error> {
        serde_json::Number::from_f64(value)
            .map(ConstantValue::Number)
            .ok_or(NotFiniteNumberError)
    }
}

impl From<bool> for ConstantValue {
    fn from(value: bool) -> Self {
        ConstantValue::Boolean(value)
    }
}

impl Display for ConstantValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstantValue::Number(n) => write!(f, "{}", n),
            ConstantValue::Boolean(b) => write!(f, "{}", b),
            ConstantValue::MathConstant(c) => write!(f, "{}", c),
        }
    }
}

/// If-then-else: computes if `if` then `left` else `right`.
///
/// The result type is the type of `left` if that is assignable from the type of
/// `right`, or the type of `right` if that is assignable from the type of `left`
/// (previously: the result type is the most specific type assignable from the
/// types of then and else).
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(tag = "op", rename = "ite")]
pub struct IteExpression {
    #[serde(rename = "if")]
    pub cond: Expression,
    #[serde(rename = "then")]
    pub left: Expression,
    #[serde(rename = "else")]
    pub right: Expression,
}

/// JANI operators with one operand.
#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// Negation: computes `¬exp`.
    #[serde(rename = "¬")]
    Not,
    /// Floor: computes `⌊exp⌋`.
    #[serde(rename = "floor")]
    Floor,
    /// Ceiling: computes `⌈exp⌉`.
    #[serde(rename = "ceil")]
    Ceil,
    /// Derivative: refers to the first derivative of x; only allowed in HA, PHA
    /// and SHA; not a constant expression. The operand must be a continuous
    /// global variable.
    #[serde(rename = "der")]
    Derivative,
}

/// JANI expressions with one operand.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct UnaryExpression {
    pub op: UnaryOp,
    pub exp: Expression,
}

/// JANI operators with two operands.
#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    #[serde(rename = "∨")]
    Or,
    #[serde(rename = "∧")]
    And,
    #[serde(rename = "=")]
    Equals,
    #[serde(rename = "≠")]
    NotEquals,
    #[serde(rename = "<")]
    Less,
    #[serde(rename = "≤")]
    LessOrEqual,
    #[serde(rename = "+")]
    Plus,
    #[serde(rename = "-")]
    Minus,
    #[serde(rename = "*")]
    Times,
    #[serde(rename = "%")]
    Modulo,
    #[serde(rename = "/")]
    Divide,
    #[serde(rename = "pow")]
    Pow,
    #[serde(rename = "log")]
    Log,

    #[serde(rename = "⇒")]
    Implication,
    #[serde(rename = ">")]
    Greater,
    #[serde(rename = "≥")]
    GreaterOrEqual,
    #[serde(rename = "min")]
    Min,
    #[serde(rename = "max")]
    Max,
    // TODO: add other derived operators!
}

/// JANI expressions with two operands.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct BinaryExpression {
    pub op: BinaryOp,
    pub left: Expression,
    pub right: Expression,
}

/// Nondeterministic selection (needs
/// [`super::models::ModelFeature::NondetSelection`]).
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(tag = "op", rename = "nondet")]
pub struct NondetSelectionExpression {
    var: Identifier,
    exp: Expression,
}

/// Function call (needs [`super::models::ModelFeature::Functions`]).
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(tag = "op", rename = "call")]
pub struct CallExpression {
    pub function: Identifier,
    pub args: Vec<Expression>,
}

/// JANI expressions.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(untagged)]
pub enum Expression {
    Constant(ConstantValue),
    Identifier(Identifier),
    IfThenElse(Box<IteExpression>),
    Unary(Box<UnaryExpression>),
    Binary(Box<BinaryExpression>),
    // TODO: DistributionSampling
    NondetSelection(Box<NondetSelectionExpression>),
    /// Function calls need [`super::models::ModelFeature::Functions`].
    Call(Box<CallExpression>),
}

impl<T> From<T> for Expression
where
    T: Into<ConstantValue>,
{
    fn from(value: T) -> Self {
        Expression::Constant(value.into())
    }
}

impl From<Identifier> for Expression {
    fn from(id: Identifier) -> Self {
        Expression::Identifier(id)
    }
}

impl From<IteExpression> for Expression {
    fn from(ite: IteExpression) -> Self {
        Expression::IfThenElse(Box::new(ite))
    }
}

impl From<UnaryExpression> for Expression {
    fn from(unary: UnaryExpression) -> Self {
        Expression::Unary(Box::new(unary))
    }
}

impl From<BinaryExpression> for Expression {
    fn from(binary: BinaryExpression) -> Self {
        Expression::Binary(Box::new(binary))
    }
}

impl From<CallExpression> for Expression {
    fn from(call: CallExpression) -> Self {
        Expression::Call(Box::new(call))
    }
}

/// Logical "NOT" operator for expressions.
impl Not for Expression {
    type Output = Self;

    fn not(self) -> Self::Output {
        UnaryExpression {
            op: UnaryOp::Not,
            exp: self,
        }
        .into()
    }
}

/// Logical "OR" operator for expressions.
impl BitOr for Expression {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        BinaryExpression {
            op: BinaryOp::Or,
            left: self,
            right: rhs,
        }
        .into()
    }
}

/// Logical "AND" operator for expressions.
impl BitAnd for Expression {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        BinaryExpression {
            op: BinaryOp::And,
            left: self,
            right: rhs,
        }
        .into()
    }
}

/// Addition operator for expressions.
impl Add for Expression {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        BinaryExpression {
            op: BinaryOp::Plus,
            left: self,
            right: rhs,
        }
        .into()
    }
}

/// Subtraction operator for expressions.
impl Sub for Expression {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        BinaryExpression {
            op: BinaryOp::Minus,
            left: self,
            right: rhs,
        }
        .into()
    }
}

/// Multiplication operator for expressions.
impl Mul for Expression {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        BinaryExpression {
            op: BinaryOp::Times,
            left: self,
            right: rhs,
        }
        .into()
    }
}

pub type LValue = Identifier;
