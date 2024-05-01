//! Models and automata.

use std::{num::NonZeroUsize, ops::Not};

use serde::{Deserialize, Serialize};

use crate::{exprs::Expression, properties::Property, types::Type, Identifier};

/// An element of a [`Composition`].
#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct CompositionElement {
    /// The name of the automaton.
    pub automaton: Identifier,
    /// a set of action names on which to make the automaton input-enabled; for
    /// CTMC and CTMDP, the new transitions have rate 1.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub input_enable: Option<Vec<Identifier>>,
    /// An optional comment.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<Box<str>>,
}

/// Synchronisations in a [`Composition`].
#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct CompositionSync {
    /// A list of action names or null, same length as `elements` of the
    /// composition.
    pub synchronise: Vec<Option<Identifier>>,
    /// An action name, the result of the synchronisation; if omitted, it is the
    /// silent action.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub result: Option<Identifier>,
    /// An optional comment.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<Box<str>>,
}

/// Automata composition.
#[derive(Serialize, Deserialize, Debug, Default)]
pub struct Composition {
    /// The automata in the composition.
    pub elements: Vec<CompositionElement>,
    /// Synchronisations in this composition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub syncs: Option<Vec<CompositionSync>>,
    /// An optional comment.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<Box<str>>,
}

/// Metadata about the [`Model`].
#[derive(Serialize, Deserialize, Debug, Default)]
pub struct Metadata {
    /// Information about the version of this model (e.g. the date when it was
    /// last modified).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub version: Option<Box<str>>,
    /// Information about the creator of the model.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub author: Option<Box<str>>,
    /// A description of the model.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub description: Option<Box<str>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    /// The DOI of the paper where this model was introduced/used/described.
    pub doi: Option<Box<str>>,
    /// A URL pointing to more information about the model.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub url: Option<Box<str>>,
}

/// The type of model. Influences which features can be used.
#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub enum ModelType {
    /// LTS: a labelled transition system (or Kripke structure or finite state
    /// automaton) (untimed).
    Lts,
    /// DTMC: a discrete-time Markov chain (untimed).
    Dtmc,
    /// CTMC: a continuous-time Markov chain (timed).
    Ctmc,
    ///  MDP: a discrete-time Markov decision process (untimed).
    Mdp,
    /// CTMDP: a continuous-time Markov decision process (timed).
    Ctmdp,
    /// MA: a Markov automaton (timed).
    Ma,
    /// TA: a timed automaton (timed).
    Ta,
    /// PTA: a probabilistic timed automaton (timed).
    Pta,
    /// STA: a stochastic timed automaton (timed).
    Sta,
    /// HA: a hybrid automaton (timed).
    Ha,
    /// PHA: a probabilistic hybrid automaton (timed).
    Pha,
    /// SHA: a stochastic hybrid automaton (timed).
    Sha,
}

/// Certain features to enable for the model.
#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub enum ModelFeature {
    /// Support for array types.
    Arrays,
    /// Support for complex datatypes.
    Datatypes,
    /// Support for some derived operators in expressions
    DerivedOperators,
    /// Support for priorities on edges.
    EdgePriorities,
    /// Support for functions.
    Functions,
    /// Support for hyperbolic functions.
    HyperbolicFunctions,
    /// Support for named subexpressions.
    NamedExpressions,
    /// Support for nondeterministic selection.
    NondetSelection,
    /// Support for accumulating rewards when leaving a state.
    StateExitRewards,
    /// Support for multi-objective tradeoff properties.
    TradeoffProperties,
    /// Support for trigonometric functions.
    TrigonometricFunctions,
    /// Names starting with "x-" will not be defined in the JANI spec and are
    /// available for internal use.
    Other(String),
}

/// A variable declaration.
#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct VariableDeclaration {
    /// Names starting with "x-" will not be defined and are available for internal use.
    pub name: Identifier,
    /// The variable's name, unique among all constants and global variables as
    /// well as among local variables if the variable is declared within an
    /// automaton.
    #[serde(rename = "type")]
    pub typ: Type,
    /// Transient variable if present and true; a transient variable behaves as
    /// follows:
    /// * when in a state, its value is that of the expression specified in
    ///   `transient_values` for the locations corresponding to that state, or
    ///   its initial value if no expression is specified in any of the
    ///   locations (and if multiple expressions are specified, that is a
    ///   modelling error);
    /// * when taking a transition, its value is set to its initial value, then
    ///   all assignments of the edges corresponding to the transition are
    ///   executed.
    #[serde(default, skip_serializing_if = "Not::not")]
    pub transient: bool,
    /// If omitted: any value allowed by type (possibly restricted by the
    /// `restrict_initial` attributes of the model or an automaton); must be
    /// present if transient is present and true.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub initial_value: Option<Box<Expression>>,
    /// An optional comment.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<Box<str>>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct ConstantDeclaration {
    /// The constant's name, unique among all constants and variables.
    pub name: Identifier,
    /// The constant's type; bounded types must not refer to this constant or
    /// constants declared after this one in the corresponding array.
    #[serde(rename = "type")]
    pub typ: Type, // TODO: OtherType is not allowed
    /// The constant's value, of type type; constant expression that must not
    /// refer to this constant or constants declared after this one in the
    /// corresponding array if omitted, the constant is a model parameter.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value: Option<Box<Expression>>,
    /// An optional comment.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<Box<str>>,
}

/// Actions of a [`Model`].
#[derive(Serialize, Deserialize, Debug)]
pub struct ModelAction {
    pub name: Identifier,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<Box<str>>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct CommentedExpression {
    pub exp: Expression,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<Box<String>>,
}

impl From<Expression> for CommentedExpression {
    fn from(value: Expression) -> Self {
        CommentedExpression {
            exp: value,
            comment: None,
        }
    }
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct Model {
    pub jani_version: NonZeroUsize,
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<Metadata>,
    #[serde(rename = "type")]
    pub typ: ModelType,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub features: Vec<ModelFeature>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub actions: Vec<ModelAction>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub constants: Vec<ConstantDeclaration>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub variables: Vec<VariableDeclaration>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub restrict_initial: Option<CommentedExpression>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub properties: Vec<Property>,
    pub automata: Vec<Automaton>,
    pub system: Composition,
}

impl Model {
    pub fn new(typ: ModelType) -> Self {
        Self {
            jani_version: NonZeroUsize::new(1).unwrap(),
            name: Default::default(),
            metadata: Default::default(),
            typ,
            features: Default::default(),
            actions: Default::default(),
            constants: Default::default(),
            variables: Default::default(),
            restrict_initial: Default::default(),
            properties: Default::default(),
            automata: Default::default(),
            system: Default::default(),
        }
    }
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct TransientValue {
    #[serde(rename = "ref")]
    pub reference: Identifier,
    pub value: Expression,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<Box<str>>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct Location {
    pub name: Identifier,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub time_progress: Option<CommentedExpression>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub transient_values: Option<Vec<TransientValue>>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct Assignment {
    #[serde(rename = "ref")]
    pub reference: Identifier,
    pub value: Expression,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub index: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<Box<str>>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct Destination {
    pub location: Identifier,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub probability: Option<CommentedExpression>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub assignments: Vec<Assignment>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<Box<str>>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct Edge {
    pub location: Identifier,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub action: Option<Identifier>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rate: Option<CommentedExpression>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub guard: Option<CommentedExpression>,
    pub destinations: Vec<Destination>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<Box<str>>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "kebab-case")]
pub struct Automaton {
    pub name: Identifier,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub variables: Vec<VariableDeclaration>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub restrict_initial: Option<CommentedExpression>,
    pub locations: Vec<Location>,
    pub initial_locations: Vec<Identifier>,
    pub edges: Vec<Edge>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comment: Option<Box<str>>,
}
