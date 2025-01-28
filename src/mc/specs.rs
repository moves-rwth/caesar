//! Extraction of quantitative specifications and conversion to JANI equivalents.

use jani::{
    exprs::{ConstantValue, Expression, UnaryExpression, UnaryOp},
    models::{Destination, Edge, Location, TransientValue, VariableDeclaration},
    properties::{
        ExpectedValueExpression, ExpectedValueKind, FilterExpression, FilterFun, Property,
        PropertyExpression, QuantifiedExpression, Quantifier, Reward, StatePredicate,
        UnaryPathExpression, UnaryPathExpressionKind,
    },
    types::{BasicType, Type},
    Identifier,
};

use crate::ast::{
    util::{is_dir_top_lit, is_top_lit},
    BinOpKind, Direction, ExprBuilder, Span, Stmt, StmtKind, TyKind, UnOpKind,
};

use super::{extract_embed, translate_expr, JaniConversionError};

/// The part of the automaton that's just for encoding the specification, such
/// as end, error, or miracle states.
pub struct SpecAutomaton {
    pub direction: Direction,
}

impl SpecAutomaton {
    pub fn new(direction: Direction) -> SpecAutomaton {
        SpecAutomaton { direction }
    }

    #[allow(clippy::vec_init_then_push)]
    pub fn get_variables(&self) -> Vec<VariableDeclaration> {
        let mut variables = vec![];

        // Reward transient variable
        variables.push(VariableDeclaration {
            name: self.var_reward(),
            typ: Type::BasicType(BasicType::Int), // integer type for now
            transient: true,
            initial_value: Some(Box::new(Expression::Constant(ConstantValue::Number(
                0.into(),
            )))),
            comment: None,
        });
        // is_sink_state transient variable
        variables.push(VariableDeclaration {
            name: self.var_is_sink_state(),
            typ: Type::BasicType(BasicType::Bool),
            transient: true,
            initial_value: Some(Box::new(Expression::Constant(ConstantValue::Boolean(
                false,
            )))),
            comment: None,
        });
        // is_error_state transient variable
        variables.push(VariableDeclaration {
            name: self.var_is_error_state(),
            typ: Type::BasicType(BasicType::Bool),
            transient: true,
            initial_value: Some(Box::new(Expression::Constant(ConstantValue::Boolean(
                false,
            )))),
            comment: None,
        });
        variables
    }

    pub fn var_reward(&self) -> Identifier {
        Identifier("reward".to_string())
    }

    pub fn end_location(&self) -> Identifier {
        Identifier("↓".to_string())
    }

    pub fn sink_location(&self) -> Identifier {
        Identifier("sink".to_string())
    }

    pub fn var_is_sink_state(&self) -> Identifier {
        Identifier("is_sink_state".to_string())
    }

    pub fn error_location(&self) -> Identifier {
        Identifier("↯".to_string())
    }

    pub fn var_is_error_state(&self) -> Identifier {
        Identifier("is_error_location".to_string())
    }

    pub fn finish(
        self,
        locations: &mut Vec<Location>,
        edges: &mut Vec<Edge>,
        expectation: Expression,
    ) {
        // end location
        locations.push(Location {
            name: self.end_location(),
            time_progress: None,
            transient_values: Some(vec![TransientValue {
                reference: self.var_reward(),
                value: expectation,
                comment: None,
            }]),
        });
        // sink location
        locations.push(Location {
            name: self.sink_location(),
            time_progress: None,
            transient_values: Some(vec![TransientValue {
                reference: self.var_is_sink_state(),
                value: Expression::Constant(ConstantValue::Boolean(true)),
                comment: None,
            }]),
        });
        // error location
        locations.push(Location {
            name: self.error_location(),
            time_progress: None,
            transient_values: Some(vec![TransientValue {
                reference: self.var_is_error_state(),
                value: Expression::Constant(ConstantValue::Boolean(true)),
                comment: None,
            }]),
        });

        // edge from end to sink
        edges.push(Edge {
            location: self.end_location(),
            action: None,
            rate: None,
            guard: None,
            destinations: vec![Destination {
                location: self.sink_location(),
                probability: None,
                assignments: vec![],
                comment: None,
            }],
            comment: None,
        });

        // edge from error to sink
        edges.push(Edge {
            location: self.error_location(),
            action: None,
            rate: None,
            guard: None,
            destinations: vec![Destination {
                location: self.sink_location(),
                probability: None,
                assignments: vec![],
                comment: None,
            }],
            comment: None,
        });
    }
}

/// The extracted JANI properties.
pub struct JaniPgclProperties {
    /// A Boolean expression to restrict the initial states.
    pub restrict_initial: Expression,
    /// The list of JANI properties.
    pub properties: Vec<Property>,
    /// The reward to attach to the sink state.
    pub sink_reward: Expression,
}

pub fn extract_properties(
    proc_span: Span,
    spec_part: &SpecAutomaton,
    stmts: &mut Vec<Stmt>,
    skip_quant_pre: bool,
) -> Result<JaniPgclProperties, JaniConversionError> {
    let reward = mk_expected_reward_property(spec_part, "reward");
    let diverge_prob = mk_diverge_prob_property(spec_part, "diverge_prob");
    let can_diverge = mk_can_diverge_property(spec_part, "can_diverge");

    let restrict_initial = extract_preconditions(spec_part, stmts, skip_quant_pre)?;
    let sink_reward = extract_post(proc_span, spec_part, stmts)?;

    Ok(JaniPgclProperties {
        restrict_initial,
        properties: vec![reward, diverge_prob, can_diverge],
        sink_reward,
    })
}

fn mk_expected_reward_property(spec_part: &SpecAutomaton, name: &str) -> Property {
    let expected_value = PropertyExpression::ExpectedValue(ExpectedValueExpression {
        op: spec_part
            .direction
            .map(ExpectedValueKind::Emin, ExpectedValueKind::Emax),
        exp: Expression::Identifier(spec_part.var_reward()),
        accumulate: Some(vec![Reward::Steps, Reward::Exit]), // TODO: what the fuck does this do?
        // we want total expected rewards. expected rewards until reaching a goal has very strange semantics.
        reach: None,
        step_instant: None,
        time_instant: None,
        reward_instants: None,
    });
    let expected_value_from_initial = PropertyExpression::Filter(FilterExpression {
        fun: FilterFun::Values,
        values: Box::new(expected_value),
        states: Box::new(PropertyExpression::Predicate(StatePredicate::Initial)),
    });
    Property {
        name: Identifier(name.to_owned()),
        expression: expected_value_from_initial,
        comment: None,
    }
}

fn mk_diverge_path(spec_part: &SpecAutomaton) -> UnaryPathExpression {
    UnaryPathExpression {
        op: UnaryPathExpressionKind::Globally,
        exp: Box::new(PropertyExpression::Expression(Expression::Unary(Box::new(
            UnaryExpression {
                op: UnaryOp::Not,
                exp: Expression::Identifier(spec_part.var_is_sink_state()),
            },
        )))),
        step_bounds: None,
        time_bounds: None,
        reward_bounds: None,
    }
}

fn mk_diverge_prob_property(spec_part: &SpecAutomaton, name: &str) -> Property {
    let quantifier = match spec_part.direction {
        Direction::Down => Quantifier::Pmin,
        Direction::Up => Quantifier::Pmax,
    };
    let diverge_prob = PropertyExpression::Quantified(QuantifiedExpression {
        op: quantifier,
        exp: Box::new(PropertyExpression::UnaryPath(mk_diverge_path(spec_part))),
    });
    let diverge_prob_from_initial = PropertyExpression::Filter(FilterExpression {
        fun: FilterFun::Values,
        values: Box::new(diverge_prob),
        states: Box::new(PropertyExpression::Predicate(StatePredicate::Initial)),
    });
    Property {
        name: Identifier(name.to_owned()),
        expression: diverge_prob_from_initial,
        comment: None,
    }
}

fn mk_can_diverge_property(spec_part: &SpecAutomaton, name: &str) -> Property {
    let can_diverge = PropertyExpression::Quantified(QuantifiedExpression {
        op: Quantifier::Exists,
        exp: Box::new(PropertyExpression::UnaryPath(mk_diverge_path(spec_part))),
    });
    let can_diverge_from_initial = PropertyExpression::Filter(FilterExpression {
        fun: FilterFun::Values,
        values: Box::new(can_diverge),
        states: Box::new(PropertyExpression::Predicate(StatePredicate::Initial)),
    });
    Property {
        name: Identifier(name.to_owned()),
        expression: can_diverge_from_initial,
        comment: None,
    }
}

/// Eat Boolean assumptions from the beginning of the program and convert them
/// to a Boolean precondition.
fn extract_preconditions(
    spec_part: &SpecAutomaton,
    stmts: &mut Vec<Stmt>,
    skip_quant_pre: bool,
) -> Result<Expression, JaniConversionError> {
    let mut restrict_initial = vec![];
    while let Some(first) = stmts.first() {
        if let StmtKind::Assume(direction, expr) = through_annotation(first) {
            if *direction != spec_part.direction {
                return Err(JaniConversionError::MismatchedDirection(first.span));
            }
            if let Some(operand) = extract_embed(expr) {
                let mut operand = operand.clone();
                if spec_part.direction == Direction::Up {
                    // TODO: if one used the !?(b) idiom, we'd have !!b in the end. optimize that
                    let builder = ExprBuilder::new(Span::dummy_span());
                    operand = builder.unary(UnOpKind::Not, Some(TyKind::Bool), operand);
                }
                restrict_initial.push(operand);
            } else if !skip_quant_pre {
                return Err(JaniConversionError::UnsupportedPre(expr.clone()));
            }
            stmts.remove(0);
        } else {
            break;
        }
    }

    // regardless of the direction, we conjunct all the preconditions we collected
    let expr_builder = ExprBuilder::new(Span::dummy_span());
    let restrict_initial = restrict_initial
        .into_iter()
        .reduce(|acc, e| expr_builder.binary(BinOpKind::And, Some(TyKind::Bool), acc, e))
        .unwrap_or_else(|| expr_builder.bool_lit(true));
    translate_expr(&restrict_initial)
}

/// Eat (co)assert statements from the end of the statements and return a single
/// JANI expression that represents the post.
///
/// These (co)assert statements may be quantitative.
fn extract_post(
    proc_span: Span,
    spec_part: &SpecAutomaton,
    stmts: &mut Vec<Stmt>,
) -> Result<Expression, JaniConversionError> {
    let mut posts = vec![];
    let mut first_infty_post = None;
    while let Some(last) = stmts.last() {
        if let StmtKind::Assert(direction, expr) = through_annotation(last) {
            if *direction != spec_part.direction {
                return Err(JaniConversionError::MismatchedDirection(last.span));
            }
            if is_top_lit(expr) {
                first_infty_post = Some(expr.clone());
            }
            posts.push(expr.clone());
            stmts.pop();
        } else {
            break;
        }
    }

    let expr_builder = ExprBuilder::new(proc_span);
    let bin_op = spec_part.direction.map(BinOpKind::Inf, BinOpKind::Sup);
    let sink_reward = posts
        .into_iter()
        .filter(|post| !is_dir_top_lit(spec_part.direction, post))
        .reduce(|acc, e| expr_builder.binary(bin_op, Some(TyKind::EUReal), acc, e))
        .unwrap_or_else(|| match spec_part.direction {
            Direction::Down => expr_builder.top_lit(&TyKind::EUReal),
            Direction::Up => expr_builder.bot_lit(&TyKind::EUReal),
        });
    if is_top_lit(&sink_reward) {
        return Err(JaniConversionError::UnsupportedInftyPost(
            first_infty_post.unwrap_or(sink_reward),
        ));
    }
    translate_expr(&sink_reward)
}

fn through_annotation(stmt: &Stmt) -> &StmtKind {
    match stmt.node {
        StmtKind::Annotation(_, _, _, ref inner) => &inner.node,
        _ => &stmt.node,
    }
}
