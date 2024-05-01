//! Extraction of quantitative specifications and conversion to JANI equivalents.

use jani::{
    exprs::{BinaryExpression, BinaryOp, ConstantValue, Expression},
    models::{Destination, Edge, Location, TransientValue, VariableDeclaration},
    properties::{
        ExpectedValueExpression, ExpectedValueKind, FilterExpression, FilterFun, Property,
        PropertyExpression, Reward, StatePredicate,
    },
    types::{BasicType, Type},
    Identifier,
};

use crate::ast::{
    BinOpKind, Direction, ExprBuilder, ExprKind, Span, Stmt, StmtKind, TyKind, UnOpKind,
};

use super::{translate_expr, JaniConversionError};

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
    spec_part: &SpecAutomaton,
    stmts: &mut Vec<Stmt>,
) -> Result<JaniPgclProperties, JaniConversionError> {
    let spec = mk_expected_reward_property(spec_part, false, "spec");
    let spec_liberal = mk_expected_reward_property(spec_part, true, "spec_strict");

    let restrict_initial = extract_preconditions(spec_part, stmts)?;
    let sink_reward = extract_post(spec_part, stmts)?;

    Ok(JaniPgclProperties {
        restrict_initial,
        properties: vec![spec, spec_liberal],
        sink_reward,
    })
}

fn mk_expected_reward_property(
    spec_part: &SpecAutomaton,
    until_sink_only: bool,
    name: &str,
) -> Property {
    let reach = if until_sink_only {
        Expression::Identifier(spec_part.var_is_sink_state())
    } else {
        Expression::Binary(Box::new(BinaryExpression {
            op: BinaryOp::Or,
            left: Expression::Identifier(spec_part.var_is_error_state()),
            right: Expression::Identifier(spec_part.var_is_sink_state()),
        }))
    };

    let expected_value = PropertyExpression::ExpectedValue(ExpectedValueExpression {
        op: spec_part
            .direction
            .map(ExpectedValueKind::Emin, ExpectedValueKind::Emax),
        exp: Expression::Identifier(spec_part.var_reward()),
        accumulate: Some(vec![Reward::Steps, Reward::Exit]), // TODO: what the fuck does this do?
        reach: Some(Box::new(PropertyExpression::Expression(reach))),
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

/// Eat Boolean assumptions from the beginning of the program and convert them
/// to a Boolean precondition.
fn extract_preconditions(
    spec_part: &SpecAutomaton,
    stmts: &mut Vec<Stmt>,
) -> Result<Expression, JaniConversionError> {
    let mut restrict_initial = vec![];
    while let Some(first) = stmts.first() {
        if let StmtKind::Assume(direction, expr) = through_annotation(first) {
            if *direction != spec_part.direction {
                return Err(JaniConversionError::MismatchedDirection(first.span));
            }
            if let ExprKind::Unary(un_op, operand) = &expr.kind {
                if un_op.node != UnOpKind::Embed {
                    return Err(JaniConversionError::UnsupportedAssume(expr.clone()));
                }
                let mut operand = operand.clone();
                if spec_part.direction == Direction::Up {
                    let builder = ExprBuilder::new(Span::dummy_span());
                    operand = builder.unary(UnOpKind::Not, Some(TyKind::Bool), operand);
                }
                restrict_initial.push(operand.clone());
                stmts.remove(0);
            } else {
                return Err(JaniConversionError::UnsupportedAssume(expr.clone()));
            }
        } else {
            break;
        }
    }

    let expr_builder = ExprBuilder::new(Span::dummy_span());
    let direction = spec_part.direction;
    let bin_op = direction.map(BinOpKind::And, BinOpKind::Or);
    let default = direction == Direction::Down;
    let restrict_initial = restrict_initial
        .into_iter()
        .reduce(|acc, e| expr_builder.binary(bin_op, Some(TyKind::Bool), acc, e))
        .unwrap_or_else(|| expr_builder.bool_lit(default));
    translate_expr(&restrict_initial)
}

/// Eat (co)assert statements from the end of the statements and return a single
/// JANI expression that represents the post.
///
/// These (co)assert statements may be quantitative.
fn extract_post(
    spec_part: &SpecAutomaton,
    stmts: &mut Vec<Stmt>,
) -> Result<Expression, JaniConversionError> {
    let mut posts = vec![];
    while let Some(last) = stmts.last() {
        if let StmtKind::Assert(direction, expr) = through_annotation(last) {
            if *direction != spec_part.direction {
                return Err(JaniConversionError::MismatchedDirection(last.span));
            }
            posts.push(expr.clone());
            stmts.pop();
        } else {
            break;
        }
    }

    let expr_builder = ExprBuilder::new(Span::dummy_span());
    let bin_op = spec_part.direction.map(BinOpKind::Inf, BinOpKind::Sup);
    let sink_reward = posts
        .into_iter()
        .reduce(|acc, e| expr_builder.binary(bin_op, Some(TyKind::EUReal), acc, e))
        .unwrap_or_else(|| match spec_part.direction {
            Direction::Down => expr_builder.top_lit(&TyKind::EUReal),
            Direction::Up => expr_builder.bot_lit(&TyKind::EUReal),
        });
    translate_expr(&sink_reward)
}

fn through_annotation(stmt: &Stmt) -> &StmtKind {
    match stmt.node {
        StmtKind::Annotation(_, _, ref inner) => &inner.node,
        _ => &stmt.node,
    }
}
