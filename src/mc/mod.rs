//! Support for exporting HeyVL programs to JANI to run a model checker on them.

// TODO: handle name conflicts

use std::{convert::TryInto, mem};

use jani::{
    exprs::{
        BinaryExpression, BinaryOp, ConstantValue, Expression, IteExpression, UnaryExpression,
        UnaryOp,
    },
    models::{
        Assignment, Automaton, Composition, CompositionElement, ConstantDeclaration, Destination, Edge, Location, Metadata, Model, ModelFeature, ModelType, TransientValue, VariableDeclaration
    },
    properties::{
        ExpectedValueExpression, ExpectedValueKind, FilterExpression, FilterFun, Property,
        PropertyExpression, QuantifiedExpression, Reward, StatePredicate, UntilExpression,
        UntilExpressionKind,
    },
    types::{BasicType, BoundedType, BoundedTypeBase, Type},
    Identifier,
};

use crate::{
    ast::{
        visit::VisitorMut, BinOpKind, DeclRef, Direction, Expr, ExprBuilder, ExprKind, Ident,
        LitKind, ProcDecl, Span, Stmt, StmtKind, TyKind, UnOpKind, VarDecl,
    },
    procs::verify_proc,
    version::self_version_info,
};

#[derive(Debug)]
pub enum JaniConversionError {
    UnsupportedType(TyKind, Span),
    UnsupportedExpr(Expr),
    UnsupportedStmt(Box<Stmt>),
    UnsupportedAssume(Expr),
    UnsupportedAssert(Expr),
    NondetSelection(Span),
    MismatchedDirection(Span),
}

/// Intermediate structure to build the JANI automaton for pGCL semantics with
/// expected rewards.
struct AutomatonBuilder {
    direction: Direction,
    variables: Vec<VariableDeclaration>,
    locations: Vec<Location>,
    edges: Vec<Edge>,
}

impl AutomatonBuilder {
    fn new(direction: Direction) -> Self {
        let mut model = AutomatonBuilder {
            direction,
            variables: vec![],
            locations: vec![],
            edges: vec![],
        };

        // Reward transient variable
        model.variables.push(VariableDeclaration {
            name: model.reward_var(),
            typ: Type::BasicType(BasicType::Int), // integer type for now
            transient: true,
            initial_value: Some(Box::new(Expression::Constant(ConstantValue::Number(
                0.into(),
            )))),
            comment: None,
        });
        // is_sink_state transient variable
        model.variables.push(VariableDeclaration {
            name: model.is_sink_state_var(),
            typ: Type::BasicType(BasicType::Bool),
            transient: true,
            initial_value: Some(Box::new(Expression::Constant(ConstantValue::Boolean(
                false,
            )))),
            comment: None,
        });
        // is_error_state transient variable
        model.variables.push(VariableDeclaration {
            name: model.is_error_state_var(),
            typ: Type::BasicType(BasicType::Bool),
            transient: true,
            initial_value: Some(Box::new(Expression::Constant(ConstantValue::Boolean(
                false,
            )))),
            comment: None,
        });

        model
    }

    fn reward_var(&self) -> Identifier {
        Identifier("reward".to_string())
    }

    fn end_location(&self) -> Identifier {
        Identifier("↓".to_string())
    }

    fn sink_location(&self) -> Identifier {
        Identifier("sink".to_string())
    }

    fn is_sink_state_var(&self) -> Identifier {
        Identifier("is_sink_state".to_string())
    }

    fn error_location(&self) -> Identifier {
        Identifier("↯".to_string())
    }

    fn is_error_state_var(&self) -> Identifier {
        Identifier("is_error_location".to_string())
    }

    fn next_stmt_location(&self) -> Identifier {
        Identifier(format!("l{}", self.locations.len()))
    }

    fn finish(
        mut self,
        name: Identifier,
        initial_location: Identifier,
        expectation: Expression,
    ) -> Automaton {
        // end location
        self.locations.push(Location {
            name: self.end_location(),
            time_progress: None,
            transient_values: Some(vec![TransientValue {
                reference: self.reward_var(),
                value: expectation,
                comment: None,
            }]),
        });
        // sink location
        self.locations.push(Location {
            name: self.sink_location(),
            time_progress: None,
            transient_values: Some(vec![TransientValue {
                reference: self.is_sink_state_var(),
                value: Expression::Constant(ConstantValue::Boolean(true)),
                comment: None,
            }]),
        });
        // error location
        self.locations.push(Location {
            name: self.error_location(),
            time_progress: None,
            transient_values: Some(vec![TransientValue {
                reference: self.is_error_state_var(),
                value: Expression::Constant(ConstantValue::Boolean(true)),
                comment: None,
            }]),
        });

        // edge from end to sink
        self.edges.push(Edge {
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

        Automaton {
            name,
            variables: self.variables,
            restrict_initial: None,
            locations: self.locations,
            initial_locations: vec![initial_location],
            edges: self.edges,
            comment: None,
        }
    }
}

pub fn proc_to_model(proc: &ProcDecl) -> Result<Model, JaniConversionError> {
    let mut automaton = AutomatonBuilder::new(proc.direction);

    let (constants, variables) = translate_variables(proc)?;
    automaton.variables.extend(variables);

    let mut body = verify_proc(proc).unwrap();
    let property = extract_properties(&automaton, &mut body)?;

    let next = automaton.end_location();
    let start = translate_stmts(&mut automaton, &body, next)?;

    let automaton_name = Identifier(proc.name.to_string());
    let mut automaton = automaton.finish(automaton_name, start, property.sink_reward);

    // TODO: change to MDP if there's nondeterminism
    let mut model = Model::new(ModelType::Dtmc);

    // Metadata
    let mut metadata = Metadata::default();
    metadata.description = Some(
        format!(
            "Created by the Caesar deductive verifier ({}).",
            self_version_info()
        )
        .into_boxed_str(),
    );
    model.metadata = Some(metadata);

    // Features
    model.features.push(ModelFeature::DerivedOperators);
    model.features.push(ModelFeature::StateExitRewards);

    // Declare the proc inputs as model parameters
    // TODO: add an option to instead declare the proc parameters as
    // (indeterminate) inputs to the automaton
    model.constants.extend(constants);

    // Make all of the automaton's variables public so they can be accessed by
    // properties (in particular our reward property).
    model.variables = mem::take(&mut automaton.variables);

    // Restriction on initial states from the pre
    model.restrict_initial = Some(property.restrict_initial.into());

    // Add the properties
    model.properties.extend(property.properties);

    // The system consists just of the one automaton
    model.system = Composition {
        elements: vec![CompositionElement {
            automaton: automaton.name.clone(),
            input_enable: None,
            comment: None,
        }],
        syncs: None,
        comment: None,
    };

    // Add the automaton
    model.automata.push(automaton);

    Ok(model)
}

fn translate_variables(
    proc: &ProcDecl,
) -> Result<(Vec<ConstantDeclaration>, Vec<VariableDeclaration>), JaniConversionError> {
    #[derive(Default)]
    struct VarDeclCollector(Vec<VariableDeclaration>);

    impl VisitorMut for VarDeclCollector {
        type Err = JaniConversionError;

        fn visit_var_decl(&mut self, var_ref: &mut DeclRef<VarDecl>) -> Result<(), Self::Err> {
            let decl = var_ref.borrow();
            let mut comment = None;
            let initial_value = if let Some(initial_expr) = &decl.init {
                let res = if is_pure(initial_expr) {
                    // TODO: check if is pure and constant!!
                    translate_expr(initial_expr)?
                } else {
                    comment = Some(
                        "(initial value arbitrarily chosen by Caesar translation to reduce state space)"
                            .to_string()
                            .into_boxed_str(),
                    );
                    translate_expr(&ExprBuilder::new(Span::dummy_span()).bot_lit(&decl.ty))?
                };
                Some(Box::new(res))
            } else {
                None
            };
            self.0.push(VariableDeclaration {
                name: Identifier(decl.name.to_string()),
                typ: translate_type(&decl.ty, decl.span)?,
                transient: false,
                initial_value,
                comment,
            });
            Ok(())
        }
    }

    let mut collector = VarDeclCollector::default();
    collector.visit_proc(&mut DeclRef::new(proc.clone()))?; // TODO: this clone should not be necessary
    let mut vars = collector.0;

    // we declare proc inputs as constants, not variables
    let mut constants = vec![];
    for param in proc.inputs.node.iter() {
        constants.push(ConstantDeclaration {
            name: Identifier(param.name.to_string()),
            typ: translate_type(&param.ty, param.span)?,
            value: None,
            comment: None,
        });
    }

    // proc outputs are normal variables
    let builder = ExprBuilder::new(Span::dummy_span());
    for param in proc.outputs.node.iter() {
        let initial_value = translate_expr(&builder.bot_lit(&param.ty))?;
        vars.push(VariableDeclaration {
            name: Identifier(param.name.to_string()),
            typ: translate_type(&param.ty, param.span)?,
            transient: false,
            initial_value: Some(Box::new(initial_value)),
            comment: None,
        });
    }

    Ok((constants, vars))
}

fn translate_type(ty: &TyKind, span: Span) -> Result<Type, JaniConversionError> {
    match ty {
        TyKind::Bool => Ok(Type::BasicType(BasicType::Bool)),
        TyKind::Int => Ok(Type::BasicType(BasicType::Int)),
        TyKind::UInt => Ok(Type::BoundedType(BoundedType {
            base: BoundedTypeBase::Int,
            lower_bound: Some(Box::new(Expression::Constant(ConstantValue::Number(
                0.into(),
            )))),
            upper_bound: None,
        })),
        TyKind::Real => Ok(Type::BasicType(BasicType::Real)),
        TyKind::UReal => Ok(Type::BoundedType(BoundedType {
            base: BoundedTypeBase::Real,
            lower_bound: Some(Box::new(Expression::Constant(ConstantValue::Number(
                0.into(),
            )))),
            upper_bound: None,
        })),
        TyKind::EUReal
        | TyKind::Tuple(_)
        | TyKind::List(_)
        | TyKind::Domain(_)
        | TyKind::SpecTy
        | TyKind::Unresolved(_)
        | TyKind::None => Err(JaniConversionError::UnsupportedType(ty.clone(), span)),
    }
}

fn translate_ident(ident: Ident) -> Identifier {
    Identifier(ident.to_string())
}

fn translate_expr(expr: &Expr) -> Result<Expression, JaniConversionError> {
    match &expr.kind {
        ExprKind::Var(ident) => Ok(Expression::Identifier(translate_ident(*ident))),
        ExprKind::Call(_, _) => Err(JaniConversionError::UnsupportedExpr(expr.clone())),
        ExprKind::Ite(cond, left, right) => Ok(Expression::IfThenElse(Box::new(IteExpression {
            cond: translate_expr(cond)?,
            left: translate_expr(left)?,
            right: translate_expr(right)?,
        }))),
        ExprKind::Binary(bin_op, left, right) => {
            Ok(Expression::Binary(Box::new(BinaryExpression {
                op: match bin_op.node {
                    BinOpKind::Add => BinaryOp::Plus,
                    BinOpKind::Sub => BinaryOp::Minus,
                    BinOpKind::Mul => BinaryOp::Times,
                    BinOpKind::Div => BinaryOp::Divide,
                    BinOpKind::Mod => BinaryOp::Modulo,
                    BinOpKind::And => BinaryOp::And,
                    BinOpKind::Or => BinaryOp::Or,
                    BinOpKind::Eq => BinaryOp::Equals,
                    BinOpKind::Lt => BinaryOp::Less,
                    BinOpKind::Le => BinaryOp::LessOrEqual,
                    BinOpKind::Ne => BinaryOp::NotEquals,
                    BinOpKind::Ge => BinaryOp::GreaterOrEqual,
                    BinOpKind::Gt => BinaryOp::Greater,
                    BinOpKind::Inf => BinaryOp::Min,
                    BinOpKind::Sup => BinaryOp::Max,
                    BinOpKind::Impl
                    | BinOpKind::CoImpl
                    | BinOpKind::Compare
                    | BinOpKind::CoCompare => {
                        Err(JaniConversionError::UnsupportedExpr(expr.clone()))?
                    }
                },
                left: translate_expr(left)?,
                right: translate_expr(right)?,
            })))
        }
        ExprKind::Unary(un_op, operand) => match un_op.node {
            UnOpKind::Not => Ok(Expression::Unary(Box::new(UnaryExpression {
                op: UnaryOp::Not,
                exp: translate_expr(operand)?,
            }))),
            UnOpKind::Non => todo!(),
            UnOpKind::Embed => todo!(),
            UnOpKind::Iverson => todo!(),
            UnOpKind::Parens => translate_expr(operand),
        },
        // TODO: for the cast we just hope for the best
        ExprKind::Cast(operand) => translate_expr(operand),
        ExprKind::Quant(_, _, _, _) => todo!(),
        ExprKind::Subst(_, _, _) => todo!(),
        ExprKind::Lit(lit) => match &lit.node {
            LitKind::UInt(val) => Ok(Expression::Constant(ConstantValue::Number(
                TryInto::<u64>::try_into(*val)
                    .map_err(|_| JaniConversionError::UnsupportedExpr(expr.clone()))?
                    .into(),
            ))),
            LitKind::Bool(val) => Ok(Expression::Constant(ConstantValue::Boolean(*val))),
            LitKind::Frac(frac) => Ok(Expression::Binary(Box::new(BinaryExpression {
                op: BinaryOp::Divide,
                left: Expression::Constant(ConstantValue::Number(
                    TryInto::<u64>::try_into(frac.numer()).unwrap().into(),
                )),
                right: Expression::Constant(ConstantValue::Number(
                    TryInto::<u64>::try_into(frac.denom()).unwrap().into(),
                )),
            }))),
            LitKind::Str(_) | LitKind::Infinity => {
                Err(JaniConversionError::UnsupportedExpr(expr.clone()))
            }
        },
    }
}

/// Translate statements with a link to the `next` location to go to. Returns
/// the created location's name.
fn translate_stmt(
    automaton: &mut AutomatonBuilder,
    stmt: &Stmt,
    next: Identifier,
) -> Result<Identifier, JaniConversionError> {
    match &stmt.node {
        StmtKind::Block(block) => translate_stmts(automaton, &block, next),
        StmtKind::Var(decl_ref) => {
            let decl = decl_ref.borrow();
            match &decl.init {
                Some(init) if !is_pure(init) => {
                    translate_assign(automaton, translate_ident(decl.name), init, next)
                }
                Some(_) => Ok(next),
                None => Err(JaniConversionError::NondetSelection(decl.span)),
            }
        }
        StmtKind::Assign(lhs, rhs) => {
            if lhs.len() != 1 {
                todo!();
            }
            let lhs = lhs[0];

            translate_assign(automaton, translate_ident(lhs), rhs, next)
        }
        StmtKind::Assert(dir, expr) => {
            if *dir != automaton.direction {
                return Err(JaniConversionError::MismatchedDirection(stmt.span));
            }
            // TODO: handle negations idiom
            // TODO: negate if in upper bounds setting
            let cond = match &expr.kind {
                ExprKind::Unary(un_op, cond) if un_op.node == UnOpKind::Embed => cond.clone(),
                _ => return Err(JaniConversionError::UnsupportedAssert(expr.clone())),
            };

            let location = Location {
                name: automaton.next_stmt_location(),
                time_progress: None,
                transient_values: None,
            };
            let start = location.name.clone();
            automaton.locations.push(location);

            let ok_edge = Edge {
                location: start.clone(),
                action: None,
                rate: None,
                guard: Some(translate_expr(&cond)?.into()),
                destinations: vec![Destination {
                    location: next,
                    probability: None,
                    assignments: vec![],
                    comment: None,
                }],
                comment: None,
            };
            automaton.edges.push(ok_edge);

            let not_cond_jani = Expression::Unary(Box::new(UnaryExpression {
                op: UnaryOp::Not,
                exp: translate_expr(&cond)?,
            }));
            let err_edge = Edge {
                location: start.clone(),
                action: None,
                rate: None,
                guard: Some(not_cond_jani.into()),
                destinations: vec![Destination {
                    location: automaton.error_location(),
                    probability: None,
                    assignments: vec![],
                    comment: None,
                }],
                comment: None,
            };
            automaton.edges.push(err_edge);

            Ok(start)
        }
        StmtKind::Havoc(_, _)
        | StmtKind::Assume(_, _) // TODO: handle assume?
        | StmtKind::Compare(_, _)
        | StmtKind::Negate(_)
        | StmtKind::Validate(_) => {
            Err(JaniConversionError::UnsupportedStmt(Box::new(stmt.clone())))
        }
        StmtKind::Tick(expr) => translate_assign(automaton, automaton.reward_var(), expr, next),
        StmtKind::Demonic(lhs, rhs) | StmtKind::Angelic(lhs, rhs) => {
            let direction = if matches!(stmt.node, StmtKind::Angelic(_, _)) {
                Direction::Down
            } else {
                Direction::Up
            };
            if direction != automaton.direction {
                return Err(JaniConversionError::MismatchedDirection(stmt.span));
            }
            let location = Location {
                name: automaton.next_stmt_location(),
                time_progress: None,
                transient_values: None,
            };
            let start = location.name.clone();
            automaton.locations.push(location);

            let lhs_start = translate_stmts(automaton, lhs, next.clone())?;
            let to_lhs_edge = Edge {
                location: start.clone(),
                action: None,
                rate: None,
                guard: None,
                destinations: vec![Destination {
                    location: lhs_start,
                    probability: None,
                    assignments: vec![],
                    comment: None,
                }],
                comment: None,
            };
            automaton.edges.push(to_lhs_edge);

            let rhs_start = translate_stmts(automaton, rhs, next.clone())?;
            let to_rhs_edge = Edge {
                location: start.clone(),
                action: None,
                rate: None,
                guard: None,
                destinations: vec![Destination {
                    location: rhs_start,
                    probability: None,
                    assignments: vec![],
                    comment: None,
                }],
                comment: None,
            };
            automaton.edges.push(to_rhs_edge);

            Ok(start)
        }
        StmtKind::If(cond, lhs, rhs) => {
            let location = Location {
                name: automaton.next_stmt_location(),
                time_progress: None,
                transient_values: None,
            };
            let start = location.name.clone();
            automaton.locations.push(location);

            let cond_jani = translate_expr(&cond)?;
            let lhs_start = translate_stmts(automaton, lhs, next.clone())?;
            let to_lhs_edge = Edge {
                location: start.clone(),
                action: None,
                rate: None,
                guard: Some(cond_jani.into()),
                destinations: vec![Destination {
                    location: lhs_start,
                    probability: None,
                    assignments: vec![],
                    comment: None,
                }],
                comment: None,
            };
            automaton.edges.push(to_lhs_edge);

            let not_cond_jani = Expression::Unary(Box::new(UnaryExpression {
                op: UnaryOp::Not,
                exp: translate_expr(&cond)?,
            }));
            let rhs_start = translate_stmts(automaton, rhs, next)?;
            let to_rhs_edge = Edge {
                location: start.clone(),
                action: None,
                rate: None,
                guard: Some(not_cond_jani.into()),
                destinations: vec![Destination {
                    location: rhs_start,
                    probability: None,
                    assignments: vec![],
                    comment: None,
                }],
                comment: None,
            };
            automaton.edges.push(to_rhs_edge);

            Ok(start)
        }
        StmtKind::While(cond, body) => {
            let location = Location {
                name: automaton.next_stmt_location(),
                time_progress: None,
                transient_values: None,
            };
            let start = location.name.clone();
            automaton.locations.push(location);

            let cond_jani = translate_expr(&cond)?;
            let body_start = translate_stmts(automaton, body, start.clone())?;
            let body_edge = Edge {
                location: start.clone(),
                action: None,
                rate: None,
                guard: Some(cond_jani.into()),
                destinations: vec![Destination {
                    location: body_start,
                    probability: None,
                    assignments: vec![],
                    comment: None,
                }],
                comment: None,
            };
            automaton.edges.push(body_edge);

            let not_cond_jani = Expression::Unary(Box::new(UnaryExpression {
                op: UnaryOp::Not,
                exp: translate_expr(&cond)?,
            }));
            let to_next_edge = Edge {
                location: start.clone(),
                action: None,
                rate: None,
                guard: Some(not_cond_jani.into()),
                destinations: vec![Destination {
                    location: next,
                    probability: None,
                    assignments: vec![],
                    comment: None,
                }],
                comment: None,
            };
            automaton.edges.push(to_next_edge);

            Ok(start)
        }
        StmtKind::Annotation(_, _, stmt) => translate_stmt(automaton, stmt, next),
        StmtKind::Label(_) => todo!(),
    }
}

fn translate_stmts(
    automaton: &mut AutomatonBuilder,
    stmts: &[Stmt],
    mut next: Identifier,
) -> Result<Identifier, JaniConversionError> {
    for stmt in stmts.iter().rev() {
        next = translate_stmt(automaton, &stmt, next)?;
    }
    Ok(next)
}

fn is_pure(expr: &Expr) -> bool {
    !matches!(expr.kind, ExprKind::Call(_, _))
}

fn translate_assign(
    automaton: &mut AutomatonBuilder,
    lhs: Identifier,
    rhs: &Expr,
    next: Identifier,
) -> Result<Identifier, JaniConversionError> {
    let location = Location {
        name: automaton.next_stmt_location(),
        time_progress: None,
        transient_values: None,
    };
    let start = location.name.clone();
    automaton.locations.push(location);

    if let ExprKind::Call(ident, args) = &rhs.kind {
        // TODO: this name matching is terrible
        if ident.name.to_string() == "flip" {
            let prob = translate_expr(&args[0])?;
            let opp_prob = Expression::Binary(Box::new(BinaryExpression {
                op: BinaryOp::Minus,
                left: Expression::Constant(ConstantValue::Number(1.into())),
                right: prob.clone(),
            }));
            automaton.edges.push(Edge {
                location: start.clone(),
                action: None,
                rate: None,
                guard: None,
                destinations: vec![
                    Destination {
                        location: next.clone(),
                        probability: Some(prob.into()),
                        assignments: vec![Assignment {
                            reference: lhs.clone(),
                            value: Expression::Constant(ConstantValue::Boolean(true)),
                            index: None,
                            comment: None,
                        }],
                        comment: None,
                    },
                    Destination {
                        location: next.clone(),
                        probability: Some(opp_prob.into()),
                        assignments: vec![Assignment {
                            reference: lhs,
                            value: Expression::Constant(ConstantValue::Boolean(false)),
                            index: None,
                            comment: None,
                        }],
                        comment: None,
                    },
                ],
                comment: None,
            });
        } else {
            todo!()
        }
    } else {
        let edge = Edge {
            location: start.clone(),
            action: None,
            rate: None,
            guard: None,
            destinations: vec![Destination {
                location: next,
                probability: None,
                assignments: vec![Assignment {
                    reference: lhs,
                    value: translate_expr(rhs)?,
                    index: None,
                    comment: None,
                }],
                comment: None,
            }],
            comment: None,
        };

        automaton.edges.push(edge);
    }

    Ok(start)
}

struct JaniPgclProperties {
    restrict_initial: Expression,
    properties: Vec<Property>,
    sink_reward: Expression,
}

// TODO: the properties are wrong for upper bounds, we need to negate the
// assumptions and assertions
fn extract_properties(
    automaton: &AutomatonBuilder,
    stmts: &mut Vec<Stmt>,
) -> Result<JaniPgclProperties, JaniConversionError> {
    // extract the preconditions (Boolean only!)
    let mut restrict_initial = vec![];
    loop {
        if let Some(first) = stmts.first() {
            match &first.node {
                StmtKind::Assume(_, expr) => {
                    if let ExprKind::Unary(un_op, operand) = &expr.kind {
                        if un_op.node != UnOpKind::Embed {
                            return Err(JaniConversionError::UnsupportedAssume(expr.clone()));
                        }
                        let mut operand = operand.clone();
                        if automaton.direction == Direction::Up {
                            let builder = ExprBuilder::new(Span::dummy_span());
                            operand = builder.unary(UnOpKind::Not, Some(TyKind::Bool), operand);
                        }
                        restrict_initial.push(operand.clone());
                        stmts.remove(0);
                    } else {
                        return Err(JaniConversionError::UnsupportedAssume(expr.clone()));
                    }
                }
                // TODO: remove this case!!!!
                StmtKind::Negate(_) => {
                    stmts.remove(0);
                }
                _ => break,
            }
        } else {
            break;
        }
    }

    let expr_builder = ExprBuilder::new(Span::dummy_span());
    let restrict_initial = {
        let direction = automaton.direction;
        let bin_op = direction.map(BinOpKind::And, BinOpKind::Or);
        let default = direction != Direction::Down;
        let restrict_initial = restrict_initial
            .into_iter()
            .reduce(|acc, e| expr_builder.binary(bin_op, Some(TyKind::Bool), acc, e))
            .unwrap_or_else(|| expr_builder.bool_lit(default));
        translate_expr(&restrict_initial)?
    };

    // the pre gives us the property already
    let expected_value = PropertyExpression::ExpectedValue(ExpectedValueExpression {
        op: automaton
            .direction
            .map(ExpectedValueKind::Emin, ExpectedValueKind::Emax),
        exp: Expression::Identifier(automaton.reward_var()),
        accumulate: Some(vec![Reward::Steps, Reward::Exit]), // TODO: what the fuck does this do?
        reach: Some(Box::new(PropertyExpression::Expression(
            Expression::Binary(Box::new(BinaryExpression {
                op: BinaryOp::Or,
                left: Expression::Identifier(automaton.is_error_state_var()),
                right: Expression::Identifier(automaton.is_sink_state_var()),
            })),
        ))),
        step_instant: None,
        time_instant: None,
        reward_instants: None,
    });
    let expected_value_from_initial = PropertyExpression::Filter(FilterExpression {
        fun: FilterFun::Values,
        values: Box::new(expected_value),
        states: Box::new(PropertyExpression::Predicate(StatePredicate::Initial)),
    });
    let spec = Property {
        name: Identifier("spec".to_owned()),
        expression: expected_value_from_initial,
        comment: None,
    };

    let expected_value = PropertyExpression::ExpectedValue(ExpectedValueExpression {
        op: automaton
            .direction
            .map(ExpectedValueKind::Emin, ExpectedValueKind::Emax),
        exp: Expression::Identifier(automaton.reward_var()),
        accumulate: Some(vec![Reward::Steps, Reward::Exit]), // TODO: what the fuck does this do?
        reach: Some(Box::new(PropertyExpression::Expression(
            Expression::Identifier(automaton.is_sink_state_var()),
        ))),
        step_instant: None,
        time_instant: None,
        reward_instants: None,
    });
    let expected_value_from_initial = PropertyExpression::Filter(FilterExpression {
        fun: FilterFun::Values,
        values: Box::new(expected_value),
        states: Box::new(PropertyExpression::Predicate(StatePredicate::Initial)),
    });
    let spec_liberal = Property {
        name: Identifier("spec_liberal".to_owned()),
        expression: expected_value_from_initial,
        comment: None,
    };

    // extract the post (may be quantitative)
    let mut post = vec![];
    loop {
        if let Some(last) = stmts.last() {
            match &last.node {
                StmtKind::Assert(_, expr) => {
                    post.push(expr.clone());
                    stmts.pop();
                }
                // TODO: remove this case!!!
                StmtKind::Negate(_) => {
                    stmts.pop();
                }
                _ => break,
            }
        } else {
            break;
        }
    }

    let sink_reward = {
        let bin_op = automaton.direction.map(BinOpKind::Inf, BinOpKind::Sup);
        post.into_iter()
            .reduce(|acc, e| expr_builder.binary(bin_op, Some(TyKind::EUReal), acc, e))
            .unwrap() // TODO: handle case where we don't have a post
    };
    let sink_reward = translate_expr(&sink_reward)?;

    let error_predicate =
        PropertyExpression::Expression(Expression::Identifier(automaton.is_error_state_var()));
    let expected_value = PropertyExpression::Quantified(QuantifiedExpression::Pmax(Box::new(
        PropertyExpression::Until(UntilExpression {
            op: UntilExpressionKind::Until,
            left: Box::new(PropertyExpression::Expression(Expression::Constant(
                ConstantValue::Boolean(true),
            ))),
            right: Box::new(error_predicate),
            step_bounds: None,
            time_bounds: None,
            reward_bounds: None,
        }),
    )));
    let expected_value_from_initial = PropertyExpression::Filter(FilterExpression {
        fun: FilterFun::Values,
        values: Box::new(expected_value),
        states: Box::new(PropertyExpression::Predicate(StatePredicate::Initial)),
    });
    let error = Property {
        name: Identifier("error".to_string()),
        expression: expected_value_from_initial,
        comment: None,
    };

    Ok(JaniPgclProperties {
        restrict_initial,
        properties: vec![error, spec, spec_liberal],
        sink_reward,
    })
}
