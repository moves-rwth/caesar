//! Translation of executable HeyVL programs to JANI by the operational
//! semantics ("opsem"). This module is concerned mostly with statements.

use std::{collections::HashMap, rc::Rc};

use jani::{
    exprs::{Expression, UnaryExpression, UnaryOp},
    models::{Assignment, Automaton, Destination, Edge, Location, VariableDeclaration},
    Identifier,
};

use crate::{
    ast::{Direction, Expr, ExprBuilder, ExprKind, Ident, Span, Stmt, StmtKind},
    intrinsic::distributions::DistributionProc,
    mc::extract_embed,
    tyctx::TyCtx,
};

use super::{specs::SpecAutomaton, translate_expr, translate_ident, JaniConversionError};

/// Intermediate structure to build the JANI automaton for pGCL semantics with
/// expected rewards.
pub struct OpAutomaton {
    distributions: HashMap<Ident, Rc<DistributionProc>>,
    pub variables: Vec<VariableDeclaration>,
    pub locations: Vec<Location>,
    pub edges: Vec<Edge>,
    pub spec_part: SpecAutomaton,
}

impl OpAutomaton {
    pub fn new(tcx: &TyCtx, spec_part: SpecAutomaton) -> Self {
        let distributions = tcx.get_distributions();
        OpAutomaton {
            distributions,
            variables: spec_part.get_variables(),
            locations: vec![],
            edges: vec![],
            spec_part,
        }
    }

    fn next_stmt_location(&self) -> Identifier {
        Identifier(format!("l{}", self.locations.len()))
    }

    pub fn finish(
        mut self,
        name: Identifier,
        initial_location: Identifier,
        expectation: Expression,
    ) -> Automaton {
        self.spec_part
            .finish(&mut self.locations, &mut self.edges, expectation);

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

/// Translate statements with a link to the `next` location to go to. Returns
/// the created location's name.
fn translate_stmt(
    automaton: &mut OpAutomaton,
    stmt: &Stmt,
    next: Identifier,
) -> Result<Identifier, JaniConversionError> {
    let span = stmt.span;
    match &stmt.node {
        StmtKind::Block(block) => translate_stmts(automaton, block, next),
        StmtKind::Var(decl_ref) => {
            let decl = decl_ref.borrow();
            match &decl.init {
                Some(init) if !is_pure(init) => {
                    translate_assign(automaton, span, translate_ident(decl.name), init, next)
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

            translate_assign(automaton, span, translate_ident(lhs), rhs, next)
        }
        StmtKind::Assert(dir, expr) => {
            if *dir != automaton.spec_part.direction {
                return Err(JaniConversionError::MismatchedDirection(stmt.span));
            }
            // only down asserts supported at the moment
            if *dir != Direction::Down {
                return Err(JaniConversionError::UnsupportedStmt(Box::new(stmt.clone())));
            }
            // TODO: negate if in upper bounds setting
            let cond = if let Some(cond) = extract_embed(expr) {
                cond
            } else {
                return Err(JaniConversionError::UnsupportedAssert(expr.clone()));
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
                    location: automaton.spec_part.error_location(),
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
        StmtKind::Tick(expr) => translate_assign(automaton,span,  automaton.spec_part.var_reward(), expr, next),
        StmtKind::Demonic(lhs, rhs) | StmtKind::Angelic(lhs, rhs) => {
            let direction = if matches!(stmt.node, StmtKind::Demonic(_, _)) {
                Direction::Down
            } else {
                Direction::Up
            };
            if direction != automaton.spec_part.direction {
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

            let cond_jani = translate_expr(cond)?;
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
                exp: translate_expr(cond)?,
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

            let cond_jani = translate_expr(cond)?;
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
                exp: translate_expr(cond)?,
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

pub fn translate_stmts(
    automaton: &mut OpAutomaton,
    stmts: &[Stmt],
    mut next: Identifier,
) -> Result<Identifier, JaniConversionError> {
    for stmt in stmts.iter().rev() {
        next = translate_stmt(automaton, stmt, next)?;
    }
    Ok(next)
}

fn is_pure(expr: &Expr) -> bool {
    !matches!(expr.kind, ExprKind::Call(_, _))
}

fn translate_assign(
    automaton: &mut OpAutomaton,
    span: Span,
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
        let decl = if let Some(decl) = automaton.distributions.get(ident) {
            decl
        } else {
            return Err(JaniConversionError::UnsupportedCall(span, *ident));
        };

        let builder = ExprBuilder::new(rhs.span);
        let dist = (decl.apply)(args, builder);

        let destinations = dist
            .0
            .iter()
            .map(|(prob, value)| {
                let prob = translate_expr(prob)?;
                let value = translate_expr(value)?;
                Ok(Destination {
                    location: next.clone(),
                    probability: Some(prob.into()),
                    assignments: vec![Assignment {
                        reference: lhs.clone(),
                        value,
                        index: None,
                        comment: None,
                    }],
                    comment: None,
                })
            })
            .collect::<Result<Vec<Destination>, _>>()?;
        automaton.edges.push(Edge {
            location: start.clone(),
            action: None,
            rate: None,
            guard: None,
            destinations,
            comment: None,
        });
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
