//! Translation of executable HeyVL programs to JANI by the operational
//! semantics ("opsem"). This module is concerned mostly with statements.

use std::{collections::HashMap, rc::Rc};

use jani::{
    exprs::Expression,
    models::{Assignment, Automaton, Destination, Edge, Location, ModelType, VariableDeclaration},
    Identifier,
};

use crate::{
    ast::{Block, Direction, Expr, ExprBuilder, ExprKind, Ident, Span, Stmt, StmtKind},
    intrinsic::distributions::DistributionProc,
    mc::extract_embed,
    tyctx::TyCtx,
};

use super::{
    is_constant, specs::SpecAutomaton, translate_expr, translate_ident, JaniConversionError,
};

/// Intermediate structure to build the JANI automaton for pGCL semantics with
/// expected rewards.
pub struct OpAutomaton<'tcx> {
    tcx: &'tcx TyCtx,
    distributions: HashMap<Ident, Rc<DistributionProc>>,
    pub variables: Vec<VariableDeclaration>,
    pub locations: Vec<Location>,
    pub edges: Vec<Edge>,
    pub spec_part: SpecAutomaton,
    has_nondet: bool,
}

impl<'a> OpAutomaton<'a> {
    pub fn new(tcx: &'a TyCtx, spec_part: SpecAutomaton) -> Self {
        let distributions = tcx.get_distributions();
        OpAutomaton {
            tcx,
            distributions,
            variables: spec_part.get_variables(),
            locations: vec![],
            edges: vec![],
            spec_part,
            has_nondet: false,
        }
    }

    /// Create a new location for the next statement.
    fn next_stmt_location(&mut self) -> Identifier {
        let ident = Identifier(format!("l{}", self.locations.len()));
        self.locations.push(Location::new(ident.clone()));
        ident
    }

    pub fn finish(
        mut self,
        name: Identifier,
        initial_location: Identifier,
        expectation: Expression,
    ) -> (ModelType, Automaton) {
        self.spec_part
            .finish(&mut self.locations, &mut self.edges, expectation);

        let model_type = if self.has_nondet {
            ModelType::Mdp
        } else {
            ModelType::Dtmc
        };
        let automaton = Automaton {
            name,
            variables: self.variables,
            restrict_initial: None,
            locations: self.locations,
            initial_locations: vec![initial_location],
            edges: self.edges,
            functions: vec![],
            comment: None,
        };
        (model_type, automaton)
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
        StmtKind::Seq(block) => translate_stmts(automaton, block, next),
        StmtKind::Var(decl_ref) => {
            let decl = decl_ref.borrow();
            match &decl.init {
                Some(init) if !is_constant(init) => {
                    translate_assign(automaton, span, translate_ident(decl.name), init, next)
                }
                Some(_) => Ok(next),
                None => Err(JaniConversionError::NondetSelection(decl.span)),
            }
        }
        StmtKind::Assign(lhs, rhs) => {
            if lhs.len() != 1 {
                return Err(JaniConversionError::UnsupportedStmt(Box::new(stmt.clone())));
            }
            let lhs = lhs[0];

            translate_assign(automaton, span, translate_ident(lhs), rhs, next)
        }
        StmtKind::Assert(dir, expr) => {
            if *dir != automaton.spec_part.direction {
                return Err(JaniConversionError::MismatchedDirection(stmt.span));
            }

            if extract_embed(expr).is_some() {
                translate_bool_assert(automaton, *dir, &next, expr)
            } else {
                translate_quant_assert(automaton, span, &next, expr)
            }
        }
        StmtKind::Assume(dir, expr) => {
            // we can translate both directions, but only with Boolean exprs
            let cond = if let Some(cond) = extract_embed(expr) {
                let cond = translate_expr(automaton.tcx, &cond)?;
                match *dir {
                    Direction::Down => cond,
                    Direction::Up => !cond,
                }
            } else {
                return Err(JaniConversionError::UnsupportedAssume(expr.clone()));
            };

            let start = automaton.next_stmt_location();

            let cont_edge = Edge::from_to_if(start.clone(), next.clone(), cond.clone());
            automaton.edges.push(cont_edge);

            let miracle_location = translate_miracle(automaton, *dir);
            let miracle_edge = Edge::from_to_if(start.clone(), miracle_location, !cond);
            automaton.edges.push(miracle_edge);

            Ok(start)
        }
        StmtKind::Havoc(_, _)
        | StmtKind::Compare(_, _)
        | StmtKind::Negate(_)
        | StmtKind::Validate(_) => {
            Err(JaniConversionError::UnsupportedStmt(Box::new(stmt.clone())))
        }
        StmtKind::Tick(expr) => translate_assign(
            automaton,
            span,
            automaton.spec_part.var_reward(),
            expr,
            next,
        ),
        StmtKind::Demonic(lhs, rhs) | StmtKind::Angelic(lhs, rhs) => {
            let direction = if matches!(stmt.node, StmtKind::Demonic(_, _)) {
                Direction::Down
            } else {
                Direction::Up
            };
            if direction != automaton.spec_part.direction {
                return Err(JaniConversionError::MismatchedDirection(stmt.span));
            }
            automaton.has_nondet = true;
            let start = automaton.next_stmt_location();

            let lhs_start = translate_block(automaton, lhs, next.clone())?;
            let to_lhs_edge = Edge::from_to(start.clone(), lhs_start);
            automaton.edges.push(to_lhs_edge);

            let rhs_start = translate_block(automaton, rhs, next)?;
            let to_rhs_edge = Edge::from_to(start.clone(), rhs_start);
            automaton.edges.push(to_rhs_edge);

            Ok(start)
        }
        StmtKind::If(cond, lhs, rhs) => {
            let start = automaton.next_stmt_location();

            let cond_jani = translate_expr(automaton.tcx, cond)?;
            let lhs_start = translate_block(automaton, lhs, next.clone())?;
            let to_lhs_edge = Edge::from_to_if(start.clone(), lhs_start, cond_jani);
            automaton.edges.push(to_lhs_edge);

            let not_cond_jani = !translate_expr(automaton.tcx, cond)?;
            let rhs_start = translate_block(automaton, rhs, next)?;
            let to_rhs_edge = Edge::from_to_if(start.clone(), rhs_start, not_cond_jani);
            automaton.edges.push(to_rhs_edge);

            Ok(start)
        }
        StmtKind::While(cond, body) => {
            let start = automaton.next_stmt_location();

            let cond_jani = translate_expr(automaton.tcx, cond)?;
            let body_start = translate_block(automaton, body, start.clone())?;
            let body_edge = Edge::from_to_if(start.clone(), body_start.clone(), cond_jani);
            automaton.edges.push(body_edge);

            let not_cond_jani = !translate_expr(automaton.tcx, cond)?;
            let to_next_edge = Edge::from_to_if(start.clone(), next, not_cond_jani);
            automaton.edges.push(to_next_edge);

            Ok(start)
        }
        StmtKind::Annotation(_, _, _, stmt) => translate_stmt(automaton, stmt, next),
        StmtKind::Label(_) => Ok(next),
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

pub fn translate_block(
    automaton: &mut OpAutomaton,
    block: &Block,
    next: Identifier,
) -> Result<Identifier, JaniConversionError> {
    translate_stmts(automaton, &block.node, next)
}

fn translate_assign(
    automaton: &mut OpAutomaton,
    span: Span,
    lhs: Identifier,
    rhs: &Expr,
    next: Identifier,
) -> Result<Identifier, JaniConversionError> {
    let start = automaton.next_stmt_location();

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
                let prob = translate_expr(automaton.tcx, prob)?;
                let value = translate_expr(automaton.tcx, value)?;
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
                    value: translate_expr(automaton.tcx, rhs)?,
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

/// Translate an assert statement with a Boolean condition.
///
/// If the condition is true, then we continue with `next`. Otherwise, we go to
/// the error location.
fn translate_bool_assert(
    automaton: &mut OpAutomaton,
    dir: Direction,
    next: &Identifier,
    expr: &Expr,
) -> Result<Identifier, JaniConversionError> {
    let cond = if let Some(cond) = extract_embed(expr) {
        let cond = translate_expr(automaton.tcx, &cond)?;
        match dir {
            Direction::Down => cond,
            Direction::Up => !cond,
        }
    } else {
        return Err(JaniConversionError::UnsupportedAssert(expr.clone()));
    };

    let start = automaton.next_stmt_location();

    let ok_edge = Edge::from_to_if(start.clone(), next.clone(), cond.clone());
    automaton.edges.push(ok_edge);

    let not_cond_jani = !cond;
    let err_edge = Edge::from_to_if(
        start.clone(),
        automaton.spec_part.error_location(),
        not_cond_jani,
    );
    automaton.edges.push(err_edge);

    Ok(start)
}

/// Translate a quantitative assert statement.
///
/// It is translated as a nondeterministic choice between either a transition to
/// the error location with the reward of the expression, or continuing the
/// execution with `next`
fn translate_quant_assert(
    automaton: &mut OpAutomaton,
    span: Span,
    next: &Identifier,
    expr: &Expr,
) -> Result<Identifier, JaniConversionError> {
    let start = automaton.next_stmt_location();
    automaton.has_nondet = true;

    let next_edge = Edge::from_to(start.clone(), next.clone());
    automaton.edges.push(next_edge);

    // increase the reward by the expression and go to the error location
    let return_start = translate_assign(
        automaton,
        span,
        automaton.spec_part.var_reward(),
        expr,
        automaton.spec_part.error_location(),
    )?;
    let return_edge = Edge::from_to(start.clone(), return_start);
    automaton.edges.push(return_edge);

    Ok(start)
}

/// The "miracle loop" is a loop that never reaches the sink state. Depending on
/// the direction, we collect infinite (down) or zero (up) reward.
fn translate_miracle(automaton: &mut OpAutomaton, dir: Direction) -> Identifier {
    let assignments = match dir {
        Direction::Down => vec![Assignment {
            reference: automaton.spec_part.var_reward(),
            value: 1.into(),
            index: None,
            comment: None,
        }],
        Direction::Up => vec![],
    };

    let start = automaton.next_stmt_location();
    let edge = Edge {
        location: start.clone(),
        action: None,
        rate: None,
        guard: None,
        destinations: vec![Destination {
            location: start.clone(),
            probability: None,
            assignments,
            comment: None,
        }],
        comment: None,
    };
    automaton.edges.push(edge);
    start
}
