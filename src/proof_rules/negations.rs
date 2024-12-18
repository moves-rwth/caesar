//! Tracking the direction of a HeyVL proof with support for negation statements.

use crate::ast::{Direction, Span, Stmt, StmtKind};
use std::ops::Deref;

/// Tracks the direction of a HeyVL proof, i.e. when we are soundly
/// under-approximating (direction is `Down`), or soundly over-approximating
/// (direction is `Up`).
///
/// This struct supports handling negation statements.
#[derive(Debug, Clone, Copy)]
pub struct DirectionTracker(pub Direction);

impl Default for DirectionTracker {
    fn default() -> Self {
        DirectionTracker(Direction::Down)
    }
}

impl DirectionTracker {
    pub fn new(direction: Direction) -> Self {
        DirectionTracker(direction)
    }

    /// Handle negation statements and toggle the direction when going *forwards*
    /// through the program. Throws a [`DirectionError`] if the negation
    /// statement is invalid here.
    pub fn handle_negation_forwards(&mut self, stmt: &Stmt) -> Result<(), DirectionError> {
        if let StmtKind::Negate(dir) = &stmt.node {
            match (self.0, dir) {
                // If we were previously under-approximating and we have a
                // normal `negate` statement, then we will be over-approximating
                // now.
                (Direction::Down, Direction::Down) => self.0 = Direction::Up,
                // If we were previously over-approximating and we have a
                // `conegate` statement, then we will be under-approximating
                // now.
                (Direction::Up, Direction::Up) => self.0 = Direction::Down,
                // The other combinations are not allowed.
                _ => {
                    return Err(DirectionError {
                        current: CurrentDirection::Before(self.0),
                        negation_dir: *dir,
                        negation_span: stmt.span,
                    })
                }
            }
        }
        Ok(())
    }

    /// Handle negation statements and toggle the direction when going *backwards* through the program.
    pub fn handle_negation_backwards(&mut self, stmt: &Stmt) -> Result<(), DirectionError> {
        if let StmtKind::Negate(dir) = &stmt.node {
            match (dir, self.0) {
                // If a `negate` statement is followed by over-approximation,
                // then the previous direction is under-approximation.
                (Direction::Down, Direction::Up) => self.0 = Direction::Down,
                // If a `conegate` statement is followed by under-approximation,
                // then the previous direction is over-approximation.
                (Direction::Up, Direction::Up) => self.0 = Direction::Down,
                // The other combinations are not allowed.
                _ => {
                    return Err(DirectionError {
                        current: CurrentDirection::After(self.0),
                        negation_dir: *dir,
                        negation_span: stmt.span,
                    })
                }
            }
        }
        Ok(())
    }
}

impl Deref for DirectionTracker {
    type Target = Direction;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone)]
pub enum CurrentDirection {
    /// The direction tracked from *before* the current statement, when we are
    /// walking forwards through the program.
    Before(Direction),
    /// The direction tracked from *after* the current statement, when we are
    /// walking backwards through the program.
    After(Direction),
}

#[derive(Debug, Clone)]
pub struct DirectionError {
    /// The current direction we had.
    pub current: CurrentDirection,
    /// The direction of the negation that was invalid.
    pub negation_dir: Direction,
    /// The span of the negation statement that caused the error.
    pub negation_span: Span,
}

impl std::fmt::Display for DirectionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.current {
            CurrentDirection::Before(direction) => write!(
                f,
                "Invalid negation statement: direction {:?} may not be followed by {} statement",
                direction,
                self.negation_dir.prefix("negate")
            ),
            CurrentDirection::After(direction) => write!(
                f,
                "Invalid negation statement: {} statement may not be followed by {:?} direction",
                self.negation_dir.prefix("negate"),
                direction
            ),
        }
    }
}

impl std::error::Error for DirectionError {}
