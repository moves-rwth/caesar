use std::fmt::{self, Display};

use crate::pretty::{pretty_block, Doc, SimplePretty};

use super::{DeclRef, Expr, Ident, Spanned, VarDecl};

pub type Block = Vec<Stmt>;

impl SimplePretty for Block {
    fn pretty(&self) -> Doc {
        Doc::intersperse(
            self.iter().map(|stmt| stmt.pretty()),
            Doc::line().flat_alt(Doc::text("; ")),
        )
    }
}

/// Executable actions that don't return values.
pub type Stmt = Spanned<StmtKind>;

/// Uses the [`SimplePretty`] instance to render this statement.
impl Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.node.fmt(f)
    }
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    /// A sequence of statements.
    Block(Block),
    /// A variable declaration.
    Var(DeclRef<VarDecl>),
    /// An assignment.
    Assign(Vec<Ident>, Expr),
    /// A havoc statement.
    Havoc(Direction, Vec<Ident>),
    /// An assertion statement.
    Assert(Direction, Expr),
    /// An assumption statement.
    Assume(Direction, Expr),
    /// A comparison statement.
    Compare(Direction, Expr),
    /// A negation statement.
    Negate(Direction),
    /// A validate statement.
    Validate(Direction),
    /// A tick statement.
    Tick(Expr),
    /// A demonic nondeterministic choice.
    Demonic(Block, Block),
    /// An angelic nondeterministic choice.
    Angelic(Block, Block),
    /// An `if` block.
    If(Expr, Block, Block),
    /// A `while` loop.
    While(Expr, Block),
    /// An annotation on a statement.
    Annotation(Ident, Vec<Expr>, Box<Stmt>),
    /// A label statement.
    Label(Ident),
}

impl SimplePretty for StmtKind {
    fn pretty(&self) -> Doc {
        fn pretty_binop(name: &'static str, dir: &Direction, expr: &Expr) -> Doc {
            dir.pretty_direction_prefix()
                .append(Doc::text(name))
                .append(Doc::space())
                .append(expr.pretty())
        }
        fn pretty_branch(cond: Doc, lhs: &Block, rhs: &Block) -> Doc {
            Doc::text("if")
                .append(Doc::space())
                .append(cond)
                .append(Doc::space())
                .append(Doc::text("{"))
                .group()
                .append(Doc::line().append(lhs.pretty()).nest(4))
                .append(Doc::line())
                .append(
                    Doc::text("}")
                        .append(Doc::space())
                        .append(Doc::text("else"))
                        .append(Doc::space())
                        .append(Doc::text("{"))
                        .group(),
                )
                .append(Doc::line().append(rhs.pretty()).nest(4))
                .append(Doc::line())
                .append(Doc::text("}"))
        }

        fn pretty_loop(cond: Doc, body: &Block) -> Doc {
            Doc::text("while")
                .append(Doc::space())
                .append(cond)
                .append(Doc::space())
                .append(pretty_block(body.pretty()))
        }

        let res = match self {
            StmtKind::Block(stmts) => pretty_block(stmts.pretty()),
            StmtKind::Var(decl_ref) => decl_ref.borrow().pretty_stmt(),
            StmtKind::Assign(lhs, rhs) => Doc::intersperse(
                lhs.iter().map(|lhs| Doc::as_string(lhs.name)),
                Doc::text(", "),
            )
            .append(Doc::text(" = "))
            .append(rhs.pretty()),
            StmtKind::Havoc(dir, vars) => dir
                .pretty_direction_prefix()
                .append(Doc::text("havoc"))
                .append(Doc::space())
                .append(Doc::intersperse(
                    vars.iter().map(|var| Doc::as_string(var.name)),
                    Doc::text(", "),
                )),
            StmtKind::Assert(dir, expr) => pretty_binop("assert", dir, expr),
            StmtKind::Assume(dir, expr) => pretty_binop("assume", dir, expr),
            StmtKind::Compare(dir, expr) => pretty_binop("compare", dir, expr),
            StmtKind::Negate(dir) => dir.pretty_direction_prefix().append(Doc::text("negate")),
            StmtKind::Validate(dir) => dir.pretty_direction_prefix().append(Doc::text("validate")),
            StmtKind::Tick(expr) => Doc::text("tick").append(Doc::space()).append(expr.pretty()),
            StmtKind::Demonic(lhs, rhs) => pretty_branch(Doc::text("⊓"), lhs, rhs),
            StmtKind::Angelic(lhs, rhs) => pretty_branch(Doc::text("⊔"), lhs, rhs),
            StmtKind::If(cond, lhs, rhs) => pretty_branch(cond.pretty(), lhs, rhs),
            StmtKind::While(cond, body) => pretty_loop(cond.pretty(), body),
            StmtKind::Annotation(ident, inputs, stmt) => Doc::text("@")
                .append(Doc::as_string(ident.name))
                .append(Doc::text("("))
                .append(Doc::intersperse(
                    inputs.iter().map(|expr| expr.pretty()),
                    Doc::text(", "),
                ))
                .append(Doc::text(")"))
                .append(Doc::line().append(stmt.pretty())),
            StmtKind::Label(ident) => Doc::text("label")
                .append(Doc::space())
                .append(Doc::as_string(ident.name)),
        };
        Doc::group(res)
    }
}

/// Uses the [`SimplePretty`] instance to render this statement.
impl Display for StmtKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.pretty().render_fmt(80, f)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Direction {
    Down,
    Up,
}

impl Direction {
    pub fn toggle(&self) -> Direction {
        match self {
            Direction::Down => Direction::Up,
            Direction::Up => Direction::Down,
        }
    }

    pub fn prefix(&self, text: &str) -> String {
        match self {
            Direction::Down => text.to_owned(),
            Direction::Up => format!("co{}", text),
        }
    }

    pub fn as_string(&self) -> &'static str {
        match self {
            Direction::Down => "",
            Direction::Up => "co",
        }
    }

    pub fn pretty_direction_prefix(&self) -> Doc {
        Doc::text(self.as_string())
    }
}

#[cfg(test)]
mod test {
    use crate::{ast::FileId, front::parser, pretty::pretty_string};

    #[test]
    fn format_expr() {
        let source = &"assume x + y * 17 / 1; coassert x ==> 18";
        let stmts = parser::parse_raw(FileId::DUMMY, source).unwrap();
        let text = pretty_string(&stmts);
        assert_eq!(text, "assume (x + (y * (17 / 1)))\ncoassert (x → 18)");
    }
}
