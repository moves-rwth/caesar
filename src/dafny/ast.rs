/// A full Dafny file emitted by the backend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct File {
    pub decls: Vec<Decl>,
}

/// Top-level Dafny declarations supported by the current backend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decl {
    Type(TypeDecl),
    Function(FunctionDecl),
    Method(MethodDecl),
}

/// A lightweight Dafny `type` declaration for an abstract HeyVL domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeDecl {
    pub name: String,
}

/// A Dafny `function` declaration, optionally with a definition body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub return_ty: Type,
    pub body: Option<Expr>,
}

/// A Dafny `method` declaration with contracts and an optional body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MethodDecl {
    pub axiom: bool,
    pub name: String,
    pub params: Vec<Param>,
    pub returns: Vec<Param>,
    pub requires: Vec<Expr>,
    pub ensures: Vec<Expr>,
    pub decreases_star: bool,
    pub body: Option<Block>,
}

/// A sequence of Dafny statements surrounded by `{ ... }`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
}

/// The statement fragment the backend knows how to emit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Block(Block),
    Var(VarDecl),
    Assign(AssignStmt),
    Call(CallStmt),
    AssignCall(AssignCallStmt),
    SuchThatAssign(SuchThatAssignStmt),
    Assert(AssertStmt),
    Assume(AssumeStmt),
    If(IfStmt),
    While(WhileStmt),
}

/// A Dafny local variable declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VarDecl {
    pub name: String,
    pub ty: Type,
    pub init: VarInit,
}

/// The initialization forms used for local variables in emitted Dafny.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VarInit {
    Expr(Expr),
    MethodCall { method: String, args: Vec<Expr> },
    SuchThat(Expr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssignStmt {
    pub lhs: String,
    pub rhs: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallStmt {
    pub method: String,
    pub args: Vec<Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssignCallStmt {
    pub lhs: Vec<String>,
    pub method: String,
    pub args: Vec<Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuchThatAssignStmt {
    pub lhs: Vec<String>,
    pub predicate: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssertStmt {
    pub expr: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssumeStmt {
    pub axiom: bool,
    pub expr: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IfStmt {
    pub cond: Expr,
    pub then_branch: Block,
    pub else_branch: Block,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WhileStmt {
    pub cond: Expr,
    pub invariants: Vec<Expr>,
    pub decreases_star: bool,
    pub body: Block,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub ty: Type,
}

/// The minimal Dafny type fragment needed by the backend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Bool,
    Int,
    Nat,
    Seq(Box<Type>),
    Named(String),
}

/// The expression fragment shared by the lowering and pretty-printing passes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Var(String),
    BoolLit(bool),
    NumberLit(String),
    StringLit(String),
    Call {
        function: String,
        args: Vec<Expr>,
    },
    Ite {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Quantified {
        quantifier: Quantifier,
        vars: Vec<QuantVar>,
        triggers: Vec<Vec<Expr>>,
        body: Box<Expr>,
    },
    SeqLen(Box<Expr>),
    Index {
        collection: Box<Expr>,
        index: Box<Expr>,
    },
    Update {
        collection: Box<Expr>,
        index: Box<Expr>,
        value: Box<Expr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
    Impl,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Parens,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Quantifier {
    Forall,
    Exists,
}

/// A typed quantified variable in a Dafny quantifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuantVar {
    pub name: String,
    pub ty: Type,
}
