//! Compatibility checks for the precedence migration.

use std::fmt::Write as _;

use crate::ast::{
    BinOpKind, Block, DeclKind, DomainSpec, Expr, ExprKind, FileId, ProcSpec, QuantVar, Span, Stmt,
    StmtKind,
};
use crate::pretty::pretty_string;

lalrpop_util::lalrpop_mod!(
    #[cfg_attr(rustfmt, rustfmt_skip)]
    grammar_old,
    "/src/front/parser/precedence_update/grammar_old.rs"
);

pub(super) fn parse_old_decls(
    file_id: FileId,
    source: &str,
) -> Result<Vec<DeclKind>, super::ParseError> {
    let parser = grammar_old::DeclsParser::new();
    parser
        .parse(file_id, source)
        .map_err(|err| super::ParseError::from_lalrpop_parse_error(file_id, err))
}

pub(super) fn parse_old_block(file_id: FileId, source: &str) -> Result<Block, super::ParseError> {
    let parser = grammar_old::SpannedStmtsParser::new();
    parser
        .parse(file_id, source)
        .map_err(|err| super::ParseError::from_lalrpop_parse_error(file_id, err))
}

pub(super) fn parse_old_decl(file_id: FileId, source: &str) -> Result<DeclKind, super::ParseError> {
    let parser = grammar_old::DeclParser::new();
    parser
        .parse(file_id, source)
        .map_err(|err| super::ParseError::from_lalrpop_parse_error(file_id, err))
}

#[derive(Debug, Clone)]
pub struct ExprMismatch {
    #[allow(dead_code)]
    pub top_span: Span,
    #[allow(dead_code)]
    pub top_new_expr: String,
    #[allow(dead_code)]
    pub top_old_expr: String,
    pub subexpr: SubexprMismatch,
}

#[derive(Debug, Clone)]
struct ExprSnapshot {
    expr: Expr,
    span: Span,
    pretty: String,
    fingerprint: String,
}

#[derive(Debug, Clone)]
pub struct SubexprMismatch {
    pub span: Span,
    pub new_expr: String,
    pub old_expr: String,
}

impl SubexprMismatch {
    fn from_exprs(new_expr: &Expr, old_expr: &Expr) -> Self {
        SubexprMismatch {
            span: new_expr.span,
            new_expr: pretty_string(new_expr),
            old_expr: pretty_string(old_expr),
        }
    }
}

pub(crate) fn decls_mismatch(
    file_id: FileId,
    source: &str,
    new_decls: &[DeclKind],
) -> Option<ExprMismatch> {
    let parser = grammar_old::DeclsParser::new();
    let old_decls = parser.parse(file_id, source).ok()?;
    first_expr_mismatch_in_decls(new_decls, &old_decls)
}

pub(crate) fn block_mismatch(
    file_id: FileId,
    source: &str,
    new_block: &Block,
) -> Option<ExprMismatch> {
    let parser = grammar_old::SpannedStmtsParser::new();
    let old_block = parser.parse(file_id, source).ok()?;
    first_expr_mismatch_in_block(new_block, &old_block)
}

pub(crate) fn decl_mismatch(
    file_id: FileId,
    source: &str,
    new_decl: &DeclKind,
) -> Option<ExprMismatch> {
    let parser = grammar_old::DeclParser::new();
    let old_decl = parser.parse(file_id, source).ok()?;
    first_expr_mismatch_in_decls(
        std::slice::from_ref(new_decl),
        std::slice::from_ref(&old_decl),
    )
}

#[cfg(test)]
pub(crate) fn expr_mismatch(
    file_id: FileId,
    source: &str,
    new_expr: &Expr,
) -> Option<ExprMismatch> {
    let parser = grammar_old::ExprParser::new();
    let old_expr = parser.parse(file_id, source).ok()?;
    let subexpr = check_expr_mismatch(new_expr, &old_expr).err()?;
    Some(ExprMismatch {
        top_span: new_expr.span,
        top_new_expr: pretty_string(new_expr),
        top_old_expr: pretty_string(&old_expr),
        subexpr,
    })
}

#[cfg(test)]
pub(super) fn parse_old_expr(file_id: FileId, source: &str) -> Result<Expr, super::ParseError> {
    let parser = grammar_old::ExprParser::new();
    parser
        .parse(file_id, source)
        .map_err(|err| super::ParseError::from_lalrpop_parse_error(file_id, err))
}

#[cfg(test)]
pub(crate) fn old_expr_pretty(file_id: FileId, source: &str) -> Result<String, String> {
    let parser = grammar_old::ExprParser::new();
    parser
        .parse(file_id, source)
        .map(|expr| pretty_string(&expr))
        .map_err(|err| format!("{err:?}"))
}

fn first_expr_mismatch_in_decls(
    new_decls: &[DeclKind],
    old_decls: &[DeclKind],
) -> Option<ExprMismatch> {
    let mut new_exprs = Vec::new();
    let mut old_exprs = Vec::new();
    collect_decls_exprs(new_decls, &mut new_exprs);
    collect_decls_exprs(old_decls, &mut old_exprs);
    first_expr_mismatch(&new_exprs, &old_exprs)
}

fn first_expr_mismatch_in_block(new_block: &Block, old_block: &Block) -> Option<ExprMismatch> {
    let mut new_exprs = Vec::new();
    let mut old_exprs = Vec::new();
    collect_block_exprs(new_block, &mut new_exprs);
    collect_block_exprs(old_block, &mut old_exprs);
    first_expr_mismatch(&new_exprs, &old_exprs)
}

fn first_expr_mismatch(
    new_exprs: &[ExprSnapshot],
    old_exprs: &[ExprSnapshot],
) -> Option<ExprMismatch> {
    if let Some((new_expr, old_expr)) = new_exprs
        .iter()
        .zip(old_exprs)
        .find(|(new_expr, old_expr)| new_expr.fingerprint != old_expr.fingerprint)
    {
        let mismatch = check_expr_mismatch(&new_expr.expr, &old_expr.expr)
            .err()
            .unwrap_or_else(|| SubexprMismatch::from_exprs(&new_expr.expr, &old_expr.expr));
        return Some(ExprMismatch {
            top_span: new_expr.span,
            top_new_expr: new_expr.pretty.clone(),
            top_old_expr: old_expr.pretty.clone(),
            subexpr: mismatch,
        });
    }
    assert!(new_exprs.len() == old_exprs.len());
    None
}

fn collect_decls_exprs(decls: &[DeclKind], out: &mut Vec<ExprSnapshot>) {
    for decl in decls {
        collect_decl_exprs(decl, out);
    }
}

fn collect_decl_exprs(decl: &DeclKind, out: &mut Vec<ExprSnapshot>) {
    match decl {
        DeclKind::VarDecl(var_decl) => {
            let var_decl = var_decl.borrow();
            if let Some(init) = var_decl.init.as_ref() {
                collect_expr(init, out);
            }
        }
        DeclKind::ProcDecl(proc_decl) => {
            let proc_decl = proc_decl.borrow();
            for spec in &proc_decl.spec {
                match spec {
                    ProcSpec::Requires(expr) | ProcSpec::Ensures(expr) => collect_expr(expr, out),
                }
            }
            let body_ref = proc_decl.body.borrow();
            if let Some(body) = body_ref.as_ref() {
                collect_block_exprs(body, out);
            }
        }
        DeclKind::DomainDecl(domain_decl) => {
            for spec in &domain_decl.borrow().body {
                match spec {
                    DomainSpec::Function(func_decl) => {
                        let func_decl = func_decl.borrow();
                        let body_ref = func_decl.body.borrow();
                        if let Some(body) = body_ref.as_ref() {
                            collect_expr(body, out);
                        }
                    }
                    DomainSpec::Axiom(axiom_decl) => {
                        collect_expr(&axiom_decl.borrow().axiom, out);
                    }
                }
            }
        }
        DeclKind::FuncDecl(func_decl) => {
            let func_decl = func_decl.borrow();
            let body_ref = func_decl.body.borrow();
            if let Some(body) = body_ref.as_ref() {
                collect_expr(body, out);
            }
        }
        DeclKind::AxiomDecl(axiom_decl) => {
            collect_expr(&axiom_decl.borrow().axiom, out);
        }
        DeclKind::ProcIntrin(_)
        | DeclKind::FuncIntrin(_)
        | DeclKind::LabelDecl(_)
        | DeclKind::AnnotationDecl(_) => {}
    }
}

fn collect_block_exprs(block: &Block, out: &mut Vec<ExprSnapshot>) {
    for stmt in &block.node {
        collect_stmt_exprs(stmt, out);
    }
}

fn collect_stmt_exprs(stmt: &Stmt, out: &mut Vec<ExprSnapshot>) {
    match &stmt.node {
        StmtKind::Seq(stmts) => {
            for stmt in stmts {
                collect_stmt_exprs(stmt, out);
            }
        }
        StmtKind::Var(var_decl) => {
            let var_decl = var_decl.borrow();
            if let Some(init) = var_decl.init.as_ref() {
                collect_expr(init, out);
            }
        }
        StmtKind::Assign(_, expr)
        | StmtKind::Assert(_, expr)
        | StmtKind::Assume(_, expr)
        | StmtKind::Compare(_, expr)
        | StmtKind::Tick(expr)
        | StmtKind::Weigh(expr) => collect_expr(expr, out),
        StmtKind::Negate(_)
        | StmtKind::Validate(_)
        | StmtKind::Havoc(_, _)
        | StmtKind::Label(_) => {}
        StmtKind::Demonic(lhs, rhs)
        | StmtKind::Angelic(lhs, rhs)
        | StmtKind::Additive(lhs, rhs) => {
            collect_block_exprs(lhs, out);
            collect_block_exprs(rhs, out);
        }
        StmtKind::If(cond, lhs, rhs) => {
            collect_expr(cond, out);
            collect_block_exprs(lhs, out);
            collect_block_exprs(rhs, out);
        }
        StmtKind::While(cond, body) => {
            collect_expr(cond, out);
            collect_block_exprs(body, out);
        }
        StmtKind::Annotation(_, _, inputs, stmt) => {
            for input in inputs {
                collect_expr(input, out);
            }
            collect_stmt_exprs(stmt, out);
        }
    }
}

fn collect_expr(expr: &Expr, out: &mut Vec<ExprSnapshot>) {
    out.push(ExprSnapshot {
        expr: expr.clone(),
        span: expr.span,
        pretty: pretty_string(expr),
        fingerprint: expr_fingerprint(expr),
    });
}

// Complexity: worst-case O(n^2) due to repeated subtree fingerprinting during recursion,
// but typical precedence mismatches are shallow and this behaves near O(n) in practice.
fn check_expr_mismatch(new_expr: &Expr, old_expr: &Expr) -> Result<(), SubexprMismatch> {
    let mismatch = || SubexprMismatch::from_exprs(new_expr, old_expr);

    if expr_fingerprint(new_expr) == expr_fingerprint(old_expr) {
        return Ok(());
    }

    match (&new_expr.kind, &old_expr.kind) {
        (
            ExprKind::Binary(new_op, _new_lhs, _new_rhs),
            ExprKind::Binary(old_op, _old_lhs, _old_rhs),
        ) => {
            if new_op.node != old_op.node {
                return Err(mismatch());
            }

            if is_associative_binop(new_op.node) {
                let mut new_terms = Vec::new();
                let mut old_terms = Vec::new();
                collect_associative_terms(new_expr, new_op.node, &mut new_terms);
                collect_associative_terms(old_expr, old_op.node, &mut old_terms);

                // Associativity-only changes are okay: same flattened terms means
                // same meaning up to parenthesization.
                if new_terms.len() == old_terms.len()
                    && new_terms
                        .iter()
                        .zip(&old_terms)
                        .all(|(new_term, old_term)| {
                            expr_fingerprint(new_term) == expr_fingerprint(old_term)
                        })
                {
                    return Ok(());
                }

                // Not just reassociation: report the whole differing associative
                // subexpression (avoids tiny/cryptic leaf mismatches like `1`).
                return Err(mismatch());
            }

            // For non-associative operators with the same top-level kind,
            // report the whole differing binary subexpression (not a child).
            Err(mismatch())
        }
        (ExprKind::Unary(new_op, new_operand), ExprKind::Unary(old_op, old_operand))
            if new_op.node == old_op.node =>
        {
            check_expr_mismatch(new_operand, old_operand)?;
            Err(mismatch())
        }
        (ExprKind::Ite(new_cond, new_lhs, new_rhs), ExprKind::Ite(old_cond, old_lhs, old_rhs)) => {
            check_expr_mismatch(new_cond, old_cond)?;
            check_expr_mismatch(new_lhs, old_lhs)?;
            check_expr_mismatch(new_rhs, old_rhs)?;
            Err(mismatch())
        }
        (ExprKind::Cast(new_inner), ExprKind::Cast(old_inner)) => {
            check_expr_mismatch(new_inner, old_inner)?;
            Err(mismatch())
        }
        (
            ExprKind::Quant(new_op, new_vars, _new_ann, new_inner),
            ExprKind::Quant(old_op, old_vars, _old_ann, old_inner),
        ) if new_op.node == old_op.node && quant_vars_compatible(new_vars, old_vars) => {
            check_expr_mismatch(new_inner, old_inner)?;
            Err(mismatch())
        }
        (
            ExprKind::Subst(new_ident, new_by, new_inner),
            ExprKind::Subst(old_ident, old_by, old_inner),
        ) if new_ident == old_ident => {
            check_expr_mismatch(new_by, old_by)?;
            check_expr_mismatch(new_inner, old_inner)?;
            Err(mismatch())
        }
        (ExprKind::Call(new_ident, new_args), ExprKind::Call(old_ident, old_args))
            if new_ident == old_ident && new_args.len() == old_args.len() =>
        {
            for (new_arg, old_arg) in new_args.iter().zip(old_args) {
                check_expr_mismatch(new_arg, old_arg)?;
            }
            Err(mismatch())
        }
        _ => Err(mismatch()),
    }
}

fn expr_fingerprint(expr: &Expr) -> String {
    let mut buf = String::new();
    write_expr_fingerprint(expr, &mut buf);
    buf
}

fn write_expr_fingerprint(expr: &Expr, out: &mut String) {
    match &expr.kind {
        ExprKind::Var(ident) => {
            let _ = write!(out, "var({})", ident.name);
        }
        ExprKind::Call(ident, args) => {
            let _ = write!(out, "call({})[", ident.name);
            for arg in args {
                write_expr_fingerprint(arg, out);
                out.push(';');
            }
            out.push(']');
        }
        ExprKind::Ite(cond, lhs, rhs) => {
            out.push_str("ite(");
            write_expr_fingerprint(cond, out);
            out.push(',');
            write_expr_fingerprint(lhs, out);
            out.push(',');
            write_expr_fingerprint(rhs, out);
            out.push(')');
        }
        ExprKind::Binary(op, _, _) if is_associative_binop(op.node) => {
            let _ = write!(out, "assoc({:?})[", op.node);
            let mut terms = Vec::new();
            collect_associative_terms(expr, op.node, &mut terms);
            for term in terms {
                write_expr_fingerprint(term, out);
                out.push(';');
            }
            out.push(']');
        }
        ExprKind::Binary(op, lhs, rhs) => {
            let _ = write!(out, "bin({:?})(", op.node);
            write_expr_fingerprint(lhs, out);
            out.push(',');
            write_expr_fingerprint(rhs, out);
            out.push(')');
        }
        ExprKind::Unary(op, expr) => {
            let _ = write!(out, "un({:?})(", op.node);
            write_expr_fingerprint(expr, out);
            out.push(')');
        }
        ExprKind::Cast(expr) => {
            out.push_str("cast(");
            write_expr_fingerprint(expr, out);
            out.push(')');
        }
        ExprKind::Quant(op, vars, ann, expr) => {
            let _ = write!(out, "quant({:?})[", op.node);
            for var in vars {
                match var {
                    QuantVar::Shadow(ident) => {
                        let _ = write!(out, "shadow({});", ident.name);
                    }
                    QuantVar::Fresh(decl_ref) => {
                        let decl_ref = decl_ref.borrow();
                        let _ = write!(out, "fresh({});", decl_ref.name.name);
                    }
                }
            }
            out.push_str("]{");
            for trigger in &ann.triggers {
                out.push('[');
                for term in trigger.terms() {
                    write_expr_fingerprint(term, out);
                    out.push(';');
                }
                out.push(']');
            }
            out.push('}');
            write_expr_fingerprint(expr, out);
        }
        ExprKind::Subst(ident, by, expr) => {
            let _ = write!(out, "subst({})(", ident.name);
            write_expr_fingerprint(by, out);
            out.push(',');
            write_expr_fingerprint(expr, out);
            out.push(')');
        }
        ExprKind::Lit(lit) => {
            let _ = write!(out, "lit({:?})", lit.node);
        }
    }
}

fn collect_associative_terms<'a>(expr: &'a Expr, op: BinOpKind, out: &mut Vec<&'a Expr>) {
    match &expr.kind {
        ExprKind::Binary(inner_op, lhs, rhs) if inner_op.node == op => {
            collect_associative_terms(lhs, op, out);
            collect_associative_terms(rhs, op, out);
        }
        _ => out.push(expr),
    }
}

fn is_associative_binop(op: BinOpKind) -> bool {
    matches!(
        op,
        BinOpKind::Add
            | BinOpKind::Mul
            | BinOpKind::And
            | BinOpKind::Or
            | BinOpKind::Inf
            | BinOpKind::Sup
    )
}

fn quant_vars_compatible(new_vars: &[QuantVar], old_vars: &[QuantVar]) -> bool {
    new_vars.len() == old_vars.len()
        && new_vars
            .iter()
            .zip(old_vars)
            .all(|(new_var, old_var)| new_var.name().name == old_var.name().name)
}

#[cfg(test)]
mod tests;
