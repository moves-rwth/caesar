//! Shared utility functions for proof rules

use std::cell::RefCell;

use num::{BigInt, BigRational, Zero};

use crate::{
    ast::{
        DeclKind, DeclRef, Direction, Expr, ExprBuilder, ExprData, ExprKind, FileId, Ident,
        LitKind, Param, ProcDecl, Shared, Span, SpanVariant, Spanned, Stmt, StmtKind, Symbol,
        TyKind, VarDecl, VarKind,
    },
    tyctx::TyCtx,
};

use super::{EncodingEnvironment, ProcInfo};

/// Encode the extend step in k-induction and bmc recursively for k times
/// # Arguments
/// * `span` - The span of the new generated statement
/// * `inner_stmt` - A While statement to be encoded
/// * `k` - How many times the loop will be extended
/// * `invariant` - The invariant which will be used in assert statements
/// * `direction` - The direction of the statements in the extend
/// * `next_iter` - Parameter necessary for the recursion
pub fn encode_extend(
    enc_env: &EncodingEnvironment,
    inner_stmt: &Stmt,
    k: u128,
    invariant: &Expr,
    direction: Direction,
    next_iter: Vec<Stmt>,
) -> Vec<Stmt> {
    if k == 0 {
        return next_iter;
    }
    let next_iter = encode_extend(enc_env, inner_stmt, k - 1, invariant, direction, next_iter);
    vec![
        Spanned::new(
            enc_env.call_span,
            StmtKind::Assert(direction, invariant.clone()),
        ),
        encode_iter(enc_env, inner_stmt, next_iter).unwrap(),
    ]
}

/// Encode the extend step in bmc recursively for k times:
///
/// # Arguments
/// * `inner_stmt` - A While statement to be encoded
/// * `k` - How many times the loop will be extended
/// * `next_iter` - Parameter necessary for the recursion
pub fn encode_unroll(
    enc_env: &EncodingEnvironment,
    inner_stmt: &Stmt,
    k: u128,
    next_iter: Vec<Stmt>,
) -> Vec<Stmt> {
    if k == 0 {
        return next_iter;
    }
    let next_iter = encode_unroll(enc_env, inner_stmt, k - 1, next_iter);
    vec![encode_iter(enc_env, inner_stmt, next_iter).unwrap()]
}

/// Encode one iteration of a while loop with an if then else statement
pub fn encode_iter(
    enc_env: &EncodingEnvironment,
    stmt: &Stmt,
    next_iter: Vec<Stmt>,
) -> Option<Stmt> {
    if let StmtKind::While(expr, body) = &stmt.node {
        let mut next_body = body.clone();
        next_body.node.extend(next_iter);
        let empty_block = Spanned::new(enc_env.stmt_span, vec![]);
        return Some(Spanned::new(
            enc_env.stmt_span,
            StmtKind::If(expr.clone(), next_body, empty_block),
        ));
    };
    None
}

/// Constant program which always evaluates to the given expression
pub fn hey_const(
    enc_env: &EncodingEnvironment,
    expr: &Expr,
    direction: Direction,
    tcx: &TyCtx,
) -> Vec<Stmt> {
    let span = enc_env.call_span;
    let builder = ExprBuilder::new(span);
    let extreme_lit = match direction {
        Direction::Up => builder.top_lit(tcx.spec_ty()),
        Direction::Down => builder.bot_lit(tcx.spec_ty()),
    };
    vec![
        Spanned::new(span, StmtKind::Assert(direction, expr.clone())),
        Spanned::new(span, StmtKind::Assume(direction, extreme_lit)),
    ]
}

pub fn new_ident_with_name(tcx: &TyCtx, ty: &TyKind, span: Span, name: &str) -> Ident {
    let new_ident = Ident {
        name: Symbol::intern(name),
        span,
    };

    // If the init_variable is not already defined.
    if tcx.get(new_ident).is_none() {
        let var_decl = VarDecl {
            name: new_ident,
            ty: ty.clone(),
            kind: VarKind::Input,
            init: None,
            span,
            created_from: None,
            range: None,
        };
        let decl = DeclRef::new(var_decl);
        tcx.declare(DeclKind::VarDecl(decl));
    }

    new_ident
}

/// Get the init versions of the given idents and declare them
pub fn get_init_idents(tcx: &TyCtx, span: Span, idents: &[Ident]) -> Vec<Ident> {
    let mut new_idents = vec![];
    for ident in idents.iter() {
        let ty = match tcx.get(*ident).unwrap().as_ref() {
            DeclKind::VarDecl(var_ref) => var_ref.borrow().ty.clone(),
            _ => panic!(),
        };

        let new_name = format!("init_{}", ident.name.to_owned());
        let new_ident = Ident {
            name: Symbol::intern(&new_name),
            span: ident.span.variant(SpanVariant::Encoding),
        };
        new_idents.push(new_ident);

        // If the init_variable is not already defined.
        if tcx.get(new_ident).is_none() {
            let var_decl = VarDecl {
                name: new_ident,
                ty: ty.clone(),
                kind: VarKind::Input,
                init: None,
                span,
                created_from: Some(*ident),
                range: None,
            };
            let decl = DeclRef::new(var_decl);
            tcx.declare(DeclKind::VarDecl(decl.clone()));
        }
    }

    new_idents
}

/// Construct multiple [`StmtKind::Assign`] expressions sequentially
pub fn multiple_assign(span: Span, lhses: Vec<Ident>, rhses: Vec<Expr>) -> Vec<Stmt> {
    assert_eq!(lhses.len(), rhses.len());
    let mut buf: Vec<Stmt> = vec![];
    lhses.iter().zip(rhses).for_each(|(lhs, rhs)| {
        let stmt = Spanned::new(span, StmtKind::Assign(vec![*lhs], rhs));
        buf.push(stmt);
    });
    buf
}

/// Construct an variable [`Expr`] from the given [`Ident`]
pub fn ident_to_expr(tcx: &TyCtx, span: Span, ident: Ident) -> Expr {
    let ty = match tcx.get(ident).unwrap().as_ref() {
        DeclKind::VarDecl(var_ref) => var_ref.borrow().ty.clone(),
        _ => panic!(),
    };
    Shared::new(ExprData {
        kind: ExprKind::Var(ident),
        ty: Some(ty),
        span,
    })
}

/// Construct an expression from the given expression
/// in which all variables given in the variables input are replaced by init versions of the corresponding variable
pub fn to_init_expr(tcx: &TyCtx, span: Span, expr: &Expr, variables: &[Ident]) -> Expr {
    let builder = ExprBuilder::new(span);

    // Construct "init_{}" versions of variables in the invariant parameters and transform them into expressions
    let init_expressions: Vec<Expr> = get_init_idents(tcx, span, variables)
        .iter()
        .map(|ident| ident_to_expr(tcx, span, *ident))
        .collect();

    // To substitute the variables with init versions, create a mapping by zipping the two vectors
    let init_mapping: Vec<(Ident, Expr)> =
        variables.iter().copied().zip(init_expressions).collect();

    // Construct the version of the invariant with all variables substituted by init versions
    let new_expr: Expr = builder.subst(expr.clone(), init_mapping);

    new_expr
}

/// Construct and declare a [`DeclKind::ProcDecl`] instance with the given arguments
pub fn generate_proc(
    span: Span,
    proc_info: ProcInfo,
    base_proc_ident: Ident,
    tcx: &TyCtx,
) -> DeclKind {
    // construct the name of the new procedure by appending the proc name to the base proc name
    let ident = Ident::with_dummy_file_span(
        Symbol::intern(format!("{}_{}", base_proc_ident.name, proc_info.name).as_str()),
        span.file,
    );
    // get a fresh ident to avoid name conflicts
    let name = tcx.fresh_ident(ident, ident.span.variant(SpanVariant::Encoding));

    let decl = DeclKind::ProcDecl(DeclRef::new(ProcDecl {
        direction: proc_info.direction,
        // TODO: replace the dummy span with a proper span
        name,
        inputs: Spanned::new(span, proc_info.inputs),
        outputs: Spanned::new(span, proc_info.outputs),
        spec: proc_info.spec,
        body: RefCell::new(Some(proc_info.body)),
        span,
        calculus: None,
    }));

    tcx.declare(decl.clone());

    decl
}

pub fn one_arg(args: &[Expr]) -> [&Expr; 1] {
    if let [a] = args {
        [a]
    } else {
        unreachable!()
    }
}

pub fn two_args(args: &[Expr]) -> [&Expr; 2] {
    if let [a, b] = args {
        [a, b]
    } else {
        unreachable!()
    }
}

pub fn three_args(args: &[Expr]) -> [&Expr; 3] {
    if let [a, b, c] = args {
        [a, b, c]
    } else {
        unreachable!()
    }
}

pub fn four_args(args: &[Expr]) -> [&Expr; 4] {
    if let [a, b, c, d] = args {
        [a, b, c, d]
    } else {
        unreachable!()
    }
}

pub fn mut_four_args(args: &mut [Expr]) -> [&mut Expr; 4] {
    if let [a, b, c, d] = args {
        [a, b, c, d]
    } else {
        unreachable!()
    }
}

pub fn five_args(args: &[Expr]) -> [&Expr; 5] {
    if let [a, b, c, d, e] = args {
        [a, b, c, d, e]
    } else {
        unreachable!()
    }
}

pub fn mut_five_args(args: &mut [Expr]) -> [&mut Expr; 5] {
    if let [ref mut a, ref mut b, ref mut c, ref mut d, ref mut e] = args {
        [a, b, c, d, e]
    } else {
        unreachable!()
    }
}

pub fn lit_rational(expr: &Expr) -> BigRational {
    match &expr.kind {
        ExprKind::Lit(lit) => match &lit.node {
            LitKind::Frac(value) => {
                return value.clone();
            }
            LitKind::UInt(value) => {
                return BigInt::from(value.clone()).into();
            }
            _ => return BigRational::zero(),
        },
        ExprKind::Cast(inner) => return lit_rational(inner),
        _ => (),
    };
    unreachable!()
}

pub fn lit_u128(expr: &Expr) -> u128 {
    if let ExprKind::Lit(lit) = &expr.kind {
        if let LitKind::UInt(value) = &lit.node {
            return TryInto::<u128>::try_into(value).unwrap();
        }
    };
    unreachable!()
}

/// Construct a [`Param`] for intrinsic annotations
pub fn intrinsic_param(file: FileId, name: &str, ty: TyKind, literal_only: bool) -> Param {
    Param {
        // TODO: replace the dummy span with a proper span
        name: Ident::with_dummy_file_span(Symbol::intern(name), file),
        ty: Box::new(ty),
        literal_only,
        span: Span::dummy_file_span(file),
        range: None,
    }
}

/// Construct [`Param`]s with the given [`Ident`]s. The idents must be declared before.
pub fn params_from_idents(idents: Vec<Ident>, tcx: &TyCtx) -> Vec<Param> {
    let mut buf: Vec<Param> = vec![];
    for ident in idents.iter() {
        if let DeclKind::VarDecl(var_ref) = tcx.get(*ident).unwrap().as_ref() {
            let var_ref = var_ref.clone();
            let var = var_ref.borrow();

            buf.push(Param {
                name: *ident,
                ty: Box::new(var.ty.clone()),
                literal_only: false,
                span: ident.span,
                range: None,
            })
        }
    }
    buf
}
