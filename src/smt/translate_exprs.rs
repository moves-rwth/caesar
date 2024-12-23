//! Translation of Caesar expressions to Z3 expressions.

use itertools::Itertools;
use once_cell::unsync::OnceCell;
use ref_cast::RefCast;
use std::{collections::HashMap, convert::TryFrom, vec};
use z3::{
    ast::{Ast, Bool, Dynamic, Int, Real},
    Pattern,
};

use crate::{
    ast::{
        BinOpKind, DeclKind, Expr, ExprKind, Ident, LitKind, QuantOpKind, QuantVar, Shared,
        Trigger, TyKind, UnOpKind,
    },
    scope_map::ScopeMap,
};

use super::{
    symbolic::{ScopeSymbolic, Symbolic, SymbolicPair},
    SmtCtx,
};
use crate::ast::visit::VisitorMut;
use crate::ast::{ExprData, PointerHashShared};
use crate::smt::limited::{ConstantExprCollector, ConstantExprs};
use z3rro::scope::WEIGHT_DEFAULT;
use z3rro::{
    eureal::EUReal,
    orders::{
        smt_bool_embed, smt_max, smt_min, SmtCompleteLattice, SmtGodel, SmtLattice, SmtOrdering,
        SmtPartialOrd,
    },
    scope::SmtScope,
    Fuel, List, LitWrap, SmtBranch, SmtEq, UInt, UReal,
};

/// Translates caesar expressions to Z3 formulas.
/// Fresh variables are created for local variables that occur in the expression.
///
/// Translations of expressions are cached.
pub struct TranslateExprs<'smt, 'ctx> {
    pub ctx: &'smt SmtCtx<'ctx>,
    limits_stack: Vec<SmtScope<'ctx>>,
    locals: ScopeMap<Ident, ScopeSymbolic<'ctx>>,
    cache: TranslateCache<'ctx>,
    fuel_context: FuelContext<'ctx>,
    constant_exprs: ConstantExprs,
}

impl<'smt, 'ctx> TranslateExprs<'smt, 'ctx> {
    pub fn new(ctx: &'smt SmtCtx<'ctx>) -> Self {
        TranslateExprs {
            ctx,
            limits_stack: vec![SmtScope::new()],
            locals: ScopeMap::new(),
            cache: TranslateCache::new(),
            fuel_context: FuelContext::call(),
            constant_exprs: ConstantExprs::default(),
        }
    }

    pub fn push(&mut self) -> &SmtScope<'ctx> {
        self.limits_stack.push(SmtScope::new());
        self.locals.push();
        self.cache.push();
        &self.limits_stack[self.limits_stack.len() - 2]
    }

    pub fn pop(&mut self) {
        assert!(self.limits_stack.len() > 1);
        self.limits_stack.pop();
        self.locals.unchecked_pop();
        self.cache.pop();
    }

    pub fn local_scope(&self) -> SmtScope<'ctx> {
        let mut scope = self.limits_stack.last().unwrap().clone();
        scope.extend(self.locals.local_iter().map(|(_ident, local)| &local.scope));
        scope.extend(
            self.fuel_context
                .quantified_fuel()
                .and_then(|qf| qf.scope()),
        );
        scope
    }

    pub fn set_fuel_context(&mut self, fuel_context: FuelContext<'ctx>) {
        self.fuel_context = fuel_context;
    }

    pub fn fuel_context(&self) -> &FuelContext<'ctx> {
        &self.fuel_context
    }

    pub fn fuel_context_mut(&mut self) -> &mut FuelContext<'ctx> {
        &mut self.fuel_context
    }

    pub fn add_constant_exprs(
        &mut self,
        functions_with_definition: &[Ident],
        constant_vars: &[Ident],
        expr_to_analyse: &mut Expr,
    ) {
        let mut collector = ConstantExprCollector::new(functions_with_definition, constant_vars);
        collector.visit_expr(expr_to_analyse).unwrap();
        self.constant_exprs.extend(collector.into_constant_exprs());
    }

    pub fn clear_constant_exprs(&mut self) {
        self.constant_exprs = ConstantExprs::default();
    }

    fn wrap_if_constant<A: LitWrap<'ctx>>(&self, expr: &Expr, ast: A) -> A
where {
        if self.constant_exprs.is_constant(expr) {
            ast.lit_wrap(self.ctx)
        } else {
            ast
        }
    }

    pub fn local_idents<'a>(&'a self) -> impl Iterator<Item = Ident> + 'a {
        self.locals.local_iter().map(|(ident, _)| *ident)
    }

    pub fn fresh(&mut self, ident: Ident) {
        self.locals.remove(ident);
    }

    pub fn t_symbolic(&mut self, expr: &Expr) -> Symbolic<'ctx> {
        match &expr.ty.as_ref().unwrap() {
            TyKind::Bool => Symbolic::Bool(self.t_bool(expr)),
            TyKind::Int => Symbolic::Int(self.t_int(expr)),
            TyKind::UInt => Symbolic::UInt(self.t_uint(expr)),
            TyKind::Real => Symbolic::Real(self.t_real(expr)),
            TyKind::UReal => Symbolic::UReal(self.t_ureal(expr)),
            TyKind::EUReal => Symbolic::EUReal(self.t_eureal(expr)),
            TyKind::Tuple(_) => todo!(),
            TyKind::List(_) => Symbolic::List(self.t_list(expr)),
            TyKind::Domain(_) => Symbolic::Uninterpreted(self.t_uninterpreted(expr)),
            TyKind::String => unreachable!(),
            TyKind::SpecTy => unreachable!(),
            TyKind::Unresolved(_) => unreachable!(),
            TyKind::None => unreachable!(),
        }
    }

    pub fn t_bool(&mut self, expr: &Expr) -> Bool<'ctx> {
        if is_expr_worth_caching(expr) {
            if let Some(res) = self.cache.get(expr) {
                return res.clone().into_bool().unwrap();
            }
        }

        let res = match &expr.kind {
            ExprKind::Var(ident) => self.get_local(*ident).symbolic.clone().into_bool().unwrap(),
            ExprKind::Call(name, args) => self.t_call(*name, args).clone().into_bool().unwrap(),
            ExprKind::Ite(cond, lhs, rhs) => {
                let cond = self.t_bool(cond);
                let lhs = self.t_bool(lhs);
                let rhs = self.t_bool(rhs);
                Bool::branch(&cond, &lhs, &rhs)
            }
            ExprKind::Binary(bin_op, lhs, rhs) => match bin_op.node {
                BinOpKind::And => Bool::and(self.ctx.ctx, &[&self.t_bool(lhs), &self.t_bool(rhs)]),
                BinOpKind::Or => Bool::or(self.ctx.ctx, &[&self.t_bool(lhs), &self.t_bool(rhs)]),
                BinOpKind::Eq | BinOpKind::Ne => {
                    let t_pair = self.t_pair(lhs, rhs);
                    let eq = match t_pair {
                        SymbolicPair::Bools(a, b) => a.smt_eq(&b),
                        SymbolicPair::Ints(a, b) => a.smt_eq(&b),
                        SymbolicPair::UInts(a, b) => a.smt_eq(&b),
                        SymbolicPair::Reals(a, b) => a.smt_eq(&b),
                        SymbolicPair::UReals(a, b) => a.smt_eq(&b),
                        SymbolicPair::EUReals(a, b) => a.smt_eq(&b),
                        SymbolicPair::Lists(a, b) => a.smt_eq(&b),
                        SymbolicPair::Uninterpreteds(a, b) => a.smt_eq(&b),
                    };
                    if bin_op.node == BinOpKind::Ne {
                        eq.not()
                    } else {
                        eq
                    }
                }
                BinOpKind::Impl => self.t_bool(lhs).implies(&self.t_bool(rhs)),
                BinOpKind::Inf => self.t_bool(lhs).inf(&self.t_bool(rhs)),
                BinOpKind::Sup => self.t_bool(lhs).sup(&self.t_bool(rhs)),
                BinOpKind::Lt | BinOpKind::Le | BinOpKind::Ge | BinOpKind::Gt => {
                    let smt_ordering = match bin_op.node {
                        BinOpKind::Lt => SmtOrdering::Less,
                        BinOpKind::Le => SmtOrdering::LessOrEqual,
                        BinOpKind::Ge => SmtOrdering::GreaterOrEqual,
                        BinOpKind::Gt => SmtOrdering::Greater,
                        _ => unreachable!(),
                    };
                    let t_pair = self.t_pair(lhs, rhs);
                    match t_pair {
                        SymbolicPair::Ints(a, b) => a.smt_cmp(&b, smt_ordering),
                        SymbolicPair::UInts(a, b) => a.smt_cmp(&b, smt_ordering),
                        SymbolicPair::Reals(a, b) => a.smt_cmp(&b, smt_ordering),
                        SymbolicPair::UReals(a, b) => a.smt_cmp(&b, smt_ordering),
                        SymbolicPair::EUReals(a, b) => a.smt_cmp(&b, smt_ordering),
                        _ => panic!("illegal smtpair {:?}", &t_pair),
                    }
                }
                _ => panic!("illegal exprkind {:?} of expression {}", bin_op, &expr),
            },
            ExprKind::Unary(un_op, operand) => match un_op.node {
                UnOpKind::Not | UnOpKind::Non => self.t_bool(operand).not(),
                UnOpKind::Parens => self.t_bool(operand),
                UnOpKind::Embed | UnOpKind::Iverson => panic!(
                    "illegal exprkind {:?} of expression {:?}",
                    &un_op.node, &expr
                ),
            },
            ExprKind::Cast(operand) => {
                panic!("illegal cast to {:?} from {:?}", &expr.ty, &operand.ty)
            }
            ExprKind::Quant(quant_op, quant_vars, ann, operand) => {
                let operand = self.t_bool(operand);
                let scope = self.mk_scope(quant_vars);
                let patterns: Vec<_> = self.t_triggers(&ann.triggers);
                let patterns: Vec<_> = patterns.iter().collect();
                let quant = match quant_op.node {
                    QuantOpKind::Forall | QuantOpKind::Inf => scope.forall(
                        format!("{:?}", quant_op.span),
                        WEIGHT_DEFAULT,
                        &patterns,
                        &operand,
                    ),
                    QuantOpKind::Exists | QuantOpKind::Sup => scope.exists(&patterns, &operand),
                };
                quant
            }
            ExprKind::Subst(_, _, _) => panic!("illegal exprkind"),
            ExprKind::Lit(lit) => match lit.node {
                LitKind::Bool(value) => Bool::from_bool(self.ctx.ctx, value),
                _ => panic!("illegal exprkind {:?} of expression {:?}", &lit.node, &expr),
            },
        };

        if is_expr_worth_caching(expr) {
            self.cache.insert(expr, Symbolic::Bool(res.clone()));
        }
        self.wrap_if_constant(expr, res)
    }

    pub fn t_int(&mut self, expr: &Expr) -> Int<'ctx> {
        if is_expr_worth_caching(expr) {
            if let Some(res) = self.cache.get(expr) {
                tracing::trace!(ref_count = Shared::ref_count(expr), "uncaching expr");
                return res.clone().into_int().unwrap();
            }
        }

        let res = match &expr.kind {
            ExprKind::Var(ident) => self.get_local(*ident).symbolic.clone().into_int().unwrap(),
            ExprKind::Call(name, args) => self.t_call(*name, args).into_int().unwrap(),
            ExprKind::Ite(cond, lhs, rhs) => {
                let cond = self.t_bool(cond);
                let lhs = self.t_int(lhs);
                let rhs = self.t_int(rhs);
                Int::branch(&cond, &lhs, &rhs)
            }
            ExprKind::Binary(bin_op, lhs, rhs) => match bin_op.node {
                BinOpKind::Add => self.t_int(lhs) + self.t_int(rhs),
                BinOpKind::Sub => self.t_int(lhs) - self.t_int(rhs),
                BinOpKind::Mul => self.t_int(lhs) * self.t_int(rhs),
                BinOpKind::Mod => self.t_int(lhs).modulo(&self.t_int(rhs)),
                BinOpKind::Inf => smt_min(&self.t_int(lhs), &self.t_int(rhs)),
                BinOpKind::Sup => smt_max(&self.t_int(lhs), &self.t_int(rhs)),
                _ => panic!("illegal exprkind {:?} of expression {:?}", bin_op, &expr),
            },
            ExprKind::Unary(un_op, operand) => match un_op.node {
                UnOpKind::Parens => self.t_int(operand),
                _ => panic!("illegal exprkind {:?} of expression {:?}", un_op, &expr),
            },
            ExprKind::Cast(operand) => {
                let operand_ty = operand.ty.as_ref().unwrap();
                match &operand_ty {
                    TyKind::UInt => {
                        let operand = self.t_uint(operand);
                        operand.into_int()
                    }
                    _ => panic!("illegal cast to {:?} from {:?}", &expr.ty, &operand.ty),
                }
            }
            ExprKind::Quant(_, _, _, _) => todo!(),
            ExprKind::Subst(_, _, _) => todo!(),
            ExprKind::Lit(lit) => {
                panic!("illegal exprkind {:?} of expression {:?}", &lit.node, &expr)
            }
        };

        if is_expr_worth_caching(expr) {
            tracing::trace!(ref_count = Shared::ref_count(expr), "caching expr");
            self.cache.insert(expr, Symbolic::Int(res.clone()));
        }
        self.wrap_if_constant(expr, res)
    }

    pub fn t_uint(&mut self, expr: &Expr) -> UInt<'ctx> {
        if is_expr_worth_caching(expr) {
            if let Some(res) = self.cache.get(expr) {
                tracing::trace!(ref_count = Shared::ref_count(expr), "uncaching expr");
                return res.clone().into_uint().unwrap();
            }
        }

        let res = match &expr.kind {
            ExprKind::Var(ident) => self.get_local(*ident).symbolic.clone().into_uint().unwrap(),
            ExprKind::Call(name, args) => self.t_call(*name, args).into_uint().unwrap(),
            ExprKind::Ite(cond, lhs, rhs) => {
                let cond = self.t_bool(cond);
                let lhs = self.t_uint(lhs);
                let rhs = self.t_uint(rhs);
                UInt::branch(&cond, &lhs, &rhs)
            }
            ExprKind::Binary(bin_op, lhs, rhs) => match bin_op.node {
                BinOpKind::Add => self.t_uint(lhs) + self.t_uint(rhs),
                BinOpKind::Sub => self.t_uint(lhs) - self.t_uint(rhs),
                BinOpKind::Mul => self.t_uint(lhs) * self.t_uint(rhs),
                BinOpKind::Mod => self.t_uint(lhs).modulo(&self.t_uint(rhs)),
                BinOpKind::Inf => smt_min(&self.t_uint(lhs), &self.t_uint(rhs)),
                BinOpKind::Sup => smt_max(&self.t_uint(lhs), &self.t_uint(rhs)),
                _ => panic!("illegal exprkind {:?} of expression {:?}", bin_op, &expr),
            },
            ExprKind::Unary(un_op, operand) => match un_op.node {
                UnOpKind::Parens => self.t_uint(operand),
                _ => panic!("illegal exprkind"),
            },
            ExprKind::Cast(operand) => {
                panic!("illegal cast to {:?} from {:?}", &expr.ty, &operand.ty)
            }
            ExprKind::Quant(_, _, _, _) => todo!(),
            ExprKind::Subst(_, _, _) => todo!(),
            ExprKind::Lit(lit) => match lit.node {
                LitKind::UInt(value) => {
                    // TODO: actually handle u128s
                    UInt::from_u64(self.ctx.ctx, u64::try_from(value).unwrap())
                }
                _ => panic!("illegal exprkind {:?} of expression {:?}", &lit.node, &expr),
            },
        };

        if is_expr_worth_caching(expr) {
            tracing::trace!(ref_count = Shared::ref_count(expr), "caching expr");
            self.cache.insert(expr, Symbolic::UInt(res.clone()));
        }

        self.wrap_if_constant(expr, res)
    }

    pub fn t_real(&mut self, expr: &Expr) -> Real<'ctx> {
        if is_expr_worth_caching(expr) {
            if let Some(res) = self.cache.get(expr) {
                tracing::trace!(ref_count = Shared::ref_count(expr), "uncaching expr");
                return res.clone().into_real().unwrap();
            }
        }

        let res = match &expr.kind {
            ExprKind::Var(ident) => self.get_local(*ident).symbolic.clone().into_real().unwrap(),
            ExprKind::Call(name, args) => self.t_call(*name, args).into_real().unwrap(),
            ExprKind::Ite(cond, lhs, rhs) => {
                let cond = self.t_bool(cond);
                let lhs = self.t_real(lhs);
                let rhs = self.t_real(rhs);
                Real::branch(&cond, &lhs, &rhs)
            }
            ExprKind::Binary(bin_op, lhs, rhs) => match bin_op.node {
                BinOpKind::Add => self.t_real(lhs) + self.t_real(rhs),
                BinOpKind::Sub => self.t_real(lhs) - self.t_real(rhs),
                BinOpKind::Mul => self.t_real(lhs) * self.t_real(rhs),
                BinOpKind::Div => self.t_real(lhs) / self.t_real(rhs),
                BinOpKind::Inf => smt_min(&self.t_real(lhs), &self.t_real(rhs)),
                BinOpKind::Sup => smt_max(&self.t_real(lhs), &self.t_real(rhs)),
                _ => panic!("illegal exprkind {:?} of expression {:?}", bin_op, &expr),
            },
            ExprKind::Unary(un_op, operand) => match un_op.node {
                UnOpKind::Parens => self.t_real(operand),
                _ => panic!("illegal exprkind {:?} of expression {:?}", un_op, &expr),
            },
            ExprKind::Cast(operand) => {
                let operand_ty = operand.ty.as_ref().unwrap();
                match &operand_ty {
                    TyKind::UInt => {
                        let operand = self.t_uint(operand);
                        Real::from_int(operand.as_int())
                    }
                    TyKind::Int => {
                        let operand = self.t_int(operand);
                        Real::from_int(&operand)
                    }
                    TyKind::UReal => {
                        let operand = self.t_ureal(operand);
                        operand.into_real()
                    }
                    _ => panic!("illegal cast to {:?} from {:?}", &expr.ty, &operand.ty),
                }
            }
            ExprKind::Quant(_, _, _, _) => todo!(),
            ExprKind::Subst(_, _, _) => todo!(),
            ExprKind::Lit(lit) => {
                panic!("illegal exprkind {:?} of expression {:?}", &lit.node, &expr)
            }
        };

        if is_expr_worth_caching(expr) {
            tracing::trace!(ref_count = Shared::ref_count(expr), "caching expr");
            self.cache.insert(expr, Symbolic::Real(res.clone()));
        }
        self.wrap_if_constant(expr, res)
    }

    pub fn t_ureal(&mut self, expr: &Expr) -> UReal<'ctx> {
        if is_expr_worth_caching(expr) {
            if let Some(res) = self.cache.get(expr) {
                tracing::trace!(ref_count = Shared::ref_count(expr), "uncaching expr");
                return res.clone().into_ureal().unwrap();
            }
        }

        let res = match &expr.kind {
            ExprKind::Var(ident) => self
                .get_local(*ident)
                .symbolic
                .clone()
                .into_ureal()
                .unwrap(),
            ExprKind::Call(name, args) => self.t_call(*name, args).into_ureal().unwrap(),
            ExprKind::Ite(cond, lhs, rhs) => {
                let cond = self.t_bool(cond);
                let lhs = self.t_ureal(lhs);
                let rhs = self.t_ureal(rhs);
                UReal::branch(&cond, &lhs, &rhs)
            }
            ExprKind::Binary(bin_op, lhs, rhs) => match bin_op.node {
                BinOpKind::Add => self.t_ureal(lhs) + self.t_ureal(rhs),
                BinOpKind::Sub => self.t_ureal(lhs) - self.t_ureal(rhs),
                BinOpKind::Mul => self.t_ureal(lhs) * self.t_ureal(rhs),
                BinOpKind::Div => self.t_ureal(lhs) / self.t_ureal(rhs),
                BinOpKind::Inf => smt_min(&self.t_ureal(lhs), &self.t_ureal(rhs)),
                BinOpKind::Sup => smt_max(&self.t_ureal(lhs), &self.t_ureal(rhs)),
                _ => panic!("illegal exprkind {:?} of expression {:?}", bin_op, &expr),
            },
            ExprKind::Unary(un_op, operand) => match un_op.node {
                UnOpKind::Parens => self.t_ureal(operand),
                _ => panic!("illegal exprkind {:?} of expression {:?}", un_op, &expr),
            },
            ExprKind::Cast(operand) => {
                let operand_ty = operand.ty.as_ref().unwrap();
                match &operand_ty {
                    TyKind::UInt => {
                        let operand = self.t_uint(operand);
                        UReal::from_uint(&operand)
                    }
                    _ => panic!("illegal cast to {:?} from {:?}", &expr.ty, &operand.ty),
                }
            }
            ExprKind::Quant(_, _, _, _) => todo!(),
            ExprKind::Subst(_, _, _) => todo!(),
            ExprKind::Lit(lit) => match &lit.node {
                LitKind::Frac(frac) => {
                    UReal::unchecked_from_real(Real::from_big_rational(self.ctx.ctx, frac))
                }
                _ => panic!("illegal exprkind {:?} of expression {:?}", &lit.node, &expr),
            },
        };

        if is_expr_worth_caching(expr) {
            tracing::trace!(ref_count = Shared::ref_count(expr), "caching expr");
            self.cache.insert(expr, Symbolic::UReal(res.clone()));
        }

        self.wrap_if_constant(expr, res)
    }

    pub fn t_eureal(&mut self, expr: &Expr) -> EUReal<'ctx> {
        let res = match &expr.kind {
            ExprKind::Var(ident) => self
                .get_local(*ident)
                .symbolic
                .clone()
                .into_eureal()
                .unwrap(),
            ExprKind::Call(name, args) => self.t_call(*name, args).into_eureal().unwrap(),
            ExprKind::Ite(cond, lhs, rhs) => {
                let cond = self.t_bool(cond);
                let lhs = self.t_eureal(lhs);
                let rhs = self.t_eureal(rhs);
                EUReal::branch(&cond, &lhs, &rhs)
            }
            ExprKind::Binary(bin_op, lhs, rhs) => {
                let lhs = self.t_eureal(lhs);
                let rhs = self.t_eureal(rhs);
                match bin_op.node {
                    BinOpKind::Add => lhs + rhs,
                    BinOpKind::Sub => lhs - rhs,
                    BinOpKind::Mul => lhs * rhs,
                    BinOpKind::Inf => lhs.inf(&rhs),
                    BinOpKind::Sup => lhs.sup(&rhs),
                    BinOpKind::Impl => lhs.implication(&rhs),
                    BinOpKind::CoImpl => lhs.coimplication(&rhs),
                    BinOpKind::Compare => lhs.compare(&rhs),
                    BinOpKind::CoCompare => lhs.cocompare(&rhs),
                    _ => panic!("illegal exprkind {:?} of expression {:?}", bin_op, &expr),
                }
            }
            ExprKind::Unary(un_op, operand) => match un_op.node {
                UnOpKind::Not => self.t_eureal(operand).negate(),
                UnOpKind::Non => self.t_eureal(operand).conegate(),
                UnOpKind::Embed => {
                    let operand = self.t_bool(operand);
                    smt_bool_embed(self.ctx.eureal(), &operand)
                }
                UnOpKind::Iverson => {
                    let operand = self.t_bool(operand);
                    EUReal::iverson(self.ctx.eureal(), &operand)
                }
                UnOpKind::Parens => self.t_eureal(operand),
            },
            ExprKind::Cast(operand) => {
                let operand_ty = operand.ty.as_ref().unwrap();
                match &operand_ty {
                    TyKind::UInt => {
                        let operand = self.t_uint(operand);
                        EUReal::from_uint(self.ctx.eureal(), &operand)
                    }
                    TyKind::UReal => {
                        let operand = self.t_ureal(operand);
                        EUReal::from_ureal(self.ctx.eureal(), &operand)
                    }
                    _ => panic!("illegal cast to {:?} from {:?}", &expr.ty, &operand.ty),
                }
            }
            ExprKind::Quant(quant_op, quant_vars, ann, operand) => {
                let operand = self.t_eureal(operand);
                let scope = self.mk_scope(quant_vars);
                let patterns: Vec<_> = self.t_triggers(&ann.triggers);
                let patterns: Vec<_> = patterns.iter().collect();
                let outer_scope = &mut self.limits_stack.last_mut().unwrap();
                match quant_op.node {
                    QuantOpKind::Inf => operand.infimum(scope, &patterns, outer_scope),
                    QuantOpKind::Sup => operand.supremum(scope, &patterns, outer_scope),
                    QuantOpKind::Forall | QuantOpKind::Exists => panic!("illegal quantopkind"),
                }
            }
            ExprKind::Subst(_, _, _) => panic!("illegal exprkind"),
            ExprKind::Lit(lit) => {
                let eureal = match &lit.node {
                    LitKind::Infinity => EUReal::infinity(self.ctx.eureal()),
                    LitKind::Frac(frac) => EUReal::from_ureal(
                        self.ctx.eureal(),
                        &UReal::unchecked_from_real(Real::from_big_rational(self.ctx.ctx, frac)),
                    ),
                    _ => panic!("illegal exprkind {:?} of expression {:?}", &lit.node, &expr),
                };
                eureal
            }
        };
        self.wrap_if_constant(expr, res)
    }

    pub fn t_uninterpreted(&mut self, expr: &Expr) -> Dynamic<'ctx> {
        if is_expr_worth_caching(expr) {
            if let Some(res) = self.cache.get(expr) {
                tracing::trace!(ref_count = Shared::ref_count(expr), "uncaching expr");
                return res.clone().into_uninterpreted().unwrap();
            }
        }

        let res = match &expr.kind {
            ExprKind::Var(ident) => self
                .get_local(*ident)
                .symbolic
                .clone()
                .into_uninterpreted()
                .unwrap(),
            ExprKind::Call(name, args) => self.t_call(*name, args).into_uninterpreted().unwrap(),
            ExprKind::Ite(cond, lhs, rhs) => {
                let cond = self.t_bool(cond);
                let lhs = self.t_uninterpreted(lhs);
                let rhs = self.t_uninterpreted(rhs);
                Dynamic::branch(&cond, &lhs, &rhs)
            }
            ExprKind::Binary(_, _, _) => panic!("illegal exprkind"),
            ExprKind::Unary(un_op, operand) => match un_op.node {
                UnOpKind::Parens => self.t_uninterpreted(operand),
                _ => panic!(
                    "illegal exprkind {:?} of expression {:?}",
                    &un_op.node, &expr
                ),
            },
            ExprKind::Cast(_) => panic!("illegal exprkind"),
            ExprKind::Quant(_, _, _, _) => todo!(),
            ExprKind::Subst(_, _, _) => todo!(),
            ExprKind::Lit(lit) => {
                panic!("illegal exprkind {:?} of expression {:?}", &lit.node, &expr)
            }
        };

        if is_expr_worth_caching(expr) {
            tracing::trace!(ref_count = Shared::ref_count(expr), "caching expr");
            self.cache
                .insert(expr, Symbolic::Uninterpreted(res.clone()));
        }
        self.wrap_if_constant(expr, res)
    }

    pub fn t_list(&mut self, expr: &Expr) -> List<'ctx> {
        if is_expr_worth_caching(expr) {
            if let Some(res) = self.cache.get(expr) {
                tracing::trace!(ref_count = Shared::ref_count(expr), "uncaching expr");
                return res.clone().into_list().unwrap();
            }
        }

        let res = match &expr.kind {
            ExprKind::Var(ident) => self.get_local(*ident).symbolic.clone().into_list().unwrap(),
            ExprKind::Call(name, args) => self.t_call(*name, args).into_list().unwrap(),
            ExprKind::Ite(cond, lhs, rhs) => {
                let cond = self.t_bool(cond);
                let lhs = self.t_list(lhs);
                let rhs = self.t_list(rhs);
                List::branch(&cond, &lhs, &rhs)
            }
            ExprKind::Binary(_, _, _) => panic!("illegal exprkind"),
            ExprKind::Unary(un_op, operand) => match un_op.node {
                UnOpKind::Parens => self.t_list(operand),
                _ => panic!("illegal exprkind"),
            },
            ExprKind::Cast(_) => panic!("illegal exprkind"),
            ExprKind::Quant(_, _, _, _) => unreachable!(),
            ExprKind::Subst(_, _, _) => unreachable!(),
            ExprKind::Lit(_) => panic!("illegal exprkind"),
        };

        if is_expr_worth_caching(expr) {
            tracing::trace!(ref_count = Shared::ref_count(expr), "caching expr");
            self.cache.insert(expr, Symbolic::List(res.clone()));
        }
        res
    }

    /// Call to a function.
    fn t_call(&mut self, name: Ident, args: &[Expr]) -> Symbolic<'ctx> {
        match self.ctx.tcx().get(name).as_deref() {
            Some(DeclKind::FuncDecl(func)) => {
                let mut args_vec = if self.ctx.is_limited_function(name) {
                    let fuel_arg: Dynamic<'ctx> = match &self.fuel_context {
                        FuelContext::Head(qf) => Fuel::succ(qf.get_or_init(self.ctx)).as_dynamic(),
                        FuelContext::Body(qf) => qf.get_or_init(self.ctx).as_dynamic(),
                        FuelContext::Call => Fuel::new(self.ctx.fuel_factory(), 1).as_dynamic(),
                    };
                    vec![fuel_arg]
                } else {
                    vec![]
                };
                args_vec.extend(
                    args.iter()
                        .map(|arg| self.t_symbolic(arg).into_dynamic(self.ctx)),
                );
                let args = args_vec.iter().map(|d| d as &dyn Ast<'ctx>).collect_vec();
                let res_dynamic = self.ctx.uninterpreteds().apply_function(name, &args);
                Symbolic::from_dynamic(self.ctx, &func.borrow().output, &res_dynamic)
            }
            Some(DeclKind::FuncIntrin(intrin)) => intrin.translate_call(self, args),
            res => panic!("cannot call {:?}", res),
        }
    }

    fn t_pair(&mut self, a: &Expr, b: &Expr) -> SymbolicPair<'ctx> {
        let t_a = self.t_symbolic(a);
        let t_b = self.t_symbolic(b);
        SymbolicPair::from_untypeds(t_a, t_b).unwrap()
    }

    pub fn get_local(&mut self, ident: Ident) -> &ScopeSymbolic<'ctx> {
        if !self.locals.contains_key(&ident) {
            self.init_local(ident);
        }
        self.locals.get(&ident).unwrap()
    }

    fn get_local_ty(&self, ident: Ident) -> TyKind {
        let decl = self
            .ctx
            .tcx()
            .get(ident)
            .unwrap_or_else(|| panic!("{} is not declared", ident));
        match decl.as_ref() {
            DeclKind::VarDecl(var_ref) => var_ref.borrow().ty.clone(),
            _ => panic!("variable is not declared"),
        }
    }

    fn init_local(&mut self, ident: Ident) {
        let local = match &self.get_local_ty(ident) {
            TyKind::Bool => ScopeSymbolic::fresh_bool(self.ctx, ident),
            TyKind::Int => ScopeSymbolic::fresh_int(self.ctx, ident),
            TyKind::UInt => ScopeSymbolic::fresh_uint(self.ctx, ident),
            TyKind::Real => ScopeSymbolic::fresh_real(self.ctx, ident),
            TyKind::UReal => ScopeSymbolic::fresh_ureal(self.ctx, ident),
            TyKind::EUReal => ScopeSymbolic::fresh_eureal(self.ctx, ident),
            TyKind::Domain(domain) => {
                let domain_name = domain.borrow().name;
                let domain_sort = self.ctx.uninterpreteds().get_sort(domain_name).unwrap();
                ScopeSymbolic::fresh_uninterpreted(self.ctx, ident, domain_sort)
            }
            TyKind::Tuple(_) => todo!(),
            TyKind::List(element_ty) => ScopeSymbolic::fresh_list(self.ctx, ident, element_ty),
            TyKind::String => unreachable!(),
            TyKind::SpecTy => unreachable!(),
            TyKind::Unresolved(_) => unreachable!(),
            TyKind::None => unreachable!(),
        };
        self.locals.insert(ident, local);
    }

    /// Create a new scope with the given quantified variables.
    pub fn mk_scope(&mut self, quant_vars: &[QuantVar]) -> SmtScope<'ctx> {
        let mut bounds = SmtScope::new();
        for quant_var in quant_vars {
            bounds.append(&self.get_local(quant_var.name()).scope);
        }
        bounds
    }

    /// Translate our [`Trigger`]s to z3's [`Pattern`]s.
    pub fn t_triggers(&mut self, triggers: &[Trigger]) -> Vec<Pattern<'ctx>> {
        triggers
            .iter()
            .map(|trigger| {
                let terms: Vec<_> = trigger
                    .terms()
                    .iter()
                    .map(|term| self.t_symbolic(term).into_dynamic(self.ctx))
                    .collect();
                let terms_ref: Vec<_> = terms.iter().map(|term| term as &dyn Ast).collect();
                Pattern::new(self.ctx.ctx, &terms_ref)
            })
            .collect()
    }
}

/// Type that determines how the fuel parameter for uninterpreted functions should be synthesised.
pub enum FuelContext<'ctx> {
    Head(QuantifiedFuel<'ctx>),
    Body(QuantifiedFuel<'ctx>),
    Call,
}

impl<'ctx> FuelContext<'ctx> {
    /// In the head of a defining axiom a non-zero universally quantified fuel parameter is
    /// synthesised i.e. `Succ(fuel)`.
    pub fn head() -> Self {
        Self::Head(QuantifiedFuel::default())
    }

    /// In the body of a defining axiom a universally quantified fuel parameter is
    /// synthesised i.e. `fuel`.
    pub fn body() -> Self {
        Self::Body(QuantifiedFuel::default())
    }

    pub fn body_with_fuel(quantified_fuel: QuantifiedFuel<'ctx>) -> Self {
        Self::Body(quantified_fuel)
    }

    /// In other positions the function application represents a call. A fixed fuel
    /// parameter is synthesized that determines how often the function definition can
    /// be instantiated i.e. `Succ(Zero)`.
    pub fn call() -> Self {
        Self::Call
    }

    pub fn quantified_fuel_scope(&self) -> Option<&SmtScope<'ctx>> {
        self.quantified_fuel().and_then(|qf| qf.scope())
    }

    fn quantified_fuel(&self) -> Option<&QuantifiedFuel<'ctx>> {
        match self {
            Self::Head(qf) => Some(qf),
            Self::Body(qf) => Some(qf),
            Self::Call => None,
        }
    }

    pub fn take_quantified_fuel(&mut self) -> Option<QuantifiedFuel<'ctx>> {
        let do_take = |qf: &mut QuantifiedFuel<'ctx>| QuantifiedFuel::new(qf.lazy_fuel.take());
        match self {
            Self::Head(qf) => Some(do_take(qf)),
            Self::Body(qf) => Some(do_take(qf)),
            Self::Call => None,
        }
    }
}

/// Lazily initialised [ScopeSymbolic] of type [Fuel]. It is initialised when a limited function is
/// encountered in context that requires a fresh quantified fuel variable ([FuelContext::Head],
/// [FuelContext::Body]). It is discarded when the context changes back to [FuelContext::Call]
/// (see [TranslateExprs::set_fuel_context]). The lazy initialisation ensures that the fuel variable
/// is only added to the quantifier if it is actually used.
#[derive(Default)]
pub struct QuantifiedFuel<'ctx> {
    lazy_fuel: OnceCell<ScopeSymbolic<'ctx>>,
}

impl<'ctx> QuantifiedFuel<'ctx> {
    pub fn new(value: Option<ScopeSymbolic<'ctx>>) -> Self {
        Self {
            lazy_fuel: match value {
                Some(s) => OnceCell::with_value(s),
                None => OnceCell::new(),
            },
        }
    }

    fn get_or_init(&self, ctx: &SmtCtx<'ctx>) -> Fuel<'ctx> {
        self.lazy_fuel
            .get_or_init(|| ScopeSymbolic::fresh_fuel(ctx))
            .symbolic
            .clone()
            .into_fuel()
            .unwrap()
    }

    pub fn get(&self) -> Option<Fuel<'ctx>> {
        self.lazy_fuel
            .get()
            .and_then(|s| s.symbolic.clone().into_fuel())
    }

    pub fn scope(&self) -> Option<&SmtScope<'ctx>> {
        self.lazy_fuel.get().map(|s| &s.scope)
    }
}

fn is_expr_worth_caching(expr: &Expr) -> bool {
    Shared::ref_count(expr) > 2
}

struct TranslateCache<'ctx> {
    cache: Vec<HashMap<CacheExpr, Symbolic<'ctx>>>,
}

impl<'ctx> TranslateCache<'ctx> {
    fn new() -> Self {
        TranslateCache {
            cache: vec![HashMap::new()],
        }
    }

    fn push(&mut self) {
        self.cache.push(HashMap::new());
    }

    fn pop(&mut self) {
        self.cache.pop();
    }

    fn insert(&mut self, expr: &Expr, value: Symbolic<'ctx>) {
        let cache_expr = CacheExpr::new(expr.clone());
        self.cache.last_mut().unwrap().insert(cache_expr, value);
    }

    fn get(&self, expr: &Expr) -> Option<&Symbolic<'ctx>> {
        self.cache.last().unwrap().get(CacheExpr::ref_cast(expr))
    }
}

type CacheExpr = PointerHashShared<ExprData>;
