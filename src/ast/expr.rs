//! Abstract representation of expressions.

use std::{fmt, str::FromStr};

use num::{BigRational, Zero};

use crate::{
    pretty::{parens_group, pretty_list, Doc, SimplePretty},
    tyctx::TyCtx,
};

use super::{shared::Shared, DeclKind, DeclRef, Ident, Span, Spanned, Symbol, TyKind, VarDecl};

pub type Expr = Shared<ExprData>;

impl Expr {
    /// Replace this expression with another expression in-place.
    ///
    /// The alternative would be to simply clone this expression and then
    /// overwrite the original location with the new expression. However, would
    /// cause an unnecessary clone of the underlying [`ExprData`].
    pub fn replace_with(&mut self, f: impl FnOnce(Expr) -> Expr) {
        let default = || {
            Shared::new(ExprData {
                kind: ExprKind::Lit(Spanned::with_dummy_span(LitKind::Bool(false))),
                ty: Some(TyKind::Bool),
                span: Span::dummy_span(),
            })
        };
        replace_with::replace_with(self, default, f)
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.pretty().render_fmt(80, f)
    }
}

#[derive(Debug, Clone)]
pub struct ExprData {
    pub kind: ExprKind,
    pub ty: Option<TyKind>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    /// A variable.
    Var(Ident),
    /// A call to a procedure or function.
    Call(Ident, Vec<Expr>),
    /// Boolean if-then-else
    Ite(Expr, Expr, Expr),
    /// Use of a binary operator.
    Binary(BinOp, Expr, Expr),
    /// Use of an unary operator.
    Unary(UnOp, Expr),
    /// Type casting.
    Cast(Expr),
    /// A quantifier over some variables.
    Quant(QuantOp, Vec<QuantVar>, QuantAnn, Expr),
    /// A substitution.
    Subst(Ident, Expr, Expr),
    /// A value literal.
    Lit(Lit),
}

impl SimplePretty for Expr {
    fn pretty(&self) -> Doc {
        let res = match &self.kind {
            ExprKind::Var(ident) => Doc::as_string(ident.name),
            ExprKind::Call(ident, args) => {
                Doc::as_string(ident.name).append(parens_group(pretty_list(args)))
            }
            ExprKind::Ite(cond, branch1, branch2) => {
                Doc::text("ite").append(parens_group(pretty_list([cond, branch1, branch2])))
            }
            ExprKind::Binary(bin_op, lhs, rhs) => parens_group(
                lhs.pretty()
                    .append(Doc::space())
                    .append(Doc::text(bin_op.node.as_str()))
                    .append(Doc::space())
                    .append(rhs.pretty()),
            ),
            ExprKind::Unary(un_op, operand) => match &un_op.node {
                UnOpKind::Not | UnOpKind::Non => Doc::as_string(un_op.node.as_str())
                    .append(Doc::space())
                    .append(parens_group(operand.pretty())),
                UnOpKind::Embed => Doc::text("?(")
                    .append(Doc::group(operand.pretty()))
                    .append(Doc::text(")")),
                UnOpKind::Iverson => Doc::text("[")
                    .append(Doc::group(operand.pretty()))
                    .append(Doc::text("]")),
                UnOpKind::Parens => parens_group(operand.pretty()),
            },
            ExprKind::Cast(operand) => Doc::text("cast").append(parens_group(
                self.ty
                    .as_ref()
                    .unwrap()
                    .pretty()
                    .append(Doc::text(", "))
                    .append(Doc::line_())
                    .append(operand.pretty()),
            )),
            ExprKind::Quant(quant_op, quant_vars, ann, expr) => Doc::text(quant_op.node.as_str())
                .append(Doc::space())
                .append(pretty_list(quant_vars))
                .append(ann.pretty())
                .append(Doc::text(". "))
                .append(expr.pretty()),
            ExprKind::Subst(var, subst, expr) => parens_group(expr.pretty())
                .append(Doc::text("["))
                .append(Doc::as_string(var.name))
                .append(Doc::text(" -> ").append(subst.pretty()))
                .append(Doc::text("]")),
            ExprKind::Lit(lit) => lit.node.pretty(),
        };
        Doc::group(res)
    }
}

pub type BinOp = Spanned<BinOpKind>;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BinOpKind {
    /// The `+` operator (addition).
    Add,
    /// The `-` operator (subtraction).
    Sub,
    /// The `*` operator (multiplication).
    Mul,
    /// The `/` operator (divison).
    Div,
    /// The `%` operator (modulo).
    Mod,
    /// The `&&` operator (logical and).
    And,
    /// The `||` operator (logical or).
    Or,
    /// The `==` operator (equality).
    Eq,
    /// The `<` operator (less than).
    Lt,
    /// The `<=` operator (less than or equal to).
    Le,
    /// The `!=` operator (not equal to).
    Ne,
    /// The `>=` operator (greater than or equal to).
    Ge,
    /// The `>` operator (greater than).
    Gt,
    /// The `⊓` operator (infimum).
    Inf,
    /// The `⊔` operator (supremum).
    Sup,
    /// The `→` operator (implication).
    Impl,
    /// The `←` operator (co-implication).
    CoImpl,
    /// The `↘` operator (hard implication/compare).
    Compare,
    /// The `↖` operator (hard co-implication/co-compare).
    CoCompare,
}

impl BinOpKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",
            Self::And => "&&",
            Self::Or => "||",
            Self::Eq => "==",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Ne => "!=",
            Self::Ge => ">=",
            Self::Gt => ">",
            Self::Inf => "⊓",
            Self::Sup => "⊔",
            Self::Impl => "→",
            Self::CoImpl => "←",
            Self::Compare => "↘",
            Self::CoCompare => "↖",
        }
    }
}

pub type UnOp = Spanned<UnOpKind>;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnOpKind {
    /// The `!` operator (negation).
    Not,
    /// The `~` operator (dual of negation),
    Non,
    /// Boolean embedding (maps true to top in the lattice).
    Embed,
    /// Iverson bracket (maps true to 1).
    Iverson,
    /// Parentheses (just to print ASTs faithfully).
    Parens,
}

impl UnOpKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Not => "!",
            Self::Non => "~",
            Self::Embed => "?",
            Self::Iverson => "[...]",
            Self::Parens => "(...)",
        }
    }
}

pub type QuantOp = Spanned<QuantOpKind>;

/// We distinguish between four kinds of quantifiers: supremum and infimum, as
/// well as their boolean versions exists and forall. Although semantically
/// supremum and infimum are the most general and subsume the boolean
/// quantifiers, we keep track of which operator the user has entered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantOpKind {
    /// The infimum of a set.
    Inf,
    /// The supremum of a set.
    Sup,
    /// Boolean forall (equivalent to `Inf` on the lattice of booleans).
    Forall,
    /// Boolean exists (equivalent to `Sup` on the lattice of booleans).
    Exists,
}

impl QuantOpKind {
    pub fn as_str(&self) -> &'static str {
        match self {
            QuantOpKind::Inf => "inf",
            QuantOpKind::Sup => "sup",
            QuantOpKind::Forall => "forall",
            QuantOpKind::Exists => "exists",
        }
    }
}

/// There are two ways to quantify over a variable: Either by reusing an existing
/// declaration ("shadowing"), or by creating a completely new variable declaration.
///
/// Shadowing does not require a type annotation, but a new declaration does.
///
/// Users of the syntax are required to always create new declarations, but
/// verification condition generation makes extensive use of shadowing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantVar {
    Shadow(Ident),
    Fresh(DeclRef<VarDecl>),
}

impl QuantVar {
    /// Get the name of this quantified variable, whether it is shadowing or not.
    pub fn name(&self) -> Ident {
        match self {
            QuantVar::Shadow(ident) => *ident,
            QuantVar::Fresh(decl_ref) => decl_ref.borrow().name,
        }
    }
}

impl SimplePretty for QuantVar {
    fn pretty(&self) -> Doc {
        match self {
            QuantVar::Shadow(ident) => Doc::as_string(ident.name),
            QuantVar::Fresh(decl_ref) => {
                let decl = decl_ref.borrow();
                Doc::as_string(decl.name.name)
                    .append(Doc::text(":"))
                    .append(Doc::space())
                    .append(decl.ty.pretty())
            }
        }
    }
}

/// Annotations on quantifiers. Right now, that's just (optional) triggers.
#[derive(Debug, Clone, Default)]
pub struct QuantAnn {
    pub triggers: Vec<Trigger>,
}

impl QuantAnn {
    /// Add the annotations from `other` to `self`.
    pub fn add(&mut self, other: Self) {
        self.triggers.extend(other.triggers);
    }
}

impl SimplePretty for QuantAnn {
    fn pretty(&self) -> Doc {
        let mut doc = Doc::nil();
        doc = doc.append(Doc::concat(self.triggers.iter().map(|trigger| {
            Doc::space()
                .append(Doc::text("@trigger("))
                .append(trigger.pretty())
                .append(Doc::text(")"))
        })));
        doc
    }
}

/// A *trigger* represents one [`z3::Pattern`] for a quantifier. Usually, it's a
/// single [`Expr`], but multiple expressions create what's called a
/// *multi-pattern*.
#[derive(Debug, Clone)]
pub struct Trigger {
    pub span: Span,
    terms: Vec<Expr>,
}

impl Trigger {
    /// Create a new trigger (multi-)pattern.
    ///
    /// Panics if the list of terms is empty.
    pub fn new(span: Span, terms: Vec<Expr>) -> Self {
        assert!(!terms.is_empty());
        Trigger { span, terms }
    }

    pub fn terms(&self) -> &[Expr] {
        &self.terms
    }

    pub fn terms_mut(&mut self) -> &mut [Expr] {
        &mut self.terms
    }
}

impl SimplePretty for Trigger {
    fn pretty(&self) -> Doc {
        pretty_list(self.terms.iter())
    }
}

pub type Lit = Spanned<LitKind>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum LitKind {
    /// A string literal (`"something"`).
    Str(Symbol),
    /// An unsigned integer literal (`123`).
    UInt(u128),
    /// A number literal represented by a fraction.
    Frac(BigRational),
    /// Infinity,
    Infinity,
    /// A boolean literal.
    Bool(bool),
}

impl LitKind {
    pub fn is_top(&self) -> bool {
        match self {
            LitKind::Infinity => true,
            LitKind::Bool(b) => *b,
            _ => false,
        }
    }

    pub fn is_bot(&self) -> bool {
        match self {
            LitKind::UInt(num) => num.is_zero(),
            LitKind::Frac(frac) => frac.is_zero(),
            LitKind::Bool(b) => !b,
            _ => false,
        }
    }
}

impl FromStr for LitKind {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        crate::front::parser::parse_lit(s)
    }
}

impl fmt::Display for LitKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LitKind::Str(symbol) => f.write_fmt(format_args!("\"{}\"", symbol)),
            LitKind::UInt(num) => num.fmt(f),
            LitKind::Frac(frac) => frac.fmt(f),
            LitKind::Infinity => f.write_str("∞"),
            LitKind::Bool(b) => b.fmt(f),
        }
    }
}

impl SimplePretty for LitKind {
    fn pretty(&self) -> Doc {
        Doc::as_string(self)
    }
}

/// Utility struct to quickly build expressions for program transformations.
#[derive(Clone, Copy)]
pub struct ExprBuilder {
    span: Span,
}

impl ExprBuilder {
    pub fn new(span: Span) -> Self {
        ExprBuilder { span }
    }

    pub fn var(&self, ident: Ident, tcx: &TyCtx) -> Expr {
        let decl = tcx.get(ident).unwrap();
        let ty = match decl.as_ref() {
            DeclKind::VarDecl(var_decl) => var_decl.borrow().ty.clone(),
            _ => panic!("expected variable declaration"),
        };
        Shared::new(ExprData {
            kind: ExprKind::Var(ident),
            ty: Some(ty),
            span: self.span,
        })
    }

    pub fn call(&self, ident: Ident, args: impl IntoIterator<Item = Expr>, tcx: &TyCtx) -> Expr {
        let decl = tcx.get(ident).unwrap();
        let ty = match decl.as_ref() {
            DeclKind::FuncDecl(func_ref) => Some(func_ref.borrow().output.clone()),
            DeclKind::ProcDecl(_) => None,
            _ => panic!("expected variable declaration"),
        };
        Shared::new(ExprData {
            kind: ExprKind::Call(ident, args.into_iter().collect()),
            ty,
            span: self.span,
        })
    }

    pub fn ite(&self, ty: Option<TyKind>, cond: Expr, lhs: Expr, rhs: Expr) -> Expr {
        Shared::new(ExprData {
            kind: ExprKind::Ite(cond, lhs, rhs),
            ty,
            span: self.span,
        })
    }

    pub fn binary(&self, kind: BinOpKind, ty: Option<TyKind>, a: Expr, b: Expr) -> Expr {
        Shared::new(ExprData {
            kind: ExprKind::Binary(Spanned::new(self.span, kind), a, b),
            ty,
            span: self.span,
        })
    }

    pub fn unary(&self, kind: UnOpKind, ty: Option<TyKind>, operand: Expr) -> Expr {
        Shared::new(ExprData {
            kind: ExprKind::Unary(Spanned::new(self.span, kind), operand),
            ty,
            span: self.span,
        })
    }

    pub fn cast(&self, ty: TyKind, operand: Expr) -> Expr {
        let cast_not_needed = operand
            .ty
            .as_ref()
            .is_some_and(|operand_ty| operand_ty == &ty);
        if cast_not_needed {
            return operand;
        }
        Shared::new(ExprData {
            kind: ExprKind::Cast(operand),
            ty: Some(ty),
            span: self.span,
        })
    }

    pub fn quant(
        &self,
        kind: QuantOpKind,
        idents: impl IntoIterator<Item = Ident>,
        operand: Expr,
    ) -> Expr {
        let quant_vars = idents.into_iter().map(QuantVar::Shadow).collect();
        let ty = operand.ty.clone();
        let ann = QuantAnn::default();
        Shared::new(ExprData {
            kind: ExprKind::Quant(Spanned::new(self.span, kind), quant_vars, ann, operand),
            ty,
            span: self.span,
        })
    }

    pub fn subst(&self, expr: Expr, iter: impl IntoIterator<Item = (Ident, Expr)>) -> Expr {
        iter.into_iter().fold(expr, |acc, (lhs, rhs)| {
            let ty = acc.ty.clone();
            Shared::new(ExprData {
                kind: ExprKind::Subst(lhs, rhs, acc),
                ty,
                span: self.span,
            })
        })
    }

    pub fn subst_by(
        &self,
        expr: Expr,
        idents: impl IntoIterator<Item = Ident>,
        mut subst: impl FnMut(Ident) -> Expr,
    ) -> Expr {
        self.subst(expr, idents.into_iter().map(|ident| (ident, subst(ident))))
    }

    pub fn literal(&self, lit: LitKind, tcx: &TyCtx) -> Expr {
        let ty = Some(tcx.lit_ty(&lit));
        Shared::new(ExprData {
            kind: ExprKind::Lit(Spanned::new(self.span, lit)),
            ty,
            span: self.span,
        })
    }

    pub fn bool_lit(&self, value: bool) -> Expr {
        Shared::new(ExprData {
            kind: ExprKind::Lit(Spanned::new(self.span, LitKind::Bool(value))),
            ty: Some(TyKind::Bool),
            span: self.span,
        })
    }

    pub fn uint(&self, value: u128) -> Expr {
        let lit = LitKind::UInt(value);
        Shared::new(ExprData {
            kind: ExprKind::Lit(Spanned::new(self.span, lit)),
            ty: Some(TyKind::UInt),
            span: self.span,
        })
    }

    /// Return the top element for this type. Panics if there is none.
    pub fn top_lit(&self, ty: &TyKind) -> Expr {
        match ty {
            TyKind::Bool => self.bool_lit(true),
            TyKind::EUReal => self.infinity_lit(),
            _ => panic!("type {} has no top element", ty),
        }
    }

    /// Return the bottom element for this type. Panics if there is none.
    pub fn bot_lit(&self, ty: &TyKind) -> Expr {
        match ty {
            TyKind::Bool => self.bool_lit(false),
            TyKind::UInt => self.uint(0),
            TyKind::UReal => Expr::new(ExprData {
                kind: ExprKind::Cast(self.uint(0)),
                ty: Some(TyKind::UReal),
                span: self.span,
            }),
            TyKind::EUReal => Expr::new(ExprData {
                kind: ExprKind::Cast(self.uint(0)),
                ty: Some(TyKind::EUReal),
                span: self.span,
            }),
            _ => panic!("type {} has no bottom element", ty),
        }
    }

    pub fn infinity_lit(&self) -> Expr {
        Shared::new(ExprData {
            kind: ExprKind::Lit(Spanned::new(self.span, LitKind::Infinity)),
            ty: Some(TyKind::EUReal),
            span: self.span,
        })
    }

    pub fn frac_lit(&self, value: BigRational) -> Expr {
        Shared::new(ExprData {
            kind: ExprKind::Lit(Spanned::new(self.span, LitKind::Frac(value))),
            ty: Some(TyKind::EUReal),
            span: self.span,
        })
    }
}

#[cfg(test)]
mod test {
    use crate::{ast::FileId, front::parser, pretty::pretty_string};

    #[test]
    fn format_expr() {
        let expr = parser::parse_expr(FileId::DUMMY, "x + y * 17 / 1").unwrap();
        let text = pretty_string(&expr);
        assert_eq!(text, "(x + (y * (17 / 1)))");
    }
}
