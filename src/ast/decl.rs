//! Declarations in the language. In contrast to the other modules under `ast`,
//! we do not aim for a direct representation of the syntax. Our [`DeclKind`]
//! includes all declarations that can occur in the language, everywhere.

use std::{
    cell::{Ref, RefCell, RefMut},
    fmt::{Display, Formatter},
    hash::{Hash, Hasher},
    rc::Rc,
};

use crate::{
    intrinsic::{annotations::AnnotationKind, FuncIntrin, ProcIntrin},
    pretty::{parens_group, pretty_block, Doc, SimplePretty},
};

use super::{Block, Direction, Expr, Ident, Span, Spanned, TyKind};

/// All different kinds of declarations. Each kind is represented by a
/// [`DeclRef`] to the data structure.
#[derive(Debug, Clone)]
pub enum DeclKind {
    VarDecl(DeclRef<VarDecl>),
    ProcDecl(DeclRef<ProcDecl>),
    DomainDecl(DeclRef<DomainDecl>),
    FuncDecl(DeclRef<FuncDecl>),
    AxiomDecl(DeclRef<AxiomDecl>),
    ProcIntrin(Rc<dyn ProcIntrin>),
    FuncIntrin(Rc<dyn FuncIntrin>),
    LabelDecl(Ident),
    AnnotationDecl(AnnotationKind),
}

impl DeclKind {
    /// Retrieve the declaration's name. This will immutably borrow the
    /// underlying [`DeclRef`]s (and will panic if there is a mutable borrow!).
    pub fn name(&self) -> Ident {
        match self {
            DeclKind::VarDecl(var_decl) => var_decl.borrow().name,
            DeclKind::ProcDecl(proc_decl) => proc_decl.borrow().name,
            DeclKind::DomainDecl(domain_decl) => domain_decl.borrow().name,
            DeclKind::FuncDecl(func_decl) => func_decl.borrow().name,
            DeclKind::AxiomDecl(axiom_decl) => axiom_decl.borrow().name,
            DeclKind::ProcIntrin(proc_intrin) => proc_intrin.name(),
            DeclKind::FuncIntrin(func_intrin) => func_intrin.name(),
            DeclKind::LabelDecl(ident) => *ident,
            DeclKind::AnnotationDecl(anno_intrin) => anno_intrin.name(),
        }
    }

    /// Convert into [`DeclKindName`].
    pub fn kind_name(&self) -> DeclKindName {
        DeclKindName::from(self)
    }
}

impl SimplePretty for DeclKind {
    fn pretty(&self) -> Doc {
        match self {
            DeclKind::VarDecl(var_decl) => var_decl.borrow().pretty_decl(),
            DeclKind::ProcDecl(proc_decl) => proc_decl.pretty(),
            DeclKind::DomainDecl(domain_decl) => domain_decl.pretty(),
            DeclKind::FuncDecl(func_decl) => func_decl.pretty(),
            DeclKind::AxiomDecl(axiom_decl) => axiom_decl.pretty(),
            DeclKind::ProcIntrin(proc_intrin) => Doc::text("intrinsic")
                .append(Doc::space())
                .append(Doc::text("proc"))
                .append(Doc::space())
                .append(Doc::as_string(proc_intrin.name().name)),
            DeclKind::FuncIntrin(fn_intrin) => Doc::text("intrinsic")
                .append(Doc::space())
                .append(Doc::text("fn"))
                .append(Doc::space())
                .append(Doc::as_string(fn_intrin.name().name)),
            DeclKind::LabelDecl(ident) => Doc::text("label")
                .append(Doc::space())
                .append(Doc::as_string(ident.name)),
            DeclKind::AnnotationDecl(anno_intrin) => Doc::text("intrinsic")
                .append(Doc::space())
                .append(Doc::text("annotation"))
                .append(Doc::space())
                .append(Doc::as_string(anno_intrin.name().name)),
        }
    }
}

/// Just the name of the [`DeclKind`] to classify different declaration kinds
/// and print the name of the kind of declaration to the user.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DeclKindName {
    Var(VarKind),
    Proc,
    Domain,
    Func,
    Axiom,
    ProcIntrin,
    FuncIntrin,
    Label,
    Annotation,
}

impl From<&DeclKind> for DeclKindName {
    fn from(decl: &DeclKind) -> Self {
        match decl {
            DeclKind::VarDecl(decl_ref) => DeclKindName::Var(decl_ref.borrow().kind),
            DeclKind::ProcDecl(_) => DeclKindName::Proc,
            DeclKind::DomainDecl(_) => DeclKindName::Domain,
            DeclKind::FuncDecl(_) => DeclKindName::Func,
            DeclKind::AxiomDecl(_) => DeclKindName::Axiom,
            DeclKind::ProcIntrin(_) => DeclKindName::ProcIntrin,
            DeclKind::FuncIntrin(_) => DeclKindName::FuncIntrin,
            DeclKind::LabelDecl(_) => DeclKindName::Label,
            DeclKind::AnnotationDecl(_) => DeclKindName::Annotation,
        }
    }
}

impl DeclKindName {
    /// Return `self`, but all intrinsic kinds are mapped to their non-intrinsic
    /// counterparts. Useful to print declaration kind names to the user who
    /// does not care about whether something is intrinsic or not.
    pub fn lose_intrin(self) -> Self {
        match self {
            DeclKindName::ProcIntrin => DeclKindName::Proc,
            DeclKindName::FuncIntrin => DeclKindName::Func,
            other => other,
        }
    }

    /// Is this declaration callable?
    pub fn is_callable(self) -> bool {
        matches!(
            self,
            DeclKindName::Proc
                | DeclKindName::Func
                | DeclKindName::ProcIntrin
                | DeclKindName::FuncIntrin
        )
    }

    /// Is this a proc (possibly intrinsic)?
    pub fn is_proc(self) -> bool {
        matches!(self, DeclKindName::Proc | DeclKindName::ProcIntrin)
    }
}

impl Display for DeclKindName {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            DeclKindName::Var(kind) => f.write_fmt(format_args!("{} variable", kind)),
            DeclKindName::Proc => f.write_str("proc"),
            DeclKindName::Domain => f.write_str("domain"),
            DeclKindName::Func => f.write_str("func"),
            DeclKindName::Axiom => f.write_str("axiom"),
            DeclKindName::ProcIntrin => f.write_str("intrinsic proc"),
            DeclKindName::FuncIntrin => f.write_str("intrinsic func"),
            DeclKindName::Label => f.write_str("label"),
            DeclKindName::Annotation => f.write_str("annotation"),
        }
    }
}

/// Declaration kinds are kept in reference-counted [`RefCell`]s This is so that
/// the symbol table ([`crate::tyctx::TyCtx`]) can keep a reference to the
/// current state of each declaration and that we can modify it after insertion
/// into the symbol table.
///
/// Each [`DeclRef`] is implements [`PartialEq`], [`Eq`], and [`Hash`] by referential equality.
#[derive(Debug, Clone)]
pub struct DeclRef<T>(Rc<RefCell<T>>);

impl<T> DeclRef<T> {
    pub fn new(decl: T) -> Self {
        DeclRef(Rc::new(RefCell::new(decl)))
    }

    /// See [`RefCell::borrow`].
    pub fn borrow(&self) -> Ref<'_, T> {
        self.0.borrow()
    }

    /// Similar to [`RefCell::borrow_mut`], but we require `&mut` here.
    pub fn borrow_mut(&mut self) -> RefMut<'_, T> {
        self.0.borrow_mut()
    }

    /// See [`Rc::try_unwrap`].
    pub fn try_unwrap(self) -> Result<T, Self> {
        Rc::try_unwrap(self.0)
            .map(|refcell| refcell.into_inner())
            .map_err(|err| DeclRef(err))
    }
}

impl<T> PartialEq for DeclRef<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl<T> Eq for DeclRef<T> {}

impl<T> Hash for DeclRef<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.as_ptr().hash(state);
    }
}

impl<T: SimplePretty> SimplePretty for DeclRef<T> {
    fn pretty(&self) -> Doc {
        let decl = self.borrow();
        decl.pretty()
    }
}

/// A variable declaration consists of a name, a type, and a mutability kind, and
/// an optional initial expression.
#[derive(Debug, Clone)]
pub struct VarDecl {
    pub name: Ident,
    pub ty: TyKind,
    pub kind: VarKind,
    pub init: Option<Expr>,
    pub span: Span,
    /// If this declaration was created by cloning another variable declaration,
    /// we track the original name here.
    pub created_from: Option<Ident>,
}

impl VarDecl {
    /// Create a variable declaration for a parameter.
    pub fn from_param(param: &Param, kind: VarKind) -> DeclRef<VarDecl> {
        let var_decl = VarDecl {
            name: param.name,
            ty: *param.ty.clone(),
            kind,
            init: None,
            span: param.span,
            created_from: None,
        };
        DeclRef::new(var_decl)
    }

    pub fn pretty_stmt(&self) -> Doc {
        self.pretty_with_kind("var")
    }

    pub fn pretty_decl(&self) -> Doc {
        self.pretty_with_kind(self.kind.to_str())
    }

    fn pretty_with_kind(&self, kind: &'static str) -> Doc {
        let res = Doc::text(kind)
            .append(Doc::space())
            .append(Doc::text(self.name.name.to_string()))
            .append(Doc::text(":"))
            .append(Doc::space())
            .append(self.ty.pretty());
        if let Some(init) = &self.init {
            res.append(Doc::text(" = ")).append(init.pretty())
        } else {
            res
        }
    }

    /// The original name of this declaration, i.e. `created_from` if it is
    /// `Some`, else `name`. This is usually the name we want to show to the
    /// user.
    pub fn original_name(&self) -> Ident {
        self.created_from.unwrap_or(self.name)
    }
}

/// What kind of variable is it?
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum VarKind {
    /// Input parameters (cannot be modified).
    Input,
    /// Output parameters (cannot be accessed in the pre).
    Output,
    /// Mutable variables.
    Mut,
    /// Variables bound by a quantifier.
    Quant,
    /// Variables from a substitution (cannot be modified).
    Subst,
    /// Variables for slicing (cannot be modified).
    Slice,
}

impl VarKind {
    /// Is the user allowed to write this variable?
    pub fn is_mutable(self) -> bool {
        matches!(self, VarKind::Mut | VarKind::Output)
    }

    pub fn to_str(&self) -> &'static str {
        match self {
            VarKind::Input => "input",
            VarKind::Output => "output",
            VarKind::Mut => "mutable",
            VarKind::Quant => "bound",
            VarKind::Subst => "subst",
            VarKind::Slice => "slice",
        }
    }
}

impl Display for VarKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.to_str())
    }
}

/// A procedure is a callable that has pre- and postconditions.
#[derive(Debug, Clone)]
pub struct ProcDecl {
    pub direction: Direction,
    pub name: Ident,
    pub inputs: Spanned<Vec<Param>>,
    pub outputs: Spanned<Vec<Param>>,
    pub spec: Vec<ProcSpec>,
    /// the body is a [`RefCell`] to support walking through the definition with
    /// (read) access to the proc declaration.
    pub body: RefCell<Option<Block>>,
    pub span: Span,
}

impl ProcDecl {
    pub fn params_iter_mut(&mut self) -> impl Iterator<Item = &mut Param> {
        self.inputs
            .node
            .iter_mut()
            .chain(self.outputs.node.iter_mut())
    }

    pub fn requires(&self) -> impl Iterator<Item = &Expr> {
        self.spec.iter().flat_map(move |spec| match &spec {
            ProcSpec::Requires(expr) => Some(expr),
            _ => None,
        })
    }

    pub fn ensures(&self) -> impl Iterator<Item = &Expr> {
        self.spec.iter().flat_map(move |spec| match &spec {
            ProcSpec::Ensures(expr) => Some(expr),
            _ => None,
        })
    }

    pub fn return_ty(&self) -> TyKind {
        TyKind::Tuple(
            self.outputs
                .node
                .iter()
                .map(|param| *param.ty.clone())
                .collect(),
        )
    }
}

impl SimplePretty for ProcDecl {
    fn pretty(&self) -> Doc {
        let mut res = Doc::text(match self.direction {
            Direction::Down => "proc",
            Direction::Up => "coproc",
        })
        .append(Doc::space())
        .append(Doc::as_string(self.name.name))
        .append(parens_group(Doc::intersperse(
            self.inputs.node.iter().map(|param| param.pretty()),
            Doc::text(", "),
        )))
        .append(Doc::space())
        .append(Doc::text("->"))
        .append(Doc::space())
        .append(parens_group(Doc::intersperse(
            self.outputs.node.iter().map(|param| param.pretty()),
            Doc::text(", "),
        )));
        if !self.spec.is_empty() {
            res = res
                .append(
                    Doc::hardline()
                        .append(Doc::intersperse(
                            self.spec.iter().map(|spec| spec.pretty()),
                            Doc::hardline(),
                        ))
                        .nest(4),
                )
                .append(Doc::hardline());
        }
        let body = self.body.borrow();
        if let Some(body) = &*body {
            if self.spec.is_empty() {
                res = res.append(Doc::space());
            }
            res = res.append(pretty_block(body.pretty()));
        }
        res
    }
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: Ident,
    pub ty: Box<TyKind>,
    pub literal_only: bool,
    pub span: Span,
}

impl SimplePretty for Param {
    fn pretty(&self) -> Doc {
        Doc::group(
            Doc::as_string(self.name.name)
                .append(Doc::text(":").append(Doc::space()).append(self.ty.pretty())),
        )
    }
}

#[derive(Debug, Clone)]
pub enum ProcSpec {
    /// A `requires` specification.
    Requires(Expr),
    /// An `ensures` specification.
    Ensures(Expr),
}

impl SimplePretty for ProcSpec {
    fn pretty(&self) -> Doc {
        match self {
            ProcSpec::Requires(expr) => Doc::text("pre").append(Doc::space()).append(expr.pretty()),
            ProcSpec::Ensures(expr) => Doc::text("post").append(Doc::space()).append(expr.pretty()),
        }
    }
}

/// A domain declaration.
#[derive(Debug, Clone)]
pub struct DomainDecl {
    pub name: Ident,
    pub body: Vec<DomainSpec>,
    pub span: Span,
}

impl SimplePretty for DomainDecl {
    fn pretty(&self) -> Doc {
        Doc::text("domain")
            .append(Doc::space())
            .append(Doc::as_string(self.name.name))
            .append(Doc::space())
            .append(pretty_block(Doc::intersperse(
                self.body.iter().map(|spec| spec.pretty()),
                Doc::hardline(),
            )))
    }
}

#[derive(Debug, Clone)]
pub enum DomainSpec {
    Function(DeclRef<FuncDecl>),
    Axiom(DeclRef<AxiomDecl>),
}

impl SimplePretty for DomainSpec {
    fn pretty(&self) -> Doc {
        match self {
            DomainSpec::Function(func_ref) => func_ref.pretty(),
            DomainSpec::Axiom(axiom_ref) => axiom_ref.pretty(),
        }
    }
}

/// An (uninterpreted) function has input parameters and exactly one output
/// value. It can be called everywhere and has no side effects.
///
/// A function declaration can also have an optional body that defines it.
#[derive(Debug, Clone)]
pub struct FuncDecl {
    pub name: Ident,
    pub inputs: Spanned<Vec<Param>>,
    pub output: TyKind,
    /// The body is in a [`RefCell`] so that we can have an exclusive reference
    /// to it while still retrieving a shared reference to the declaration
    pub body: RefCell<Option<Expr>>,
    pub span: Span,
}

impl SimplePretty for FuncDecl {
    fn pretty(&self) -> Doc {
        let res = Doc::text("fn")
            .append(Doc::space())
            .append(Doc::as_string(self.name.name))
            .append(parens_group(Doc::intersperse(
                self.inputs.node.iter().map(|param| param.pretty()),
                Doc::text(", "),
            )))
            .append(Doc::space())
            .append(Doc::text("->"))
            .append(Doc::space())
            .append(self.output.pretty());
        let body = self.body.borrow();
        if let Some(body) = &*body {
            res.append(Doc::space())
                .append(Doc::text("="))
                .append(Doc::space())
                .append(body.pretty())
        } else {
            res
        }
    }
}

#[derive(Debug, Clone)]
pub struct AxiomDecl {
    pub name: Ident,
    pub axiom: Expr,
    pub span: Span,
}

impl SimplePretty for AxiomDecl {
    fn pretty(&self) -> Doc {
        Doc::text("axiom")
            .append(Doc::space())
            .append(Doc::as_string(self.name.name))
            .append(Doc::space())
            .append(self.axiom.pretty())
    }
}
