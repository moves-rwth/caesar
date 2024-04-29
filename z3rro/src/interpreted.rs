//! Small wrapper type for interpreted functions: Those where we have one explicit definition we can insert.

use once_cell::unsync::OnceCell;
use z3::{
    ast::{Ast, Dynamic},
    RecFuncDecl, Symbol,
};

/// An interpreted function. It's basically a [`z3::FuncDecl`] with an explicit definition.
///
/// The actual Z3 declaration is created lazily to avoid polluting the context with unused symbols.
#[derive(Debug)]
pub struct FuncDef<'ctx> {
    name: Symbol,
    args: Vec<Dynamic<'ctx>>,
    body: Dynamic<'ctx>,
    decl: OnceCell<RecFuncDecl<'ctx>>,
}

impl<'ctx> FuncDef<'ctx> {
    pub fn new<S: Into<Symbol>>(name: S, args: &[&Dynamic<'ctx>], body: &Dynamic<'ctx>) -> Self {
        FuncDef {
            name: name.into(),
            args: args.iter().map(|arg| (*arg).clone()).collect(),
            body: body.clone(),
            decl: OnceCell::new(),
        }
    }

    fn get_decl(&self) -> &RecFuncDecl<'ctx> {
        let ctx = self.body.get_ctx();
        self.decl.get_or_init(|| {
            let domain: Vec<_> = self.args.iter().map(|arg| arg.get_sort()).collect();
            let domain: Vec<_> = domain.iter().collect();
            let decl = RecFuncDecl::new(ctx, self.name.clone(), &domain, &self.body.get_sort());
            let args: Vec<_> = self.args.iter().map(|ast| ast as &dyn Ast).collect();
            decl.add_def(&args, &self.body);
            decl
        })
    }

    /// Apply the function with a call to the declared function.
    ///
    /// A call to this function will initialize the Z3 declaration if needed.
    pub fn apply_call(&self, args: &[&Dynamic<'ctx>]) -> Dynamic<'ctx> {
        let decl = self.get_decl();
        let args: Vec<&dyn Ast> = args.iter().map(|ast| *ast as &dyn Ast).collect();
        decl.apply(&args)
    }

    /// Apply the function by inlining its body and substituting the arguments.
    pub fn apply_inline(&self, args: &[&Dynamic<'ctx>]) -> Dynamic<'ctx> {
        assert_eq!(self.args.len(), args.len());
        let substitutions: Vec<_> = self
            .args
            .iter()
            .zip(args)
            .map(|(name, arg)| (name, *arg))
            .collect();
        self.body.substitute(substitutions.as_slice())
    }
}
