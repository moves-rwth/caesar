use crate::interpreted::FuncDef;
use std::fmt::Debug;
use z3::ast::{Ast, Dynamic};
use z3::{Context, Sort};

/// Identity function that is used to mark constants values. They allow for axioms instantiation
/// without consuming fuel. This allows the SMT to still compute the result of functions where the
/// arguments are known, while limiting instantiation in other cases.
///
/// Conceptually the `Lit` function is generic over its argument. For encoding into SMT it must be
/// monomorphized. A [LitDecl] instance represents a concrete monomorphization and is parameterised
/// by the z3 sort of the argument/ return value.
#[derive(Debug)]
pub struct LitDecl<'ctx> {
    _ctx: &'ctx Context,
    arg_sort: Sort<'ctx>,
    func: FuncDef<'ctx>,
}

impl<'ctx> LitDecl<'ctx> {
    pub fn new(ctx: &'ctx Context, arg_sort: Sort<'ctx>) -> Self {
        // TODO: How do we avoid clashes with user defined code?
        let lit_name = format!("Lit[{}]", &arg_sort);
        let x = Dynamic::fresh_const(ctx, "x", &arg_sort);
        // TODO: FuncDef uses an RecFuncDecl internally. This seems a bit overkill for this use-case.
        //       A FuncInterp would probably suffice, but there is no way of constructing it.
        // identity function
        let func = FuncDef::new(lit_name, &[&x], &x);

        Self {
            _ctx: ctx,
            arg_sort,
            func,
        }
    }

    /// Wrap a value in a `Lit` marker.
    pub fn apply_call(&self, arg: &Dynamic<'ctx>) -> Dynamic<'ctx> {
        assert_eq!(self.arg_sort, arg.get_sort());
        self.func.apply_call(&[arg])
    }

    pub fn arg_sort(&self) -> &Sort<'ctx> {
        &self.arg_sort
    }
}