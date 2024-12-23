use crate::scope::WEIGHT_DEFAULT;
use crate::SmtEq;
use std::fmt::Debug;
use z3::ast::{quantifier_const, Ast, Bool, Dynamic};
use z3::{Context, FuncDecl, Pattern, Sort};

/// Identity function that is used to mark constants values. They allow for axioms instantiation
/// without consuming fuel. This allows the SMT to still compute the result of functions where the
/// arguments are known, while limiting instantiation in other cases.
///
/// Conceptually the `Lit` function is generic over its argument. For encoding into SMT it must be
/// monomorphized. A [LitDecl] instance represents a concrete monomorphization and is parameterised
/// by the z3 sort of the argument/ return value.
///
/// An equivalent rust function would look like the following:
/// ```
/// # #[allow(non_snake_case)]
/// fn Lit<S>(x: S) -> S {
///     x
/// }
/// ```
pub struct LitDecl<'ctx> {
    ctx: &'ctx Context,
    arg_sort: Sort<'ctx>,
    func: FuncDecl<'ctx>,
}

impl<'ctx> Debug for LitDecl<'ctx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LitDecl")
            .field("arg_sort", &self.arg_sort)
            .finish_non_exhaustive()
    }
}

impl<'ctx> LitDecl<'ctx> {
    pub fn new(ctx: &'ctx Context, arg_sort: Sort<'ctx>) -> Self {
        // Clashes with user defined code are avoided by `$` in the name
        let lit_name = format!("$Lit{}", &arg_sort);
        // We add an uninterpreted function and add a separate defining axiom.
        // Using z3 RecFuncDecl causes the applications to get "optimised" away before solving.
        let func = FuncDecl::new(ctx, lit_name, &[&arg_sort], &arg_sort);
        Self {
            ctx,
            arg_sort,
            func,
        }
    }

    /// Wrap a value in a `Lit` marker.
    pub fn apply_call(&self, arg: &Dynamic<'ctx>) -> Dynamic<'ctx> {
        assert_eq!(self.arg_sort, arg.get_sort());
        self.func.apply(&[arg])
    }

    pub fn arg_sort(&self) -> &Sort<'ctx> {
        &self.arg_sort
    }

    pub fn defining_axiom(&self) -> Vec<Bool<'ctx>> {
        let generic_forall = || {
            // identity function: forall x: ArgSort . Lit(x) == x
            let x = Dynamic::fresh_const(self.ctx, "x", &self.arg_sort);
            let app = self.func.apply(&[&x]);
            quantifier_const(
                self.ctx,
                true,
                WEIGHT_DEFAULT,
                format!("Lit{}(definitional)", self.arg_sort),
                "",
                &[&x],
                &[&Pattern::new(self.ctx, &[&app])],
                &[],
                &app.smt_eq(&x),
            )
        };
        /*match self.arg_sort.kind() {
            SortKind::Bool => [true, false]
                .iter()
                .map(|boolean| {
                    let bool = Bool::from_bool(self.ctx, *boolean);
                    let app = self.func.apply(&[&bool]);
                    app.smt_eq(&bool.into())
                })
                .collect(),
            SortKind::Real => {
                let mut axioms = vec![generic_forall()];
                axioms.extend([-1, 0, 1].into_iter().map(|n| {
                    let real = Real::from_real(self.ctx, n, 1);
                    let app = self.func.apply(&[&real]);
                    app.smt_eq(&real.into())
                }));
                axioms
            }
            SortKind::Int => {
                let mut axioms = vec![generic_forall()];
                axioms.extend([-1, 0, 1].into_iter().map(|n| {
                    let int = Int::from_i64(self.ctx, n);
                    let app = self.func.apply(&[&int]);
                    app.smt_eq(&int.into())
                }));
                axioms
            }
            _ => {
                vec![generic_forall()]
            }
        }*/
        vec![generic_forall()]
    }
}

/// Object that does the actual `Lit` wrapping on SMT level including monomorphization.
pub trait LitFactory<'ctx> {
    /// Wrap a [Dynamic] Z3 object in a `Lit` marker. The sort of the returned value must be
    /// the same as the sort of the argument.
    fn lit_wrap_dynamic(&self, arg: &Dynamic<'ctx>) -> Dynamic<'ctx>;
}

/// SMT values that can be wrapped in a `Lit` marker.
pub trait LitWrap<'ctx> {
    /// Wrap the value in a `Lit` marker (if enabled by the [LitFactory]).
    fn lit_wrap(&self, factory: &impl LitFactory<'ctx>) -> Self;
}

/// Any built-in Z3 [Ast] object that can be converted to/from [Dynamic] trivially implements [LitWrap]
impl<'ctx, A: Ast<'ctx>> LitWrap<'ctx> for A
where
    A: TryFrom<Dynamic<'ctx>> + Into<Dynamic<'ctx>> + Clone,
    <A as TryFrom<Dynamic<'ctx>>>::Error: Debug,
{
    fn lit_wrap(&self, factory: &impl LitFactory<'ctx>) -> Self {
        factory
            .lit_wrap_dynamic(&self.clone().into())
            .try_into()
            .unwrap()
    }
}
