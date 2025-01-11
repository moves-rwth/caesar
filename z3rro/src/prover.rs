//! Not a SAT solver, but a prover. There's a difference.

use std::collections::HashMap;
use std::{fmt::Display, time::Duration};
use z3::{
    ast::{forall_const, Ast, Bool, Dynamic},
    Context, Model, Params, SatResult, Solver, Symbol,
};

use crate::{model::InstrumentedModel, smtlib::Smtlib, util::ReasonUnknown};

/// The result of a prove query.
#[derive(Debug)]
pub enum ProveResult<'ctx> {
    Proof,
    Counterexample(InstrumentedModel<'ctx>),
    Unknown(ReasonUnknown),
}

impl Display for ProveResult<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProveResult::Proof => f.write_str("Proof"),
            ProveResult::Counterexample(_) => f.write_str("Counterexample"),
            ProveResult::Unknown(reason) => {
                f.write_fmt(format_args!("Unknown (reason: {})", reason))
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParamValue {
    Bool(bool),
    Symbol(Symbol),
    U32(u32),
    F64(f64),
}

impl ParamValue {
    fn set_to_params(&self, k: impl Into<Symbol>, params: &mut Params) {
        match self {
            ParamValue::Bool(b) => params.set_bool(k, *b),
            ParamValue::Symbol(s) => params.set_symbol(k, s.clone()),
            ParamValue::U32(u) => params.set_u32(k, *u),
            ParamValue::F64(f) => params.set_f64(k, *f),
        }
    }
}

impl From<bool> for ParamValue {
    fn from(v: bool) -> Self {
        ParamValue::Bool(v)
    }
}

impl From<u32> for ParamValue {
    fn from(v: u32) -> Self {
        ParamValue::U32(v)
    }
}

impl From<f64> for ParamValue {
    fn from(v: f64) -> Self {
        ParamValue::F64(v)
    }
}

impl From<Symbol> for ParamValue {
    fn from(v: Symbol) -> Self {
        ParamValue::Symbol(v)
    }
}

fn to_params<'ctx>(ctx: &'ctx Context, param_map: &HashMap<String, ParamValue>) -> Params<'ctx> {
    let mut parms = Params::new(ctx);
    for (k, v) in param_map.iter() {
        v.set_to_params(&**k, &mut parms);
    }
    parms
}

/// A prover wraps a SAT solver, but it's used to prove validity of formulas.
/// It's a bit of a more explicit API to distinguish between assumptions for a
/// proof ([`Prover::add_assumption`]) and provables ([`Prover::add_provable`]).
///
/// It keeps track of whether there are any assertions added to the solver. If
/// there are none, then [`Prover::check_proof`] will return
/// [`ProveResult::Proof`] (instead of [`SatResult::Sat`], i.e.
/// [`ProveResult::Counterexample`]). Therefore, you shouldn't add assertions
/// via [`Prover::solver`] to not mess that tracking up.
///
/// In contrast to [`z3::Solver`], the [`Prover`] requires exclusive ownership
/// to do any modifications of the solver.
#[derive(Debug)]
pub struct Prover<'ctx> {
    /// The underlying solver.
    solver: Solver<'ctx>,
    /// We are tracking the params ourselves
    params: HashMap<String, ParamValue>,
    /// Number of times push was called minus number of times pop was called.
    level: usize,
    /// The minimum level where an assertion was added to the solver.
    min_level_with_provables: Option<usize>,
}

impl<'ctx> Clone for Prover<'ctx> {
    fn clone(&self) -> Self {
        println!("cloning prover");
        let solver = self.solver.clone();
        // Solver::clone does not copy the params.
        // Therefore, we track them separately and copy them here.
        solver.set_params(&to_params(solver.get_context(), &self.params));

        Prover {
            solver,
            params: self.params.clone(),
            level: self.level,
            min_level_with_provables: self.min_level_with_provables,
        }
    }
}

impl<'ctx> Prover<'ctx> {
    /// Create a new prover with the given [`Context`].
    pub fn new(ctx: &'ctx Context) -> Self {
        let mut prover = Prover {
            solver: Solver::new(ctx),
            params: HashMap::default(),
            level: 0,
            min_level_with_provables: None,
        };
        // default params
        prover.set_param("smt.qi.eager_threshold", 100.0);
        prover.set_param("smt.qi.lazy_threshold", 1000.0);
        prover.set_param("auto-config", false);
        prover
    }

    /// Set a solver timeout with millisecond precision.
    ///
    /// Panics if the duration is not representable as a 32-bit unsigned integer.
    pub fn set_timeout(&mut self, duration: Duration) {
        self.set_param(
            "timeout",
            ParamValue::U32(duration.as_millis().try_into().unwrap()),
        );
    }

    pub fn enforce_ematching(&mut self) {
        self.set_param("smt.mbqi", false);
    }

    pub fn seed(&mut self, seed: u32) {
        self.set_param("smt.random_seed", seed);
    }

    pub fn set_param(&mut self, k: impl Into<String>, v: impl Into<ParamValue>) {
        let key = k.into();
        println!("set_param {}", key);
        let value = v.into();
        let mut params = Params::new(self.solver.get_context());
        value.set_to_params(&*key, &mut params);
        self.params.insert(key, value);
        self.solver.set_params(&params);
    }

    /// Add an assumption to this prover.
    pub fn add_assumption(&mut self, value: &Bool<'ctx>) {
        self.solver.assert(value);
    }

    /// Add a proof obligation to this prover. It adds the negated formula to
    /// the underlying SAT solver's assertions.
    ///
    /// We call it `provable` to avoid confusion between the Z3 solver's
    /// `assert` methods.
    pub fn add_provable(&mut self, value: &Bool<'ctx>) {
        self.solver.assert(&value.not());
        self.min_level_with_provables.get_or_insert(self.level);
    }

    pub fn check_proof(&mut self) -> ProveResult<'ctx> {
        self.check_proof_assuming(&[])
    }

    /// Do the SAT check, but consider a check with no provables to be a
    /// [`ProveResult::Proof`].
    pub fn check_proof_assuming(&mut self, assumptions: &[Bool<'ctx>]) -> ProveResult<'ctx> {
        if self.min_level_with_provables.is_none() {
            return ProveResult::Proof;
        }
        let res = if assumptions.is_empty() {
            self.solver.check()
        } else {
            self.solver.check_assumptions(assumptions)
        };
        match res {
            SatResult::Unsat => ProveResult::Proof,
            SatResult::Unknown => ProveResult::Unknown(self.get_reason_unknown().unwrap()),
            SatResult::Sat => {
                let model = self.get_model().unwrap();
                let model = InstrumentedModel::new(model);
                ProveResult::Counterexample(model)
            }
        }
    }

    /// Do the regular SAT check.
    pub fn check_sat(&mut self) -> SatResult {
        self.solver().check()
    }

    /// Retrieve the model from the solver.
    pub fn get_model(&self) -> Option<Model<'ctx>> {
        self.solver.get_model()
    }

    /// Retrieve the UNSAT core. See [`Solver::get_unsat_core()`].
    pub fn get_unsat_core(&self) -> Vec<Bool<'ctx>> {
        self.solver.get_unsat_core()
    }

    /// See [`Solver::get_reason_unknown`].
    pub fn get_reason_unknown(&self) -> Option<ReasonUnknown> {
        self.solver
            .get_reason_unknown()
            .map(|reason| reason.parse().unwrap())
    }

    /// See [`Solver::push`].
    pub fn push(&mut self) {
        self.solver.push();
        self.level += 1;
    }

    /// See [`Solver::pop`].
    pub fn pop(&mut self) {
        println!("solver pop");
        self.solver.pop(1);
        self.level = self.level.checked_sub(1).expect("cannot pop level 0");
        if let Some(prev_min_level) = self.min_level_with_provables {
            // if there are no assertions at this level, remove the counter
            if prev_min_level > self.level {
                self.min_level_with_provables.take();
            }
        }
    }

    /// Retrieve the current stack level. Useful for debug assertions.
    pub fn level(&self) -> usize {
        self.level
    }

    /// Return a reference to the underlying solver. Please do not modifiy it!
    pub fn solver(&self) -> &Solver<'ctx> {
        &self.solver
    }

    /// Turns this prover into a regular [`Solver`].
    pub fn into_solver(self) -> Solver<'ctx> {
        self.solver
    }

    /// Create an exists-forall solver. All constants provided in the iterator
    /// will be universally quantified. The rest will be existentially
    /// quantified.
    ///
    /// The result is a [`Prover`] for convenience (such as using the
    /// [`Self::level()`] function), but it should be used as a [`Solver`] via
    /// [`Self::check_sat()`].
    pub fn to_exists_forall(&self, universal: &[Dynamic<'ctx>]) -> Prover<'ctx> {
        // TODO: what about the params?
        let ctx = self.solver.get_context();
        let universal: Vec<&dyn Ast<'ctx>> =
            universal.iter().map(|v| v as &dyn Ast<'ctx>).collect();
        let assertions = self.solver.get_assertions();
        let theorem = forall_const(ctx, &universal, &[], &Bool::and(ctx, &assertions).not());
        let mut res = Prover::new(ctx);
        res.add_assumption(&theorem);
        res
    }

    /// Return the SMT-LIB that represents the solver state.
    pub fn get_smtlib(&self) -> Smtlib {
        Smtlib::from_solver(&self.solver)
    }
}

#[cfg(test)]
mod test {
    use super::{ProveResult, Prover};
    use crate::scope::{SmtFresh, SmtScope};
    use crate::{Fuel, FuelFactory, SmtBranch, SmtEq};
    use z3::ast::{forall_const, Ast, Int};
    use z3::{ast::Bool, Config, Context, FuncDecl, Params, Pattern, SatResult, Solver, Sort};

    #[test]
    fn test_prover() {
        let ctx = Context::new(&Config::default());
        let mut prover = Prover::new(&ctx);
        assert!(matches!(prover.check_proof(), ProveResult::Proof));
        assert_eq!(prover.check_sat(), SatResult::Sat);

        prover.push();
        prover.add_assumption(&Bool::from_bool(&ctx, true));
        assert!(matches!(prover.check_proof(), ProveResult::Proof));
        assert_eq!(prover.check_sat(), SatResult::Sat);
        prover.pop();

        assert!(matches!(prover.check_proof(), ProveResult::Proof));
        assert_eq!(prover.check_sat(), SatResult::Sat);
    }

    // Tests that disabling mbqi works. For that we use a limited version of the faculty function
    // (fac) and try to prove that fac(n) != 0. This is not for the smt solver.
    // - MBQI active -> the solver creates new terms and hangs.
    // - MBQI disabled -> The solver options are quickly exhausted, and it returns Unknown.
    #[test]
    fn enforce_ematching() {
        fn fac<'ctx>(decl: &FuncDecl<'ctx>, fuel: &Fuel<'ctx>, n: &Int<'ctx>) -> Int<'ctx> {
            decl.apply(&[&fuel.as_dynamic() as &dyn Ast, n as &dyn Ast])
                .as_int()
                .unwrap()
                .clone()
        }

        let mut config = Config::new();
        // config.set_bool_param_value("proof", true);
        // config.set_bool_param_value("trace", true);
        let ctx = Context::new(&config);

        let mut solver = Solver::new(&ctx);

        let mut scope = SmtScope::new();
        let fuel_factory = FuelFactory::new(&ctx);

        let int = Sort::int(&ctx);
        let zero = Int::from_i64(&ctx, 0);
        let one = Int::from_i64(&ctx, 1);
        let two = Int::from_i64(&ctx, 2);
        let fuel1 = Fuel::new(fuel_factory.clone(), 1);
        let fac_decl = FuncDecl::new(&ctx, "fac", &[fuel_factory.sort(), &int], &int);

        let fuel = Fuel::fresh(&fuel_factory, &mut scope, "fuel");
        let n = Int::fresh(&&ctx, &mut scope, "n");
        let app = fac(&fac_decl, &Fuel::succ(fuel.clone()), &n);

        // forall fuel: Fuel, n: Int @trigger(fac(S(fuel), n)). fac(S(fuel), n) == ite(n < 2, 1, n * fac(fuel, n-1))
        solver.assert(&forall_const(
            &ctx,
            &[&fuel.as_dynamic() as &dyn Ast, &n as &dyn Ast],
            &[&Pattern::new(&ctx, &[&app as &dyn Ast])],
            &app.smt_eq(&Int::branch(
                &n.lt(&two),
                &one,
                &(&n * fac(&fac_decl, &fuel, &(&n - 1i64))),
            )),
        ));
        // forall fuel: Fuel, n: Int @trigger(fac(S(fuel), n)). fac(S(fuel), n) == fac(fuel, n)
        solver.assert(&forall_const(
            &ctx,
            &[&fuel.as_dynamic() as &dyn Ast, &n as &dyn Ast],
            &[&Pattern::new(&ctx, &[&app as &dyn Ast])],
            &app.smt_eq(&fac(&fac_decl, &fuel, &n)),
        ));
        let n2 = Int::fresh(&&ctx, &mut scope, "n2");
        // fac(n2) != 0
        solver.assert(&fac(&fac_decl, &fuel1, &n2).smt_eq(&zero).not().not());

        // disabling mbqi
        let mut params = Params::new(&ctx);
        params.set_bool("smt.mbqi", false);
        params.set_bool("auto-config", false);
        solver.set_params(&params);

        // Uncommenting will make the test succeed
        // solver.push();
        // solver.pop(1);

        assert_eq!(solver.check(), SatResult::Unknown);
    }
}
