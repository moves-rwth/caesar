use std::{
    collections::BTreeMap,
    fmt::{self, Display},
};

use num::BigInt;
use z3::{
    ast::{Array, Ast, Dynamic},
    DeclKind,
};

use crate::{
    list::ConcreteList,
    model::{InstrumentedModel, SmtEval, SmtEvalError},
    util::parse_big_int,
};

/// A concrete representation of a Z3 array with integer indices and any value type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConcreteArrayValue {
    pub default: String,
    pub stores: BTreeMap<BigInt, String>,
}

impl ConcreteArrayValue {
    pub fn from_dynamic(value: &Dynamic<'_>) -> Option<Self> {
        match value.safe_decl().ok()?.kind() {
            DeclKind::STORE => {
                let base = Self::from_dynamic(&value.nth_child(0)?)?;
                let index = parse_big_int(&value.nth_child(1)?.as_int()?)?;
                let entry = dynamic_to_string(&value.nth_child(2)?);
                let mut stores = base.stores;
                stores.insert(index, entry);
                Some(Self {
                    default: base.default,
                    stores,
                })
            }
            DeclKind::CONST_ARRAY => Some(Self {
                default: dynamic_to_string(&value.nth_child(0)?),
                stores: BTreeMap::new(),
            }),
            _ => None,
        }
    }
}

impl Display for ConcreteArrayValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "const({})", self.default)?;
        if !self.stores.is_empty() {
            write!(f, " [")?;
            for (index, (key, value)) in self.stores.iter().enumerate() {
                if index > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{key} -> {value}")?;
            }
            write!(f, "]")?;
        }
        Ok(())
    }
}

impl<'ctx> SmtEval<'ctx> for Array<'ctx> {
    type Value = ConcreteArrayValue;

    fn eval(&self, model: &InstrumentedModel<'ctx>) -> Result<Self::Value, SmtEvalError> {
        let value = model.eval_ast(self, true).ok_or(SmtEvalError::EvalError)?;
        let value = Dynamic::from_ast(&value);
        ConcreteArrayValue::from_dynamic(&value).ok_or(SmtEvalError::ParseError)
    }
}

fn dynamic_to_string(value: &Dynamic<'_>) -> String {
    ConcreteList::from_dynamic(value)
        .map(|value| value.to_string())
        .unwrap_or_else(|_| {
            ConcreteArrayValue::from_dynamic(value)
                .map(|value| value.to_string())
                .unwrap_or_else(|| format!("{value}"))
        })
}

#[cfg(test)]
mod tests {
    use z3::{
        ast::{Array, Int},
        Config, Context, SatResult, Solver, Sort,
    };

    use crate::model::{InstrumentedModel, ModelConsistency, SmtEval};

    #[test]
    fn concrete_array_eval_shows_store_chain() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);
        assert_eq!(solver.check(), SatResult::Sat);

        let array = Array::const_array(&ctx, &Sort::int(&ctx), &Int::from_i64(&ctx, 4))
            .store(&Int::from_i64(&ctx, 1), &Int::from_i64(&ctx, 10))
            .store(&Int::from_i64(&ctx, -1), &Int::from_i64(&ctx, 12));
        let model =
            InstrumentedModel::new(ModelConsistency::Consistent, solver.get_model().unwrap());

        assert_eq!(
            array.eval(&model).unwrap().to_string(),
            "const(4) [-1 -> 12, 1 -> 10]"
        );
    }
}
