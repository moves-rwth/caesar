use std::{borrow::Cow, fmt::Write, rc::Rc};

use z3::{
    ast::{quantifier_const, Ast, Bool, Dynamic},
    Pattern,
};

/// Weights for quantifiers.
///
/// The weights are used to prioritize quantifier instantiation in the SMT solver.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
#[repr(transparent)]
pub struct Weight(pub u32);

impl Weight {
    /// Default weight for quantifiers.
    pub const DEFAULT: Weight = Weight(1);
}

impl Default for Weight {
    fn default() -> Self {
        Self::DEFAULT
    }
}

/// Metadata to create quantifiers.
#[derive(Debug, Clone)]
pub struct QuantifierMeta<'ctx> {
    /// A user-given name for the quantifier.
    pub user_name: String,
    /// Whether to use the MBQI prefix (to enable MBQI with Z3's `smt.mbqi.id`
    /// option).
    pub mbqi: bool,
    /// A suffix for a variant (e.g. for one of the two axioms for the supremum
    /// encoding).
    pub variant: Option<Cow<'static, str>>,
    /// The weight of the quantifier.
    pub weight: Weight,
    /// Patterns for the quantifier. Wrapped in an `Rc` because `Pattern` is not
    /// `Clone`.
    pub patterns: Vec<Rc<Pattern<'ctx>>>,
    /// Subexpressions to be excluded from inferred patterns.
    pub no_patterns: Vec<Dynamic<'ctx>>,
}

impl<'ctx> QuantifierMeta<'ctx> {
    /// The prefix for the quantifier ID when MBQI should be enabled.
    pub const MBQI_PREFIX: &'static str = "mbqi_";

    /// Create a new quantifier metadata with the given user name.
    pub fn new(user_name: impl Into<String>) -> Self {
        Self {
            user_name: user_name.into(),
            mbqi: false,
            variant: None,
            weight: Weight::DEFAULT,
            patterns: Vec::new(),
            no_patterns: Vec::new(),
        }
    }

    /// Generate the quantifier ID based on the metadata.
    pub fn qid(&self) -> String {
        let mut qid = String::new();
        if self.mbqi {
            qid.push_str(Self::MBQI_PREFIX);
        }
        qid.push_str(&self.user_name);
        if let Some(ref variant) = self.variant {
            writeln!(&mut qid, "_{variant}").unwrap();
        }
        qid
    }

    /// Wrap the patterns in an `Rc`.
    pub fn set_patterns(&mut self, patterns: Vec<Pattern<'ctx>>) {
        self.patterns = patterns.into_iter().map(Rc::new).collect();
    }

    pub fn variant(&self, variant: Cow<'static, str>) -> Self {
        Self {
            variant: Some(variant),
            ..self.clone()
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantifierType {
    Forall,
    Exists,
}

/// Create a quantifier with the given metadata, bounds, and body.
pub fn mk_quantifier<'ctx>(
    meta: &QuantifierMeta<'ctx>,
    typ: QuantifierType,
    bounds: &[&dyn Ast<'ctx>],
    body: &Bool<'ctx>,
) -> Bool<'ctx> {
    let ctx = body.get_ctx();
    let is_forall = typ == QuantifierType::Forall;
    let weight = meta.weight.0;
    let quantifier_id = meta.qid();
    let skolem_id = ""; // TODO
    let patterns = meta.patterns.iter().map(|p| p.as_ref()).collect::<Vec<_>>();
    let no_patterns = meta
        .no_patterns
        .iter()
        .map(|p| p as &dyn Ast)
        .collect::<Vec<_>>();
    quantifier_const(
        ctx,
        is_forall,
        weight,
        quantifier_id,
        skolem_id,
        bounds,
        &patterns,
        &no_patterns,
        body,
    )
}
