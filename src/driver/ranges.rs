use std::rc::Rc;

use indexmap::IndexMap;
use num::BigRational;

use crate::ast::{BinOpKind, DeclKind, Expr, ExprBuilder, Ident, Range, Span, TyKind};

/// Builds a Boolean expression `range.lower <= ident <= range.upper` in type `ty`.
pub fn create_range_constraint(ident: Ident, range: &Range, ty: TyKind) -> Expr {
    let builder = ExprBuilder::new(Span::dummy_span());

    let (var, lower_lit, upper_lit) = match ty {
        TyKind::UReal => {
            let var = builder.var_ty(ident, TyKind::UReal);
            let lower =
                builder.frac_lit_not_extended(BigRational::from_integer(range.lower.into()));
            let upper =
                builder.frac_lit_not_extended(BigRational::from_integer(range.upper.into()));
            (var, lower, upper)
        }
        _ => {
            let var = builder.var_ty(ident, TyKind::UInt);
            let lower = builder.uint(range.lower.into());
            let upper = builder.uint(range.upper.into());
            (var, lower, upper)
        }
    };

    let lower = builder.binary(BinOpKind::Le, Some(TyKind::Bool), lower_lit, var.clone());

    let upper = builder.binary(BinOpKind::Le, Some(TyKind::Bool), var, upper_lit);

    builder.binary(BinOpKind::And, Some(TyKind::Bool), lower, upper)
}

/// Returns a map from variable identifiers to their declared `(Range, TyKind)` pairs.
pub fn collect_ranges_from_decls(
    declarations: &IndexMap<Ident, Rc<DeclKind>>,
) -> IndexMap<Ident, (Range, TyKind)> {
    let mut ranges = IndexMap::new();

    for (ident, decl) in declarations.iter() {
        if let DeclKind::VarDecl(var_ref) = decl.as_ref() {
            let var = var_ref.borrow();
            if let Some(range) = &var.range {
                ranges.insert(*ident, (*range, var.ty.clone()));
            }
        }
    }

    ranges
}
