use std::{cmp::Ordering, fmt};

use crate::pretty::{Doc, SimplePretty};

use super::{DeclRef, DomainDecl, Ident};

/// Defines the kinds of types.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum TyKind {
    /// The primitive boolean type `Bool`.
    Bool,
    /// A signed integer type.
    Int,
    /// A unsigned integer type.
    UInt,
    /// Real numbers.
    Real,
    /// Unsigned real numbers
    UReal,
    /// Unsigned real numbers with infinity.
    EUReal,
    /// A tuple type.
    Tuple(Vec<TyKind>),
    /// A list type.
    List(Box<TyKind>),
    /// A domain type.
    Domain(DeclRef<DomainDecl>),
    /// This is the current TyCtx's spec_ty
    SpecTy,
    /// A type defined somewhere which is not resolved yet.
    Unresolved(Ident),
    /// A placeholder or an error.
    None,
}

impl TyKind {
    /// For tuple types, return an iterator over the inner types.
    /// For all other types, the one-element iterator with `self` is returned.
    pub fn unpack(&self) -> impl Iterator<Item = &TyKind> {
        match self {
            TyKind::Tuple(tys) => tys.iter(),
            _ => std::slice::from_ref(self).iter(),
        }
    }

    /// Is this a complete lattice type that has a bottom and top type? This is
    /// satisfied by Bool and EUReal.
    pub fn is_complete_lattice(&self) -> bool {
        matches!(self, TyKind::Bool | TyKind::EUReal)
    }
}

// We have a custom [`fmt::Debug`] implementation so that printing domains does not explode
impl fmt::Debug for TyKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "Bool"),
            Self::Int => write!(f, "Int"),
            Self::UInt => write!(f, "UInt"),
            Self::Real => write!(f, "Real"),
            Self::UReal => write!(f, "UReal"),
            Self::EUReal => write!(f, "EUReal"),
            Self::Tuple(arg0) => f.debug_tuple("Tuple").field(arg0).finish(),
            Self::List(arg0) => f.debug_tuple("List").field(arg0).finish(),
            Self::Domain(arg0) => f.debug_tuple("Domain").field(&arg0.borrow().name).finish(),
            Self::SpecTy => write!(f, "<spec ty>"),
            Self::Unresolved(arg0) => f.debug_tuple("Unresolved").field(arg0).finish(),
            Self::None => write!(f, "None"),
        }
    }
}

impl fmt::Display for TyKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "Bool"),
            Self::Int => write!(f, "Int"),
            Self::UInt => write!(f, "UInt"),
            Self::Real => write!(f, "Real"),
            Self::UReal => write!(f, "UReal"),
            Self::EUReal => write!(f, "EUReal"),
            Self::Tuple(parts) => {
                write!(f, "(")?;
                if let [front @ .., last] = parts.as_slice() {
                    for part in front.iter() {
                        write!(f, "{}, ", part)?;
                    }
                    write!(f, "{}", last)?;
                }
                write!(f, ")")
            }
            Self::List(element_ty) => write!(f, "[]{}", element_ty),
            Self::Domain(arg0) => write!(f, "{}", &arg0.borrow().name),
            Self::SpecTy => write!(f, "<spec ty>"),
            Self::Unresolved(name) => write!(f, "{}", name),
            Self::None => write!(f, "<none>"),
        }
    }
}

impl SimplePretty for TyKind {
    fn pretty(&self) -> Doc {
        Doc::as_string(self)
    }
}

impl PartialOrd for TyKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        fn less(lhs: &TyKind, rhs: &TyKind) -> bool {
            matches!(
                (lhs, rhs),
                (TyKind::UInt, TyKind::UReal)
                    | (TyKind::UInt, TyKind::EUReal)
                    | (TyKind::UInt, TyKind::Int)
                    | (TyKind::UInt, TyKind::Real)
                    | (TyKind::Int, TyKind::Real)
                    | (TyKind::UReal, TyKind::Real)
                    | (TyKind::UReal, TyKind::EUReal)
            )
        }

        if self == other {
            Some(Ordering::Equal)
        } else if less(self, other) {
            Some(Ordering::Less)
        } else if less(other, self) {
            Some(Ordering::Greater)
        } else {
            None
        }
    }
}
