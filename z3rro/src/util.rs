use std::{
    fmt::{Display, Formatter},
    io::Write,
    str::FromStr,
};

use num::BigRational;
use z3::{ast::Real, Context};

/// Build a conjunction of Boolean expressions.
macro_rules! z3_and {
    ($first:expr, $( $x:expr, )*) => {
        {
            use z3::ast::{Ast, Bool};
            let first = $first;
            Bool::and(first.get_ctx(),  &[first, $($x,)*])
        }
    };
    ($( $x:expr ),*) => { z3_and!($($x,)*) }
}

/// Build a disjunction of Boolean expressions.
#[allow(unused_imports)]
macro_rules! z3_or {
    ($first:expr, $( $x:expr, )*) => {
        {
            use z3::ast::{Ast, Bool};
            let first = $first;
            Bool::or(first.get_ctx(),  &[first, $($x,)*])
        }
    };
    ($( $x:expr ),*) => { z3_or!($($x,)*) }
}

// this function is present in the z3 crate, but they use an ancient version of `num`.
pub fn real_from_big_rational<'ctx>(ctx: &'ctx Context, value: &BigRational) -> Real<'ctx> {
    let num = value.numer();
    let den = value.denom();
    Real::from_real_str(ctx, &num.to_str_radix(10), &den.to_str_radix(10)).unwrap()
}

/// Create forwarding trait implementations for a binary operator that use an
/// existing trait implementation on reference types, providing implementation
/// on value types (and value types with references).
///
/// E.g. if there's a trait implementation for `&a + &b`, then this macro will
/// create implementations for `a + b`, `&a + b`, and `a + &b`.
///
/// The macro parameters are as follows. `forward_binary_op!(self_ty, rhs_ty, output,
/// op_trait, base_fn, function)` are:
///
///   - `self_ty`: the `self` type,
///   - `rhs_ty`: the right-hand side operand type,
///   - `output_ty`: the output type,
///   - `op_trait`: the name of the operand trait (e.g. `Add`),
///   - `op_fn`: the name of the trait method to implement (e.g. `add`),
///   - `base_fn`: the name of the function to call (e.g. `add` again).
#[macro_export]
macro_rules! forward_binary_op {
    ($self_ty:ty, $rhs_ty:ty, $output_ty:ty, $op_trait:ident, $op_fn:ident, $base_fn:ident) => {
        impl<'ctx> $op_trait<$rhs_ty> for $self_ty {
            type Output = $output_ty;

            fn $op_fn(self, rhs: $rhs_ty) -> Self::Output {
                (&self).$base_fn(&rhs)
            }
        }

        impl<'ctx, 'a> $op_trait<$rhs_ty> for &'a $self_ty {
            type Output = $output_ty;

            fn $op_fn(self, rhs: $rhs_ty) -> Self::Output {
                self.$base_fn(&rhs)
            }
        }

        impl<'ctx, 'a> $op_trait<&'a $rhs_ty> for $self_ty {
            type Output = $output_ty;

            fn $op_fn(self, rhs: &'a $rhs_ty) -> Self::Output {
                (&self).$base_fn(rhs)
            }
        }
    };
}

/// Wrap the writer and write a prefix at the start of each line. Lines are
/// separated by '\n'.
#[derive(Debug)]
pub struct PrefixWriter<'a, W> {
    prefix: &'a [u8],
    line_start: bool,
    writer: W,
}

impl<'a, W> PrefixWriter<'a, W> {
    pub fn new(prefix: &'a [u8], writer: W) -> Self {
        PrefixWriter {
            prefix,
            line_start: true,
            writer,
        }
    }
}

impl<'a, W: Write> Write for PrefixWriter<'a, W> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        for line in buf.split_inclusive(|c| *c == b'\n') {
            if self.line_start {
                self.writer.write_all(self.prefix)?;
            }
            self.writer.write_all(line)?;
            self.line_start = line.ends_with(&[b'\n']);
        }
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.writer.flush()
    }
}

/// A type to represent the `:reason-unknown` values from Z3.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReasonUnknown {
    Interrupted,
    Other(String),
}

impl FromStr for ReasonUnknown {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "interrupted from keyboard" => Ok(ReasonUnknown::Interrupted),
            other => Ok(ReasonUnknown::Other(other.to_owned())),
        }
    }
}

impl Display for ReasonUnknown {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ReasonUnknown::Interrupted => f.write_str("interrupted from keyboard"),
            ReasonUnknown::Other(reason) => f.write_str(reason),
        }
    }
}

#[cfg(test)]
mod test {
    use super::ReasonUnknown;

    #[test]
    fn test_reason_unknown_parse_fmt() {
        let values = [
            ReasonUnknown::Interrupted,
            ReasonUnknown::Other("x".to_owned()),
        ];
        for value in &values {
            let parsed_fmt = format!("{}", value).parse::<ReasonUnknown>().unwrap();
            assert_eq!(value, &parsed_fmt);
        }
    }
}
