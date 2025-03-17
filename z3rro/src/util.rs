use std::{
    borrow::Cow,
    collections::HashMap,
    fmt::{Display, Formatter, Write},
    str::FromStr,
    time::Duration,
};

use num::{BigInt, BigRational, Integer, Signed, Zero};

use z3::{Params, Solver};

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

impl<W: std::io::Write> std::io::Write for PrefixWriter<'_, W> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        for line in buf.split_inclusive(|c| *c == b'\n') {
            if self.line_start {
                self.writer.write_all(self.prefix)?;
            }
            self.writer.write_all(line)?;
            self.line_start = line.ends_with(b"\n");
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
    Timeout,
    Other(String),
}

impl FromStr for ReasonUnknown {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "interrupted from keyboard" | "canceled" => Ok(ReasonUnknown::Interrupted),
            "timeout" => Ok(ReasonUnknown::Timeout),
            other => Ok(ReasonUnknown::Other(other.to_owned())),
        }
    }
}

impl Display for ReasonUnknown {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ReasonUnknown::Interrupted => f.write_str("interrupted from keyboard"),
            ReasonUnknown::Timeout => f.write_str("timeout"),
            ReasonUnknown::Other(reason) => f.write_str(reason),
        }
    }
}

/// Set a solver timeout with millisecond precision.
///
/// Panics if the duration is not representable as a 32-bit unsigned integer.
pub fn set_solver_timeout(solver: &Solver, duration: Duration) {
    let mut params = Params::new(solver.get_context());
    params.set_u32("timeout", duration.as_millis().try_into().unwrap());
    solver.set_params(&params);
}

/// Pretty-printing wrapper type for [`BigRational`] values. This type's
/// [`Display`] instance will format this value exactly as a decimal. If the
/// rational is not a terminating fraction, the repeating fraction will be
/// displayed alongside the original fraction.
#[derive(Debug)]
pub struct PrettyRational<'a>(pub Cow<'a, BigRational>);

impl PrettyRational<'_> {
    const DECIMAL_EXPANSION_LIMIT: usize = 5;
}

impl From<BigRational> for PrettyRational<'_> {
    fn from(value: BigRational) -> Self {
        PrettyRational(Cow::Owned(value))
    }
}

impl Display for PrettyRational<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.0.is_negative() {
            write!(f, "-")?;
        }
        let abs = self.0.abs();
        let (div, mut rem) = abs.numer().div_rem(abs.denom());
        write!(f, "{}", div)?;

        let mut frac = String::new();
        let mut map = HashMap::new();
        let ten = &BigInt::from(10);
        let mut approx = false;
        loop {
            if rem.is_zero() || map.contains_key(&rem) {
                break;
            }
            if map.len() >= Self::DECIMAL_EXPANSION_LIMIT {
                approx = true;
                break;
            }
            map.insert(rem.clone(), frac.len());
            let (div, new_rem) = (rem * ten).div_rem(abs.denom());
            write!(&mut frac, "{}", div)?;
            rem = new_rem;
        }

        if frac.is_empty() {
            return Ok(());
        }

        if rem.is_zero() || approx {
            // print a finite rational
            write!(f, ".{}", frac)?;
            if approx {
                write!(f, "...")?;
            }
        } else {
            // print a repeating decimal
            write!(f, ".{}", &frac[..map[&rem]])?;
            for ch in frac[map[&rem]..].chars() {
                // combine with COMBINING OVERLINE unicode
                write!(f, "{}\u{0305}", ch)?;
            }
        }

        // write the original fraction in parentheses if we couldn't get a
        // terminating decimal
        if !rem.is_zero() || approx {
            write!(f, " ({})", self.0)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::{borrow::Cow, str::FromStr};

    use num::BigRational;

    use crate::util::PrettyRational;

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

    #[test]
    fn test_pretty_rational() {
        let test_cases = [
            // simplify integers
            ("0/1", "0"),
            ("2/1", "2"),
            // simplify common fraction
            ("1/3", "0.3\u{305} (1/3)"),
            // this fraction has a huge decimal expansion
            (
                "241765600173973671370/376619014637248564543",
                "0.64193... (241765600173973671370/376619014637248564543)",
            ),
        ];
        for (rational, res) in test_cases {
            let rational = BigRational::from_str(rational).unwrap();
            let formatted = format!("{}", PrettyRational(Cow::Owned(rational)));
            assert_eq!(formatted, res);
        }
    }
}
