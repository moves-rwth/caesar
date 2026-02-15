use std::{convert::TryFrom, str::FromStr};

use num::{rational::Ratio, BigInt, BigRational};

use crate::ast::{FileId, Span, SpanVariant, Spanned};

pub fn span(file: FileId, start: usize, end: usize) -> Span {
    Span::new(file, start, end, SpanVariant::Parser)
}

pub fn spanned<T>(file: FileId, start: usize, end: usize, value: T) -> Spanned<T> {
    Spanned::new(span(file, start, end), value)
}

#[derive(Debug, PartialEq, Eq)]
pub struct DecimalParseError;

/// Parse a decimal string and return a `BigRational` that represents it.
pub fn parse_decimal(num: &str) -> Result<BigRational, DecimalParseError> {
    if let Some(pos) = num.find('.') {
        let (integer, comma) = num.split_at(pos);
        let comma = &comma[1..]; // remove the dot
        let comma_len = u32::try_from(comma.len()).map_err(|_| DecimalParseError)?;

        // Handle optional sign
        let (sign, integer_digits) = if let Some(stripped) = integer.strip_prefix('-') {
            (-1, stripped)
        } else if let Some(stripped) = integer.strip_prefix('+') {
            (1, stripped)
        } else {
            (1, integer)
        };

        let numer: BigInt =
            BigInt::from_str(&format!("{integer_digits}{comma}"))
                .map_err(|_| DecimalParseError)?
                * sign;

        let denom: BigInt = BigInt::from(10).pow(comma_len);
        Ok(Ratio::new_raw(numer, denom))
    } else {
        Err(DecimalParseError)
    }
}


#[cfg(test)]
mod test {
    use num::BigRational;

    use super::parse_decimal;

    #[test]
    fn test_parse_decimal() {
        assert_eq!(
            parse_decimal("1.0"),
            Ok(BigRational::new(1.into(), 1.into()))
        );
        assert_eq!(
            parse_decimal("0.5"),
            Ok(BigRational::new(1.into(), 2.into()))
        );
        assert_eq!(
            parse_decimal("0.9999999"),
            Ok(BigRational::new(9999999.into(), 10000000.into()))
        );
    }
}
