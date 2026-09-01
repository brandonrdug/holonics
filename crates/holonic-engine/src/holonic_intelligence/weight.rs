use num_bigint::BigInt;
use relational_geometry::Rat;
use thiserror::Error;

use crate::foreign_map::ForeignDtype;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactLowPrecisionValue {
    Finite(Rat),
    PositiveInfinity,
    NegativeInfinity,
    NotANumber,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactLowPrecisionDatum {
    pub dtype: ForeignDtype,
    pub codeword: u8,
    pub value: ExactLowPrecisionValue,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LowPrecisionPreimageFibre {
    WitnessedSource { source: Rat, residual: Rat },
    OpenQuantizationLaw,
    NonFiniteCodeword,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactLowPrecisionPassage {
    pub datum: ExactLowPrecisionDatum,
    pub preimage: LowPrecisionPreimageFibre,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ExactLowPrecisionError {
    #[error("dtype {0} is not an admitted low-precision codeword species")]
    Unsupported(String),
    #[error("{dtype} codeword {codeword:#04x} carries bits above its declared width")]
    CodewordOverflow { dtype: String, codeword: u8 },
    #[error("{dtype} payload holds {available} bits for {elements} declared elements")]
    TruncatedPayload {
        dtype: String,
        available: usize,
        elements: usize,
    },
}

pub fn decode_low_precision(
    dtype: &ForeignDtype,
    codeword: u8,
) -> Result<ExactLowPrecisionDatum, ExactLowPrecisionError> {
    let value = match dtype {
        ForeignDtype::F4 => finite_minifloat(codeword, 4, 2, 1, 1)?,
        ForeignDtype::F6E2M3 => finite_minifloat(codeword, 6, 2, 3, 1)?,
        ForeignDtype::F6E3M2 => finite_minifloat(codeword, 6, 3, 2, 3)?,
        ForeignDtype::F8E4M3 => decode_e4m3(codeword),
        ForeignDtype::F8E5M2 => decode_e5m2(codeword),
        ForeignDtype::F8E8M0 => {
            if codeword == u8::MAX {
                ExactLowPrecisionValue::NotANumber
            } else {
                ExactLowPrecisionValue::Finite(power_of_two(i32::from(codeword) - 127))
            }
        }
        ForeignDtype::I4 => {
            require_width(dtype, codeword, 4)?;
            let value = if codeword & 0x8 == 0 {
                i8::try_from(codeword).expect("four bits fit i8")
            } else {
                i8::try_from(codeword).expect("four bits fit i8") - 16
            };
            ExactLowPrecisionValue::Finite(Rat::from_integer(BigInt::from(value)))
        }
        ForeignDtype::U4 => {
            require_width(dtype, codeword, 4)?;
            ExactLowPrecisionValue::Finite(Rat::from_integer(BigInt::from(codeword)))
        }
        ForeignDtype::I2 => {
            require_width(dtype, codeword, 2)?;
            let value = if codeword & 0x2 == 0 {
                i8::try_from(codeword).expect("two bits fit i8")
            } else {
                i8::try_from(codeword).expect("two bits fit i8") - 4
            };
            ExactLowPrecisionValue::Finite(Rat::from_integer(BigInt::from(value)))
        }
        ForeignDtype::U2 => {
            require_width(dtype, codeword, 2)?;
            ExactLowPrecisionValue::Finite(Rat::from_integer(BigInt::from(codeword)))
        }
        other => {
            return Err(ExactLowPrecisionError::Unsupported(
                other.declared().to_owned(),
            ))
        }
    };
    Ok(ExactLowPrecisionDatum {
        dtype: dtype.clone(),
        codeword,
        value,
    })
}

/// Admit one stored codeword with an exact richer-source residual when supplied.
///
/// When the departed source and quantization law are unavailable, the preimage remains explicitly
/// open. The stored dyadic value is still exact; it is not promoted to a unique source value.
pub fn admit_low_precision(
    dtype: &ForeignDtype,
    codeword: u8,
    source: Option<Rat>,
) -> Result<ExactLowPrecisionPassage, ExactLowPrecisionError> {
    let datum = decode_low_precision(dtype, codeword)?;
    let preimage = match (&datum.value, source) {
        (ExactLowPrecisionValue::Finite(stored), Some(source)) => {
            LowPrecisionPreimageFibre::WitnessedSource {
                residual: &source - stored,
                source,
            }
        }
        (ExactLowPrecisionValue::Finite(_), None) => LowPrecisionPreimageFibre::OpenQuantizationLaw,
        (_, _) => LowPrecisionPreimageFibre::NonFiniteCodeword,
    };
    Ok(ExactLowPrecisionPassage { datum, preimage })
}

/// Decode the first `elements` codewords from a packed little-endian bitstream.
pub fn decode_packed_low_precision(
    dtype: &ForeignDtype,
    payload: &[u8],
    elements: usize,
) -> Result<Vec<ExactLowPrecisionDatum>, ExactLowPrecisionError> {
    let bits = dtype
        .bits()
        .and_then(|bits| usize::try_from(bits).ok())
        .filter(|bits| matches!(*bits, 2 | 4 | 6 | 8))
        .ok_or_else(|| ExactLowPrecisionError::Unsupported(dtype.declared().to_owned()))?;
    let required =
        elements
            .checked_mul(bits)
            .ok_or_else(|| ExactLowPrecisionError::TruncatedPayload {
                dtype: dtype.declared().to_owned(),
                available: payload.len() * 8,
                elements,
            })?;
    if required > payload.len().saturating_mul(8) {
        return Err(ExactLowPrecisionError::TruncatedPayload {
            dtype: dtype.declared().to_owned(),
            available: payload.len() * 8,
            elements,
        });
    }
    let mask = (1u16 << bits) - 1;
    (0..elements)
        .map(|element| {
            let bit = element * bits;
            let byte = bit / 8;
            let shift = bit % 8;
            let low = u16::from(payload[byte]);
            let high = payload.get(byte + 1).copied().map(u16::from).unwrap_or(0);
            let codeword = ((low | (high << 8)) >> shift) & mask;
            decode_low_precision(dtype, codeword as u8)
        })
        .collect()
}

fn decode_e4m3(codeword: u8) -> ExactLowPrecisionValue {
    let sign = codeword & 0x80 != 0;
    let exponent = (codeword >> 3) & 0x0f;
    let mantissa = codeword & 0x07;
    if exponent == 0x0f && mantissa == 0x07 {
        return ExactLowPrecisionValue::NotANumber;
    }
    finite_fields(sign, exponent, mantissa, 3, 7)
}

fn decode_e5m2(codeword: u8) -> ExactLowPrecisionValue {
    let sign = codeword & 0x80 != 0;
    let exponent = (codeword >> 2) & 0x1f;
    let mantissa = codeword & 0x03;
    if exponent == 0x1f {
        return match (sign, mantissa) {
            (false, 0) => ExactLowPrecisionValue::PositiveInfinity,
            (true, 0) => ExactLowPrecisionValue::NegativeInfinity,
            _ => ExactLowPrecisionValue::NotANumber,
        };
    }
    finite_fields(sign, exponent, mantissa, 2, 15)
}

fn finite_minifloat(
    codeword: u8,
    width: u8,
    exponent_bits: u8,
    mantissa_bits: u8,
    bias: i32,
) -> Result<ExactLowPrecisionValue, ExactLowPrecisionError> {
    require_width_name(codeword, width, "finite minifloat")?;
    let sign = codeword & (1 << (width - 1)) != 0;
    let mantissa_mask = (1 << mantissa_bits) - 1;
    let mantissa = codeword & mantissa_mask;
    let exponent = (codeword >> mantissa_bits) & ((1 << exponent_bits) - 1);
    Ok(finite_fields(sign, exponent, mantissa, mantissa_bits, bias))
}

fn finite_fields(
    negative: bool,
    exponent: u8,
    mantissa: u8,
    mantissa_bits: u8,
    bias: i32,
) -> ExactLowPrecisionValue {
    let (significand, power) = if exponent == 0 {
        (i64::from(mantissa), 1 - bias - i32::from(mantissa_bits))
    } else {
        (
            i64::from((1 << mantissa_bits) | mantissa),
            i32::from(exponent) - bias - i32::from(mantissa_bits),
        )
    };
    let value = scaled_integer(if negative { -significand } else { significand }, power);
    ExactLowPrecisionValue::Finite(value)
}

fn scaled_integer(value: i64, power: i32) -> Rat {
    if power >= 0 {
        Rat::from_integer(BigInt::from(value) << power as usize)
    } else {
        Rat::new(BigInt::from(value), BigInt::from(1u8) << (-power) as usize)
    }
}

fn power_of_two(power: i32) -> Rat {
    scaled_integer(1, power)
}

fn require_width(
    dtype: &ForeignDtype,
    codeword: u8,
    width: u8,
) -> Result<(), ExactLowPrecisionError> {
    require_width_name(codeword, width, dtype.declared())
}

fn require_width_name(codeword: u8, width: u8, dtype: &str) -> Result<(), ExactLowPrecisionError> {
    if width < 8 && codeword >= (1 << width) {
        Err(ExactLowPrecisionError::CodewordOverflow {
            dtype: dtype.to_owned(),
            codeword,
        })
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn finite(dtype: &ForeignDtype, codeword: u8) -> Rat {
        let datum = decode_low_precision(dtype, codeword).expect("decode");
        let ExactLowPrecisionValue::Finite(value) = datum.value else {
            panic!("expected finite value")
        };
        value
    }

    #[test]
    fn fp4_codewords_are_exact_dyadic_ratios() {
        assert_eq!(finite(&ForeignDtype::F4, 0x0), Rat::from_integer(0.into()));
        assert_eq!(finite(&ForeignDtype::F4, 0x1), Rat::new(1.into(), 2.into()));
        assert_eq!(finite(&ForeignDtype::F4, 0x2), Rat::from_integer(1.into()));
        assert_eq!(finite(&ForeignDtype::F4, 0x3), Rat::new(3.into(), 2.into()));
        assert_eq!(finite(&ForeignDtype::F4, 0x7), Rat::from_integer(6.into()));
        assert_eq!(
            finite(&ForeignDtype::F4, 0xf),
            Rat::from_integer((-6).into())
        );
    }

    #[test]
    fn fp8_special_and_extreme_codewords_remain_explicit() {
        assert_eq!(
            finite(&ForeignDtype::F8E4M3, 0x38),
            Rat::from_integer(1.into())
        );
        assert_eq!(
            finite(&ForeignDtype::F8E4M3, 0x7e),
            Rat::from_integer(448.into())
        );
        assert!(matches!(
            decode_low_precision(&ForeignDtype::F8E4M3, 0x7f)
                .expect("NaN codeword")
                .value,
            ExactLowPrecisionValue::NotANumber
        ));
        assert!(matches!(
            decode_low_precision(&ForeignDtype::F8E5M2, 0x7c)
                .expect("infinity codeword")
                .value,
            ExactLowPrecisionValue::PositiveInfinity
        ));
    }

    #[test]
    fn packed_fp4_stream_reconstructs_each_codeword_without_padding_an_element() {
        let decoded = decode_packed_low_precision(&ForeignDtype::F4, &[0x21, 0x03], 3)
            .expect("packed decode");
        assert_eq!(
            decoded
                .iter()
                .map(|datum| datum.codeword)
                .collect::<Vec<_>>(),
            vec![1, 2, 3]
        );
        assert_eq!(
            decoded
                .into_iter()
                .map(|datum| datum.value)
                .collect::<Vec<_>>(),
            vec![
                ExactLowPrecisionValue::Finite(Rat::new(1.into(), 2.into())),
                ExactLowPrecisionValue::Finite(Rat::from_integer(1.into())),
                ExactLowPrecisionValue::Finite(Rat::new(3.into(), 2.into())),
            ]
        );
    }

    #[test]
    fn richer_source_returns_exact_residual_and_absent_source_keeps_preimage_open() {
        let source = Rat::new(5.into(), 4.into());
        let passage = admit_low_precision(&ForeignDtype::F4, 0x2, Some(source.clone()))
            .expect("witnessed passage");
        assert_eq!(
            passage.preimage,
            LowPrecisionPreimageFibre::WitnessedSource {
                source,
                residual: Rat::new(1.into(), 4.into()),
            }
        );
        assert_eq!(
            admit_low_precision(&ForeignDtype::F4, 0x2, None)
                .expect("open passage")
                .preimage,
            LowPrecisionPreimageFibre::OpenQuantizationLaw
        );
    }
}
