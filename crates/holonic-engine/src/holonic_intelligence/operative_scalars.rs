//! The exact scalar projections of the recurrent operator: binary64 and bfloat16 projections of
//! rational constraints, the enclosure of a declared scale, and the bound read from a passage.

use num_bigint::BigInt;
use relational_geometry::Rat;

use holonics::exact_value::ieee754::{BinaryFloatSpecies, decode_bfloat16_bits, round_into};
use holonics::exact_value::{AlgebraicRoot, ExactInterval};
use crate::{resident_section::{Dyadic, DyadicEnclosure}};

use super::{ExtractedOperatorRefusal, NativeScaleConstraint};

pub(super) fn binary64_projection(value: &Rat) -> Result<Dyadic, ExtractedOperatorRefusal> {
    let (datum, _) = round_into(value, BinaryFloatSpecies::Binary64)
        .map_err(|_| ExtractedOperatorRefusal::Operation)?;
    let magnitude =
        i64::try_from(&datum.significand).map_err(|_| ExtractedOperatorRefusal::Operation)?;
    Ok(Dyadic {
        significand: if datum.negative {
            -magnitude
        } else {
            magnitude
        },
        exponent: datum.ulp_exponent,
    })
}

pub(super) fn scale_enclosure(
    constraint: &NativeScaleConstraint,
) -> Result<DyadicEnclosure, ExtractedOperatorRefusal> {
    let interval = match constraint {
        NativeScaleConstraint::ReciprocalSquareRootOf(value) if *value > 0 => {
            AlgebraicRoot::nth_root(&Rat::from_integer(BigInt::from(*value)), 2, 64)
                .map_err(|_| ExtractedOperatorRefusal::Operation)?
                .enclosure()
                .reciprocal()
                .map_err(|_| ExtractedOperatorRefusal::Operation)?
        }
        NativeScaleConstraint::Rational {
            numerator,
            denominator,
        } if *denominator > 0 => ExactInterval::point(Rat::new(
            BigInt::from(*numerator),
            BigInt::from(*denominator),
        )),
        _ => return Err(ExtractedOperatorRefusal::Operation),
    };
    finest_enclosure(&interval)
}

pub(super) fn finest_enclosure(interval: &ExactInterval) -> Result<DyadicEnclosure, ExtractedOperatorRefusal> {
    for grain in (0..=60).rev() {
        if let Ok(enclosure) = DyadicEnclosure::of_interval(&interval, grain) {
            return Ok(enclosure);
        }
    }
    Err(ExtractedOperatorRefusal::Operation)
}

pub(super) fn projected_scale(constraint: &NativeScaleConstraint) -> Result<Dyadic, ExtractedOperatorRefusal> {
    let NativeScaleConstraint::Bfloat16NearestSquareRootOf(value) = constraint else {
        return Err(ExtractedOperatorRefusal::Operation);
    };
    nearest_bfloat16_square_root(*value)
}

fn nearest_bfloat16_square_root(value: u32) -> Result<Dyadic, ExtractedOperatorRefusal> {
    if value == 0 {
        return Ok(Dyadic {
            significand: 0,
            exponent: 0,
        });
    }
    let target = Rat::from_integer(BigInt::from(value));
    let mut low_word = 0u16;
    let mut high_word = 0x7f7fu16;
    while low_word + 1 < high_word {
        let middle = low_word + (high_word - low_word) / 2;
        let middle_value = decode_bfloat16_bits(middle)
            .map_err(|_| ExtractedOperatorRefusal::Operation)?
            .value();
        if &middle_value * &middle_value <= target {
            low_word = middle;
        } else {
            high_word = middle;
        }
    }
    let low = decode_bfloat16_bits(low_word)
        .map_err(|_| ExtractedOperatorRefusal::Operation)?
        .value();
    let high = decode_bfloat16_bits(high_word)
        .map_err(|_| ExtractedOperatorRefusal::Operation)?
        .value();
    let midpoint = (&low + &high) / Rat::from_integer(BigInt::from(2));
    let word = if &midpoint * &midpoint < target {
        high_word
    } else if &midpoint * &midpoint > target || low_word & 1 == 0 {
        low_word
    } else {
        high_word
    };
    Dyadic::of_bfloat16_bits(word).map_err(ExtractedOperatorRefusal::Resident)
}

pub(super) fn operation_bound(
    operation: u32,
    reading: &crate::resident_section::PassageReading,
) -> Result<u32, ExtractedOperatorRefusal> {
    exact_bound(reading)
        .map_err(|flags| ExtractedOperatorRefusal::ResidentObstruction { operation, flags })
}

fn exact_bound(reading: &crate::resident_section::PassageReading) -> Result<u32, u32> {
    if !reading.obstruction.is_empty() {
        return Err(reading.obstruction.joined_flags());
    }
    Ok(reading
        .slots
        .last()
        .map(|slot| slot.max_octave.max(1))
        .unwrap_or(1))
}
