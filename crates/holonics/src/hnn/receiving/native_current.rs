//! NativeCurrentPredictionV1: one actual native logit source, no landmark/population operand.
use super::*;
use crate::ratio::algebraic::{ExactInterval, log2_enclosure_at};
use num_traits::{One, Signed, Zero};

/// Constructor is private to the library's native producing Word boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NativeCurrentFace {
    wave: Vec<Rat>,
    masses: Vec<ExactInterval>,
    weights: Vec<ExactInterval>,
    bits: u32,
}
impl NativeCurrentFace {
    pub(crate) fn at(wave: Vec<Rat>, bits: u32) -> Result<Self, HnnError> {
        if wave.is_empty() || wave.len() % 2 != 0 || bits == 0 || bits > 128 {
            return Err(HnnError::Unadmitted {
                reason: "bounded complete native current receiving chart",
            });
        }
        let terms: Vec<_> = wave
            .iter()
            .step_by(2)
            .map(|w| (Rat::one(), w.clone()))
            .collect();
        let top = terms
            .iter()
            .map(|(_, w)| w.floor().to_integer())
            .max()
            .expect("nonempty admitted chart");
        let weights = terms
            .into_iter()
            .map(|(_, w)| native_power(&(w - Rat::from_integer(top.clone())), bits))
            .collect::<Result<Vec<_>, _>>()?;
        let masses = super::single_grain::normalize_weights(&weights)?;
        Ok(Self {
            wave,
            masses,
            weights,
            bits,
        })
    }
    pub(crate) fn wave(&self) -> &[Rat] {
        &self.wave
    }
    pub(crate) fn masses(&self) -> &[ExactInterval] {
        &self.masses
    }
    pub(crate) fn score(&self, target: usize) -> Result<ExactInterval, HnnError> {
        let p = self.masses.get(target).ok_or(HnnError::Unadmitted {
            reason: "actual class in native predictor",
        })?;
        let lo = log2_enclosure_at(&p.lower, self.bits)?;
        let hi = log2_enclosure_at(&p.upper, self.bits)?;
        ExactInterval::new(-hi.upper, -lo.lower).map_err(Into::into)
    }
    pub(crate) fn returned(&self, target: usize) -> Result<RetainedStationReturn, HnnError> {
        if target >= self.masses.len() {
            return Err(HnnError::Unadmitted {
                reason: "native target in the original class chart",
            });
        }
        let representatives: Vec<Rat> = self
            .weights
            .iter()
            .map(|w| (&w.lower + &w.upper) / crate::ratio::integer(2))
            .collect();
        let z: Rat = representatives.iter().cloned().sum();
        let normalized_representative: Vec<Rat> = representatives.iter().map(|w| w / &z).collect();
        let packed_foil = super::pack_simplex(&normalized_representative, self.bits)?;
        let gradient: Vec<Rat> = packed_foil
            .iter()
            .enumerate()
            .map(|(c, v)| v - if c == target { Rat::one() } else { Rat::zero() })
            .collect();
        let component_bounds: Vec<ExactInterval> = self
            .masses
            .iter()
            .enumerate()
            .map(|(c, m)| {
                let e = if c == target { Rat::one() } else { Rat::zero() };
                ExactInterval::new(&m.lower - &e, &m.upper - &e)
            })
            .collect::<Result<_, _>>()?;
        let component_error = component_bounds
            .iter()
            .zip(&gradient)
            .map(|(m, g)| (&m.lower - g).abs().max((&m.upper - g).abs()))
            .collect();
        Ok(RetainedStationReturn {
            target,
            normalized_representative,
            packed_foil,
            packing_bits: self.bits,
            gradient,
            component_bounds,
            component_error,
        })
    }
}

/// Bounded finite observation of 2^x, including a rational whose denominator does not
/// fit a root-degree word. Binary prefix + outward square roots; no value/centre cast.
fn native_power(x: &Rat, bits: u32) -> Result<ExactInterval, HnnError> {
    use num_traits::ToPrimitive;
    let n = x.floor().to_integer();
    let exponent = n
        .to_i32()
        .filter(|n| n.unsigned_abs() <= 4096)
        .ok_or(HnnError::CountOverflow)?;
    let scale = if exponent >= 0 {
        Rat::from_integer(num_bigint::BigInt::one() << exponent as usize)
    } else {
        Rat::new(
            num_bigint::BigInt::one(),
            num_bigint::BigInt::one() << (-exponent) as usize,
        )
    };
    let f = x - Rat::from_integer(n);
    if f.is_zero() {
        return Ok(ExactInterval::point(scale));
    }
    let grid = bits.checked_add(32).ok_or(HnnError::CountOverflow)?;
    let prefix = bits.checked_add(8).ok_or(HnnError::CountOverflow)?;
    let denominator = num_bigint::BigInt::one() << grid as usize;
    let unit = Rat::new(num_bigint::BigInt::one(), denominator.clone());
    let rounding = |x: Rat, up: bool| {
        let y = x * Rat::from_integer(denominator.clone());
        Rat::new(
            if up {
                y.ceil().to_integer()
            } else {
                y.floor().to_integer()
            },
            denominator.clone(),
        )
    };
    let (mut theta_lo, mut theta_hi) = (crate::ratio::integer(2), crate::ratio::integer(2));
    let (mut lower, mut upper) = (Rat::one(), Rat::one());
    let mut remainder = f.numer().clone();
    for _ in 0..prefix {
        theta_lo =
            (crate::holon::deposition::sqrt_ceiling(&theta_lo, grid) - &unit).max(Rat::one());
        theta_hi = crate::holon::deposition::sqrt_ceiling(&theta_hi, grid);
        remainder <<= 1usize;
        if remainder >= *f.denom() {
            remainder -= f.denom();
            lower = rounding(lower * &theta_lo, false);
            upper = rounding(upper * &theta_hi, true);
        }
        if remainder.is_zero() {
            break;
        }
    }
    if !remainder.is_zero() {
        // 0<=tail<2^-prefix and convexity gives 2^tail<=1+tail on [0,1].
        upper *= Rat::one()
            + Rat::new(
                num_bigint::BigInt::one(),
                num_bigint::BigInt::one() << prefix as usize,
            );
    }
    ExactInterval::new(lower * &scale, upper * scale).map_err(Into::into)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn native_context_pure_power_handles_non_word_root_degree_without_changing_source() {
        for x in [
            crate::ratio::rat(0, 1),
            crate::ratio::rat(1, 2),
            crate::ratio::rat(-2, 3),
            Rat::new(7.into(), (num_bigint::BigInt::one() << 80usize) + 1),
        ] {
            let a = native_power(&x, 32).unwrap();
            let b = native_power(&x, 64).unwrap();
            assert!(a.lower > Rat::zero() && a.lower <= b.upper && b.lower <= a.upper);
            assert!(&b.upper - &b.lower < Rat::new(1.into(), num_bigint::BigInt::one() << 60usize));
        }
        let half = native_power(&crate::ratio::rat(1, 2), 64).unwrap();
        assert!(&half.lower * &half.lower <= crate::ratio::integer(2));
        assert!(&half.upper * &half.upper >= crate::ratio::integer(2));
        assert!(native_power(&crate::ratio::integer(-4097), 64).is_err());
    }
}
