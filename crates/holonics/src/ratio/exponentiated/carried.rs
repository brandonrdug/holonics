//! **The carried power `2^(n + k/L)` and its exact field `ℚ(θ)`, `θ^L = 2`** (rebuild step 4
//! addition 4, §8.4).
//!
//! [definition] A rational exponent `x = n + k/L + ε` read at a grain `L` is carried as its carry
//! `n` (an exact shift by `2^n`) and its phase class `k ∈ ℤ/L` ([`CarriedPower`]): `2^(n + k/L) =
//! 2^n θ^k` in `ℚ(θ) = ℚ[X]/(X^L − 2)` ([`PhaseField`], `L` rational coordinates in the power
//! basis). The phase's carry is multiplication by `2` (`k + L ↦ n + 1`), and carried powers
//! multiply with carry. `ℚ(θ)` is a field because `X^L − 2` is Eisenstein at `2`, so a sum of carried
//! powers normalizes by exact division there ([`PhaseField::inverse`]). The real chart
//! `θ ↦ 2^(1/L)` is read only as an [`ExactInterval`] enclosure at [`READING_BITS`], an exterior
//! face; nothing here rounds. It is the arc-to-whole transition of this module at a fractional
//! exponent: the finer chart a fractional coefficient lands in, entered rather than enclosed.
//!
//! | Lean `Objects/Ratio/CarriedPower` | Rust |
//! |---|---|
//! | `PhaseField`, `theta`, `theta_pow`, `irreducible_X_pow_sub_two`, `irreducible_X_pow_sub_two_int` | [`PhaseField`] |
//! | `carriedPower`, `carriedPower_exact`, `realChart`, `realRoot`, `realRoot_pow` | [`CarriedPower`], [`PhaseField::enclosure`] |
//! | `zero_grain_is_not_a_field` | [`CarriedPower::new`] refuses `L = 0` |

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::ratio::algebraic::ExactInterval;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer};

use super::RatioError;

/// The bits of a real-chart enclosure of `θ^i`: the declared reading grain of every enclosure of
/// the carried power (an exterior face, never a law's value).
pub const READING_BITS: u32 = 64;

/// [definition] **A value of `ℚ(θ)`, `θ^L = 2`**, in the power basis `1, θ, …, θ^(L−1)` (Lean
/// `Objects/Ratio/CarriedPower.PhaseField`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PhaseField {
    coordinates: Vec<Rat>,
}

impl PhaseField {
    /// Zero at grain `L ≥ 1`.
    pub fn zero(grain: u64) -> Self {
        Self {
            coordinates: vec![Rat::zero(); grain_width(grain)],
        }
    }

    /// The rational `value` at grain `L`.
    pub fn rational(value: Rat, grain: u64) -> Self {
        let mut field = Self::zero(grain);
        field.coordinates[0] = value;
        field
    }

    /// `L`.
    pub fn grain(&self) -> u64 {
        self.coordinates.len() as u64
    }

    /// The power-basis coordinates.
    pub fn coordinates(&self) -> &[Rat] {
        &self.coordinates
    }

    pub fn is_zero(&self) -> bool {
        self.coordinates.iter().all(Zero::is_zero)
    }

    /// The value when it is rational (every coordinate but the first vanishes).
    pub fn as_rational(&self) -> Option<&Rat> {
        self.coordinates[1..]
            .iter()
            .all(Zero::is_zero)
            .then(|| &self.coordinates[0])
    }

    fn same_grain(&self, other: &Self) -> Result<(), RatioError> {
        if self.coordinates.len() != other.coordinates.len() {
            return Err(RatioError::GrainMismatch {
                left: self.grain(),
                right: other.grain(),
            });
        }
        Ok(())
    }

    pub fn plus(&self, other: &Self) -> Result<Self, RatioError> {
        self.same_grain(other)?;
        Ok(Self {
            coordinates: self
                .coordinates
                .iter()
                .zip(&other.coordinates)
                .map(|(a, b)| a + b)
                .collect(),
        })
    }

    pub fn minus(&self, other: &Self) -> Result<Self, RatioError> {
        self.plus(&other.scaled(&-Rat::one()))
    }

    pub fn scaled(&self, factor: &Rat) -> Self {
        Self {
            coordinates: self.coordinates.iter().map(|x| x * factor).collect(),
        }
    }

    /// `θ^k · self`: each coordinate moves up `k` places, and a place past `L − 1` wraps doubled
    /// (`θ^L = 2`, the phase carry).
    pub fn shifted(&self, k: u64) -> Self {
        let width = self.coordinates.len();
        let mut coordinates = vec![Rat::zero(); width];
        for (place, value) in self.coordinates.iter().enumerate() {
            if value.is_zero() {
                continue;
            }
            let total = place as u64 + k;
            let (carries, target) = (total / width as u64, (total % width as u64) as usize);
            // A place carries at most `⌊(L − 1 + k)/L⌋` times: a shift by a machine-word count.
            coordinates[target] += value * Rat::from_integer(BigInt::one() << carries);
        }
        Self { coordinates }
    }

    /// `self · other` modulo `θ^L = 2`.
    pub fn times(&self, other: &Self) -> Result<Self, RatioError> {
        self.same_grain(other)?;
        let width = self.coordinates.len();
        let mut coordinates = vec![Rat::zero(); width];
        for (i, a) in self.coordinates.iter().enumerate() {
            if a.is_zero() {
                continue;
            }
            for (j, b) in other.coordinates.iter().enumerate() {
                if b.is_zero() {
                    continue;
                }
                let place = i + j;
                if place < width {
                    coordinates[place] += a * b;
                } else {
                    coordinates[place - width] += integer(2) * a * b;
                }
            }
        }
        Ok(Self { coordinates })
    }

    /// **The exact inverse in `ℚ(θ)`**: the solution of the multiplication map's linear system
    /// `(x ↦ self · x) y = 1`. Refused at zero; every other value is invertible because `ℚ(θ)` is
    /// a field (Lean `Objects/Ratio/CarriedPower.irreducible_X_pow_sub_two`).
    pub fn inverse(&self) -> Result<Self, RatioError> {
        if self.is_zero() {
            return Err(RatioError::ZeroHasNoInverse);
        }
        if let Some(value) = self.as_rational() {
            return Ok(Self::rational(value.recip(), self.grain()));
        }
        let width = self.coordinates.len();
        // Column j is self · θ^j.
        let columns: Vec<Vec<Rat>> = (0..width)
            .map(|j| self.shifted(j as u64).coordinates)
            .collect();
        let matrix = ExactRatMatrix::shaped(
            width,
            width,
            (0..width)
                .map(|row| columns.iter().map(|column| column[row].clone()).collect())
                .collect(),
        )?;
        let inverse = matrix.inverse()?;
        Ok(Self {
            coordinates: (0..width)
                .map(|row| inverse.get(row, 0).cloned())
                .collect::<Result<_, _>>()?,
        })
    }

    /// **The real chart** `θ ↦ 2^(1/L)`, enclosed at [`READING_BITS`]: an exterior reading.
    pub fn enclosure(&self) -> Result<ExactInterval, RatioError> {
        let grain = self.grain();
        let (mut lower, mut upper) = (Rat::zero(), Rat::zero());
        for (place, value) in self.coordinates.iter().enumerate() {
            if value.is_zero() {
                continue;
            }
            let (low, high) = theta_power_bounds(place as u64, grain);
            if value.is_negative() {
                lower += value * &high;
                upper += value * &low;
            } else {
                lower += value * &low;
                upper += value * &high;
            }
        }
        ExactInterval::new(lower, upper).map_err(|_| RatioError::Enclosure)
    }
}

fn grain_width(grain: u64) -> usize {
    usize::try_from(grain.max(1)).expect("a declared grain fits the machine word")
}

/// `2^n` exactly, for any integer `n`: the carry's shift. A carry past the machine word is refused
/// with [`RatioError::CarryTooWide`], never rounded.
pub fn power_of_two(n: &BigInt) -> Result<Rat, RatioError> {
    let magnitude = n
        .abs()
        .to_usize()
        .ok_or_else(|| RatioError::CarryTooWide { carry: n.clone() })?;
    let shifted = BigInt::one() << magnitude;
    Ok(if n.is_negative() {
        Rat::new(BigInt::one(), shifted)
    } else {
        Rat::from_integer(shifted)
    })
}

/// Rational bounds of `θ^i = 2^(i/L)` at [`READING_BITS`]: `⌊2^(i/L + b)⌋ / 2^b` below and one unit
/// above, exact when the power is.
fn theta_power_bounds(i: u64, grain: u64) -> (Rat, Rat) {
    if i == 0 {
        return (Rat::one(), Rat::one());
    }
    let bits = u64::from(READING_BITS);
    let target = BigUint::one() << (i + bits * grain) as usize;
    let floor = target.nth_root(u32::try_from(grain).expect("a grain fits u32"));
    let unit = Rat::new(BigInt::one(), BigInt::one() << READING_BITS as usize);
    let lower = Rat::from_integer(BigInt::from(floor.clone())) * &unit;
    let exact = floor.pow(u32::try_from(grain).expect("a grain fits u32")) == target;
    let upper = if exact {
        lower.clone()
    } else {
        Rat::from_integer(BigInt::from(floor + 1u32)) * &unit
    };
    (lower, upper)
}

// -------------------------------------------------------------------------------------------
// the carried power

/// [definition] **The carried power `2^(n + k/L) = 2^n θ^k`**: a carry `n` and a phase class
/// `k ∈ ℤ/L` (Lean `Objects/Ratio/CarriedPower.carriedPower`, `carriedPower_exact`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarriedPower {
    carry: BigInt,
    phase: u64,
    grain: u64,
}

impl CarriedPower {
    /// Refused unless `L ≥ 1` and `k < L`.
    pub fn new(carry: BigInt, phase: u64, grain: u64) -> Result<Self, RatioError> {
        if grain == 0 || phase >= grain {
            return Err(RatioError::Grain { phase, grain });
        }
        Ok(Self {
            carry,
            phase,
            grain,
        })
    }

    pub fn carry(&self) -> &BigInt {
        &self.carry
    }

    pub fn phase(&self) -> u64 {
        self.phase
    }

    /// `L`.
    pub fn grain(&self) -> u64 {
        self.grain
    }

    /// `2^(n+k/L) · 2^(m+l/L)`: the phases add, and a sum past `L` carries one doubling into the
    /// carry (the phase odometer's carry is multiplication by 2).
    pub fn times(&self, other: &Self) -> Result<Self, RatioError> {
        if self.grain != other.grain {
            return Err(RatioError::GrainMismatch {
                left: self.grain,
                right: other.grain,
            });
        }
        let total = self.phase + other.phase;
        Ok(Self {
            carry: &self.carry + &other.carry + BigInt::from(total / self.grain),
            phase: total % self.grain,
            grain: self.grain,
        })
    }

    /// Its value `2^n θ^k` in `ℚ(θ)`; refused when the carry is past the machine word.
    pub fn value(&self) -> Result<PhaseField, RatioError> {
        Ok(PhaseField::rational(power_of_two(&self.carry)?, self.grain).shifted(self.phase))
    }

    /// **The odometer chart** `2^n (1 + k/L)`: exact at every carry, continuous across it
    /// (`2^n · 2 = 2^(n+1) · 1`), monotone and rational; the HNN's declared learning chart
    /// (`crate::hnn::ratio`, Lean `HNN/Ratio.odometer_covector_descends`).
    pub fn odometer(&self) -> Result<Rat, RatioError> {
        Ok(power_of_two(&self.carry)?
            * (Rat::one() + Rat::new(BigInt::from(self.phase), BigInt::from(self.grain))))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Lean `Objects/Ratio/CarriedPower.carriedPower_exact`: the phase carry is multiplication by
    /// two, carried powers multiply with carry, the grain root's `L`-th power is `2`, a nonzero
    /// value of `ℚ(θ)` has its exact inverse, the real chart encloses `2^(n + k/L)`, and a zero
    /// grain or a phase past it is refused (`zero_grain_is_not_a_field`).
    #[test]
    fn the_carried_power_carries_by_doubling_and_normalizes_exactly() {
        let grain = 4;
        let a = CarriedPower::new(BigInt::from(1), 3, grain).unwrap();
        let b = CarriedPower::new(BigInt::from(-2), 2, grain).unwrap();
        let product = a.times(&b).unwrap();
        assert_eq!((product.carry(), product.phase()), (&BigInt::zero(), 1));
        assert_eq!(
            product.value().unwrap(),
            a.value().unwrap().times(&b.value().unwrap()).unwrap()
        );
        let root = CarriedPower::new(BigInt::zero(), 1, grain).unwrap();
        let mut power = PhaseField::rational(Rat::one(), grain);
        for _ in 0..grain {
            power = power.times(&root.value().unwrap()).unwrap();
        }
        assert_eq!(power, PhaseField::rational(integer(2), grain));
        let sum = a.value().unwrap().plus(&b.value().unwrap()).unwrap();
        assert_eq!(
            sum.times(&sum.inverse().unwrap()).unwrap(),
            PhaseField::rational(Rat::one(), grain)
        );
        let enclosed = a.value().unwrap().enclosure().unwrap();
        // 2^(1 + 3/4) = 2 · 2^(3/4) ∈ (3.36, 3.37).
        assert!(enclosed.lower > Rat::new(BigInt::from(336), BigInt::from(100)));
        assert!(enclosed.upper < Rat::new(BigInt::from(337), BigInt::from(100)));
        assert_eq!(
            a.odometer().unwrap(),
            integer(2) * Rat::new(BigInt::from(7), BigInt::from(4))
        );
        assert_eq!(
            CarriedPower::new(BigInt::zero(), 0, 0),
            Err(RatioError::Grain { phase: 0, grain: 0 })
        );
        assert!(CarriedPower::new(BigInt::zero(), 4, grain).is_err());
        assert!(PhaseField::zero(grain).inverse().is_err());
        assert!(
            a.times(&CarriedPower::new(BigInt::zero(), 0, 2).unwrap())
                .is_err()
        );
    }
}
