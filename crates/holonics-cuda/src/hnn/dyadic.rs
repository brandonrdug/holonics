//! **Dyadic coordinates: the card's reading of an exact value** (the device port's host side).
//!
//! [definition] Every value the resident word carries is dyadic: an integer `X` on a declared
//! scale, `x = X · 2^(−σ)` (Decision 24's lattices, and campaign 1's declared scalars, `h = 1`,
//! `Y = 2`, on `2^0ℤ`). A [`DyadicMatrix`] is an exact matrix read at its least common dyadic
//! exponent as signed 64-bit words; a value whose denominator is not a power of two, or whose
//! coordinate passes the word, is refused, never rounded ([`HnnError::Realization`]). The inverse
//! reading, [`value`], is the reduced rational `X / 2^σ`, so a value read back from the card equals
//! the host's value exactly as a `Rat` (a reduced ratio is canonical).

use holonics::hnn::HnnError;
use holonics::ratio::Rat;
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};

/// The refusal of a value the card's dyadic words cannot carry.
pub(crate) fn refused(what: &'static str) -> HnnError {
    HnnError::Realization { what }
}

/// **The exponent of a dyadic value**: `σ` with `denominator = 2^σ`, or `None` off the dyadics.
pub(crate) fn exponent_of(value: &Rat) -> Option<u32> {
    let denominator = value.denom();
    let bits = denominator.bits();
    // A power of two has exactly one bit set: its bit length minus one is its exponent.
    (denominator.magnitude().count_ones() == 1).then(|| (bits - 1) as u32)
}

/// **The least common dyadic exponent** of a family of values, or the refusal.
pub(crate) fn common_exponent<'a>(
    values: impl IntoIterator<Item = &'a Rat>,
    what: &'static str,
) -> Result<u32, HnnError> {
    let mut exponent = 0u32;
    for value in values {
        exponent = exponent.max(exponent_of(value).ok_or_else(|| refused(what))?);
    }
    Ok(exponent)
}

/// **A value's coordinate at a scale** `2^σ`: `x · 2^σ`, exactly, or `None` when the value is not
/// on `2^(−σ)ℤ`.
pub(crate) fn coordinate(value: &Rat, exponent: u32) -> Option<BigInt> {
    let own = exponent_of(value)?;
    (own <= exponent).then(|| value.numer() << (exponent - own) as usize)
}

/// **A value's coordinate as a signed 64-bit word** at a scale, or the refusal.
pub(crate) fn word(value: &Rat, exponent: u32, what: &'static str) -> Result<i64, HnnError> {
    coordinate(value, exponent)
        .and_then(|coordinate| coordinate.to_i64())
        .ok_or_else(|| refused(what))
}

/// **The value of a coordinate** `X · 2^(−σ)`, reduced.
pub(crate) fn value(coordinate: impl Into<BigInt>, exponent: u32) -> Rat {
    Rat::new(coordinate.into(), BigInt::one() << exponent as usize)
}

/// [definition] **An exact matrix at its least common dyadic exponent**: `rows × columns` signed
/// 64-bit words, row-major, the matrix being `words · 2^(−exponent)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DyadicMatrix {
    pub(crate) rows: usize,
    pub(crate) columns: usize,
    pub(crate) exponent: u32,
    pub(crate) words: Vec<i64>,
}

impl DyadicMatrix {
    /// Read an exact matrix at its least common dyadic exponent, or refuse it.
    pub(crate) fn of(matrix: &ExactRatMatrix, what: &'static str) -> Result<Self, HnnError> {
        let exponent = common_exponent(matrix.entries(), what)?;
        Self::at(matrix, exponent, what)
    }

    /// Read an exact matrix at a declared exponent (at least each entry's own), or refuse it.
    pub(crate) fn at(
        matrix: &ExactRatMatrix,
        exponent: u32,
        what: &'static str,
    ) -> Result<Self, HnnError> {
        let words = matrix
            .entries()
            .iter()
            .map(|entry| word(entry, exponent, what))
            .collect::<Result<Vec<i64>, HnnError>>()?;
        Ok(Self {
            rows: matrix.rows(),
            columns: matrix.columns(),
            exponent,
            words,
        })
    }

    /// Whether every entry is zero (an absent form: the host reads it as no term at all).
    pub(crate) fn is_zero(&self) -> bool {
        self.words.iter().all(|w| *w == 0)
    }

    /// `M v` for a vector of coordinates at scale `σ_v`: coordinates at `exponent + σ_v`, exact.
    pub(crate) fn apply(&self, vector: &[BigInt]) -> Vec<BigInt> {
        (0..self.rows)
            .map(|i| {
                let row = &self.words[i * self.columns..(i + 1) * self.columns];
                row.iter()
                    .zip(vector)
                    .filter(|(m, _)| **m != 0)
                    .map(|(m, v)| BigInt::from(*m) * v)
                    .sum()
            })
            .collect()
    }

    /// The largest absolute row sum `‖M‖∞`, exactly.
    pub(crate) fn row_norm(&self) -> Rat {
        let largest = (0..self.rows)
            .map(|i| {
                self.words[i * self.columns..(i + 1) * self.columns]
                    .iter()
                    .map(|w| BigInt::from(*w).abs())
                    .sum::<BigInt>()
            })
            .max()
            .unwrap_or_else(BigInt::zero);
        value(largest, self.exponent)
    }
}

/// **A vector's integral chart**: its entries as integers over their least common denominator
/// (the value is the same rational whatever the chart; the chart only avoids a normalization per
/// term).
pub(crate) fn integral(vector: &[Rat]) -> (Vec<BigInt>, BigInt) {
    let gcd = |a: &BigInt, b: &BigInt| {
        let (mut a, mut b) = (a.abs(), b.abs());
        while !b.is_zero() {
            let r = &a % &b;
            a = b;
            b = r;
        }
        a
    };
    let mut common = BigInt::one();
    for entry in vector {
        let denominator = entry.denom();
        let divisor = gcd(&common, denominator);
        common = &common / &divisor * denominator;
    }
    let numerators = vector
        .iter()
        .map(|entry| entry.numer() * (&common / entry.denom()))
        .collect();
    (numerators, common)
}

/// `⟨a, b⟩` of two coordinate vectors, exactly (its scale the sum of theirs).
pub(crate) fn dot(a: &[BigInt], b: &[BigInt]) -> BigInt {
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}

/// `Σ |x|` of a coordinate vector.
pub(crate) fn l1(vector: &[BigInt]) -> BigInt {
    vector.iter().map(|x| x.abs()).sum()
}

/// `max |x|` of a coordinate vector (zero for none).
pub(crate) fn sup(vector: &[BigInt]) -> BigInt {
    vector
        .iter()
        .map(|x| x.abs())
        .max()
        .unwrap_or_else(BigInt::zero)
}

/// A coordinate vector moved from scale `σ` to a finer scale `σ + shift`.
pub(crate) fn lift(vector: &[BigInt], shift: u32) -> Vec<BigInt> {
    vector.iter().map(|x| x << shift as usize).collect()
}

/// Words as coordinates.
pub(crate) fn wide(words: &[i64]) -> Vec<BigInt> {
    words.iter().map(|w| BigInt::from(*w)).collect()
}

/// Wide words as coordinates.
pub(crate) fn wider(words: &[i128]) -> Vec<BigInt> {
    words.iter().map(|w| BigInt::from(*w)).collect()
}

/// **A power of two `2^η`**: its exponent `η`, or `None` for any other positive value.
pub(crate) fn power_of_two(value: &Rat) -> Option<i64> {
    if !value.is_positive() {
        return None;
    }
    let (numerator, denominator) = (value.numer(), value.denom());
    if numerator.is_one() && denominator.magnitude().count_ones() == 1 {
        Some(-((denominator.bits() - 1) as i64))
    } else if denominator.is_one() && numerator.magnitude().count_ones() == 1 {
        Some((numerator.bits() - 1) as i64)
    } else {
        None
    }
}

/// **A dyadic value as `(numerator, exponent)`** reduced (`value = numerator · 2^(−exponent)`,
/// exponent ≥ 0), with the numerator a signed 64-bit word, or the refusal.
pub(crate) fn reduced_word(value: &Rat, what: &'static str) -> Result<(i64, u32), HnnError> {
    let exponent = exponent_of(value).ok_or_else(|| refused(what))?;
    let numerator = value.numer().to_i64().ok_or_else(|| refused(what))?;
    Ok((numerator, exponent))
}
