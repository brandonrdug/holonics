//! **The arithmetic terrain: products and prime streams as digit cells, with their exact faces**
//! (the record `2026-09-27_THE_EGG_IS_A_GENERATORS_GENOME_…_THE_FACES_OF_INTEGERS_ARE_MOIRES_OF_GRATINGS.md`,
//! §7 and §9; rebuild step 4, #73).
//!
//! [definition; agent-inferred] **An integer is a digit vector on a helix** (the record's §7.1). Its
//! `L` digits in base `b` are the reading of an odometer of `L` levels of radix `b` ([`digits`],
//! through `geometry::winding::Odometer`, Lean `Geometry/PhaseCarry.value_digits`), and the carry
//! between levels is the helix's winding. Multiplication is the convolution of two digit vectors
//! (carry-free and linear) followed by that carry ([`digit_product`]). Two terrains are made of
//! it, each emitted as a cell stream beside its exact truth, so a receiver is gauged on the faces
//! the record names: the trailing face, the leading face with its carry fibre, the cheap faces and
//! the gratings.
//!
//! | Terrain | Its Holarchy | Its truth receipt | The faces it isolates |
//! |---|---|---|---|
//! | [`Products`] | two operand odometers of `L` levels drawn uniformly (the keys), joined by the convolution of their digit vectors, whose carry cascade is the product's odometer of `2L` levels | [`ProductTruth`]: the operands and their factorizations, the convolution before carry, the carry word, the product's digits, its trailing face `mod b^k` and its leading face with the carry fibre ([`LeadingFace`]) | the trailing face (a ring homomorphism: the carry flows up, never down) and the leading face (multiplicative up to the fibre the unread lower places carry into it) |
//! | [`PrimeWindow`] | a window's integers as one odometer ticking once a record, met by the gratings: each prime `p ∤ b` a ring of period `p` on the leading index | [`IntegerTruth`] for each integer: its factorization and least prime factor, its leading index and residue, the gratings covering it with their classes, its cheap readings; the base's [`CheapFaces`]; the density's code read through a face ([`FaceCode`]) | the cheap faces of `b`, `b − 1`, `b + 1` and the gratings on the leading index |
//!
//! [proved-derived; formal-checked in Lean, implemented-exact here] The joins to Lean
//! `Mathematics/RadixWindowReceiver` (the tests realize each on hand-computed fixtures):
//!
//! | Lean | Rust |
//! |---|---|
//! | `digit_product_is_carry_of_convolution` | [`DigitProduct::convolution_value`]: `Σ_j c_j b^j = x(b)·y(b)` |
//! | `carry_step_value` | each step of [`digit_product`]'s carry, `total = phase + b·winding` (`geometry::winding::{phase, winding}`) |
//! | `carried_word_is_product_digits` | [`DigitProduct::digits`]: the carried word, no zero at its top, is the product's digit word |
//! | `grating_on_digit_index` | [`grating_class`], [`IntegerTruth::gratings`] |
//! | `cheap_faces` | [`CheapReading`], [`CheapFaces`] |
//!
//! [proved-standard] The trailing face's ring homomorphism is Mathlib's `Nat.mul_mod`. [open]
//! Owed in #62: the leading face's fibre, `⌊a/b^s⌋ = A ∧ ⌊c/b^s⌋ = C ⇒ A C b^(2s) ≤ a c ≤
//! ((A + 1) b^s − 1)((C + 1) b^s − 1)` (monotonicity of the product; no Lean statement yet).
//!
//! [definition] The computational object is the helical pair interaction, here as the terrain it
//! meets: an integer as a digit vector on a helix, the carry its winding. Of the winding guide's six
//! general objects this owner touches two: the **helix** (the odometer's levels and the carry word,
//! circle plus carry) and **faces and placement** (the trailing face, the leading face with its
//! fibre, the cheap faces and the gratings placed on the leading index). The **pair** (the
//! convolution pairs digit `i` with digit `j` at place `i + j`, with no lock address claimed), the
//! **cell holonomy** (none: the digits exchange no power), the **tube** (the window's span, one
//! record a tick) and the **tower thread** (the base chain `2 → 4 → 16` restricts a trailing face
//! to the next, §7.4) stay attached.

mod primes;
mod products;

#[cfg(test)]
mod tests;

pub use primes::{
    CheapFaces, CheapReading, ClassCount, FaceCode, GratingCover, IntegerTruth, PrimeCell,
    PrimeEmission, PrimeWindow, grating_class,
};
pub use products::{LeadingFace, ProductCell, ProductFamily, ProductTruth, Products};

use num_bigint::BigUint;
use num_traits::Zero;

use super::{TerrainError, refuse};
use crate::geometry::winding::{Odometer, phase, winding};
use crate::ratio::surprisal::factor_biguint;

/// [definition] **The declared digit order** of an emission: the least or the most significant
/// digit first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DigitOrder {
    LeastFirst,
    MostFirst,
}

impl DigitOrder {
    /// A word's digits (given least significant first) in the declared order.
    pub fn arrange(self, digits: &[u64]) -> Vec<u64> {
        match self {
            Self::LeastFirst => digits.to_vec(),
            Self::MostFirst => digits.iter().rev().copied().collect(),
        }
    }

    /// The place (significance) of the digit emitted at `offset` of a word of `length` digits.
    pub fn place(self, offset: usize, length: usize) -> usize {
        match self {
            Self::LeastFirst => offset,
            Self::MostFirst => length - 1 - offset,
        }
    }
}

fn check_base(base: u64) -> Result<(), TerrainError> {
    if base < 2 {
        return Err(refuse("a base", "it needs at least two digits"));
    }
    Ok(())
}

/// `b^e`, refused when it leaves the machine word.
fn checked_power(base: u64, exponent: usize) -> Result<u64, TerrainError> {
    u32::try_from(exponent)
        .ok()
        .and_then(|exponent| base.checked_pow(exponent))
        .ok_or_else(|| refuse("a power of the base", "it leaves the machine word"))
}

/// **The word of `length` digits of `value` in base `b`, least significant first**: the reading of
/// an odometer of `length` levels of radix `b` holding `value` (`geometry::winding::Odometer`, Lean
/// `Geometry/PhaseCarry.value_digits`), zero-padded at the top. Refused when the value does not fit
/// (the odometer's overflow winding is not zero) or the base holds fewer than two digits.
pub fn digits(value: u64, base: u64, length: usize) -> Result<Vec<u64>, TerrainError> {
    check_base(base)?;
    let odometer = Odometer::from_value(vec![BigUint::from(base); length], &BigUint::from(value))
        .map_err(|_| refuse("a digit word", "its base needs at least two digits"))?;
    if !odometer.overflow_winding().is_zero() {
        return Err(refuse(
            "a digit word",
            "the value does not fit its declared length",
        ));
    }
    Ok(odometer
        .digits()
        .iter()
        .map(|digit| u64::try_from(digit).expect("a digit lies below a machine-word base"))
        .collect())
}

/// The number of base-`b` digits of `value` (one for zero).
fn digit_count(value: u64, base: u64) -> usize {
    let mut count = 1;
    let mut rest = value / base;
    while rest > 0 {
        count += 1;
        rest /= base;
    }
    count
}

/// [definition] **A factorization** `n = ∏ p^e`: ascending primes with their exponents.
pub type Factorization = Vec<(u64, u32)>;

/// **The factorization** `n = ∏ p^e`, ascending primes with their exponents (the crate's trial
/// division, `ratio::surprisal`): the empty product for `1`, none for `0`.
pub fn factorization(value: u64) -> Option<Factorization> {
    (value > 0).then(|| {
        factor_biguint(&BigUint::from(value)).expect("a machine word factors within its carrier")
    })
}

/// [definition] **A digit product** (the record's §7.1): the convolution `c_j = Σ_(i+l=j) x_i y_l`
/// of two digit vectors (least significant first) before carry, the **carry word** (the carry
/// leaving each place of the carried word, its last zero), and the carried word, least significant
/// first with no zero at its top: the product's digit word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DigitProduct {
    pub base: u64,
    pub convolution: Vec<u64>,
    pub carries: Vec<u64>,
    pub digits: Vec<u64>,
}

/// `Σ_j w_j b^j`, exactly.
fn horner(word: &[u64], base: u64) -> BigUint {
    word.iter().rev().fold(BigUint::zero(), |value, digit| {
        value * BigUint::from(base) + BigUint::from(*digit)
    })
}

impl DigitProduct {
    /// `Σ_j c_j b^j`: the convolution's value, the product of the two vectors' values (Lean
    /// `RadixWindowReceiver.digit_product_is_carry_of_convolution`).
    pub fn convolution_value(&self) -> BigUint {
        horner(&self.convolution, self.base)
    }

    /// `Σ_j d_j b^j`: the carried word's value, the convolution's value (Lean `carry_step_value`,
    /// one step at a time).
    pub fn value(&self) -> BigUint {
        horner(&self.digits, self.base)
    }
}

/// **Multiplication is convolution with carry** (the record's §7.1; Lean
/// `RadixWindowReceiver.digit_product_is_carry_of_convolution`, `carry_step_value`,
/// `carried_word_is_product_digits`). The digits may be any naturals, as in Lean's polynomials; each
/// place's total (its convolution term and the carry arriving from below) is read on the circle of
/// `b` steps, its phase the digit and its winding the carry passed up (`geometry::winding`), until
/// the convolution and the carry are exhausted; the zeros at the top are then dropped (their totals
/// and carries are zero). Refused when the base holds fewer than two digits or a convolution term
/// leaves the machine word.
pub fn digit_product(base: u64, left: &[u64], right: &[u64]) -> Result<DigitProduct, TerrainError> {
    check_base(base)?;
    let overflow = || refuse("a digit product", "its convolution leaves the machine word");
    let places = if left.is_empty() || right.is_empty() {
        0
    } else {
        left.len() + right.len() - 1
    };
    let mut convolution = vec![0u64; places];
    for (i, x) in left.iter().enumerate() {
        for (j, y) in right.iter().enumerate() {
            let term = x.checked_mul(*y).ok_or_else(overflow)?;
            convolution[i + j] = convolution[i + j].checked_add(term).ok_or_else(overflow)?;
        }
    }
    let radix = BigUint::from(base);
    let (mut digits, mut carries) = (Vec::new(), Vec::new());
    let mut carry = BigUint::zero();
    let mut place = 0;
    while place < convolution.len() || !carry.is_zero() {
        let total = BigUint::from(convolution.get(place).copied().unwrap_or(0)) + &carry;
        let digit = phase(&radix, &total).expect("a base of at least two steps");
        carry = winding(&radix, &total).expect("a base of at least two steps");
        digits.push(u64::try_from(&digit).expect("a digit lies below a machine-word base"));
        carries.push(u64::try_from(&carry).map_err(|_| overflow())?);
        place += 1;
    }
    while digits.last() == Some(&0) {
        digits.pop();
        carries.pop();
    }
    Ok(DigitProduct {
        base,
        convolution,
        carries,
        digits,
    })
}
