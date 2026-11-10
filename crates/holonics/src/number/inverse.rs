//! **Inversion** (N6): one map, `x ↦ x(2 − a x)`, whose residual squares, completed from a declared end of the
//! place graph and returning `(X, E)` with its certificate. The top end (Newton) reads the lattice reciprocal
//! `X = ⌊2^p / a⌋` with `0 ≤ E = 2^p − a X < a`; the bottom end (Hensel) the inverse of an odd value modulo `2^w`
//! with `a X − 1 ≡ 0 (mod 2^w)`; Euclid's end the inverse modulo `m` as a word of shears. Each is scheduled by the
//! target width's halvings: a step doubles the certified places.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

use super::closing::mod_inverse;
use super::value::{Digits, Section, Value};
use super::{refuse, Grain, Result, Width};

/// The end an inversion completes from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum End {
    /// The top of the place graph: the lattice reciprocal at `p` places, `X = ⌊2^p / a⌋`.
    Top(u32),
    /// The bottom: the inverse of an odd value modulo `2^w`.
    Bottom(u32),
    /// Euclid's: the inverse modulo `m`, by the shear word of the extended Euclidean descent.
    Euclid(Value),
    /// A matrix's Newton–Schulz end (owed: `hnn::chart` holds its certified realization until it moves here).
    Matrix,
    /// The pseudoinverse on the range (owed).
    Range,
}

/// **An inverse with its residual**: `X`, `E`, the end it completed from, the places its certificate holds,
/// and the steps the schedule took.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Inverse {
    pub x: Value,
    pub residual: Value,
    pub end: End,
    pub certified: Width,
    pub steps: u32,
}

fn ray_at(digits: BigInt, grain: Grain) -> Result<Value> {
    let d = Digits::from_big(digits);
    let w = d.places_in(Section::TwosComplement).max(1);
    Value::of(grain, Width::new(w), Section::TwosComplement, d)
}

/// **Invert a value** at a declared end.
pub fn invert(a: &Value, end: End) -> Result<Inverse> {
    let av = a.digits.big();
    match &end {
        End::Top(p) => {
            if !av.is_positive() {
                return refuse("a lattice reciprocal of a value that is not positive");
            }
            let p = *p;
            // Newton on the reciprocal from the top: start at 2^(p − bits(a)), where 1/2 ≤ a x / 2^p < 1, and
            // x ← x + x(2^p − a x) / 2^p squares the relative residual, doubling the certified places; the last
            // places are then settled so 0 ≤ E < a. Below a's top place the reciprocal is under one: start at
            // zero, and the settling reads whether 2^p = a.
            let target = BigInt::one() << p as usize;
            let bits = av.bits();
            let mut x = if u64::from(p) >= bits { BigInt::one() << (u64::from(p) - bits) as usize } else { BigInt::zero() };
            let mut steps = 0u32;
            let rounds = 64 - (u64::from(p.max(1)) - 1).leading_zeros() + 2;
            for _ in 0..rounds {
                let e = &target - &av * &x;
                let dx = (&x * &e) >> p as usize;
                if dx.is_zero() {
                    break;
                }
                x += dx;
                steps += 1;
            }
            let mut e = &target - &av * &x;
            while e.is_negative() {
                x -= 1;
                e += &av;
                steps += 1;
            }
            while e >= av {
                x += 1;
                e -= &av;
                steps += 1;
            }
            Ok(Inverse { x: ray_at(x, Grain::new(-(p as i32)))?, residual: ray_at(e, Grain::new(-(p as i32)))?, end, certified: Width::new(p), steps })
        }
        End::Bottom(w) => {
            if a.grain().lo() != 0 || av.is_even() {
                return refuse("an inverse modulo 2^w of a value that is not odd at grain one");
            }
            let w = *w;
            let m = BigInt::one() << w as usize;
            // Hensel from the bottom, carrying the residual: x₀ = (3a) ⊕ 2 is right modulo 2⁵ (every odd residue
            // mod 32), E = 1 − a x, and X′ = X(1 + E), E′ = E² (since 1 − aX(1 + E) = E²): two independent
            // products a step, a x never recomputed, E's valuation 5, 10, 20, 40, 80, so four steps reach 64 places
            // (the record's §5.1; theory, November 8). E is the certificate: it vanishes modulo 2^w.
            let mut x = ((&av * 3u32) ^ BigInt::from(2)).mod_floor(&m);
            let mut e = (BigInt::one() - &av * &x).mod_floor(&m);
            let mut certified = w.min(5);
            let mut steps = 0u32;
            while certified < w {
                x = (&x * (BigInt::one() + &e)).mod_floor(&m);
                e = (&e * &e).mod_floor(&m);
                certified = (2 * certified).min(w);
                steps += 1;
            }
            if !e.is_zero() || !(&av * &x - BigInt::one()).mod_floor(&m).is_zero() {
                return refuse("a bottom inverse whose residual does not vanish (a law defect)");
            }
            let xw = Width::new(w);
            Ok(Inverse { x: Value::of(Grain::new(0), xw, Section::Low, Digits::from_big(x))?, residual: Value::zero(Grain::new(0)), end, certified: xw, steps })
        }
        End::Euclid(modulus) => {
            let m = modulus.digits.big();
            if a.grain().lo() != 0 || modulus.grain().lo() != 0 || !m.is_positive() {
                return refuse("an inverse modulo m of values not at grain one, or a modulus not positive");
            }
            let x = mod_inverse(&av.mod_floor(&m), &m).ok_or(super::NumberError::Refused("a value that shares a factor with its modulus has no inverse"))?;
            let e = (&av * &x - BigInt::one()).mod_floor(&m);
            let w = Width::new(((&m - 1u32).bits() as u32).max(1));
            Ok(Inverse { x: Value::of(Grain::new(0), w, Section::Low, Digits::from_big(x))?, residual: ray_at(e, Grain::new(0))?, end, certified: w, steps: 1 })
        }
        End::Matrix | End::Range => refuse("the matrix and range ends are owed (hnn::chart holds Newton–Schulz until it moves here)"),
    }
}
