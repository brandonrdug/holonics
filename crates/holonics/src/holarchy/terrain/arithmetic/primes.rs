//! **Prime streams: a window's integers as digit cells with a primality cell, or the prime
//! indicator** (the record's §7.3).
//!
//! [definition; agent-inferred] **The layout** ([`PrimeWindow`]). The integers `n ∈ [start, end)`
//! in order. As [`PrimeEmission::Digits`] each is its `L` digit cells in base `b` (zero-padded, in
//! the declared order) and a primality cell, the mark `b` (not prime) or `b + 1` (prime), which also
//! closes the record: alphabet `b + 2`, a record `L + 1` cells. As [`PrimeEmission::Indicator`]
//! each integer is one cell, `1` prime and `0` not, and the base enters only the truth. The digit
//! cells are one odometer's successive readings (the counter, its carry the winding), so every cell
//! of either emission is determined by the cells before it: the stream's own rate is zero.
//!
//! [proved-derived; implemented-exact] **The truth.**
//! - **Each integer** ([`IntegerTruth`]): its factorization and least prime factor (the crate's
//!   trial division), whether it is prime, its leading index `k = ⌊n/b^m⌋` and residue
//!   `r = n mod b^m` for the declared `m` trailing digits, and **the gratings covering it**: each
//!   prime `p ∤ b`, `p < n`, dividing `n`, with its class `k_p(r) = −r (b^m)⁻¹ mod p`
//!   ([`grating_class`]). `p ∣ b^m k + r ⇔ k ≡ k_p(r) mod p` (Lean
//!   `RadixWindowReceiver.grating_on_digit_index`), so a grating is a ring of period `p` on the
//!   leading index, and a prime is a gap of every grating below it. Its **cheap readings**
//!   ([`CheapReading`]): the last digit, the digit sum and the alternating digit sum, congruent to
//!   `n` modulo every divisor of `b`, `b − 1` and `b + 1` respectively (Lean `cheap_faces`).
//! - **The base** ([`CheapFaces`]): `b`, `b − 1` and `b + 1` with their factorizations, the
//!   moduli the three cheap faces read.
//! - **The density read through a face** ([`FaceCode`]): partition the window by `n mod d` for a
//!   declared modulus `d`; the indicator coded at each class's own density costs
//!   `Σ_r |W_r| H(π_r/|W_r|)` bits, exactly, as its form in `log₂ p` (`ratio::surprisal::entropy`).
//!   At `d = 1` it is **the density's code**, the code at a known density `π/n`; a receiver
//!   knowing only how many primes the window holds pays `log₂ C(n, π)`, which is smaller. At
//!   `d = b` it is the trailing face's (the last digit). Neither is the stream's
//!   rate, which is zero; they place a receiver's code between the density and the determined.

use std::collections::BTreeMap;

use num_bigint::BigUint;

use super::super::{TerrainError, refuse};
use super::{
    DigitOrder, Factorization, check_base, checked_power, digit_count, digits, factorization,
};
use crate::ratio::Rat;
use crate::ratio::primality::is_prime;
use crate::ratio::ring::{ExactRing, ModularWords};
use crate::ratio::surprisal::{Support, SymbolicSurprisal, entropy};

/// [definition] **The emission** (module header): digit cells with a primality cell, or the
/// indicator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrimeEmission {
    Digits,
    Indicator,
}

/// [definition] **A cell's class** (module header): a digit, or the primality cell (every cell of
/// the indicator).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PrimeCell {
    Digit,
    Primality,
}

/// [definition] **A grating covering an integer** (module header): the prime and its class on the
/// leading index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GratingCover {
    pub prime: u64,
    pub class: u64,
}

/// [definition] **An integer's cheap readings** (module header): the last digit `n mod b`, the
/// digit sum and the alternating digit sum `Σ_i (−1)^i d_i` (from the least significant digit).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheapReading {
    pub last: u64,
    pub sum: u64,
    pub alternating: i64,
}

/// [definition] **The base's cheap faces** (module header): the factorizations of `b` (read by the
/// last digit), `b − 1` (the digit sum) and `b + 1` (the alternating sum).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheapFaces {
    pub base: u64,
    pub last: Factorization,
    pub sum: Factorization,
    pub alternating: Factorization,
}

impl CheapFaces {
    /// **The cheap faces of base `b`** (module header).
    pub fn of(base: u64) -> Result<Self, TerrainError> {
        check_base(base)?;
        let factored = |value: u64| factorization(value).expect("a positive modulus");
        Ok(Self {
            base,
            last: factored(base),
            sum: factored(base - 1),
            alternating: factored(base + 1),
        })
    }

    /// The primes each face reads: `[last digit, digit sum, alternating sum]`.
    pub fn primes(&self) -> [Vec<u64>; 3] {
        let primes = |factors: &[(u64, u32)]| factors.iter().map(|(p, _)| *p).collect();
        [
            primes(&self.last),
            primes(&self.sum),
            primes(&self.alternating),
        ]
    }
}

/// `x^e` in `ℤ/p`, by exact square-and-multiply in the ring.
fn power(ring: &ModularWords, base: u64, mut exponent: u64) -> u64 {
    let mut standing = ring.canonical(base);
    let mut accumulated = ring.canonical(1);
    while exponent > 0 {
        if exponent & 1 == 1 {
            accumulated = ring.mul(accumulated, standing).expect("a total ring");
        }
        standing = ring.mul(standing, standing).expect("a total ring");
        exponent >>= 1;
    }
    accumulated
}

/// **The grating's class** `k_p(r) = −r (b^m)⁻¹ mod p` on the leading index of the integers whose
/// `m` trailing digits read `r` (Lean `RadixWindowReceiver.grating_on_digit_index`): `p` divides
/// `b^m k + r` exactly when `k ≡ k_p(r) mod p`. The inverse is Fermat's, `(b^m)^(p−2)` in `ℤ/p`.
/// `None` when `p` is not a prime or divides `b` (a prime of the base is read by the trailing face,
/// not a grating).
pub fn grating_class(base: u64, trailing: usize, residue: u64, prime: u64) -> Option<u64> {
    if !is_prime(prime) || base.is_multiple_of(prime) {
        return None;
    }
    let ring = ModularWords::new(prime).expect("a prime modulus");
    let unit = power(&ring, base, trailing as u64);
    let inverse = power(&ring, unit, prime - 2);
    let negated = (prime - ring.canonical(residue)) % prime;
    ring.mul(negated, inverse)
}

/// [definition] **An integer's exact truth** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntegerTruth {
    pub value: u64,
    pub factors: Option<Factorization>,
    pub least_factor: Option<u64>,
    pub prime: bool,
    pub leading: u64,
    pub residue: u64,
    pub gratings: Vec<GratingCover>,
    pub cheap: CheapReading,
}

impl IntegerTruth {
    /// **The truth of `n` in base `b` with `m` trailing digits** (module header). Refused when the
    /// base holds fewer than two digits or `b^m` leaves the machine word.
    pub fn of(value: u64, base: u64, trailing: usize) -> Result<Self, TerrainError> {
        check_base(base)?;
        let unit = checked_power(base, trailing)?;
        let (leading, residue) = (value / unit, value % unit);
        let factors = factorization(value);
        let least_factor = factors
            .as_ref()
            .and_then(|factors| factors.first().map(|(p, _)| *p));
        let prime = factors.as_deref() == Some(&[(value, 1)][..]);
        let gratings = factors
            .iter()
            .flatten()
            .filter(|(p, _)| *p < value)
            .filter_map(|(p, _)| {
                grating_class(base, trailing, residue, *p)
                    .map(|class| GratingCover { prime: *p, class })
            })
            .collect();
        let word = digits(value, base, digit_count(value, base))?;
        let alternating = word
            .iter()
            .enumerate()
            .map(|(i, d)| if i % 2 == 0 { *d as i64 } else { -(*d as i64) })
            .sum();
        Ok(Self {
            value,
            factors,
            least_factor,
            prime,
            leading,
            residue,
            gratings,
            cheap: CheapReading {
                last: value % base,
                sum: word.iter().sum(),
                alternating,
            },
        })
    }
}

/// [definition] **A residue class of the window**: its residue, its integers and its primes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassCount {
    pub residue: u64,
    pub integers: u64,
    pub primes: u64,
}

/// [definition] **The density read through the face `n mod d`** (module header): the classes and
/// the code `Σ_r |W_r| H(π_r/|W_r|)` bits as its exact form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaceCode {
    pub modulus: u64,
    pub classes: Vec<ClassCount>,
    pub code: SymbolicSurprisal,
}

/// [definition] **A prime window** (module header): base `b`, the window `[start, end)`, `L`
/// digits an integer (`end ≤ b^L`), the `m` trailing digits fixing the gratings' leading index,
/// the digit order and the emission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimeWindow {
    pub base: u64,
    pub start: u64,
    pub end: u64,
    pub digits: usize,
    pub trailing: usize,
    pub order: DigitOrder,
    pub emission: PrimeEmission,
}

impl PrimeWindow {
    fn check(&self) -> Result<(), TerrainError> {
        check_base(self.base)?;
        if self.start >= self.end {
            return Err(refuse("a prime window", "it needs start < end"));
        }
        if checked_power(self.base, self.digits).map_or(true, |range| range < self.end) {
            return Err(refuse(
                "a prime window",
                "its integers need end ≤ b^L within the machine word",
            ));
        }
        checked_power(self.base, self.trailing)?;
        Ok(())
    }

    /// The mark `b`: not prime.
    pub fn composite_mark(&self) -> usize {
        self.base as usize
    }

    /// The mark `b + 1`: prime.
    pub fn prime_mark(&self) -> usize {
        self.base as usize + 1
    }

    /// The alphabet: `b + 2` for the digit cells, `2` for the indicator.
    pub fn alphabet(&self) -> usize {
        match self.emission {
            PrimeEmission::Digits => self.base as usize + 2,
            PrimeEmission::Indicator => 2,
        }
    }

    /// A record's cells: `L + 1`, or one.
    pub fn record_length(&self) -> usize {
        match self.emission {
            PrimeEmission::Digits => self.digits + 1,
            PrimeEmission::Indicator => 1,
        }
    }

    /// **The cells** (module header).
    pub fn emit(&self) -> Result<Vec<usize>, TerrainError> {
        self.check()?;
        let mut cells = Vec::new();
        for n in self.start..self.end {
            let prime = is_prime(n);
            match self.emission {
                PrimeEmission::Indicator => cells.push(usize::from(prime)),
                PrimeEmission::Digits => {
                    let word = digits(n, self.base, self.digits)?;
                    cells.extend(self.order.arrange(&word).into_iter().map(|d| d as usize));
                    cells.push(if prime {
                        self.prime_mark()
                    } else {
                        self.composite_mark()
                    });
                }
            }
        }
        Ok(cells)
    }

    /// **Each cell's class** (module header), in emission order.
    pub fn classes(&self) -> Vec<PrimeCell> {
        let length = self.record_length();
        (0..(self.end.saturating_sub(self.start) as usize) * length)
            .map(|position| {
                if position % length == length - 1 {
                    PrimeCell::Primality
                } else {
                    PrimeCell::Digit
                }
            })
            .collect()
    }

    /// **Every integer's exact truth** (module header).
    pub fn truth(&self) -> Result<Vec<IntegerTruth>, TerrainError> {
        self.check()?;
        (self.start..self.end)
            .map(|n| IntegerTruth::of(n, self.base, self.trailing))
            .collect()
    }

    /// The base's cheap faces.
    pub fn cheap_faces(&self) -> Result<CheapFaces, TerrainError> {
        CheapFaces::of(self.base)
    }

    /// **The density read through the face `n mod d`** (module header), `d ≥ 1`.
    pub fn face_code(&self, modulus: u64) -> Result<FaceCode, TerrainError> {
        self.check()?;
        if modulus == 0 {
            return Err(refuse("a face's modulus", "it needs d ≥ 1"));
        }
        let mut counts: BTreeMap<u64, (u64, u64)> = BTreeMap::new();
        for n in self.start..self.end {
            let entry = counts.entry(n % modulus).or_insert((0, 0));
            entry.0 += 1;
            entry.1 += u64::from(is_prime(n));
        }
        let mut code = SymbolicSurprisal::zero();
        let mut classes = Vec::with_capacity(counts.len());
        for (residue, (integers, primes)) in counts {
            let population: BTreeMap<u64, BigUint> = [(0, integers - primes), (1, primes)]
                .into_iter()
                .filter(|(_, count)| *count > 0)
                .map(|(event, count)| (event, BigUint::from(count)))
                .collect();
            let Support::Supported(rate) = entropy(&population)? else {
                return Err(refuse(
                    "a residue class's density",
                    "its own population supports every event it holds",
                ));
            };
            code = code.plus(&rate.scaled(&Rat::from_integer(integers.into())));
            classes.push(ClassCount {
                residue,
                integers,
                primes,
            });
        }
        Ok(FaceCode {
            modulus,
            classes,
            code,
        })
    }
}
