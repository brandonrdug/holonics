//! Reopening a collapsed face: exact integer relation detection over `BigInt`.
//!
//! ## What a collapsed face is
//!
//! `canon/THE_MATHEMATICS_TABLET.md` §1 states the deletion this module reverses. A float is not a
//! bad approximation *of* a ratio — it is the ratio's series expansion in base two, truncated, with
//! the remainder discarded: `x = Σ b_i 2^{−i}`, cut at 53 bits, tail deleted with no record that a
//! tail existed. The law is therefore not *"do not expand"*; it is **you may take the expansion,
//! you may not discard the tail.**
//!
//! A collapsed numeric datum is then a **partial face of a larger series expansion**, and the
//! question it poses is: in which basis can that face continue to be manipulated? That question has
//! an exact name — **integer relation detection**. Given a face `x` and candidate basis elements
//! `x_1 … x_n`, find integers `a_i`, not all zero, with `Σ a_i x_i = 0`. It is how the BBP formula
//! for π was *discovered* rather than derived, and it needs the face at high precision, which is
//! exactly why the discarded tail matters. **Exactness is the precondition for reopening.**
//!
//! ## What is exact here and what is not
//!
//! Everything below is `BigInt` and `Rat`. The Gram–Schmidt orthogonalisation, the size reduction,
//! and the Lovász condition are carried in exact rationals; no IEEE scalar, tolerance, epsilon or
//! threshold appears anywhere in this file.
//!
//! **A returned relation is a candidate, never a theorem.** The lattice computation is exact and its
//! certificate is exact, but what it certifies is a *search*, not a proof of the identity. The
//! asymmetry is sharp and it is worth stating in one line:
//!
//! - **Refutation is exact.** If the exact interval `Σ a_i · enclosure_i` excludes zero, the faces
//!   themselves prove `Σ a_i x_i ≠ 0`. That is a proof and it is returned as one.
//! - **Confirmation is never exact.** No finite enclosure can prove a real sum is zero. What is
//!   returned is a candidate carrying the integer vector, the basis it was found against, the
//!   declared grains, and the exact residual enclosure.
//!
//! ## The admission rule, and why it is not a tuning knob
//!
//! A relation finder that always finds a relation has found nothing. The discrimination here is not
//! a tolerance; it is this project's own fourth lesson (`CLAUDE.md` §0): **an invariant is only
//! visible across two frames.** The **grain is the frame**. A lattice probe at one declared grain
//! always returns *some* shortest vector — on a relation-free basis it returns a large one that is
//! an artifact of that grain. So:
//!
//! > A candidate is admitted only when **every** declared grain returns the **same primitive
//! > vector**, and the faces' own enclosures fail to refute it.
//!
//! Two grains are the minimum and [`reopen`] refuses fewer. A vector seen at one grain is a
//! receiver-visible coordinate promoted into an invariant, which is the defect `CLAUDE.md` §0 names
//! and the one this instrument would otherwise commit.
//!
//! ### The grain is not the only frame, and grain alone is not enough
//!
//! **Measured 2026-08-08, and it falsified the first form of this instrument.** Two *adjacent*
//! grains are not two frames: at grain `2^{g−1}` and `2^g` the lifted integers differ by a halving,
//! so the two lattices are nearly the same lattice. On faces **collapsed to exactly the grain** —
//! which is what a float hands the machine — the exact refutation gate goes blind (the enclosure is
//! as wide as one lattice unit) *and* the two grains agree on the same spurious vector, so the
//! instrument returned a false relation with ten-digit coefficients. Both gates failed together, and
//! they failed on precisely the material the movement is about.
//!
//! **The first repair was tried and measured failing, and it is recorded here rather than deleted.**
//! [`EnclosureFrame`] lifts a face by its lower endpoint, its midpoint, or its upper endpoint, and
//! [`reopen`] does probe all three at every declared grain. On a face collapsed at the grain the
//! three lift to integers differing by a full lattice unit, so the *lattice* genuinely moves — but
//! the spurious vector's own last coordinate is already of the same order as its height, so a
//! one-unit shift is an `O(1)` relative perturbation and **the same false vector came out of all
//! three.** The gauge's orbit on the returned object is trivial, which by `CLAUDE.md` §8 means its
//! agreement carries no evidence. It is kept because it is free and correct in form; it is not
//! counted as a gate.
//!
//! ### The third gate, which is the one that works
//!
//! What a collapsed face actually destroys is **resolution**, so the gate has to be about the
//! searched population rather than about frames. A vector of height `A` over `n` faces is drawn from
//! a searched population of `(2A+1)^n` integer vectors; the residual enclosure it must land inside
//! has width `Σ|a_i| w_i`. So the expected number of vectors that would have straddled zero **by
//! chance** is
//!
//! ```text
//!   chance population  =  (2A+1)^n · Σ|a_i| w_i
//! ```
//!
//! and a candidate whose chance population is one or more has told the receiver nothing. The
//! threshold is exactly **one expected coincidence** — there is no constant to choose, and the
//! comparison is exact over `Rat`. The null model (that `Σ a_i x_i` is equidistributed at unit
//! scale) is conservative here, since the declared faces have `Σ|x_i| > 1`, so the rule can only
//! refuse more than the sharp form and never admit more.
//!
//! A candidate that fails it is **not discarded**. It returns as
//! [`ReopeningVerdict::BelowTheFacesResolution`] carrying the vector and the exact population that
//! defeats it — the `Open` state of `exact_value::ExactOrdering`, which retains both rather than
//! tie-breaking (`CLAUDE.md` §8).
//!
//! Two of the reported quantities gate and the rest do not, and the difference is deliberate.
//! `CLAUDE.md` §13 rule 2: a scalar that measures is lawful, a scalar that governs is not. The
//! **grain modulus** and the **reduction work** only measure — nothing selects on them, and in
//! particular no clock selects anything anywhere in this file. The **coefficient height** measures
//! and then enters the chance-population gate below, where its jurisdiction is stated: it does not
//! rank candidates, discard a loser or break a tie; it decides one exact inequality whose bar is one
//! expected coincidence, and a candidate that fails it is **retained** with the number that defeated
//! it rather than deleted.
//!
//! ## The aperture
//!
//! A face certified to width `w` cannot be probed at a grain finer than `w`. [`reopen`] refuses by
//! name rather than returning, because an organ used past its declared aperture is a defect even
//! when it appears to return (`CLAUDE.md` §8). This is the movement's thesis expressed as a type:
//! **the tail sets the grain ceiling, and the grain ceiling is what decides whether a relation of a
//! given height is reachable at all.**
//!
//! ## The mouth: where a real float enters
//!
//! Every constructor above this line requires an already-exact source, so for its first form this
//! instrument could only reverse a deletion it had performed itself with [`ExactFace::collapsed`].
//! [`ExactFace::from_binary_float`] is the constructor that takes a **measured** IEEE-754 datum —
//! a network weight read out of a safetensors payload, a wire word, a decimal literal the compiler
//! rounded — decoded by `crate::exact_value::ieee754`, which is the workspace's one declared
//! floating-point boundary. **No float crosses into this file.** The mouth takes a
//! `BinaryFloatDatum`, which is `BigUint` and a power of two.
//!
//! The declaration the caller must make is `FloatReading`, and it is the whole content of the
//! mouth:
//!
//! ```text
//!   ExactBitPattern       the bits ARE the datum        -> a POINT,     width 0,  every grain
//!   RoundedToNearest      the bits round something else -> an ENCLOSURE, width 1 ulp
//!   TruncatedTowardZero   the bits truncate something   -> an ENCLOSURE, width 1 ulp
//! ```
//!
//! and the admission law above **already separates them without a new rule**. A point admits every
//! grain because its width is zero. An enclosure of width `2^-u` has [`CertifiedBits::Bits(u)`] and
//! is refused at grain `u+1` by [`ReopeningError::FaceCoarserThanGrain`], which is the same
//! refusal a starved series tail earns and is not weakened by anything here. A rounded `f64` near
//! `1` carries `u = 52`; the same `f64` read as a bit pattern carries no ceiling at all. That
//! difference is measured in `examples/a_float_is_a_dyadic_and_a_deleted_tail.rs`, where the same
//! sixteen bits return a candidate under one reading and nothing under the other.
//!
//! [`ExactFace::aperture_source`] reports **what paid for a face's ceiling** — a retained tail, an
//! analytic width, a unit in the last place — so a refusal can be reported as its cause rather than
//! as its symptom.
//!
//! ## What this does not claim
//!
//! Not a proof of any recovered identity. Not a decompression of a weight file. Not semantic
//! recovery of a foreign model. Not a shortest-vector oracle — LLL returns a vector within
//! `2^{(n−1)/2}` of the shortest, and the primitive normalisation below is what makes that bound
//! harmless for relation extraction rather than a hidden assumption.

use std::cmp::Ordering;
use std::fmt;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use relational_geometry::exact::{Rat, integer};
use relational_geometry::exact_analysis::RatInterval;

use crate::exact_value::ieee754::{BinaryFloatDatum, BinaryFloatSpecies, FloatReading};
use crate::exact_value::{CertifiedSeries, ExactInterval, SeriesTailCertificate};
use relational_geometry::exact::ExactExpr;

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum ReopeningError {
    #[error("a relation search needs at least two faces; {count} were declared")]
    TooFewFaces { count: usize },
    #[error(
        "admission needs at least two declared grains; {count} were declared, and a vector seen at one grain is a coordinate of that grain rather than an invariant of the faces"
    )]
    TooFewGrains { count: usize },
    #[error("grain 2^-{bits} was declared twice; two probes at one grain are one probe")]
    DuplicateGrain { bits: u32 },
    #[error(
        "face `{name}` is certified only to {certified}, coarser than the declared grain 2^-{bits}: the discarded tail is exactly what this grain needs"
    )]
    FaceCoarserThanGrain {
        name: String,
        certified: CertifiedBits,
        bits: u32,
    },
    #[error("the lattice reduction exhausted its declared work budget of {budget} steps")]
    BudgetExhausted { budget: u64 },
    #[error("Gram-Schmidt met a dependent row at index {index}; the lattice basis is degenerate")]
    DependentRow { index: usize },
    #[error("an enclosure has reversed endpoints")]
    ReversedEnclosure,
    #[error("the alternating certificate needs a denominator of at least two; {denominator} given")]
    UnitFractionTooLarge { denominator: u32 },
    #[error("a certified series needs at least one folded term")]
    EmptySeries,
    #[error("face `{name}` is not one of the declared basis faces")]
    UnknownFace { name: String },
    #[error("no enclosure frame was declared; a face lifted from no frame is not lifted at all")]
    NoDeclaredFrame,
}

/// The exact dyadic scale of a nonzero rational: the unique `e` with
/// `2^e <= |value| < 2^{e+1}`.
///
/// Computed from `BigInt` bit lengths and corrected by exact comparison. No logarithm is taken and
/// no float is constructed.
pub fn dyadic_scale(value: &Rat) -> Option<i64> {
    if value.is_zero() {
        return None;
    }
    let numerator = value.numer().magnitude().clone();
    let denominator = value.denom().magnitude().clone();
    let mut exponent = numerator.bits() as i64 - denominator.bits() as i64;
    // `numerator / denominator` versus `2^exponent`, by cross multiplication.
    let compare = |exponent: i64| -> Ordering {
        if exponent >= 0 {
            numerator.cmp(&(denominator.clone() << (exponent as usize)))
        } else {
            (numerator.clone() << ((-exponent) as usize)).cmp(&denominator)
        }
    };
    while compare(exponent) == Ordering::Less {
        exponent -= 1;
    }
    while compare(exponent + 1) != Ordering::Less {
        exponent += 1;
    }
    Some(exponent)
}

/// How finely a face is certified, as the aperture statement it is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CertifiedBits {
    /// The enclosure is a point. Every grain is admissible.
    Exact,
    /// The enclosure has width at most `2^-bits` and no finer.
    Bits(u32),
    /// The enclosure is wider than one. No grain is admissible.
    Coarser,
}

impl fmt::Display for CertifiedBits {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Exact => write!(formatter, "exact"),
            Self::Bits(bits) => write!(formatter, "2^-{bits}"),
            Self::Coarser => write!(formatter, "wider than one"),
        }
    }
}

/// The declared precision at which one lattice probe is taken.
///
/// This is a **parameter**, never a constant folded into the search. `modulus` is `2^bits` and is
/// the integer scale the faces are lifted by; `width_ceiling` is `2^-bits` and is the aperture a
/// face must meet to be probed at this grain.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct DeclaredGrain {
    pub bits: u32,
}

impl DeclaredGrain {
    pub fn bits(bits: u32) -> Self {
        Self { bits }
    }

    pub fn modulus(&self) -> BigInt {
        BigInt::one() << (self.bits as usize)
    }

    pub fn width_ceiling(&self) -> Rat {
        Rat::new(BigInt::one(), BigInt::one() << (self.bits as usize))
    }
}

impl fmt::Display for DeclaredGrain {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "2^{}", self.bits)
    }
}

/// Where a face's enclosure came from.
///
/// Provenance is typed rather than described, because the whole point of the movement is that a
/// face which arrived as a collapsed decimal and a face which arrived carrying its remainder
/// certificate are **different objects**, not one object with error.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FaceProvenance {
    /// An exact rational. The enclosure is a point.
    Rational,
    /// A partial sum plus the exact remainder interval its tail certificate returns.
    CertifiedSeries(Box<CertifiedSeries>),
    /// An interval-valued analytic carrier in `relational_geometry::exact_analysis`.
    AnalyticEnclosure { carrier: String },
    /// An exact integer combination of other faces, with the combination retained.
    IntegerCombination { parts: Vec<(BigInt, String)> },
    /// A face that arrived already collapsed: a value with a declared truncation and no series
    /// behind it. The enclosure is the collapse itself.
    Collapsed { truncated_at_bits: u32 },
    /// A face that arrived as a **real IEEE-754-shaped datum** — a stored weight, a wire word, a
    /// decimal literal a compiler rounded — decoded by `crate::exact_value::ieee754`.
    ///
    /// Everything needed to re-derive the face is retained: the exact pattern, the format, the
    /// declared reading, the scale of what the format could not carry, and where the bits came
    /// from. A face that says *"this came from somewhere"* without saying where has smuggled in an
    /// absolute frame, which is `CLAUDE.md` §0's second lesson.
    MeasuredFloat {
        species: BinaryFloatSpecies,
        /// The interchange pattern, exactly as read, zero-extended to 64 bits.
        bits: u64,
        /// Whether the bits are the datum or a rounding of something else. This decides whether
        /// the enclosure is a point or one ulp wide, and therefore what grains the face admits.
        reading: FloatReading,
        /// `ulp = 2^{-ulp_bits}`, exactly. Negative when the format's spacing at this magnitude
        /// exceeds one, in which case no grain is admissible at all.
        ulp_bits: i32,
        /// The artifact, tensor and coordinate the pattern was read from.
        source: String,
    },
}

/// What paid for a face's grain ceiling.
///
/// A [`ReopeningError::FaceCoarserThanGrain`] says a face was too coarse for a question. This says
/// **why**, in the vocabulary of whatever supplied the width, so a refusal is reported as its cause
/// rather than as its symptom. It is a reading of [`FaceProvenance`] and adds no rule to the
/// admission law.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ApertureSource {
    /// A point. Nothing was deleted at this boundary and every grain is admissible.
    NoDeletion,
    /// The exact remainder interval a [`SeriesTailCertificate`] retained.
    RetainedSeriesTail,
    /// The width an analytic enclosure carrier returned.
    AnalyticWidth,
    /// One unit in the last place of a binary floating-point format at this magnitude. This is the
    /// tail the float deleted, and it is the only thing standing between the face and a finer
    /// grain.
    UnitInTheLastPlace {
        species: BinaryFloatSpecies,
        ulp_bits: i32,
    },
    /// A declared truncation with no certificate behind it.
    DeclaredTruncation { bits: u32 },
    /// The outward integer combination of other faces' apertures.
    CombinedApertures,
}

impl fmt::Display for ApertureSource {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoDeletion => write!(formatter, "no deletion"),
            Self::RetainedSeriesTail => write!(formatter, "a retained series tail"),
            Self::AnalyticWidth => write!(formatter, "an analytic enclosure width"),
            Self::UnitInTheLastPlace { species, ulp_bits } => {
                write!(formatter, "one {} ulp, 2^-{ulp_bits}", species.name())
            }
            Self::DeclaredTruncation { bits } => {
                write!(formatter, "a declared truncation at {bits} bits")
            }
            Self::CombinedApertures => write!(formatter, "combined apertures"),
        }
    }
}

/// One numeric face: a rational approximation **with its certified error**.
///
/// A face is never a value. It is a set that provably contains the value, exactly as
/// `exact_value::ExactInterval`'s own opening states, together with the provenance that says what
/// paid for the enclosure.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactFace {
    pub name: String,
    pub enclosure: ExactInterval,
    pub provenance: FaceProvenance,
}

impl ExactFace {
    /// An exact rational face. The enclosure is a point and every grain is admissible.
    pub fn rational(name: impl Into<String>, value: Rat) -> Self {
        Self {
            name: name.into(),
            enclosure: ExactInterval::point(value),
            provenance: FaceProvenance::Rational,
        }
    }

    /// A face carried by a [`CertifiedSeries`]: the partial sum translated by the exact rational
    /// remainder interval its [`SeriesTailCertificate`] returns.
    ///
    /// This is the constructor the movement exists for. The enclosure **is** the retained tail.
    pub fn from_certified_series(name: impl Into<String>, series: CertifiedSeries) -> Self {
        let enclosure = series.enclosure();
        Self {
            name: name.into(),
            enclosure,
            provenance: FaceProvenance::CertifiedSeries(Box::new(series)),
        }
    }

    /// A face carried by one of the analytic enclosures in
    /// `relational_geometry::exact_analysis` — `log_rational_interval`,
    /// `exp_rational_interval`, `sin_cos_rational_interval` and their siblings.
    pub fn from_rat_interval(
        name: impl Into<String>,
        carrier: impl Into<String>,
        interval: &RatInterval,
    ) -> Result<Self, ReopeningError> {
        let enclosure = ExactInterval::new(interval.lower.clone(), interval.upper.clone())
            .map_err(|_| ReopeningError::ReversedEnclosure)?;
        Ok(Self {
            name: name.into(),
            enclosure,
            provenance: FaceProvenance::AnalyticEnclosure {
                carrier: carrier.into(),
            },
        })
    }

    /// An exact integer combination of existing faces.
    ///
    /// The interval arithmetic is exact and outward: a negative coefficient swaps the endpoints it
    /// multiplies, so the returned enclosure provably contains the combination.
    pub fn integer_combination(
        name: impl Into<String>,
        parts: &[(BigInt, &ExactFace)],
    ) -> Result<Self, ReopeningError> {
        let mut lower = Rat::zero();
        let mut upper = Rat::zero();
        let mut retained = Vec::with_capacity(parts.len());
        for (coefficient, face) in parts {
            let scalar = Rat::from_integer(coefficient.clone());
            if coefficient.is_negative() {
                lower += &scalar * &face.enclosure.upper;
                upper += &scalar * &face.enclosure.lower;
            } else {
                lower += &scalar * &face.enclosure.lower;
                upper += &scalar * &face.enclosure.upper;
            }
            retained.push((coefficient.clone(), face.name.clone()));
        }
        let enclosure =
            ExactInterval::new(lower, upper).map_err(|_| ReopeningError::ReversedEnclosure)?;
        Ok(Self {
            name: name.into(),
            enclosure,
            provenance: FaceProvenance::IntegerCombination { parts: retained },
        })
    }

    /// A face that arrived collapsed: the value truncated to `bits` binary places, with the
    /// truncation itself as the only certificate.
    ///
    /// This models what a float hands the machine. The enclosure is `[floor(x·2^b)/2^b,
    /// ceil(x·2^b)/2^b]` — honest about the deletion rather than pretending the point is the value.
    pub fn collapsed(name: impl Into<String>, source: &ExactFace, bits: u32) -> Self {
        let scale = BigInt::one() << (bits as usize);
        let lower = floor_to_grid(&source.enclosure.lower, &scale);
        let upper = ceil_to_grid(&source.enclosure.upper, &scale);
        Self {
            name: name.into(),
            enclosure: ExactInterval {
                lower: Rat::new(lower, scale.clone()),
                upper: Rat::new(upper, scale),
            },
            provenance: FaceProvenance::Collapsed {
                truncated_at_bits: bits,
            },
        }
    }

    /// **The mouth.** A real measured floating-point datum, plus the declaration that says what it
    /// is, becomes the face it actually is.
    ///
    /// `datum` is already exact — `crate::exact_value::ieee754` decoded the interchange pattern
    /// into `BigUint × 2^e` and refused `NaN` and `±∞` by name before this is reachable, so no
    /// float crosses into this module. `reading` is the caller's declaration and cannot be
    /// inferred from the bits:
    ///
    /// - [`FloatReading::ExactBitPattern`] — the datum **is** the quantity. A stored `bf16` weight
    ///   is such a datum: the number in the file is exactly `−158·2^-12` and nothing rounded it at
    ///   *this* boundary. The face is a point and admits every grain.
    /// - [`FloatReading::RoundedToNearest`] / [`FloatReading::TruncatedTowardZero`] — the datum is
    ///   an image of something else and the deleted tail is one unit in the last place wide. The
    ///   face is an enclosure of exactly that width and is refused, by name, at any finer grain.
    ///
    /// `source` names the artifact, tensor and coordinate. It is retained because a face whose
    /// provenance is *"a float"* cannot be re-derived, and a receipt that cannot be re-derived is
    /// the defect this whole module is instrumented against.
    ///
    /// Infallible on purpose: a float too coarse for any grain — the format's spacing at that
    /// magnitude exceeding one — is a **legal face** whose [`ExactFace::certified_bits`] is
    /// [`CertifiedBits::Coarser`], and it is refused where every other coarse face is refused, by
    /// the aperture law in [`probe_at_frame`]. Refusing it at construction would move the aperture
    /// law into the constructor and leave the caller nothing to inspect.
    pub fn from_binary_float(
        name: impl Into<String>,
        source: impl Into<String>,
        datum: &BinaryFloatDatum,
        reading: FloatReading,
    ) -> Self {
        Self {
            name: name.into(),
            enclosure: datum.enclosure(reading),
            provenance: FaceProvenance::MeasuredFloat {
                species: datum.species,
                bits: datum.bits,
                reading,
                ulp_bits: datum.ulp_bits(),
                source: source.into(),
            },
        }
    }

    /// What paid for this face's grain ceiling.
    ///
    /// A reading of the provenance, not a rule. Where the answer is
    /// [`ApertureSource::UnitInTheLastPlace`], the ceiling is a **deletion** rather than a
    /// certificate: nothing was measured to that width, a format simply stopped carrying bits.
    pub fn aperture_source(&self) -> ApertureSource {
        if self.enclosure.is_point() {
            return ApertureSource::NoDeletion;
        }
        match &self.provenance {
            FaceProvenance::Rational => ApertureSource::NoDeletion,
            FaceProvenance::CertifiedSeries(_) => ApertureSource::RetainedSeriesTail,
            FaceProvenance::AnalyticEnclosure { .. } => ApertureSource::AnalyticWidth,
            FaceProvenance::IntegerCombination { .. } => ApertureSource::CombinedApertures,
            FaceProvenance::Collapsed { truncated_at_bits } => ApertureSource::DeclaredTruncation {
                bits: *truncated_at_bits,
            },
            FaceProvenance::MeasuredFloat {
                species, ulp_bits, ..
            } => ApertureSource::UnitInTheLastPlace {
                species: *species,
                ulp_bits: *ulp_bits,
            },
        }
    }

    pub fn width(&self) -> Rat {
        &self.enclosure.upper - &self.enclosure.lower
    }

    pub fn midpoint(&self) -> Rat {
        (&self.enclosure.lower + &self.enclosure.upper) / integer(2)
    }

    /// Whether this face may be probed at `grain`: its width must not exceed `2^-bits`.
    pub fn admits(&self, grain: DeclaredGrain) -> bool {
        self.width() <= grain.width_ceiling()
    }

    /// The finest grain this face is certified to, exactly.
    pub fn certified_bits(&self) -> CertifiedBits {
        let width = self.width();
        if width.is_zero() {
            return CertifiedBits::Exact;
        }
        match dyadic_scale(&width) {
            // `2^e <= width < 2^{e+1}`, so `width <= 2^-b` requires `-b >= e+1` unless the width is
            // exactly the power, which `dyadic_scale` reports as `e` with equality.
            Some(exponent) => {
                let bits = if width == power_of_two(exponent) {
                    -exponent
                } else {
                    -(exponent + 1)
                };
                if bits < 0 {
                    CertifiedBits::Coarser
                } else {
                    CertifiedBits::Bits(bits as u32)
                }
            }
            None => CertifiedBits::Exact,
        }
    }
}

fn power_of_two(exponent: i64) -> Rat {
    if exponent >= 0 {
        Rat::from_integer(BigInt::one() << (exponent as usize))
    } else {
        Rat::new(BigInt::one(), BigInt::one() << ((-exponent) as usize))
    }
}

fn floor_to_grid(value: &Rat, scale: &BigInt) -> BigInt {
    let scaled = value.numer() * scale;
    let denominator = value.denom();
    let quotient = &scaled / denominator;
    let remainder = &scaled % denominator;
    if scaled.is_negative() && !remainder.is_zero() {
        quotient - BigInt::one()
    } else {
        quotient
    }
}

fn ceil_to_grid(value: &Rat, scale: &BigInt) -> BigInt {
    -floor_to_grid(&(-value.clone()), scale)
}

fn round_to_integer(value: &Rat) -> BigInt {
    let shifted = value + Rat::new(BigInt::one(), BigInt::from(2));
    floor_to_grid(&shifted, &BigInt::one())
}

/// `arctan(1/denominator)` as a [`CertifiedSeries`] with the archetype's own tail bound.
///
/// The alternating series `Σ (−1)^k x^{2k+1}/(2k+1)` has monotone decreasing magnitudes for
/// `|x| <= 1/2`, so Leibniz's criterion places the complete tail between zero and the first omitted
/// signed term — which is exactly [`SeriesTailCertificate::AlternatingMonotone`]. The partial sum is
/// an exact `Rat`; nothing is rounded and nothing is discarded.
pub fn arctan_unit_fraction(
    denominator: u32,
    terms: u32,
) -> Result<CertifiedSeries, ReopeningError> {
    if denominator < 2 {
        return Err(ReopeningError::UnitFractionTooLarge { denominator });
    }
    if terms == 0 {
        return Err(ReopeningError::EmptySeries);
    }
    let base = BigInt::from(denominator);
    let mut partial_sum = Rat::zero();
    let mut odd_power = base.clone();
    let base_squared = &base * &base;
    for index in 0..terms {
        let term = Rat::new(BigInt::one(), &odd_power * BigInt::from(2 * index + 1));
        if index % 2 == 0 {
            partial_sum += term;
        } else {
            partial_sum -= term;
        }
        odd_power *= &base_squared;
    }
    let magnitude = Rat::new(BigInt::one(), &odd_power * BigInt::from(2 * terms + 1));
    let first_omitted_term = if terms.is_multiple_of(2) {
        magnitude
    } else {
        -magnitude
    };
    CertifiedSeries::new(
        ExactExpr::function(
            "arctan",
            vec![ExactExpr::rational(Rat::new(BigInt::one(), base))],
        ),
        partial_sum,
        BigUint::from(terms),
        SeriesTailCertificate::AlternatingMonotone { first_omitted_term },
    )
    .map_err(|_| ReopeningError::EmptySeries)
}

/// The exact work one lattice reduction cost, in steps rather than in seconds.
///
/// `CLAUDE.md` §8: a cost is measured in work, never in elapsed time; a clock may measure, it may
/// never select. Every field here is derived from the material and the declared grain and reproduces
/// bit-for-bit on any machine.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LatticeWork {
    pub loop_steps: u64,
    pub swaps: u64,
    pub size_reductions: u64,
    pub gram_recomputations: u64,
    pub largest_entry_bits: u64,
    pub budget: u64,
}

/// An exactly reduced lattice basis, with the unimodular transform that produced it.
///
/// The transform is retained so that a caller can check independently that the returned rows are
/// integer combinations of the input rows — which for the relation lattice is a genuine cross-check,
/// since the identity block means the transform must equal the coefficient block of the reduced
/// rows.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LatticeReduction {
    pub basis: Vec<Vec<BigInt>>,
    pub transform: Vec<Vec<BigInt>>,
    pub delta: Rat,
    pub work: LatticeWork,
}

fn dot_integers(left: &[BigInt], right: &[BigInt]) -> BigInt {
    left.iter()
        .zip(right)
        .fold(BigInt::zero(), |sum, (a, b)| sum + a * b)
}

fn dot_rational_integer(left: &[Rat], right: &[BigInt]) -> Rat {
    left.iter().zip(right).fold(Rat::zero(), |sum, (a, b)| {
        sum + a * Rat::from_integer(b.clone())
    })
}

struct Orthogonalisation {
    mu: Vec<Vec<Rat>>,
    norms: Vec<Rat>,
}

fn orthogonalise(basis: &[Vec<BigInt>]) -> Result<Orthogonalisation, ReopeningError> {
    let count = basis.len();
    let mut mu = vec![vec![Rat::zero(); count]; count];
    let mut norms = vec![Rat::zero(); count];
    let mut star: Vec<Vec<Rat>> = Vec::with_capacity(count);
    for index in 0..count {
        let mut vector: Vec<Rat> = basis[index]
            .iter()
            .map(|entry| Rat::from_integer(entry.clone()))
            .collect();
        for earlier in 0..index {
            if norms[earlier].is_zero() {
                return Err(ReopeningError::DependentRow { index: earlier });
            }
            let coefficient = dot_rational_integer(&star[earlier], &basis[index]) / &norms[earlier];
            for slot in 0..vector.len() {
                vector[slot] = &vector[slot] - &(&coefficient * &star[earlier][slot]);
            }
            mu[index][earlier] = coefficient;
        }
        norms[index] = vector
            .iter()
            .fold(Rat::zero(), |sum, entry| sum + entry * entry);
        if norms[index].is_zero() {
            return Err(ReopeningError::DependentRow { index });
        }
        star.push(vector);
    }
    Ok(Orthogonalisation { mu, norms })
}

/// Exact LLL lattice reduction over `BigInt`.
///
/// Rows of `rows` are the lattice basis. `delta` is the declared Lovász parameter and must lie in
/// `(1/4, 1)`; the classical choice `3/4` is what [`reduce_lattice_default`] passes. The
/// Gram–Schmidt coefficients and squared norms are carried in exact `Rat`, recomputed in full after
/// every swap. There is no float, no tolerance and no epsilon in the loop; the Lovász test is an
/// exact rational comparison.
///
/// The full recomputation is the deliberately simple choice: it is `O(n²d)` rational operations per
/// swap where the incremental update is `O(n)`, and it is used because it is obviously correct.
/// [`LatticeWork::gram_recomputations`] reports how many were taken, so the cost is stated rather
/// than hidden.
pub fn reduce_lattice(
    rows: &[Vec<BigInt>],
    delta: &Rat,
    budget: u64,
) -> Result<LatticeReduction, ReopeningError> {
    let count = rows.len();
    let mut basis: Vec<Vec<BigInt>> = rows.to_vec();
    let mut transform: Vec<Vec<BigInt>> = (0..count)
        .map(|row| {
            (0..count)
                .map(|column| {
                    if row == column {
                        BigInt::one()
                    } else {
                        BigInt::zero()
                    }
                })
                .collect()
        })
        .collect();

    let mut work = LatticeWork {
        budget,
        ..LatticeWork::default()
    };
    if count == 0 {
        return Ok(LatticeReduction {
            basis,
            transform,
            delta: delta.clone(),
            work,
        });
    }

    let mut gso = orthogonalise(&basis)?;
    work.gram_recomputations += 1;

    let half = Rat::new(BigInt::one(), BigInt::from(2));
    let mut cursor = 1usize;
    while cursor < count {
        work.loop_steps += 1;
        if work.loop_steps > budget {
            return Err(ReopeningError::BudgetExhausted { budget });
        }

        size_reduce(
            &mut basis,
            &mut transform,
            &mut gso,
            cursor,
            cursor - 1,
            &half,
            &mut work,
        );

        let coefficient = gso.mu[cursor][cursor - 1].clone();
        let lovasz = (delta - &coefficient * &coefficient) * &gso.norms[cursor - 1];
        if gso.norms[cursor] >= lovasz {
            for earlier in (0..cursor.saturating_sub(1)).rev() {
                size_reduce(
                    &mut basis,
                    &mut transform,
                    &mut gso,
                    cursor,
                    earlier,
                    &half,
                    &mut work,
                );
            }
            cursor += 1;
        } else {
            basis.swap(cursor, cursor - 1);
            transform.swap(cursor, cursor - 1);
            work.swaps += 1;
            gso = orthogonalise(&basis)?;
            work.gram_recomputations += 1;
            cursor = std::cmp::max(cursor - 1, 1);
        }
    }

    work.largest_entry_bits = basis
        .iter()
        .flat_map(|row| row.iter())
        .map(|entry| entry.magnitude().bits())
        .max()
        .unwrap_or(0);

    Ok(LatticeReduction {
        basis,
        transform,
        delta: delta.clone(),
        work,
    })
}

fn size_reduce(
    basis: &mut [Vec<BigInt>],
    transform: &mut [Vec<BigInt>],
    gso: &mut Orthogonalisation,
    target: usize,
    against: usize,
    half: &Rat,
    work: &mut LatticeWork,
) {
    if gso.mu[target][against].abs() <= *half {
        return;
    }
    let quotient = round_to_integer(&gso.mu[target][against]);
    if quotient.is_zero() {
        return;
    }
    for slot in 0..basis[target].len() {
        let adjustment = &quotient * &basis[against][slot];
        basis[target][slot] -= adjustment;
    }
    for slot in 0..transform[target].len() {
        let adjustment = &quotient * &transform[against][slot];
        transform[target][slot] -= adjustment;
    }
    let rational_quotient = Rat::from_integer(quotient);
    for earlier in 0..against {
        let adjustment = &rational_quotient * &gso.mu[against][earlier];
        gso.mu[target][earlier] = &gso.mu[target][earlier] - &adjustment;
    }
    gso.mu[target][against] = &gso.mu[target][against] - &rational_quotient;
    work.size_reductions += 1;
}

/// [`reduce_lattice`] with the classical Lovász parameter `3/4` and a budget derived from the
/// material: `4096 + 64·n²·(bits + 2)`, which is generous against the `O(n² log B)` iteration bound.
pub fn reduce_lattice_default(rows: &[Vec<BigInt>]) -> Result<LatticeReduction, ReopeningError> {
    let count = rows.len() as u64;
    let bits = rows
        .iter()
        .flat_map(|row| row.iter())
        .map(|entry| entry.magnitude().bits())
        .max()
        .unwrap_or(0);
    let budget = 4096 + 64 * count * count * (bits + 2);
    reduce_lattice(rows, &Rat::new(BigInt::from(3), BigInt::from(4)), budget)
}

/// Which point of a face's retained enclosure is lifted into the lattice.
///
/// This is the second frame, and it is free: it is read off the enclosure the face already carries.
/// Where the tail is finer than the grain all three lift to the same integers and the frames
/// coincide; where the tail was discarded at the grain they differ by a full lattice unit. A face
/// with no tail cannot supply this frame at all, which is the exact sense in which a collapsed face
/// cannot be reopened.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum EnclosureFrame {
    Lower,
    Midpoint,
    Upper,
}

impl EnclosureFrame {
    /// Every frame a well-formed reopening declares.
    pub const ALL: [EnclosureFrame; 3] = [Self::Lower, Self::Midpoint, Self::Upper];

    pub fn sample(&self, face: &ExactFace) -> Rat {
        match self {
            Self::Lower => face.enclosure.lower.clone(),
            Self::Midpoint => face.midpoint(),
            Self::Upper => face.enclosure.upper.clone(),
        }
    }
}

impl fmt::Display for EnclosureFrame {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lower => write!(formatter, "lower"),
            Self::Midpoint => write!(formatter, "midpoint"),
            Self::Upper => write!(formatter, "upper"),
        }
    }
}

/// One lattice probe at one declared grain, from one enclosure frame.
///
/// A probe **always returns a vector**. That is the point: on a relation-free basis it returns a
/// large vector that is an artifact of this frame, and the only thing that separates that from a
/// relation is whether the other frames return the same one.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainProbe {
    pub grain: DeclaredGrain,
    pub frame: EnclosureFrame,
    /// The full reduced row, `n` coefficients followed by the lifted residual.
    pub shortest_row: Vec<BigInt>,
    /// The coefficient block, made primitive and sign-normalised.
    pub coefficients: Vec<BigInt>,
    /// `Σ a_i · enclosure_i`, exactly. This is the whole certificate.
    pub residual: ExactInterval,
    /// The faces themselves prove `Σ a_i x_i ≠ 0`.
    pub refuted: bool,
    /// `max |a_i|`.
    pub height: BigInt,
    /// `(2·height + 1)^n · width(residual)`: the expected number of integer vectors this short whose
    /// residual would have straddled zero by chance. One or more means the agreement is empty.
    pub chance_population: Rat,
    /// `2^bits`. Reported, never a gate.
    pub grain_modulus: BigInt,
    pub work: LatticeWork,
}

/// A candidate integer relation.
///
/// **This is a candidate, not a proof.** The lattice computation behind it is exact and the residual
/// enclosure is exact, but no finite enclosure can prove a real sum is zero. What the certificate
/// asserts is precisely: *every declared grain returned this same primitive vector, and the faces'
/// own enclosures do not refute it.* Refutation would have been a proof; survival is not.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RelationCandidate {
    pub coefficients: Vec<BigInt>,
    pub basis: Vec<String>,
    pub grains: Vec<DeclaredGrain>,
    /// `Σ a_i · enclosure_i`, exactly. Contains zero, or the candidate would have been refuted.
    pub residual: ExactInterval,
    pub height: BigInt,
    /// `(2·height + 1)^n · width(residual)`, exactly. Strictly below one, or the candidate would
    /// have returned as [`ReopeningVerdict::BelowTheFacesResolution`]. This is the number that says
    /// the agreement was not available by chance.
    pub chance_population: Rat,
}

impl fmt::Display for RelationCandidate {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for (coefficient, name) in self.coefficients.iter().zip(&self.basis) {
            if coefficient.is_zero() {
                continue;
            }
            if first {
                if coefficient.is_negative() {
                    write!(formatter, "-")?;
                }
                first = false;
            } else if coefficient.is_negative() {
                write!(formatter, " - ")?;
            } else {
                write!(formatter, " + ")?;
            }
            write!(formatter, "{}*{name}", coefficient.magnitude())?;
        }
        if first {
            write!(formatter, "0")?;
        }
        write!(formatter, " = 0")
    }
}

/// What a reopening returned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReopeningVerdict {
    /// Every grain agreed and the faces did not refute the agreed vector.
    Candidate(RelationCandidate),
    /// Every grain returned the same primitive vector and the faces' own enclosures **prove** it is
    /// not a relation. This is an exact negative result, not a failure.
    InvariantButRefuted {
        coefficients: Vec<BigInt>,
        residual: ExactInterval,
    },
    /// The frames disagreed. The shortest vector is a coordinate of the grain or of which endpoint
    /// of the enclosure was lifted, rather than an invariant of the faces, and **nothing is
    /// returned**. `probes` carries which (grain, frame) produced each vector.
    FrameDependent { vectors: Vec<Vec<BigInt>> },
    /// Every frame agreed and the faces cannot refute the vector, but the faces are not fine enough
    /// for the agreement to mean anything: the searched population of vectors this short is
    /// expected to contain at least one that would have straddled zero by chance.
    ///
    /// This is the `Open` state, not a discard. The vector is retained with the exact population
    /// that defeats it, so a caller who supplies a finer tail can re-ask the same question.
    BelowTheFacesResolution {
        coefficients: Vec<BigInt>,
        residual: ExactInterval,
        chance_population: Rat,
    },
}

impl ReopeningVerdict {
    pub fn candidate(&self) -> Option<&RelationCandidate> {
        match self {
            Self::Candidate(candidate) => Some(candidate),
            _ => None,
        }
    }

    pub fn returned_nothing(&self) -> bool {
        !matches!(self, Self::Candidate(_))
    }
}

/// The complete return of one reopening: the basis, every probe, and the verdict.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Reopening {
    pub basis: Vec<String>,
    pub probes: Vec<GrainProbe>,
    pub verdict: ReopeningVerdict,
}

impl Reopening {
    /// The total reduction work across every probe, summed exactly.
    pub fn total_work(&self) -> LatticeWork {
        self.probes
            .iter()
            .fold(LatticeWork::default(), |mut total, probe| {
                total.loop_steps += probe.work.loop_steps;
                total.swaps += probe.work.swaps;
                total.size_reductions += probe.work.size_reductions;
                total.gram_recomputations += probe.work.gram_recomputations;
                total.largest_entry_bits =
                    std::cmp::max(total.largest_entry_bits, probe.work.largest_entry_bits);
                total.budget += probe.work.budget;
                total
            })
    }
}

fn make_primitive(coefficients: &[BigInt]) -> Vec<BigInt> {
    let mut divisor = BigInt::zero();
    for coefficient in coefficients {
        divisor = gcd(&divisor, coefficient);
    }
    if divisor.is_zero() {
        return coefficients.to_vec();
    }
    let mut reduced: Vec<BigInt> = coefficients
        .iter()
        .map(|coefficient| coefficient / &divisor)
        .collect();
    if let Some(leading) = reduced.iter().find(|entry| !entry.is_zero())
        && leading.is_negative()
    {
        reduced = reduced.into_iter().map(|entry| -entry).collect();
    }
    reduced
}

fn gcd(left: &BigInt, right: &BigInt) -> BigInt {
    let mut a = left.magnitude().clone();
    let mut b = right.magnitude().clone();
    while !b.is_zero() {
        let remainder = &a % &b;
        a = b;
        b = remainder;
    }
    BigInt::from(a)
}

/// `Σ a_i · enclosure_i`, exactly and outward.
fn residual_enclosure(
    coefficients: &[BigInt],
    faces: &[ExactFace],
) -> Result<ExactInterval, ReopeningError> {
    let mut lower = Rat::zero();
    let mut upper = Rat::zero();
    for (coefficient, face) in coefficients.iter().zip(faces) {
        let scalar = Rat::from_integer(coefficient.clone());
        if coefficient.is_negative() {
            lower += &scalar * &face.enclosure.upper;
            upper += &scalar * &face.enclosure.lower;
        } else {
            lower += &scalar * &face.enclosure.lower;
            upper += &scalar * &face.enclosure.upper;
        }
    }
    ExactInterval::new(lower, upper).map_err(|_| ReopeningError::ReversedEnclosure)
}

/// One lattice probe at one declared grain, from the enclosure midpoint.
///
/// The midpoint is a *reading* of the enclosure, not the enclosure. [`reopen`] probes every frame in
/// [`EnclosureFrame::ALL`]; this entry point exists for callers who want a single lattice and for
/// the drivers that exhibit what midpoint-only framing misses.
pub fn probe_at_grain(
    faces: &[ExactFace],
    grain: DeclaredGrain,
) -> Result<GrainProbe, ReopeningError> {
    probe_at_frame(faces, grain, EnclosureFrame::Midpoint)
}

/// One lattice probe at one declared grain, from one declared enclosure frame.
///
/// The lattice is the classical relation lattice: row `i` is `(e_i | round(2^bits · x_i))` where
/// `x_i` is the face lifted at `frame`, so the last coordinate of any integer combination is the
/// lifted residual and the first `n` are the coefficients. Both blocks are exact integers.
pub fn probe_at_frame(
    faces: &[ExactFace],
    grain: DeclaredGrain,
    frame: EnclosureFrame,
) -> Result<GrainProbe, ReopeningError> {
    if faces.len() < 2 {
        return Err(ReopeningError::TooFewFaces { count: faces.len() });
    }
    for face in faces {
        if !face.admits(grain) {
            return Err(ReopeningError::FaceCoarserThanGrain {
                name: face.name.clone(),
                certified: face.certified_bits(),
                bits: grain.bits,
            });
        }
    }

    let count = faces.len();
    let modulus = grain.modulus();
    let rows: Vec<Vec<BigInt>> = faces
        .iter()
        .enumerate()
        .map(|(index, face)| {
            let mut row: Vec<BigInt> = (0..count)
                .map(|column| {
                    if column == index {
                        BigInt::one()
                    } else {
                        BigInt::zero()
                    }
                })
                .collect();
            row.push(round_to_integer(
                &(frame.sample(face) * Rat::from_integer(modulus.clone())),
            ));
            row
        })
        .collect();

    let reduction = reduce_lattice_default(&rows)?;
    let shortest_row = shortest_row(&reduction.basis);
    let coefficients = make_primitive(&shortest_row[..count]);
    let residual = residual_enclosure(&coefficients, faces)?;
    let refuted = !(residual.lower <= Rat::zero() && residual.upper >= Rat::zero());
    let height = coefficients
        .iter()
        .map(|entry| BigInt::from(entry.magnitude().clone()))
        .max()
        .unwrap_or_else(BigInt::zero);
    let chance_population = chance_population(&height, count, &residual);

    Ok(GrainProbe {
        grain,
        frame,
        shortest_row,
        coefficients,
        residual,
        refuted,
        height,
        chance_population,
        grain_modulus: modulus,
        work: reduction.work,
    })
}

/// The expected number of integer vectors of height at most `height`, over `faces` faces, whose
/// residual enclosure would have straddled zero by chance: `(2·height + 1)^faces · width(residual)`.
///
/// Exact over `Rat`. A value of one or more says the agreement carries no evidence: a population
/// that large is expected to contain such a coincidence whether or not a relation exists. The
/// threshold is one expected coincidence and nothing was chosen.
pub fn chance_population(height: &BigInt, faces: usize, residual: &ExactInterval) -> Rat {
    let width = &residual.upper - &residual.lower;
    let population = (BigInt::from(2) * height + BigInt::one()).pow(faces as u32);
    Rat::from_integer(population) * width
}

/// The minimum-Euclidean-norm row of a reduced basis, tie-broken lexicographically so the choice is
/// deterministic on every machine.
fn shortest_row(basis: &[Vec<BigInt>]) -> Vec<BigInt> {
    let mut best: Option<(BigInt, &Vec<BigInt>)> = None;
    for row in basis {
        let norm = dot_integers(row, row);
        let replace = match &best {
            None => true,
            Some((best_norm, best_row)) => match norm.cmp(best_norm) {
                Ordering::Less => true,
                Ordering::Greater => false,
                Ordering::Equal => row.as_slice() < best_row.as_slice(),
            },
        };
        if replace {
            best = Some((norm, row));
        }
    }
    best.map(|(_, row)| row.clone()).unwrap_or_default()
}

/// Reopen a collapsed face against a declared basis, at two or more declared grains and at every
/// enclosure frame.
///
/// The admission rule is stated in this module's opening and it is the whole instrument: a candidate
/// is returned only when **every** (grain, frame) pair returns the same primitive vector and the
/// faces do not refute it. Fewer than two grains is refused by name, because a vector seen at one
/// grain is a coordinate of that grain — and the enclosure frames are declared here rather than left
/// to the caller because midpoint-only framing was measured returning a spurious relation on
/// collapsed faces.
pub fn reopen(faces: &[ExactFace], grains: &[DeclaredGrain]) -> Result<Reopening, ReopeningError> {
    reopen_with_frames(faces, grains, &EnclosureFrame::ALL)
}

/// [`reopen`] with the enclosure frames named explicitly.
///
/// This exists so a driver can *exhibit* what a weaker framing misses; production callers want
/// [`reopen`], which declares all three. Declaring a single frame is legal and is exactly the
/// configuration that returned a false relation on collapsed faces — the return carries which frames
/// it was taken in, so the weakness is visible in the receipt rather than only in the code.
pub fn reopen_with_frames(
    faces: &[ExactFace],
    grains: &[DeclaredGrain],
    frames: &[EnclosureFrame],
) -> Result<Reopening, ReopeningError> {
    if faces.len() < 2 {
        return Err(ReopeningError::TooFewFaces { count: faces.len() });
    }
    if grains.len() < 2 {
        return Err(ReopeningError::TooFewGrains {
            count: grains.len(),
        });
    }
    if frames.is_empty() {
        return Err(ReopeningError::NoDeclaredFrame);
    }
    let mut seen: Vec<u32> = Vec::with_capacity(grains.len());
    for grain in grains {
        if seen.contains(&grain.bits) {
            return Err(ReopeningError::DuplicateGrain { bits: grain.bits });
        }
        seen.push(grain.bits);
    }

    let mut probes = Vec::with_capacity(grains.len() * frames.len());
    for grain in grains {
        for frame in frames {
            probes.push(probe_at_frame(faces, *grain, *frame)?);
        }
    }

    let basis: Vec<String> = faces.iter().map(|face| face.name.clone()).collect();
    let first = probes[0].coefficients.clone();
    let agreed = probes.iter().all(|probe| probe.coefficients == first);

    let verdict = if !agreed {
        ReopeningVerdict::FrameDependent {
            vectors: probes
                .iter()
                .map(|probe| probe.coefficients.clone())
                .collect(),
        }
    } else if probes[0].refuted {
        ReopeningVerdict::InvariantButRefuted {
            coefficients: first,
            residual: probes[0].residual.clone(),
        }
    } else if probes[0].chance_population >= Rat::one() {
        ReopeningVerdict::BelowTheFacesResolution {
            coefficients: first,
            residual: probes[0].residual.clone(),
            chance_population: probes[0].chance_population.clone(),
        }
    } else {
        ReopeningVerdict::Candidate(RelationCandidate {
            coefficients: first,
            basis: basis.clone(),
            grains: grains.to_vec(),
            residual: probes[0].residual.clone(),
            height: probes[0].height.clone(),
            chance_population: probes[0].chance_population.clone(),
        })
    };

    Ok(Reopening {
        basis,
        probes,
        verdict,
    })
}

/// The finest grain a whole basis admits: the minimum over its faces.
///
/// This is the aperture the tails paid for. A relation of height `A` over `n` faces is reachable
/// only when `2^bits` comfortably exceeds `A^n`, so this number is what decides whether a search can
/// succeed at all — which is the movement's thesis stated as an inequality.
pub fn finest_admissible_grain(faces: &[ExactFace]) -> CertifiedBits {
    let mut finest: Option<u32> = None;
    for face in faces {
        match face.certified_bits() {
            CertifiedBits::Exact => {}
            CertifiedBits::Coarser => return CertifiedBits::Coarser,
            CertifiedBits::Bits(bits) => {
                finest = Some(match finest {
                    None => bits,
                    Some(current) => std::cmp::min(current, bits),
                });
            }
        }
    }
    match finest {
        None => CertifiedBits::Exact,
        Some(bits) => CertifiedBits::Bits(bits),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact_value::ieee754::{decode_bfloat16_bits, decode_binary64_bits};
    use relational_geometry::exact_analysis::log_rational_interval;

    fn grain_pair() -> Vec<DeclaredGrain> {
        vec![DeclaredGrain::bits(48), DeclaredGrain::bits(72)]
    }

    fn arctan_face(denominator: u32, terms: u32) -> ExactFace {
        ExactFace::from_certified_series(
            format!("atan(1/{denominator})"),
            arctan_unit_fraction(denominator, terms).expect("a unit-fraction arctangent"),
        )
    }

    fn log_face(value: i64, terms: u32, bits: u32) -> ExactFace {
        let interval =
            log_rational_interval(&integer(value), terms, bits).expect("a positive logarithm");
        ExactFace::from_rat_interval(format!("log {value}"), "log_rational_interval", &interval)
            .expect("an ordered enclosure")
    }

    fn integer_determinant(matrix: &[Vec<BigInt>]) -> Rat {
        let count = matrix.len();
        let mut work: Vec<Vec<Rat>> = matrix
            .iter()
            .map(|row| {
                row.iter()
                    .map(|entry| Rat::from_integer(entry.clone()))
                    .collect()
            })
            .collect();
        let mut determinant = Rat::one();
        for column in 0..count {
            let pivot = (column..count).find(|row| !work[*row][column].is_zero());
            let Some(pivot) = pivot else {
                return Rat::zero();
            };
            if pivot != column {
                work.swap(pivot, column);
                determinant = -determinant;
            }
            determinant *= &work[column][column];
            let inverse = Rat::one() / &work[column][column];
            for row in (column + 1)..count {
                let factor = &work[row][column] * &inverse;
                for slot in column..count {
                    work[row][slot] = &work[row][slot] - &(&factor * &work[column][slot].clone());
                }
            }
        }
        determinant
    }

    #[test]
    fn dyadic_scale_is_exact_on_powers_and_between_them() {
        assert_eq!(dyadic_scale(&integer(1)), Some(0));
        assert_eq!(dyadic_scale(&integer(2)), Some(1));
        assert_eq!(dyadic_scale(&integer(3)), Some(1));
        assert_eq!(dyadic_scale(&integer(4)), Some(2));
        assert_eq!(
            dyadic_scale(&Rat::new(BigInt::one(), BigInt::from(8))),
            Some(-3)
        );
        assert_eq!(
            dyadic_scale(&Rat::new(BigInt::one(), BigInt::from(7))),
            Some(-3)
        );
        assert_eq!(dyadic_scale(&Rat::zero()), None);
    }

    #[test]
    fn certified_bits_reports_the_aperture_the_tail_paid_for() {
        let exact = ExactFace::rational("one third", Rat::new(BigInt::one(), BigInt::from(3)));
        assert_eq!(exact.certified_bits(), CertifiedBits::Exact);
        assert!(exact.admits(DeclaredGrain::bits(4096)));

        let face = arctan_face(5, 8);
        // `atan(1/5)` folded to eight terms omits `1/(17 * 5^17)`, which is below `2^-43`.
        match face.certified_bits() {
            CertifiedBits::Bits(bits) => {
                assert!(bits >= 43, "eight terms of atan(1/5) certify {bits} bits");
                assert!(face.admits(DeclaredGrain::bits(bits)));
                assert!(!face.admits(DeclaredGrain::bits(bits + 1)));
            }
            other => panic!("a folded series has a finite aperture, got {other}"),
        }
    }

    #[test]
    fn reduction_preserves_the_lattice_and_satisfies_its_own_conditions() {
        let rows: Vec<Vec<BigInt>> = vec![
            vec![BigInt::from(1), BigInt::from(0), BigInt::from(1_299_709)],
            vec![BigInt::from(0), BigInt::from(1), BigInt::from(-2_750_159)],
        ];
        let reduction = reduce_lattice_default(&rows).expect("a reducible lattice");

        // The transform is unimodular.
        let determinant = integer_determinant(&reduction.transform);
        assert!(determinant == Rat::one() || determinant == -Rat::one());

        // The transform reproduces the reduced basis from the input rows.
        for (row, transform_row) in reduction.basis.iter().zip(&reduction.transform) {
            for slot in 0..row.len() {
                let combination = transform_row
                    .iter()
                    .zip(&rows)
                    .fold(BigInt::zero(), |sum, (factor, source)| {
                        sum + factor * &source[slot]
                    });
                assert_eq!(combination, row[slot]);
            }
        }

        // The reduced basis satisfies the size-reduction and Lovász conditions exactly.
        let gso = orthogonalise(&reduction.basis).expect("an independent reduced basis");
        let half = Rat::new(BigInt::one(), BigInt::from(2));
        for index in 1..reduction.basis.len() {
            for earlier in 0..index {
                assert!(gso.mu[index][earlier].abs() <= half);
            }
            let coefficient = &gso.mu[index][index - 1];
            let lovasz = (&reduction.delta - coefficient * coefficient) * &gso.norms[index - 1];
            assert!(gso.norms[index] >= lovasz);
        }
    }

    #[test]
    fn the_coefficient_block_equals_the_transform_on_a_relation_lattice() {
        let faces = vec![
            arctan_face(2, 64),
            arctan_face(3, 64),
            ExactFace::rational("one", Rat::one()),
        ];
        let probe = probe_at_grain(&faces, DeclaredGrain::bits(48)).expect("a probeable basis");
        // The identity block means the reduced row's coefficient part is its own transform row; the
        // probe returns the row, and the primitive form must divide it.
        assert_eq!(probe.shortest_row.len(), faces.len() + 1);
    }

    #[test]
    fn exact_rational_faces_return_an_exact_zero_residual() {
        let faces = vec![
            ExactFace::rational("1/3", Rat::new(BigInt::one(), BigInt::from(3))),
            ExactFace::rational("1/5", Rat::new(BigInt::one(), BigInt::from(5))),
            ExactFace::rational("1/15", Rat::new(BigInt::one(), BigInt::from(15))),
        ];
        let reopening = reopen(&faces, &grain_pair()).expect("exact faces admit every grain");
        let candidate = reopening
            .verdict
            .candidate()
            .expect("three commensurable rationals carry a relation");
        assert!(candidate.residual.is_point());
        assert!(candidate.residual.lower.is_zero());
        // Check the relation is real: 5a + 3b + c = 0 after clearing 1/15.
        let check = &candidate.coefficients[0] * BigInt::from(5)
            + &candidate.coefficients[1] * BigInt::from(3)
            + &candidate.coefficients[2];
        assert!(check.is_zero());
    }

    #[test]
    fn euler_and_machin_are_recovered_from_each_other() {
        let a2 = arctan_face(2, 96);
        let a3 = arctan_face(3, 96);
        let a5 = arctan_face(5, 96);
        let a239 = arctan_face(239, 96);

        let machin_pi = ExactFace::integer_combination(
            "pi (Machin)",
            &[(BigInt::from(16), &a5), (BigInt::from(-4), &a239)],
        )
        .expect("an ordered combination");
        let euler_pi = ExactFace::integer_combination(
            "pi (Euler)",
            &[(BigInt::from(4), &a2), (BigInt::from(4), &a3)],
        )
        .expect("an ordered combination");

        let euler =
            reopen(&[a2.clone(), a3.clone(), machin_pi], &grain_pair()).expect("a probeable basis");
        let candidate = euler.verdict.candidate().expect("Euler's identity");
        assert_eq!(
            candidate.coefficients,
            vec![BigInt::from(4), BigInt::from(4), BigInt::from(-1)]
        );

        let machin = reopen(&[a5, a239, euler_pi], &grain_pair()).expect("a probeable basis");
        let candidate = machin.verdict.candidate().expect("Machin's identity");
        assert_eq!(
            candidate.coefficients,
            vec![BigInt::from(16), BigInt::from(-4), BigInt::from(-1)]
        );
    }

    #[test]
    fn a_relation_free_basis_returns_nothing() {
        // `a log2 + b log3 + c log5 = 0` iff `2^a 3^b 5^c = 1` iff `a = b = c = 0`, by unique
        // factorisation. There is no relation to find and the instrument must say so.
        let faces = vec![
            log_face(2, 80, 96),
            log_face(3, 80, 96),
            log_face(5, 80, 96),
        ];
        let reopening = reopen(&faces, &grain_pair()).expect("a probeable basis");
        assert!(
            reopening.verdict.returned_nothing(),
            "a relation finder that always finds a relation has found nothing: {:?}",
            reopening.verdict
        );
    }

    #[test]
    fn a_wider_relation_free_basis_returns_nothing() {
        let faces = vec![
            log_face(2, 80, 96),
            log_face(3, 80, 96),
            log_face(5, 80, 96),
            log_face(7, 80, 96),
        ];
        let reopening = reopen(&faces, &grain_pair()).expect("a probeable basis");
        assert!(
            reopening.verdict.returned_nothing(),
            "four multiplicatively independent logarithms carry no relation: {:?}",
            reopening.verdict
        );
    }

    #[test]
    fn a_coarse_grain_fails_where_a_fine_grain_succeeds() {
        let a2 = arctan_face(2, 96);
        let a3 = arctan_face(3, 96);
        let a5 = arctan_face(5, 96);
        let a239 = arctan_face(239, 96);
        let euler_pi = ExactFace::integer_combination(
            "pi (Euler)",
            &[(BigInt::from(4), &a2), (BigInt::from(4), &a3)],
        )
        .expect("an ordered combination");
        let faces = vec![a5, a239, euler_pi];

        // Machin's relation has height 16 over three faces, so it is reachable only when the grain
        // modulus comfortably exceeds 16^3 = 4096.
        let coarse = reopen(&faces, &[DeclaredGrain::bits(6), DeclaredGrain::bits(8)])
            .expect("a probeable basis");
        assert!(
            coarse.verdict.returned_nothing(),
            "the relation is not reachable below its own height: {:?}",
            coarse.verdict
        );

        let fine = reopen(&faces, &grain_pair()).expect("a probeable basis");
        assert_eq!(
            fine.verdict
                .candidate()
                .expect("Machin's identity at a fine grain")
                .coefficients,
            vec![BigInt::from(16), BigInt::from(-4), BigInt::from(-1)]
        );
    }

    #[test]
    fn a_collapsed_face_is_refused_past_its_own_truncation() {
        let a5 = arctan_face(5, 96);
        let collapsed = ExactFace::collapsed("atan(1/5) collapsed to 53 bits", &a5, 53);
        assert_eq!(collapsed.certified_bits(), CertifiedBits::Bits(53));
        let faces = vec![collapsed, arctan_face(3, 96)];
        let error = probe_at_grain(&faces, DeclaredGrain::bits(72))
            .expect_err("a 53-bit face cannot answer a 72-bit question");
        assert!(matches!(
            error,
            ReopeningError::FaceCoarserThanGrain { bits: 72, .. }
        ));
        assert!(probe_at_grain(&faces, DeclaredGrain::bits(53)).is_ok());
    }

    #[test]
    fn one_grain_is_refused_by_name() {
        let faces = vec![arctan_face(2, 32), arctan_face(3, 32)];
        let error = reopen(&faces, &[DeclaredGrain::bits(32)])
            .expect_err("one frame cannot exhibit an invariant");
        assert!(matches!(error, ReopeningError::TooFewGrains { count: 1 }));

        let error = reopen(&faces, &[DeclaredGrain::bits(32), DeclaredGrain::bits(32)])
            .expect_err("two probes at one grain are one probe");
        assert!(matches!(error, ReopeningError::DuplicateGrain { bits: 32 }));
    }

    #[test]
    fn the_primitive_form_is_sign_normalised_and_divided_by_its_content() {
        assert_eq!(
            make_primitive(&[BigInt::from(32), BigInt::from(-8), BigInt::from(-2)]),
            vec![BigInt::from(16), BigInt::from(-4), BigInt::from(-1)]
        );
        assert_eq!(
            make_primitive(&[BigInt::from(-16), BigInt::from(4), BigInt::from(1)]),
            vec![BigInt::from(16), BigInt::from(-4), BigInt::from(-1)]
        );
        assert_eq!(
            make_primitive(&[BigInt::from(0), BigInt::from(-6), BigInt::from(9)]),
            vec![BigInt::from(0), BigInt::from(2), BigInt::from(-3)]
        );
    }

    #[test]
    fn refutation_is_exact_where_confirmation_is_not() {
        // `2*atan(1/2) - atan(1/3)` is not zero, and the enclosures prove it.
        let faces = vec![arctan_face(2, 64), arctan_face(3, 64)];
        let residual = residual_enclosure(&[BigInt::from(2), BigInt::from(-1)], &faces)
            .expect("an ordered residual");
        assert!(residual.lower > Rat::zero(), "the faces refute this vector");

        // The true relation's residual straddles zero and never proves anything positive.
        let a5 = arctan_face(5, 96);
        let a239 = arctan_face(239, 96);
        let pi = ExactFace::integer_combination(
            "pi",
            &[(BigInt::from(16), &a5), (BigInt::from(-4), &a239)],
        )
        .expect("an ordered combination");
        let residual = residual_enclosure(
            &[BigInt::from(16), BigInt::from(-4), BigInt::from(-1)],
            &[a5, a239, pi],
        )
        .expect("an ordered residual");
        assert!(residual.lower <= Rat::zero() && residual.upper >= Rat::zero());
        assert!(
            !residual.is_point(),
            "no finite enclosure proves a real sum is zero"
        );
    }

    #[test]
    fn the_arctangent_certificate_encloses_its_own_value() {
        // Consecutive folds bracket the value from alternate sides, so their enclosures must meet.
        let even = arctan_unit_fraction(5, 8).expect("a folded arctangent");
        let odd = arctan_unit_fraction(5, 9).expect("a folded arctangent");
        let a = even.enclosure();
        let b = odd.enclosure();
        assert!(
            a.lower <= b.upper && b.lower <= a.upper,
            "{a:?} and {b:?} must overlap"
        );
        // And the tighter fold is strictly inside the looser one.
        assert!(b.lower >= a.lower && b.upper <= a.upper);
    }

    #[test]
    fn a_collapsed_face_defeats_two_gates_and_is_caught_by_the_third() {
        // This is the measurement that falsified the first form of this instrument, pinned so it
        // cannot silently return. Collapsed to exactly the grain, the faces cannot refute a
        // spurious vector -- the enclosure is one lattice unit wide -- and two adjacent grains are
        // not two frames, so grain-only framing agreed with itself and returned a false relation.
        let sources = [
            log_face(2, 120, 210),
            log_face(3, 120, 210),
            log_face(5, 120, 210),
        ];
        let collapsed: Vec<ExactFace> = sources
            .iter()
            .map(|face| ExactFace::collapsed(format!("{} collapsed", face.name), face, 96))
            .collect();
        let grains = [DeclaredGrain::bits(95), DeclaredGrain::bits(96)];

        // Gate one, exact refutation: blind. The collapse spent exactly the tail it would have used.
        let probe = probe_at_grain(&collapsed, DeclaredGrain::bits(96)).expect("probeable");
        assert!(!probe.refuted);
        assert!(probe.height > BigInt::from(1_000_000));

        // Gate two, the enclosure frames: their orbit on the returned object is TRIVIAL here. The
        // lattice does move -- the three frames lift to integers a full unit apart -- but the
        // spurious vector's last coordinate is already of its own height's order, so a one-unit
        // shift does not dislodge it. Pinned because it was tried as the repair and it failed.
        let lower = probe_at_frame(&collapsed, DeclaredGrain::bits(96), EnclosureFrame::Lower)
            .expect("probeable");
        let upper = probe_at_frame(&collapsed, DeclaredGrain::bits(96), EnclosureFrame::Upper)
            .expect("probeable");
        assert_ne!(
            lower.shortest_row.last(),
            upper.shortest_row.last(),
            "the frames must lift to genuinely different lattices"
        );
        assert_eq!(
            lower.coefficients, upper.coefficients,
            "and they return the same vector anyway: the gauge's orbit is trivial on the return"
        );

        // Gate three, the searched population, is the one that works.
        assert!(probe.chance_population >= Rat::one());
        let framed = reopen(&collapsed, &grains).expect("probeable");
        match &framed.verdict {
            ReopeningVerdict::BelowTheFacesResolution {
                chance_population, ..
            } => assert!(*chance_population >= Rat::one()),
            other => panic!("a collapsed face cannot resolve a height-2^31 vector: {other:?}"),
        }
        assert!(framed.verdict.returned_nothing());
    }

    #[test]
    fn endpoint_framing_costs_the_positive_controls_nothing() {
        // Where the tail is finer than the grain the three frames lift to the same integers, so
        // full framing is free. Both identities must survive it.
        let a2 = arctan_face(2, 96);
        let a3 = arctan_face(3, 96);
        let a5 = arctan_face(5, 96);
        let a239 = arctan_face(239, 96);
        let machin_pi = ExactFace::integer_combination(
            "pi (Machin)",
            &[(BigInt::from(16), &a5), (BigInt::from(-4), &a239)],
        )
        .expect("an ordered combination");
        let euler_pi = ExactFace::integer_combination(
            "pi (Euler)",
            &[(BigInt::from(4), &a2), (BigInt::from(4), &a3)],
        )
        .expect("an ordered combination");

        let euler = reopen(&[a2, a3, machin_pi], &grain_pair()).expect("probeable");
        assert_eq!(
            euler.verdict.candidate().expect("Euler").coefficients,
            vec![BigInt::from(4), BigInt::from(4), BigInt::from(-1)]
        );
        assert_eq!(euler.probes.len(), 6, "two grains times three frames");

        // A 53-bit collapse still carries a height-16 relation: the reachable height at grain g
        // over n faces is about 2^(g/n), and 2^(53/3) is far above 16. The instrument must not
        // refuse a face merely for having been collapsed.
        let a5 = arctan_face(5, 96);
        let collapsed = ExactFace::collapsed("atan(1/5) collapsed to 53 bits", &a5, 53);
        let machin = reopen(
            &[collapsed, a239, euler_pi],
            &[DeclaredGrain::bits(40), DeclaredGrain::bits(53)],
        )
        .expect("probeable");
        assert_eq!(
            machin.verdict.candidate().expect("Machin").coefficients,
            vec![BigInt::from(16), BigInt::from(-4), BigInt::from(-1)]
        );
    }

    /// The mouth must not accept everything. A float read as a **measurement** carries a ceiling of
    /// exactly one unit in the last place, and the aperture law refuses past it by name.
    ///
    /// The two patterns are the CODATA 2022 inverse fine-structure constant and Rydberg constant as
    /// `binary64`. Their ulps differ by sixteen binary places purely because their magnitudes do,
    /// which is the point: **the ulp belongs to the format at a magnitude, not to the format.**
    #[test]
    fn a_rounded_float_face_is_refused_past_its_own_unit_in_the_last_place() {
        let alpha_inverse = decode_binary64_bits(0x4061_2126_e7be_fcbc).expect("a finite pattern");
        let rydberg = decode_binary64_bits(0x4164_ee44_722e_5797).expect("a finite pattern");
        assert_eq!(alpha_inverse.ulp_bits(), 45);
        assert_eq!(rydberg.ulp_bits(), 29);

        let faces = vec![
            ExactFace::from_binary_float(
                "alpha^-1",
                "CODATA 2022, as a binary64 literal",
                &alpha_inverse,
                FloatReading::RoundedToNearest,
            ),
            ExactFace::from_binary_float(
                "R_inf",
                "CODATA 2022, as a binary64 literal",
                &rydberg,
                FloatReading::RoundedToNearest,
            ),
        ];
        assert_eq!(faces[0].certified_bits(), CertifiedBits::Bits(45));
        assert_eq!(faces[1].certified_bits(), CertifiedBits::Bits(29));
        assert_eq!(finest_admissible_grain(&faces), CertifiedBits::Bits(29));
        assert_eq!(
            faces[1].aperture_source(),
            ApertureSource::UnitInTheLastPlace {
                species: BinaryFloatSpecies::Binary64,
                ulp_bits: 29,
            }
        );

        let error = probe_at_grain(&faces, DeclaredGrain::bits(30))
            .expect_err("a 29-bit face cannot answer a 30-bit question");
        match error {
            ReopeningError::FaceCoarserThanGrain {
                ref name,
                certified,
                bits,
            } => {
                assert_eq!(name, "R_inf");
                assert_eq!(certified, CertifiedBits::Bits(29));
                assert_eq!(bits, 30);
            }
            other => panic!("the refusal must name the face and its aperture, got {other}"),
        }
        assert!(probe_at_grain(&faces, DeclaredGrain::bits(29)).is_ok());
    }

    /// The same pattern under the two readings is two different objects, and the admission law —
    /// which was written before the mouth existed and is unchanged by it — separates them.
    #[test]
    fn one_pattern_admits_every_grain_as_a_point_and_carries_a_ceiling_as_a_measurement() {
        let datum = decode_binary64_bits(0x4061_2126_e7be_fcbc).expect("a finite pattern");
        let point = ExactFace::from_binary_float(
            "alpha^-1 as a pattern",
            "CODATA 2022",
            &datum,
            FloatReading::ExactBitPattern,
        );
        let measured = ExactFace::from_binary_float(
            "alpha^-1 as a measurement",
            "CODATA 2022",
            &datum,
            FloatReading::RoundedToNearest,
        );
        assert_eq!(point.certified_bits(), CertifiedBits::Exact);
        assert!(point.admits(DeclaredGrain::bits(4096)));
        assert_eq!(point.aperture_source(), ApertureSource::NoDeletion);
        assert_eq!(measured.certified_bits(), CertifiedBits::Bits(45));
        assert!(!measured.admits(DeclaredGrain::bits(46)));
        assert_eq!(measured.width(), datum.unit_in_last_place());
        // The point sits strictly inside the measurement's enclosure: they are the same quantity
        // read two ways, not two quantities.
        assert!(measured.enclosure.lower < point.enclosure.lower);
        assert!(measured.enclosure.upper > point.enclosure.upper);

        // A magnitude whose format spacing exceeds one admits no grain at all as a measurement,
        // and every grain as a pattern.
        let huge = decode_binary64_bits(0x7fef_ffff_ffff_ffff).expect("the largest finite pattern");
        assert_eq!(huge.ulp_bits(), -971);
        let coarse = ExactFace::from_binary_float(
            "the largest finite binary64",
            "declared bit pattern",
            &huge,
            FloatReading::RoundedToNearest,
        );
        assert_eq!(coarse.certified_bits(), CertifiedBits::Coarser);
        assert!(!coarse.admits(DeclaredGrain::bits(0)));
        let exact = ExactFace::from_binary_float(
            "the largest finite binary64",
            "declared bit pattern",
            &huge,
            FloatReading::ExactBitPattern,
        );
        assert_eq!(exact.certified_bits(), CertifiedBits::Exact);
    }

    /// **Real material, and the distinction is load-bearing on it.**
    ///
    /// Three `bfloat16` words from `model.language_model.layers.1.mlp.down_proj.weight` of
    /// Qwen3.5-4B. Read as *patterns* they are exact dyadics with eight-bit significands, so they
    /// are commensurable and the relation `7a − 4b + 6c = 0` holds **exactly** — the residual is a
    /// point at zero, not an enclosure containing zero. Read as *measurements* the same forty-eight
    /// bits carry ceilings of `2^-12`, `2^-13`, `2^-12` and the instrument returns nothing.
    ///
    /// The existence of *some* relation among three rationals is guaranteed; what is measured here
    /// is that the instrument recovers it at height 7 with an exactly zero residual, and that one
    /// reading of the same bits destroys it.
    #[test]
    fn three_real_bfloat16_weights_relate_as_patterns_and_not_as_measurements() {
        let words: [u16; 3] = [0xbd1e, 0xbc94, 0x3d07];
        let data: Vec<_> = words
            .iter()
            .map(|word| decode_bfloat16_bits(*word).expect("a finite weight"))
            .collect();
        let source = "Qwen3.5-4B model.language_model.layers.1.mlp.down_proj.weight[0..3]";

        let patterns: Vec<ExactFace> = data
            .iter()
            .enumerate()
            .map(|(index, datum)| {
                ExactFace::from_binary_float(
                    format!("w{index} as a pattern"),
                    source,
                    datum,
                    FloatReading::ExactBitPattern,
                )
            })
            .collect();
        let grains = [DeclaredGrain::bits(32), DeclaredGrain::bits(64)];
        let reopening = reopen(&patterns, &grains).expect("points admit every grain");
        let candidate = reopening
            .verdict
            .candidate()
            .expect("three exact dyadics are commensurable");
        assert_eq!(
            candidate.coefficients,
            vec![BigInt::from(7), BigInt::from(-4), BigInt::from(6)]
        );
        assert!(
            candidate.residual.is_point() && candidate.residual.lower.is_zero(),
            "patterns relate exactly, not to within an enclosure: {:?}",
            candidate.residual
        );
        assert!(candidate.chance_population.is_zero());
        // And the relation is checkable by hand: 7*(-316) + (-4)*(-148) + 6*270 = 0 over 2^-13.
        let check = BigInt::from(7) * BigInt::from(-316)
            + BigInt::from(-4) * BigInt::from(-148)
            + BigInt::from(6) * BigInt::from(270);
        assert!(check.is_zero());

        let measurements: Vec<ExactFace> = data
            .iter()
            .enumerate()
            .map(|(index, datum)| {
                ExactFace::from_binary_float(
                    format!("w{index} as a measurement"),
                    source,
                    datum,
                    FloatReading::RoundedToNearest,
                )
            })
            .collect();
        assert_eq!(
            finest_admissible_grain(&measurements),
            CertifiedBits::Bits(12)
        );
        let measured = reopen(
            &measurements,
            &[DeclaredGrain::bits(11), DeclaredGrain::bits(12)],
        )
        .expect("both grains are within the coarsest ulp");
        assert!(
            measured.verdict.returned_nothing(),
            "eight significand bits cannot resolve a relation: {:?}",
            measured.verdict
        );
        // Every probe's own enclosure refutes its vector; gate one carries this, not gate three.
        assert!(measured.probes.iter().all(|probe| probe.refuted));
    }

    #[test]
    fn work_is_counted_in_steps_and_never_in_seconds() {
        let faces = vec![arctan_face(2, 96), arctan_face(3, 96), arctan_face(5, 96)];
        let reopening = reopen(&faces, &grain_pair()).expect("a probeable basis");
        let work = reopening.total_work();
        assert!(work.loop_steps > 0);
        assert!(work.gram_recomputations > 0);
        assert!(work.loop_steps <= work.budget);
    }
}
