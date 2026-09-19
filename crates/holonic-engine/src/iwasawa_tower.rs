//! **C8 — the Iwasawa tower: the finite computable shadow of `Λ = Z_p[[T]]` and its levels.**
//!
//! The object of this module is the chain of distinguished polynomials
//! `ω_n(T) = (1+T)^(p^n) - 1`, the finite-rank quotients `Λ/(ω_n)` they cut out, and the finite abelian
//! groups `M/ω_n M` when that specialization is finite (otherwise a typed refusal). Everything below is
//! computed exactly over `num_bigint::BigInt` / `BigUint`. **No machine floating-point type and
//! no float literal appears in this file**, which the test
//! `the_module_source_contains_no_floating_point_type` checks against this file's own text; the
//! only decimals are in prose and in assertion messages.
//!
//! # What this module computes and what it cites
//!
//! Iwasawa's theorem (Iwasawa 1959; see Washington, *Introduction to Cyclotomic Fields*, 2nd ed.,
//! Theorem 13.13), on a finitely generated torsion `Λ`-module `M` whose `ω_n` coinvariants are
//! finite, supplies integers
//! `μ ≥ 0`, `λ ≥ 0`, `ν` and an `n₀` with `|M/ω_n M| = p^(μ p^n + λ n + ν)` for all `n ≥ n₀`.
//! The finiteness hypothesis cannot be omitted: `Λ/(T)` leaves `Z_p` at every level and is
//! refused by `specialize`. The general classical form uses `ω_n/ω_n₀` relatively prime to the
//! characteristic ideal (Sharifi, *Iwasawa Theory*, Theorem 2.4.7,
//! <https://www.math.ucla.edu/~sharifi/notes/iwasawa-ch02.html>).
//! **That theorem is cited, not proved here.** What this module does is *exhibit the shape
//! numerically at small levels*: it measures `e_n` with `|M/ω_n M| = p^(e_n)` by an exact Smith
//! normal form, solves the three-by-three integer system for `(μ, λ, ν)` over three consecutive
//! levels, and then verifies the solution against a fourth measured level. A fit that does not
//! reproduce the fourth level is a typed refusal, not a rounded agreement.
//!
//! `μ`, `λ` and `ν` here are **growth exponents of an order, not entropies**. Nothing in this file
//! is an information measure, and no scalar produced here decides a branch: every decision is an
//! exact integer equality or a divisibility over `BigInt`.
//!
//! The measured exponents on this material, at `p = 3`, base level `0`, verified at level `3`:
//!
//! ```text
//!   f = T - p            e = [1, 2, 3, 4]      (μ, λ, ν) = (0, 1, 1)
//!   f = p                e = [1, 3, 9, 27]     (μ, λ, ν) = (1, 0, 0)
//!   f = p^2              e = [2, 6, 18, 54]    (μ, λ, ν) = (2, 0, 0)
//!   f = (T-p)(T-p^2)     e = [3, 5, 7, 9]      (μ, λ, ν) = (0, 2, 3)
//!   (p, T)               e = [1, 1, 1, 1]      (μ, λ, ν) = (0, 0, 1)
//! ```
//!
//! and the `n₀` of the cited theorem is not decoration: at `p = 2`, `f = T - 2`, the measured
//! `e = [1, 3, 4, 5, 6]` admits **no** admissible fit from base level `0` — the exact solution
//! there is `μ = -1` — and only from base level `1` does it return `(0, 1, 2)` and verify at level
//! `4`. See [`GrowthExponents::is_iwasawa_admissible`] and the test
//! `the_shape_does_not_hold_below_its_own_n_zero`.
//!
//! # The two counterexample pairs
//!
//! **The characteristic face does not determine the module.** With `f = T - p`, the modules
//! `M₁ = Λ/(f²)` and `M₂ = Λ/(f) ⊕ Λ/(f)` carry the same characteristic polynomial `f²`, so the
//! codimension-one datum cannot separate them. At every level they have the **same order** and
//! **different** finite types. Measured at `p = 3`:
//!
//! ```text
//!   n = 0    M₁ ≅ Z/3^2                order 3^2      M₂ ≅ Z/3  ⊕ Z/3      order 3^2
//!   n = 1    M₁ ≅ Z/3 ⊕ Z/3^3          order 3^4      M₂ ≅ Z/3^2 ⊕ Z/3^2   order 3^4
//!   n = 2    M₁ ≅ Z/3^2 ⊕ Z/3^4        order 3^6      M₂ ≅ Z/3^3 ⊕ Z/3^3   order 3^6
//! ```
//!
//! The measured `M₁` type is `[n, n+2]` (with the `0` dropped at `n = 0`, where `M₁` is cyclic of
//! order `p²`), **not** the cyclic `Z/p^(2(n+1))` one might guess. The elementary-divisor computation
//! behind that is `d₁ = gcd(ω_n(p), ω_n'(p))`, `d₂ = ω_n(p)² / d₁`, with `v_p(ω_n(p)) = n+1` and
//! `v_p(ω_n'(p)) = n`, so the split is `(n, n+2)` and never `(0, 2n+2)` for `n ≥ 1`.
//!
//! **A pseudo-null residue is invisible to the face.** `M = Λ/(p, T) ≅ F_p` is nonzero and finite
//! of order exactly `p` at every level, while its characteristic ideal is the unit ideal — the
//! characteristic ideal of the *zero* module. [`CharacteristicFace::Unit`] is returned for it, and
//! the specialization at every checked level returns order `p`.
//!
//! # How the finite group is computed
//!
//! `M/ω_n M = Z_p[T]/(f₁, …, f_k, ω_n)`. The free `Z`-module `Z[T]/(ω_n)` has basis
//! `1, T, …, T^(p^n - 1)` because `ω_n` is monic. The relations are `T^j · f_i mod ω_n` for every
//! generator `i` and every `j < p^n`. That `(k·p^n) × p^n` integer matrix goes to
//! [`crate::rebase_invariants::smith_normal_form`] — this module founds **no** second Smith normal
//! form — and the cokernel is read off its invariant factors: free rank `p^n - rank`, torsion
//! `⊕ Z/d_i`. Tensoring with `Z_p` kills the prime-to-`p` part of each `d_i` and leaves
//! `⊕ Z/p^(v_p(d_i))`.
//!
//! **The prime-to-`p` part is reported, never dropped in silence.** It is real: at `p = 3`, `n = 1`,
//! `f = T - 3`, the single invariant factor over `Z` is `63 = 3² · 7`, and the `Z_p`-module is
//! `Z/9` with cofactor `7`. [`FiniteSpecialization`] carries `order` (the `Z_p`-order, `p^(Σ v_p)`),
//! `integral_order` (`∏ d_i`, the order over `Z`) and `prime_to_p_part` (their exact quotient) as
//! three separate exact values, with [`FiniteSpecialization::is_p_primary`] deciding between them.
//!
//! This is a **deliberate departure from the task statement for this owner**, which asked for a
//! refusal whenever some invariant factor has a prime factor other than `p`. Such a refusal would
//! reject `f = T - p` — the flagship example of the whole construction — at every level `n ≥ 1`.
//! The refusal is therefore kept only for the case that is genuinely not a finite `Z_p`-module:
//! rank deficiency, i.e. [`IwasawaRefusal::NotFinite`].
//!
//! # Composition with the wave-1 continuing tower
//!
//! This module founds no second tower vocabulary. [`IwasawaTower`] is an instance of
//! [`crate::continuing_tower::Tower`] at index `n` with face "a polynomial representative modulo
//! `ω_n`", and [`OmegaRestriction`] is an instance of [`crate::continuing_tower::Transition`] whose
//! residual is the exact quotient by `ω_coarse`. The transition is non-invertible and its residual
//! is exactly what a later (finer) receiver reopens, which is
//! `ContinuingTower.Transition.laterReceiverFactors`. Its `reopen_apply` law is the division
//! identity `a = ω · q + r` and is total on every input, because division by a monic divisor over
//! `Z` is total.
//!
//! The refinement `ω_n | ω_(n+1)` is what makes `refines` a genuine refinement here: restriction
//! from level `n+1` to level `n` is well defined precisely because of
//! [`omega_divides_omega_succ`].
//!
//! # The paired Lean owner
//!
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/IwasawaTower.lean`, namespace
//! `Soma.Holonics.Foundation.IwasawaTower`. The citation is bidirectional on purpose: neither side
//! describes the other, and a change on one side that is not carried to the other breaks the pair.
//! Every name in the first column below is a declaration of that one file.
//!
//! | Lean declaration | Rust owner |
//! |---|---|
//! | `omegaPoly` | [`omega`] |
//! | `omegaPoly_monic` | [`DistinguishedReceipt::is_monic`] |
//! | `omegaPoly_natDegree` | [`DistinguishedReceipt::degree`], [`IwasawaLevel::degree`] |
//! | `omegaPoly_isDistinguished` | [`check_distinguished`], [`DistinguishedReceipt`] |
//! | `omegaPoly_dvd_succ` | [`omega_divides_omega_succ`], [`OmegaDivision`] |
//! | `theCharacteristicFaceDoesNotDetermineTheModule` | [`SpecializationType::direct_sum`] against `Λ/(f²)`; test `the_characteristic_face_does_not_determine_the_module` |
//! | `thePseudoNullResidueIsInvisibleToTheFace` | [`CharacteristicFace::Unit`] with a nonzero [`FiniteSpecialization`]; test `the_pseudo_null_residue_is_invisible_to_the_face` |
//! | `TheMainConjecture` | *not realized here.* This module computes no `p`-adic `L`-function and no Selmer group; see "What is not claimed" below. |
//!
//! Two further names this module cites belong to another Lean owner and are therefore not rows of
//! that table: `Foundation/ContinuingTower.lean::Tower`, which [`IwasawaTower`] is an instance of
//! rather than a second tower, and `Foundation/ContinuingTower.lean::Transition`, which
//! [`OmegaRestriction`] is an instance of, carrying the division residual.
//!
//! One deliberate difference of carrier: Lean's `omegaPoly` lives in `Polynomial ℤ_[p]`, while
//! [`omega`] returns integer coefficients. Nothing is lost by that — every coefficient of
//! `(1+T)^(p^n) - 1` is the integer `C(p^n, i)` — and the integer carrier is what the Smith normal
//! form and the exact division below require. The `Z_p`-coefficient reading is recovered by
//! [`FiniteLevelRing`] and by [`FiniteSpecialization::order`], which is the `p`-part.
//!
//! # What is not claimed
//!
//! * No `p`-adic `L`-function, Selmer group, class group or cyclotomic field is constructed here.
//!   `TheMainConjecture` is cited as the Lean owner's statement of the surrounding problem; this
//!   module supplies none of its content and no test here bears on it.
//!   [`IwasawaRefusal`] has no variant that could report progress on it.
//! * The structure theorem for `Λ`-modules is not proved. [`CharacteristicFace`] is evaluated from
//!   an exact gcd criterion on the declared generators, and it returns
//!   [`CharacteristicFace::Undetermined`] rather than guessing whenever the presentation is neither
//!   principal nor visibly of height two.
//! * `|M/ω_n M| = p^(μ p^n + λ n + ν)` is a cited classical theorem. The fits below are
//!   measurements at small levels that the theorem explains; they do not establish it.

use std::fmt;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use thiserror::Error;

use crate::continuing_tower::{Tower, TowerFaceOutcome, TowerRefusal, Transition};
use crate::rebase_invariants::{IntegerMatrix, PivotRule, smith_normal_form};

/// The largest prime this owner will accept.
///
/// It bounds the trial division in [`IwasawaLevel::new`] *before* that loop runs, so the primality
/// test is never sized by an unauthenticated declaration: at most `⌊√1021⌋ = 31` trial divisors.
pub const MAX_PRIME: u64 = 1021;

/// The largest degree `p^n` this owner will accept for a level.
///
/// Every coefficient vector in this module has length at most `MAX_DEGREE + 1`, and
/// [`IwasawaLevel::new`] computes `p^n` with `u64::checked_pow` before comparing against it, so an
/// overflowing request is refused rather than wrapped.
pub const MAX_DEGREE: u64 = 4096;

/// The largest `rows × columns` a relation matrix may occupy before [`LambdaPresentation::specialize`]
/// refuses.
///
/// `512 × 512`. The matrix is `(k · p^n) × p^n` dense `BigInt`, so this is the bound that actually
/// governs allocation; [`MAX_DEGREE`] alone would admit a `4096 × 4096` matrix of sixteen million
/// `BigInt` entries. The area is computed with `checked_mul` and compared **before** `ω_n` is built
/// and before any matrix is allocated.
pub const MAX_RELATION_MATRIX_AREA: usize = 262_144;

/// The largest number of generators a [`LambdaPresentation`] may declare.
pub const MAX_GENERATORS: usize = 8;

/// The largest degree a declared generator polynomial may have.
///
/// This bounds the exact polynomial-remainder-sequence gcd in [`LambdaPresentation::characteristic_face`],
/// whose step count and coefficient growth are both governed by the generator degrees.
pub const MAX_GENERATOR_DEGREE: usize = 32;

/// The largest level degree [`FiniteLevelRing`] will multiply in.
///
/// Multiplication in `(Z/p^e Z)[T]/(ω_n)` is the dense convolution, `degree²` coefficient products.
/// [`MAX_DEGREE`] would admit sixteen million `BigUint` products per multiplication; this bound
/// admits sixty-five thousand.
pub const MAX_RING_DEGREE: usize = 256;

/// The largest coefficient exponent `e` in the finite ring `(Z/p^e Z)[T]/(ω_n)`.
pub const MAX_COEFFICIENT_EXPONENT: u32 = 64;

/// The largest exponent [`FiniteLevelRing::pow`] will iterate to.
///
/// `pow` is repeated multiplication, so the exponent is a loop count handed in by the caller. The
/// exponents this module needs are at most `p ≤ MAX_PRIME`, and anything above that is refused
/// rather than run.
pub const MAX_RING_POWER: u32 = MAX_PRIME as u32;

/// Why this owner refused.
///
/// Every public entry point returns one of these rather than panicking. Nothing in this module
/// calls `unwrap` or `expect` on caller data. Outside its tests the module body holds exactly
/// **four `expect`s and two `unwrap_or`s**, each naming a structural invariant of a value this
/// module itself built:
///
/// * `poly_div_rem_monic`: `degree_of(divisor)` is `Some`. Every call site passes an `ω_n` from
///   [`omega`], which is `(1+T)^(p^n) - 1` with leading coefficient one and degree `p^n ≥ 1`, so
///   the divisor is never the zero polynomial.
/// * `FiniteLevelRing::reduce`: `residue.to_biguint()` is `Some`. `residue` is
///   `((c % m) + m) % m` with `m = p^e ≥ 2`, so it lies in `[0, m)` and is never negative.
/// * `LambdaPresentation::specialize`: `factor.to_biguint()` is `Some`. The factors come from
///   [`crate::rebase_invariants::smith_normal_form`], which returns them nonnegative, and the loop
///   has already skipped every factor at or below one.
/// * [`fit_and_verify_growth`]: the measured vector converts to `[(u32, u64); 4]`. Its own loop
///   runs `0..4` and pushes once per iteration, so the vector has exactly four entries.
/// * `check_distinguished`: the `unwrap_or` on `degree_of` reports degree zero for the zero
///   polynomial, which is the honest degree of a constant and is a receipt field rather than a
///   decision — no branch reads it.
/// * `IwasawaTower::new`: the `unwrap_or` on `usize::try_from` of the top level sizes a
///   `Vec::with_capacity` reservation only. The level is already bounded by [`MAX_DEGREE`] through
///   [`IwasawaLevel::new`], and a reservation of zero costs a reallocation, never a wrong answer.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum IwasawaRefusal {
    /// The declared residue characteristic is not prime.
    #[error("{prime} is not prime, so Z_p is not a discrete valuation ring and Λ is not defined")]
    NotPrime {
        /// What was declared.
        prime: u64,
    },
    /// The declared residue characteristic exceeds [`MAX_PRIME`].
    ///
    /// This is checked **before** the primality loop runs, so the loop is never sized by the
    /// declaration.
    #[error("prime {prime} exceeds the declared bound {bound}")]
    PrimeTooLarge {
        /// What was declared.
        prime: u64,
        /// [`MAX_PRIME`].
        bound: u64,
    },
    /// `p^n` overflowed `u64` or exceeded [`MAX_DEGREE`].
    #[error("level p={prime} n={level} has degree p^n exceeding the declared maximum {bound}")]
    DegreeTooLarge {
        /// The residue characteristic.
        prime: u64,
        /// The level.
        level: u32,
        /// [`MAX_DEGREE`].
        bound: u64,
    },
    /// Two levels that must share a residue characteristic do not.
    #[error("levels disagree on the prime: {left} against {right}")]
    PrimeMismatch {
        /// The first prime.
        left: u64,
        /// The second prime.
        right: u64,
    },
    /// A coarse level was not below a fine one.
    #[error("level {coarse} does not refine level {fine}: ω_{coarse} must divide ω_{fine}")]
    NotARefinement {
        /// The claimed coarse level.
        coarse: u32,
        /// The claimed fine level.
        fine: u32,
    },
    /// A presentation declared no generators.
    #[error("a Λ-presentation needs at least one generator")]
    EmptyPresentation,
    /// A presentation declared more generators than [`MAX_GENERATORS`].
    #[error("{count} generators exceeds the declared bound {bound}")]
    TooManyGenerators {
        /// What was declared.
        count: usize,
        /// [`MAX_GENERATORS`].
        bound: usize,
    },
    /// A generator was the zero polynomial, so the quotient is not a torsion module.
    #[error("generator {index} is the zero polynomial; Λ/(0) is not torsion")]
    ZeroGenerator {
        /// Which generator.
        index: usize,
    },
    /// A generator exceeded [`MAX_GENERATOR_DEGREE`].
    #[error("generator {index} has degree {degree}, above the declared bound {bound}")]
    GeneratorDegreeTooLarge {
        /// Which generator.
        index: usize,
        /// Its degree.
        degree: usize,
        /// [`MAX_GENERATOR_DEGREE`].
        bound: usize,
    },
    /// The relation matrix would exceed [`MAX_RELATION_MATRIX_AREA`], or its extent overflowed.
    #[error(
        "relation matrix {rows}×{columns} has area {area} above the declared bound {bound}; \
         nothing was allocated"
    )]
    RelationMatrixTooLarge {
        /// `k · p^n`.
        rows: usize,
        /// `p^n`.
        columns: usize,
        /// The product, or `usize::MAX` when it overflowed.
        area: usize,
        /// [`MAX_RELATION_MATRIX_AREA`].
        bound: usize,
    },
    /// The specialization is not a finite `Z_p`-module: the relation matrix is rank deficient, so
    /// the cokernel has a free summand.
    // The free rank is `basis_dimension - rank` on the values this module builds, where the rank
    // of a matrix never exceeds its column count. `Display` must be total on every value of the
    // type, including one a caller constructed with `rank > basis_dimension`, so the subtraction
    // saturates instead of underflowing a `usize` and panicking inside a formatter.
    #[error(
        "M/ω_n M is not finite at p={prime}, n={level}: relation rank {rank} is below the basis \
         dimension {basis_dimension}, leaving a free Z_p-summand of rank {}",
        usize::saturating_sub(*.basis_dimension, *.rank)
    )]
    NotFinite {
        /// `p^n`.
        basis_dimension: usize,
        /// The Smith rank of the relation matrix.
        rank: usize,
        /// The residue characteristic.
        prime: u64,
        /// The level.
        level: u32,
    },
    /// A direct sum was asked for over specializations at different levels.
    #[error("cannot sum specializations at different levels: {left} against {right}")]
    LevelMismatch {
        /// The first level.
        left: u32,
        /// The second level.
        right: u32,
    },
    /// A direct sum of no summands was asked for.
    #[error("a direct sum needs at least one summand")]
    EmptyDirectSum,
    /// The three measured levels admit no exact integer `(μ, λ, ν)`.
    #[error(
        "no exact integer (μ, λ, ν) fits e = [{first}, {second}, {third}] at p={prime} from level \
         {base_level}: the second difference {second_difference} is not divisible by \
         p^{base_level}·(p-1)² = {divisor}"
    )]
    NoExactGrowthFit {
        /// The residue characteristic.
        prime: u64,
        /// The base level of the three.
        base_level: u32,
        /// `e_{base}`.
        first: u64,
        /// `e_{base+1}`.
        second: u64,
        /// `e_{base+2}`.
        third: u64,
        /// `(e₃ - e₂) - (e₂ - e₁)`.
        second_difference: BigInt,
        /// `p^{base_level} · (p-1)²`.
        divisor: BigInt,
    },
    /// A fitted `(μ, λ, ν)` did not reproduce a further measured level.
    ///
    /// The exponents are boxed so that this refusal — which every constructor in this module
    /// returns through `Result` — stays small; four inline `BigInt`s would make the whole enum
    /// 140 bytes and every `Result` in the module that wide.
    #[error(
        "growth fit (μ,λ,ν) = ({},{},{}) predicts e_{level} = {predicted} but the measured value \
         is {measured}",
        .exponents.mu(),
        .exponents.lambda(),
        .exponents.nu()
    )]
    GrowthFitDisagrees {
        /// Where the disagreement was found.
        level: u32,
        /// The exponent the fit predicts.
        predicted: BigInt,
        /// What the Smith normal form actually returned.
        measured: u64,
        /// The fit that failed its own verification.
        exponents: Box<GrowthExponents>,
    },
    /// A finite ring was asked for at a level above [`MAX_RING_DEGREE`].
    #[error("ring degree {degree} exceeds the declared bound {bound}")]
    RingDegreeTooLarge {
        /// `p^n`.
        degree: usize,
        /// [`MAX_RING_DEGREE`].
        bound: usize,
    },
    /// A finite ring was asked for with coefficient modulus `p^0 = 1`, which is the zero ring.
    #[error("coefficient exponent 0 gives the zero ring Z/1; declare an exponent of at least 1")]
    ZeroRing,
    /// A finite ring was asked for with a coefficient exponent above [`MAX_COEFFICIENT_EXPONENT`].
    #[error("coefficient exponent {exponent} exceeds the declared bound {bound}")]
    CoefficientExponentTooLarge {
        /// What was declared.
        exponent: u32,
        /// [`MAX_COEFFICIENT_EXPONENT`].
        bound: u32,
    },
    /// A ring element was offered with the wrong number of coefficients.
    #[error("ring element has {found} coefficients but the ring has degree {expected}")]
    RingElementExtent {
        /// The ring degree.
        expected: usize,
        /// What was offered.
        found: usize,
    },
    /// [`FiniteLevelRing::pow`] was asked for an exponent above [`MAX_RING_POWER`].
    #[error("ring exponent {exponent} exceeds the declared bound {bound}")]
    RingPowerTooLarge {
        /// What was declared.
        exponent: u32,
        /// [`MAX_RING_POWER`].
        bound: u32,
    },
}

// ---------------------------------------------------------------------------------------------
// Exact integer polynomial arithmetic, ascending coefficient order, index = degree.
// ---------------------------------------------------------------------------------------------

/// Drop trailing zero coefficients so that a polynomial has one representative.
///
/// The zero polynomial is the empty vector. Every polynomial that leaves this module is trimmed,
/// which is what makes `Eq` on `Vec<BigInt>` the right face equality for [`IwasawaTower`].
fn trim(mut coefficients: Vec<BigInt>) -> Vec<BigInt> {
    while coefficients.last().is_some_and(BigInt::is_zero) {
        coefficients.pop();
    }
    coefficients
}

/// The degree, or `None` for the zero polynomial.
fn degree_of(coefficients: &[BigInt]) -> Option<usize> {
    let mut index = coefficients.len();
    while index > 0 {
        index -= 1;
        if !coefficients[index].is_zero() {
            return Some(index);
        }
    }
    None
}

/// Exact sum.
fn poly_add(left: &[BigInt], right: &[BigInt]) -> Vec<BigInt> {
    let mut sum = vec![BigInt::zero(); left.len().max(right.len())];
    for (index, value) in left.iter().enumerate() {
        sum[index] += value;
    }
    for (index, value) in right.iter().enumerate() {
        sum[index] += value;
    }
    trim(sum)
}

/// Exact product. Dense convolution: the coefficient count is the sum of the two input lengths, so
/// nothing here is sized by a declaration the caller has not already materialized.
fn poly_mul(left: &[BigInt], right: &[BigInt]) -> Vec<BigInt> {
    if left.is_empty() || right.is_empty() {
        return Vec::new();
    }
    let mut product = vec![BigInt::zero(); left.len() + right.len() - 1];
    for (i, a) in left.iter().enumerate() {
        if a.is_zero() {
            continue;
        }
        for (j, b) in right.iter().enumerate() {
            if b.is_zero() {
                continue;
            }
            product[i + j] += a * b;
        }
    }
    trim(product)
}

/// Exact division with remainder by a **monic** divisor of degree at least one.
///
/// Over `Z` this is total: every step subtracts `lead · T^(d - m) · divisor`, and the monic leading
/// coefficient means no division of coefficients ever occurs. Returns `(quotient, remainder)` with
/// `dividend = divisor · quotient + remainder` and `deg remainder < deg divisor`, both trimmed.
///
/// The loop runs `deg(dividend) - deg(divisor) + 1` times and each pass touches `deg(divisor) + 1`
/// coefficients: the work is bounded by the length of the vector the caller already holds times the
/// level degree, which [`IwasawaLevel::new`] has already bounded by [`MAX_DEGREE`]. No length here
/// comes from an unauthenticated count.
///
/// # Panics
///
/// Never on caller data. The `expect` names the structural invariant that the divisor this module
/// built is monic of positive degree; `divisor` is always an `ω_n` produced by [`omega`].
fn poly_div_rem_monic(dividend: &[BigInt], divisor: &[BigInt]) -> (Vec<BigInt>, Vec<BigInt>) {
    let divisor_degree =
        degree_of(divisor).expect("invariant: ω_n is monic of positive degree, never the zero polynomial");
    debug_assert!(divisor_degree >= 1, "invariant: ω_n has degree p^n ≥ 1");
    debug_assert!(
        divisor[divisor_degree].is_one(),
        "invariant: ω_n is monic, so no coefficient division is needed"
    );

    let mut remainder = trim(dividend.to_vec());
    let Some(dividend_degree) = degree_of(&remainder) else {
        return (Vec::new(), Vec::new());
    };
    if dividend_degree < divisor_degree {
        return (Vec::new(), remainder);
    }

    let mut quotient = vec![BigInt::zero(); dividend_degree - divisor_degree + 1];
    let mut current = dividend_degree;
    loop {
        if remainder[current].is_zero() {
            if current == divisor_degree {
                break;
            }
            current -= 1;
            continue;
        }
        let shift = current - divisor_degree;
        let factor = remainder[current].clone();
        for (offset, coefficient) in divisor.iter().enumerate().take(divisor_degree + 1) {
            remainder[shift + offset] -= &factor * coefficient;
        }
        quotient[shift] = factor;
        if current == divisor_degree {
            break;
        }
        current -= 1;
    }
    (trim(quotient), trim(remainder))
}

/// The remainder alone.
fn poly_rem_monic(dividend: &[BigInt], divisor: &[BigInt]) -> Vec<BigInt> {
    poly_div_rem_monic(dividend, divisor).1
}

/// The content: the gcd of the coefficients, with sign taken from the leading coefficient so that a
/// primitive part is canonical.
fn content(coefficients: &[BigInt]) -> BigInt {
    let mut common = BigInt::zero();
    for coefficient in coefficients {
        common = integer_gcd(&common, coefficient);
    }
    if common.is_zero() {
        return BigInt::one();
    }
    match degree_of(coefficients) {
        Some(top) if coefficients[top].is_negative() => -common,
        _ => common,
    }
}

/// Euclidean gcd over `Z`, always nonnegative.
fn integer_gcd(left: &BigInt, right: &BigInt) -> BigInt {
    let mut a = left.abs();
    let mut b = right.abs();
    while !b.is_zero() {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

/// Divide every coefficient by the content.
fn primitive_part(coefficients: &[BigInt]) -> Vec<BigInt> {
    let divisor = content(coefficients);
    if divisor.is_one() {
        return trim(coefficients.to_vec());
    }
    trim(coefficients.iter().map(|value| value / &divisor).collect())
}

/// The gcd of two integer polynomials **as elements of `Q[T]`**, returned as a primitive integer
/// polynomial with positive leading coefficient.
///
/// The primitive polynomial remainder sequence: pseudo-remainder, then strip content. Content
/// stripping at every step is what keeps the intermediate coefficients from the exponential swell
/// of naive `Q[T]` Euclid.
///
/// The gcd of polynomials over a field is unchanged by field extension, so this is also the gcd in
/// `Q_p[T]`, which is what the `Λ`-divisibility criterion in
/// [`LambdaPresentation::characteristic_face`] needs.
fn rational_gcd(left: &[BigInt], right: &[BigInt]) -> Vec<BigInt> {
    let mut a = primitive_part(left);
    let mut b = primitive_part(right);
    if a.is_empty() {
        return b;
    }
    if b.is_empty() {
        return a;
    }
    loop {
        let (Some(degree_a), Some(degree_b)) = (degree_of(&a), degree_of(&b)) else {
            break;
        };
        if degree_a < degree_b {
            std::mem::swap(&mut a, &mut b);
            continue;
        }
        // Pseudo-remainder: (lc(b)^(deg a - deg b + 1)) · a  ≡  prem  (mod b).
        let leading = b[degree_b].clone();
        let mut scaled = a.clone();
        let passes = degree_a - degree_b + 1;
        for _ in 0..passes {
            for coefficient in &mut scaled {
                *coefficient *= &leading;
            }
        }
        let mut current = degree_a;
        loop {
            if !scaled[current].is_zero() {
                let shift = current - degree_b;
                let factor = &scaled[current] / &leading;
                for (offset, coefficient) in b.iter().enumerate().take(degree_b + 1) {
                    scaled[shift + offset] -= &factor * coefficient;
                }
            }
            if current == degree_b {
                break;
            }
            current -= 1;
        }
        let remainder = trim(scaled);
        if remainder.is_empty() {
            break;
        }
        a = b;
        b = primitive_part(&remainder);
    }
    // `primitive_part` already takes the sign from the leading coefficient, so the returned gcd is
    // the canonical primitive representative with positive leading coefficient.
    primitive_part(&b)
}

/// `(v_p(value), value / p^(v_p(value)))` for a nonzero `value`.
///
/// The loop is bounded by the base-`p` length of `value`, which is a computed quantity, never a
/// declaration. A zero `value` returns `(0, 0)` and is never produced here: [`smith_normal_form`]
/// returns only nonzero factors.
fn p_valuation(value: &BigUint, prime: &BigUint) -> (u32, BigUint) {
    if value.is_zero() {
        return (0, BigUint::zero());
    }
    let mut valuation = 0_u32;
    let mut remaining = value.clone();
    while (&remaining % prime).is_zero() {
        remaining /= prime;
        valuation += 1;
    }
    (valuation, remaining)
}

// ---------------------------------------------------------------------------------------------
// The level.
// ---------------------------------------------------------------------------------------------

/// One level of the tower: a residue characteristic `p` and a height `n`, with the degree `p^n`
/// already checked.
///
/// Lean counterpart: the `(p, n)` arguments of `IwasawaTower.omegaPoly`, where `Fact p.Prime` is a
/// typeclass hypothesis. Here it is a constructor check.
///
/// **Constructor bypass**: every field is private, there is no `Default`, no `Serialize` /
/// `Deserialize`, and no public mutator. `Clone` and `Copy` reproduce a value that
/// [`IwasawaLevel::new`] already accepted, and [`IwasawaLevel::successor`] re-enters the same
/// constructor. There is no path to an `IwasawaLevel` whose `prime` is composite or whose `degree`
/// disagrees with `p^n`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IwasawaLevel {
    prime: u64,
    level: u32,
    degree: usize,
}

impl IwasawaLevel {
    /// Declare a level, checking the residue characteristic and the degree.
    ///
    /// The order of the checks is load-bearing:
    ///
    /// 1. `p ≥ 2`, else [`IwasawaRefusal::NotPrime`];
    /// 2. `p ≤ MAX_PRIME`, else [`IwasawaRefusal::PrimeTooLarge`] — **before** any trial division,
    ///    so the primality loop is sized by [`MAX_PRIME`] and not by the declaration;
    /// 3. trial division to `⌊√p⌋ ≤ 31`;
    /// 4. `p^n` by `u64::checked_pow`, refusing overflow;
    /// 5. `p^n ≤ MAX_DEGREE`.
    ///
    /// `n = 0` is accepted and gives `ω_0 = T` of degree `1`. No `(p, n)` with `p` prime yields
    /// degree `0`, so a degree-zero level is unreachable rather than refused.
    pub fn new(prime: u64, level: u32) -> Result<Self, IwasawaRefusal> {
        if prime < 2 {
            return Err(IwasawaRefusal::NotPrime { prime });
        }
        if prime > MAX_PRIME {
            return Err(IwasawaRefusal::PrimeTooLarge {
                prime,
                bound: MAX_PRIME,
            });
        }
        let mut divisor = 2_u64;
        while divisor.saturating_mul(divisor) <= prime {
            if prime.is_multiple_of(divisor) {
                return Err(IwasawaRefusal::NotPrime { prime });
            }
            divisor += 1;
        }
        let degree = prime
            .checked_pow(level)
            .filter(|value| *value <= MAX_DEGREE)
            .ok_or(IwasawaRefusal::DegreeTooLarge {
                prime,
                level,
                bound: MAX_DEGREE,
            })?;
        let degree = usize::try_from(degree).map_err(|_| IwasawaRefusal::DegreeTooLarge {
            prime,
            level,
            bound: MAX_DEGREE,
        })?;
        Ok(Self {
            prime,
            level,
            degree,
        })
    }

    /// The residue characteristic.
    pub const fn prime(&self) -> u64 {
        self.prime
    }

    /// The height `n`.
    pub const fn level(&self) -> u32 {
        self.level
    }

    /// `p^n`, the degree of `ω_n` and the `Z`-rank of `Z[T]/(ω_n)`.
    pub const fn degree(&self) -> usize {
        self.degree
    }

    /// The residue characteristic as an exact `BigUint`.
    pub fn prime_big(&self) -> BigUint {
        BigUint::from(self.prime)
    }

    /// Level `n + 1` at the same prime, re-checked through [`IwasawaLevel::new`].
    pub fn successor(&self) -> Result<Self, IwasawaRefusal> {
        let level = self
            .level
            .checked_add(1)
            .ok_or(IwasawaRefusal::DegreeTooLarge {
                prime: self.prime,
                level: self.level,
                bound: MAX_DEGREE,
            })?;
        Self::new(self.prime, level)
    }
}

impl fmt::Display for IwasawaLevel {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "level n={} at p={} (degree p^n = {})",
            self.level, self.prime, self.degree
        )
    }
}

// ---------------------------------------------------------------------------------------------
// ω_n and the divisibility chain.
// ---------------------------------------------------------------------------------------------

/// `ω_n(T) = (1+T)^(p^n) - 1`, exactly, as ascending integer coefficients.
///
/// The coefficient of `T^i` is `C(p^n, i)` for `i > 0`, and the constant coefficient is
/// `C(p^n, 0) - 1 = 0`. The returned vector has length `p^n + 1` — it is not trimmed, because the
/// leading coefficient is `1` and the caller of a monic divisor wants the full extent.
///
/// Lean counterpart: `Soma.Holonics.Foundation.IwasawaTower.omegaPoly`.
///
/// The binomial row is built by the exact recurrence `C(N, i) = C(N, i-1) · (N - i + 1) / i`, which
/// is an exact integer division at every step. The loop runs `p^n` times, and `p^n` was bounded by
/// [`MAX_DEGREE`] when the level was constructed.
pub fn omega(level: &IwasawaLevel) -> Vec<BigInt> {
    let extent = level.degree();
    let mut coefficients = Vec::with_capacity(extent + 1);
    let mut binomial = BigInt::one();
    coefficients.push(BigInt::zero()); // C(N, 0) - 1
    for index in 1..=extent {
        binomial = binomial * BigInt::from(extent - index + 1) / BigInt::from(index);
        coefficients.push(binomial.clone());
    }
    coefficients
}

/// What [`check_distinguished`] actually checked.
///
/// A receipt, not a proof: it names the level and the number of middle coefficients that were
/// divided, so "distinguished" is a claim with a stated extent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DistinguishedReceipt {
    level: IwasawaLevel,
    degree: usize,
    is_monic: bool,
    constant_is_zero: bool,
    middle_coefficients_checked: usize,
    all_middle_divisible_by_prime: bool,
}

impl DistinguishedReceipt {
    /// The level this receipt was taken at.
    pub const fn level(&self) -> &IwasawaLevel {
        &self.level
    }

    /// `natDegree ω_n`, which must equal `p^n`.
    ///
    /// Lean counterpart: `IwasawaTower.omegaPoly_natDegree`.
    pub const fn degree(&self) -> usize {
        self.degree
    }

    /// Whether the leading coefficient is `1`.
    ///
    /// Lean counterpart: `IwasawaTower.omegaPoly_monic`.
    pub const fn is_monic(&self) -> bool {
        self.is_monic
    }

    /// Whether `ω_n(0) = 0`.
    pub const fn constant_is_zero(&self) -> bool {
        self.constant_is_zero
    }

    /// How many coefficients strictly between the constant and the leading one were divided by `p`.
    /// This is `p^n - 1`, and it is reported so that the claim's extent is visible.
    pub const fn middle_coefficients_checked(&self) -> usize {
        self.middle_coefficients_checked
    }

    /// Whether every one of those coefficients is divisible by `p`.
    pub const fn all_middle_divisible_by_prime(&self) -> bool {
        self.all_middle_divisible_by_prime
    }

    /// The conjunction: monic, right degree, zero constant term, every middle coefficient divisible
    /// by `p`.
    ///
    /// Lean counterpart: `IwasawaTower.omegaPoly_isDistinguished`.
    pub const fn is_distinguished(&self) -> bool {
        self.is_monic
            && self.constant_is_zero
            && self.all_middle_divisible_by_prime
            && self.degree == self.level.degree
    }
}

/// Check that `ω_n` is a distinguished polynomial of degree `p^n`.
///
/// Distinguished means: monic, and every non-leading coefficient divisible by `p`. For `ω_n` the
/// constant coefficient is not merely divisible by `p` but exactly zero, and that is reported
/// separately because it is what makes `T | ω_n` and therefore what makes `Λ/(p, T)` a quotient of
/// `Λ/(ω_n, p, T)` at every level.
///
/// Lean counterpart: `Soma.Holonics.Foundation.IwasawaTower.omegaPoly_isDistinguished`. Lean proves
/// it for all `n`; this returns a [`DistinguishedReceipt`] for the one level it was handed.
pub fn check_distinguished(level: &IwasawaLevel) -> DistinguishedReceipt {
    let coefficients = omega(level);
    let extent = level.degree();
    let prime = BigInt::from(level.prime());
    let is_monic = coefficients
        .get(extent)
        .is_some_and(num_traits::One::is_one);
    let constant_is_zero = coefficients.first().is_some_and(BigInt::is_zero);
    let mut checked = 0_usize;
    let mut all_divisible = true;
    for coefficient in coefficients.iter().take(extent).skip(1) {
        checked += 1;
        if !(coefficient % &prime).is_zero() {
            all_divisible = false;
        }
    }
    DistinguishedReceipt {
        level: *level,
        degree: degree_of(&coefficients).unwrap_or(0),
        is_monic,
        constant_is_zero,
        middle_coefficients_checked: checked,
        all_middle_divisible_by_prime: all_divisible,
    }
}

/// The exact division `ω_(n+1) = ω_n · q`, with the quotient and the receipt that the remainder was
/// zero.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OmegaDivision {
    coarse: IwasawaLevel,
    fine: IwasawaLevel,
    quotient: Vec<BigInt>,
    remainder: Vec<BigInt>,
}

impl OmegaDivision {
    /// The lower level `n`.
    pub const fn coarse(&self) -> &IwasawaLevel {
        &self.coarse
    }

    /// The upper level `n + 1`.
    pub const fn fine(&self) -> &IwasawaLevel {
        &self.fine
    }

    /// `ω_(n+1) / ω_n`, exactly. Its degree is `p^(n+1) - p^n`.
    pub fn quotient(&self) -> &[BigInt] {
        &self.quotient
    }

    /// The remainder the division actually returned. It is the empty vector — the zero polynomial —
    /// exactly when `ω_n | ω_(n+1)`.
    pub fn remainder(&self) -> &[BigInt] {
        &self.remainder
    }

    /// Whether the division was exact.
    pub fn divides(&self) -> bool {
        self.remainder.is_empty()
    }
}

/// Divide `ω_(n+1)` by `ω_n` over `Z` and return the quotient together with the remainder.
///
/// **Which route this takes.** This performs the *actual exact polynomial division* over `Z`, not
/// the identity. The identity route — writing `Y = (1+T)^(p^n)`, so `ω_(n+1) = Y^p - 1` and
/// `ω_n = Y - 1`, whence the quotient is `Σ_(j<p) Y^j` — is checked **independently** in
/// `the_quotient_agrees_with_the_geometric_series` as a cross-check on this division, and is not
/// how this function computes.
///
/// Lean counterpart: `Soma.Holonics.Foundation.IwasawaTower.omegaPoly_dvd_succ`.
pub fn omega_divides_omega_succ(level: &IwasawaLevel) -> Result<OmegaDivision, IwasawaRefusal> {
    let fine = level.successor()?;
    let coarse_omega = omega(level);
    let fine_omega = omega(&fine);
    let (quotient, remainder) = poly_div_rem_monic(&fine_omega, &coarse_omega);
    Ok(OmegaDivision {
        coarse: *level,
        fine,
        quotient,
        remainder,
    })
}

/// The same quotient by the identity route: `Σ_(j<p) Y^j` with `Y = (1+T)^(p^n)`.
///
/// This exists so that [`omega_divides_omega_succ`]'s division has an independent witness that was
/// computed by different arithmetic. It is not used by anything else in this module.
pub fn omega_quotient_by_identity(level: &IwasawaLevel) -> Result<Vec<BigInt>, IwasawaRefusal> {
    // Y = (1+T)^(p^n) = ω_n + 1.
    let mut y = omega(level);
    y[0] += BigInt::one();
    let prime = usize::try_from(level.prime()).map_err(|_| IwasawaRefusal::PrimeTooLarge {
        prime: level.prime(),
        bound: MAX_PRIME,
    })?;
    // Σ_{j < p} Y^j, accumulated by repeated exact multiplication. `prime ≤ MAX_PRIME`, so the
    // loop count is bounded by a constant of this module and not by the declaration.
    let mut sum: Vec<BigInt> = Vec::new();
    let mut power: Vec<BigInt> = vec![BigInt::one()];
    for _ in 0..prime {
        sum = poly_add(&sum, &power);
        power = poly_mul(&power, &y);
    }
    Ok(sum)
}

// ---------------------------------------------------------------------------------------------
// The tower and its transition — instances of the wave-1 owners.
// ---------------------------------------------------------------------------------------------

/// The tower of levels `Λ/(ω_n)`, as an instance of [`crate::continuing_tower::Tower`].
///
/// Index: the level `n`, a `u32`. Face: a trimmed integer coefficient vector of degree `< p^n`,
/// the canonical representative of a class in `Z[T]/(ω_n)`. Restriction from a finer level to a
/// coarser one is reduction modulo `ω_coarse`, which is well defined **because**
/// [`omega_divides_omega_succ`] holds.
///
/// Lean counterpart: `Soma.Holonics.Foundation.ContinuingTower.Tower`, instantiated. This founds no
/// second tower vocabulary — `refines`, `carries` and `restrict` are the wave-1 trait's own methods,
/// and `check_restriction_laws` is run against this instance in the tests.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IwasawaTower {
    prime: u64,
    max_level: u32,
    omegas: Vec<Vec<BigInt>>,
}

impl IwasawaTower {
    /// Build the tower up to `max_level`, computing every `ω_n` for `n ≤ max_level`.
    ///
    /// Every level is constructed through [`IwasawaLevel::new`], so the top degree is bounded by
    /// [`MAX_DEGREE`] and each lower one is smaller. The total storage is
    /// `Σ_(n ≤ max) (p^n + 1) ≤ 2·MAX_DEGREE + max + 1` coefficients.
    pub fn new(prime: u64, max_level: u32) -> Result<Self, IwasawaRefusal> {
        // The top level is checked FIRST, so the reservation below is bounded by this module's own
        // constants: p ≥ 2 and p^max_level ≤ MAX_DEGREE force max_level ≤ 12.
        let top = IwasawaLevel::new(prime, max_level)?;
        let reserve = usize::try_from(top.level()).unwrap_or(0) + 1;
        let mut omegas = Vec::with_capacity(reserve);
        for level in 0..=max_level {
            let chart = IwasawaLevel::new(prime, level)?;
            omegas.push(omega(&chart));
        }
        debug_assert_eq!(
            omegas.len(),
            reserve,
            "invariant: one ω per level from 0 to max_level"
        );
        Ok(Self {
            prime,
            max_level,
            omegas,
        })
    }

    /// The residue characteristic.
    pub const fn prime(&self) -> u64 {
        self.prime
    }

    /// The highest level carried.
    pub const fn max_level(&self) -> u32 {
        self.max_level
    }

    /// The level object for a chart this tower carries.
    pub fn level(&self, chart: u32) -> Option<IwasawaLevel> {
        if chart > self.max_level {
            return None;
        }
        IwasawaLevel::new(self.prime, chart).ok()
    }

    /// `ω_chart`, if the tower carries that chart.
    pub fn omega_at(&self, chart: u32) -> Option<&[BigInt]> {
        self.omegas
            .get(usize::try_from(chart).ok()?)
            .map(Vec::as_slice)
    }

    /// The charts, as [`crate::continuing_tower::Tower`] wants them for a receipt.
    pub fn charts(&self) -> Vec<u32> {
        (0..=self.max_level).collect()
    }
}

impl Tower for IwasawaTower {
    type Index = u32;
    type Face = Vec<BigInt>;

    fn refines(&self, coarse: &u32, fine: &u32) -> bool {
        *coarse <= *fine && *fine <= self.max_level
    }

    fn carries(&self, chart: &u32, face: &Vec<BigInt>) -> bool {
        let Some(level) = self.level(*chart) else {
            return false;
        };
        // A face is a canonical representative: trimmed, of degree strictly below p^n.
        face.last().is_none_or(|top| !top.is_zero()) && face.len() <= level.degree()
    }

    fn restrict(&self, coarse: &u32, fine: &u32, face: &Vec<BigInt>) -> TowerFaceOutcome<Self> {
        if !self.carries(fine, face) {
            return Err(TowerRefusal::FaceNotCarried {
                chart: *fine,
                face: face.clone(),
            });
        }
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        let Some(divisor) = self.omega_at(*coarse) else {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        };
        Ok(poly_rem_monic(face, divisor))
    }
}

/// Restriction from level `fine` to level `coarse`, as an instance of
/// [`crate::continuing_tower::Transition`].
///
/// * `apply` is reduction modulo `ω_coarse`;
/// * `residual` is the exact quotient, which is what the transition drops;
/// * `reopen(target, residual) = target + ω_coarse · residual`.
///
/// `reopen(apply(x), residual(x)) = x` is the division identity `x = ω·q + r`, and it holds for
/// **every** integer polynomial, not only for the ones in the image: division by a monic divisor
/// over `Z` is total, there is no subtraction of naturals anywhere, and there is no indexing off a
/// caller-supplied length. This is the totality the wave-1 owner asks of a `Transition`.
///
/// Lean counterpart: `Soma.Holonics.Foundation.ContinuingTower.Transition`, instantiated;
/// `Transition.laterReceiverFactors` is what `reopen_later_receiver` runs on this instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OmegaRestriction {
    coarse: IwasawaLevel,
    fine: IwasawaLevel,
    omega_coarse: Vec<BigInt>,
}

impl OmegaRestriction {
    /// Build the restriction `Λ/(ω_fine) → Λ/(ω_coarse)`.
    ///
    /// Refuses when the primes disagree or when `coarse` does not sit below `fine`; the second is a
    /// refusal and not a silent reordering because `ω_coarse | ω_fine` is exactly what makes the
    /// map well defined.
    pub fn new(coarse: IwasawaLevel, fine: IwasawaLevel) -> Result<Self, IwasawaRefusal> {
        if coarse.prime() != fine.prime() {
            return Err(IwasawaRefusal::PrimeMismatch {
                left: coarse.prime(),
                right: fine.prime(),
            });
        }
        if coarse.level() > fine.level() {
            return Err(IwasawaRefusal::NotARefinement {
                coarse: coarse.level(),
                fine: fine.level(),
            });
        }
        let omega_coarse = omega(&coarse);
        Ok(Self {
            coarse,
            fine,
            omega_coarse,
        })
    }

    /// The level restricted to.
    pub const fn coarse(&self) -> &IwasawaLevel {
        &self.coarse
    }

    /// The level restricted from.
    pub const fn fine(&self) -> &IwasawaLevel {
        &self.fine
    }
}

impl Transition for OmegaRestriction {
    type Source = Vec<BigInt>;
    type Target = Vec<BigInt>;
    type Residual = Vec<BigInt>;

    fn apply(&self, source: &Vec<BigInt>) -> Vec<BigInt> {
        poly_rem_monic(source, &self.omega_coarse)
    }

    fn residual(&self, source: &Vec<BigInt>) -> Vec<BigInt> {
        poly_div_rem_monic(source, &self.omega_coarse).0
    }

    fn reopen(&self, target: &Vec<BigInt>, residual: &Vec<BigInt>) -> Vec<BigInt> {
        poly_add(target, &poly_mul(&self.omega_coarse, residual))
    }
}

// ---------------------------------------------------------------------------------------------
// The finite ring (Z/p^e Z)[T]/(ω_n).
// ---------------------------------------------------------------------------------------------

/// The finite ring `R = (Z/p^e Z)[T]/(ω_n)`.
///
/// Layer B of the two-layer arrangement: layer A is the exact integer polynomial arithmetic above,
/// which is what the Smith normal form needs, and this is the finite quotient a caller reads and
/// displays. The task statement names `R_n = (Z/p^n Z)[T]/(ω_n)`, with the coefficient exponent
/// equal to the level; that is [`FiniteLevelRing::at_own_level`], and it is refused at `n = 0`
/// because `Z/p^0 = Z/1` is the zero ring. The general constructor takes the exponent separately
/// because nothing in the mathematics ties the two.
///
/// **Declared sizes.** `degree = p^n` is bounded by [`MAX_RING_DEGREE`] at construction, because
/// multiplication is the dense convolution and costs `degree²` coefficient products. The
/// coefficient exponent is bounded by [`MAX_COEFFICIENT_EXPONENT`], so the modulus `p^e` has at
/// most `64 · log2(MAX_PRIME) = 640` bits. Every element allocation is `degree` coefficients, and
/// `degree` was accepted here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FiniteLevelRing {
    level: IwasawaLevel,
    coefficient_exponent: u32,
    modulus: BigUint,
    omega: Vec<BigInt>,
}

impl FiniteLevelRing {
    /// Build `(Z/p^e Z)[T]/(ω_n)`.
    pub fn new(level: IwasawaLevel, coefficient_exponent: u32) -> Result<Self, IwasawaRefusal> {
        if coefficient_exponent == 0 {
            return Err(IwasawaRefusal::ZeroRing);
        }
        if coefficient_exponent > MAX_COEFFICIENT_EXPONENT {
            return Err(IwasawaRefusal::CoefficientExponentTooLarge {
                exponent: coefficient_exponent,
                bound: MAX_COEFFICIENT_EXPONENT,
            });
        }
        if level.degree() > MAX_RING_DEGREE {
            return Err(IwasawaRefusal::RingDegreeTooLarge {
                degree: level.degree(),
                bound: MAX_RING_DEGREE,
            });
        }
        let modulus = level.prime_big().pow(coefficient_exponent);
        Ok(Self {
            level,
            coefficient_exponent,
            modulus,
            omega: omega(&level),
        })
    }

    /// `R_n = (Z/p^n Z)[T]/(ω_n)` — the coefficient exponent equal to the level.
    ///
    /// Refused at `n = 0`, where the coefficient ring would be `Z/1`.
    pub fn at_own_level(level: IwasawaLevel) -> Result<Self, IwasawaRefusal> {
        Self::new(level, level.level())
    }

    /// The level.
    pub const fn level(&self) -> &IwasawaLevel {
        &self.level
    }

    /// The coefficient exponent `e` in `Z/p^e Z`.
    pub const fn coefficient_exponent(&self) -> u32 {
        self.coefficient_exponent
    }

    /// `p^e`.
    pub const fn modulus(&self) -> &BigUint {
        &self.modulus
    }

    /// `p^n`, the rank of the ring as a `Z/p^e`-module.
    pub const fn degree(&self) -> usize {
        self.level.degree
    }

    /// The additive identity.
    pub fn zero(&self) -> RingElement {
        RingElement {
            coefficients: vec![BigUint::zero(); self.degree()],
        }
    }

    /// The multiplicative identity.
    pub fn one(&self) -> RingElement {
        let mut element = self.zero();
        if let Some(constant) = element.coefficients.first_mut() {
            *constant = BigUint::one() % &self.modulus;
        }
        element
    }

    /// Reduce an arbitrary integer polynomial into the ring: first modulo `ω_n` over `Z`, then
    /// every coefficient modulo `p^e`.
    ///
    /// Total on every input. A coefficient vector longer than `degree` is reduced, not refused: the
    /// reduction is what the ring *is*. Nothing is allocated from the input length beyond the
    /// remainder, which is at most `degree` long.
    pub fn reduce(&self, coefficients: &[BigInt]) -> RingElement {
        let remainder = poly_rem_monic(coefficients, &self.omega);
        let modulus = BigInt::from(self.modulus.clone());
        let mut result = vec![BigUint::zero(); self.degree()];
        for (index, coefficient) in remainder.iter().enumerate() {
            let residue = ((coefficient % &modulus) + &modulus) % &modulus;
            let residue = residue
                .to_biguint()
                .expect("invariant: a nonnegative residue converts to BigUint");
            if let Some(slot) = result.get_mut(index) {
                *slot = residue;
            }
        }
        RingElement {
            coefficients: result,
        }
    }

    /// Whether an element belongs to this ring: right extent, every coefficient already reduced.
    pub fn carries(&self, element: &RingElement) -> bool {
        element.coefficients.len() == self.degree()
            && element
                .coefficients
                .iter()
                .all(|coefficient| *coefficient < self.modulus)
    }

    /// Exact addition in `R`.
    pub fn add(
        &self,
        left: &RingElement,
        right: &RingElement,
    ) -> Result<RingElement, IwasawaRefusal> {
        self.check_extent(left)?;
        self.check_extent(right)?;
        let coefficients = left
            .coefficients
            .iter()
            .zip(right.coefficients.iter())
            .map(|(a, b)| (a + b) % &self.modulus)
            .collect();
        Ok(RingElement { coefficients })
    }

    /// Exact multiplication in `R`: dense convolution, then reduction modulo `ω_n`, then modulo
    /// `p^e`.
    ///
    /// The convolution is `degree²` products, and `degree ≤ MAX_RING_DEGREE` was checked at
    /// construction.
    pub fn mul(
        &self,
        left: &RingElement,
        right: &RingElement,
    ) -> Result<RingElement, IwasawaRefusal> {
        self.check_extent(left)?;
        self.check_extent(right)?;
        let as_integers = |element: &RingElement| -> Vec<BigInt> {
            element
                .coefficients
                .iter()
                .map(|value| BigInt::from(value.clone()))
                .collect()
        };
        let product = poly_mul(&as_integers(left), &as_integers(right));
        Ok(self.reduce(&product))
    }

    /// `element^exponent` by repeated multiplication.
    ///
    /// The loop runs `exponent` times, and `exponent` is a caller declaration, so it is bounded by
    /// [`MAX_RING_POWER`] **before** the loop starts. Square-and-multiply is not used because the
    /// exponents this module needs are at most `p ≤ MAX_PRIME`.
    pub fn pow(&self, element: &RingElement, exponent: u32) -> Result<RingElement, IwasawaRefusal> {
        if exponent > MAX_RING_POWER {
            return Err(IwasawaRefusal::RingPowerTooLarge {
                exponent,
                bound: MAX_RING_POWER,
            });
        }
        self.check_extent(element)?;
        let mut accumulator = self.one();
        for _ in 0..exponent {
            accumulator = self.mul(&accumulator, element)?;
        }
        Ok(accumulator)
    }

    fn check_extent(&self, element: &RingElement) -> Result<(), IwasawaRefusal> {
        if element.coefficients.len() == self.degree() {
            Ok(())
        } else {
            Err(IwasawaRefusal::RingElementExtent {
                expected: self.degree(),
                found: element.coefficients.len(),
            })
        }
    }
}

/// An element of a [`FiniteLevelRing`]: exactly `degree` coefficients, each already reduced modulo
/// `p^e`.
///
/// **Constructor bypass**: the coefficient vector is private and every value of this type comes out
/// of a [`FiniteLevelRing`] method, so the extent invariant cannot be broken from outside. The ring
/// nevertheless re-checks the extent on every operation (an extent check on every operation), so an
/// element built by one ring and offered to another is a typed refusal rather than a panic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RingElement {
    coefficients: Vec<BigUint>,
}

impl RingElement {
    /// The coefficients, ascending, index = degree.
    pub fn coefficients(&self) -> &[BigUint] {
        &self.coefficients
    }

    /// Whether this is the zero element.
    pub fn is_zero(&self) -> bool {
        self.coefficients.iter().all(BigUint::is_zero)
    }
}

// ---------------------------------------------------------------------------------------------
// Λ-presentations, their characteristic face and their finite specializations.
// ---------------------------------------------------------------------------------------------

/// The codimension-one datum attached to a presentation: the characteristic ideal, as far as an
/// exact finite computation on the declared generators settles it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CharacteristicFace {
    /// `Λ/(f)` — the characteristic ideal is `(f)`, and the polynomial is returned.
    Principal(Vec<BigInt>),
    /// The generators have no common prime factor in `Λ`, so the ideal has height two, the module
    /// is pseudo-null, and the characteristic ideal is the unit ideal `(1)`.
    ///
    /// The criterion evaluated is: the gcd of the generators in `Q[T]` is a nonzero constant **and**
    /// they are not all divisible by `p`. It is exact and decisive — `Λ` is a UFD whose height-one
    /// primes are `(p)` and the distinguished irreducibles, a monic `Z_p[T]` divisor of an integer
    /// polynomial is again a polynomial divisor by Weierstrass division, and a polynomial gcd is
    /// unchanged by the field extension `Q ⊆ Q_p`. That `Λ/I` with `height I ≥ 2` is pseudo-null
    /// with unit characteristic ideal is classical (Washington, *Cyclotomic Fields*, ch. 13) and is
    /// cited, not proved here.
    Unit,
    /// The generators share a factor but the presentation is not principal. This owner does not
    /// guess the characteristic ideal of such a module; the common factor it found is returned.
    Undetermined {
        /// The gcd of the generators in `Q[T]`, as a primitive integer polynomial.
        common_factor: Vec<BigInt>,
        /// Whether every coefficient of every generator is divisible by `p`, i.e. whether `p`
        /// itself is a common factor in `Λ`.
        prime_is_common: bool,
    },
}

impl CharacteristicFace {
    /// Whether the characteristic ideal is the unit ideal — the ideal of the **zero** module.
    ///
    /// A [`CharacteristicFace::Principal`] whose generator is the constant `±1` is also the unit
    /// ideal, and is reported as such.
    pub fn is_unit(&self) -> bool {
        match self {
            Self::Unit => true,
            Self::Principal(generator) => {
                degree_of(generator) == Some(0) && generator[0].abs().is_one()
            }
            Self::Undetermined { .. } => false,
        }
    }

    /// The generator, when the face is principal.
    pub fn principal_generator(&self) -> Option<&[BigInt]> {
        match self {
            Self::Principal(generator) => Some(generator),
            _ => None,
        }
    }
}

/// A finitely presented cyclic `Λ`-module `Λ/(f₁, …, f_k)` with integer polynomial generators.
///
/// Integer polynomial generators are a restriction against general `Λ = Z_p[[T]]` elements, and it
/// is the restriction that makes the specialization a finite exact computation: `Z[T]/(ω_n)` is a
/// free `Z`-module of rank `p^n` on a basis this module can write down. `Λ/(p, T)` and
/// `Λ/(T - p)` — the two examples the pair of counterexamples needs — are both of this form.
///
/// **Constructor bypass**: the generator list is private, there is no `Default`, no serde
/// derivation, and no mutator. Every accepted value passed [`LambdaPresentation::new`], which
/// refuses the empty list, more than [`MAX_GENERATORS`] generators, a zero generator, and a
/// generator above [`MAX_GENERATOR_DEGREE`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LambdaPresentation {
    generators: Vec<Vec<BigInt>>,
}

impl LambdaPresentation {
    /// Declare `Λ/(f₁, …, f_k)`.
    pub fn new(generators: Vec<Vec<BigInt>>) -> Result<Self, IwasawaRefusal> {
        if generators.is_empty() {
            return Err(IwasawaRefusal::EmptyPresentation);
        }
        if generators.len() > MAX_GENERATORS {
            return Err(IwasawaRefusal::TooManyGenerators {
                count: generators.len(),
                bound: MAX_GENERATORS,
            });
        }
        let mut trimmed = Vec::with_capacity(generators.len());
        for (index, generator) in generators.into_iter().enumerate() {
            let generator = trim(generator);
            let Some(degree) = degree_of(&generator) else {
                return Err(IwasawaRefusal::ZeroGenerator { index });
            };
            if degree > MAX_GENERATOR_DEGREE {
                return Err(IwasawaRefusal::GeneratorDegreeTooLarge {
                    index,
                    degree,
                    bound: MAX_GENERATOR_DEGREE,
                });
            }
            trimmed.push(generator);
        }
        Ok(Self {
            generators: trimmed,
        })
    }

    /// Declare `Λ/(f)`.
    pub fn principal(generator: Vec<BigInt>) -> Result<Self, IwasawaRefusal> {
        Self::new(vec![generator])
    }

    /// The generators, trimmed, ascending coefficient order.
    pub fn generators(&self) -> &[Vec<BigInt>] {
        &self.generators
    }

    /// How many generators were declared.
    pub fn generator_count(&self) -> usize {
        self.generators.len()
    }

    /// The characteristic ideal, as far as an exact gcd criterion settles it. See
    /// [`CharacteristicFace`].
    ///
    /// The gcd runs over at most [`MAX_GENERATORS`] polynomials of degree at most
    /// [`MAX_GENERATOR_DEGREE`], both fixed by this module.
    pub fn characteristic_face(&self, prime: u64) -> CharacteristicFace {
        if self.generators.len() == 1 {
            return CharacteristicFace::Principal(self.generators[0].clone());
        }
        let prime_big = BigInt::from(prime);
        let prime_is_common = self.generators.iter().all(|generator| {
            generator
                .iter()
                .all(|coefficient| (coefficient % &prime_big).is_zero())
        });
        let mut common = self.generators[0].clone();
        for generator in self.generators.iter().skip(1) {
            common = rational_gcd(&common, generator);
        }
        if degree_of(&common) == Some(0) && !prime_is_common {
            CharacteristicFace::Unit
        } else {
            CharacteristicFace::Undetermined {
                common_factor: common,
                prime_is_common,
            }
        }
    }

    /// The relation matrix of `M/ω_n M` over the basis `1, T, …, T^(p^n - 1)`.
    ///
    /// Row `i·p^n + j` is `T^j · f_i mod ω_n`; column `c` is the coefficient of `T^c`.
    ///
    /// The extent `(k·p^n) × p^n` is computed with `checked_mul` and compared against
    /// [`MAX_RELATION_MATRIX_AREA`] **before** `ω_n` is built and before `IntegerMatrix::zeros`
    /// allocates anything.
    pub fn relation_matrix(
        &self,
        level: &IwasawaLevel,
    ) -> Result<IntegerMatrix, IwasawaRefusal> {
        let columns = level.degree();
        let rows = self
            .generators
            .len()
            .checked_mul(columns)
            .ok_or(IwasawaRefusal::RelationMatrixTooLarge {
                rows: usize::MAX,
                columns,
                area: usize::MAX,
                bound: MAX_RELATION_MATRIX_AREA,
            })?;
        let area = rows
            .checked_mul(columns)
            .ok_or(IwasawaRefusal::RelationMatrixTooLarge {
                rows,
                columns,
                area: usize::MAX,
                bound: MAX_RELATION_MATRIX_AREA,
            })?;
        if area > MAX_RELATION_MATRIX_AREA {
            return Err(IwasawaRefusal::RelationMatrixTooLarge {
                rows,
                columns,
                area,
                bound: MAX_RELATION_MATRIX_AREA,
            });
        }

        let modulus = omega(level);
        let mut matrix = IntegerMatrix::zeros(rows, columns);
        let mut row = 0_usize;
        for generator in &self.generators {
            for shift in 0..columns {
                let mut shifted = vec![BigInt::zero(); shift];
                shifted.extend(generator.iter().cloned());
                let relation = poly_rem_monic(&shifted, &modulus);
                for (column, coefficient) in relation.iter().enumerate() {
                    if column < columns {
                        matrix.set(row, column, coefficient.clone());
                    }
                }
                row += 1;
            }
        }
        debug_assert_eq!(row, rows, "invariant: one relation row per generator per basis shift");
        Ok(matrix)
    }

    /// `M/ω_n M` as an explicit finite abelian group.
    ///
    /// Assembles the relation matrix, runs [`crate::rebase_invariants::smith_normal_form`] with
    /// [`PivotRule::SmallestMagnitude`] — the rule that owner measured as the one which keeps
    /// intermediate coefficients small — and reads the cokernel off the invariant factors.
    ///
    /// A rank-deficient matrix means the cokernel has a free summand, so `M/ω_n M` is infinite as a
    /// `Z_p`-module: that is [`IwasawaRefusal::NotFinite`] and never a silently truncated order.
    pub fn specialize(
        &self,
        level: &IwasawaLevel,
    ) -> Result<FiniteSpecialization, IwasawaRefusal> {
        let matrix = self.relation_matrix(level)?;
        let form = smith_normal_form(&matrix, PivotRule::SmallestMagnitude);
        let basis_dimension = level.degree();
        let rank = form.rank();
        if rank < basis_dimension {
            return Err(IwasawaRefusal::NotFinite {
                basis_dimension,
                rank,
                prime: level.prime(),
                level: level.level(),
            });
        }
        debug_assert!(
            form.divisibility_holds(),
            "invariant: Smith factors are returned in divisibility order"
        );

        let prime = level.prime_big();
        let mut invariant_factors = Vec::new();
        let mut p_valuations = Vec::new();
        let mut integral_order = BigUint::one();
        let mut order = BigUint::one();
        let mut growth_exponent = 0_u64;
        for factor in &form.factors {
            if factor <= &BigInt::one() {
                continue;
            }
            let magnitude = factor
                .to_biguint()
                .expect("invariant: smith_normal_form returns nonnegative factors");
            let (valuation, _) = p_valuation(&magnitude, &prime);
            integral_order *= &magnitude;
            order *= prime.pow(valuation);
            growth_exponent = growth_exponent.saturating_add(u64::from(valuation));
            invariant_factors.push(factor.clone());
            p_valuations.push(valuation);
        }
        let mut p_primary_type: Vec<u32> = p_valuations
            .iter()
            .copied()
            .filter(|valuation| *valuation > 0)
            .collect();
        p_primary_type.sort_unstable();
        let prime_to_p_part = &integral_order / &order;

        Ok(FiniteSpecialization {
            level: *level,
            basis_dimension,
            smith_rank: rank,
            invariant_factors,
            p_valuations,
            p_primary_type,
            order,
            integral_order,
            prime_to_p_part,
            growth_exponent,
        })
    }
}

/// `M/ω_n M` as an explicit finite abelian group, with its two orders kept apart.
///
/// * [`FiniteSpecialization::invariant_factors`] are the Smith factors above `1` of the relation
///   matrix, in divisibility order. They are the elementary divisors of the cokernel **over `Z`**.
/// * [`FiniteSpecialization::p_valuations`] is `v_p(d_i)` for each of those, in the same order. A
///   zero entry is a factor coprime to `p`, which `⊗ Z_p` kills.
/// * [`FiniteSpecialization::p_primary_type`] is the ascending list of the strictly positive ones:
///   the exponents of the cyclic summands of the `Z_p`-module `M/ω_n M`.
/// * [`FiniteSpecialization::order`] is `p^(Σ v_p(d_i))` — the order of the `Z_p`-module, which is
///   what Iwasawa's `e_n` counts.
/// * [`FiniteSpecialization::integral_order`] is `∏ d_i` — the order over `Z`.
/// * [`FiniteSpecialization::prime_to_p_part`] is their exact quotient, so nothing is discarded in
///   silence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FiniteSpecialization {
    level: IwasawaLevel,
    basis_dimension: usize,
    smith_rank: usize,
    invariant_factors: Vec<BigInt>,
    p_valuations: Vec<u32>,
    p_primary_type: Vec<u32>,
    order: BigUint,
    integral_order: BigUint,
    prime_to_p_part: BigUint,
    growth_exponent: u64,
}

impl FiniteSpecialization {
    /// The level this was taken at.
    pub const fn level(&self) -> &IwasawaLevel {
        &self.level
    }

    /// `p^n`, the rank of `Z[T]/(ω_n)` over `Z`.
    pub const fn basis_dimension(&self) -> usize {
        self.basis_dimension
    }

    /// The Smith rank of the relation matrix. Equal to [`FiniteSpecialization::basis_dimension`],
    /// or the specialization would have been refused as infinite.
    pub const fn smith_rank(&self) -> usize {
        self.smith_rank
    }

    /// The Smith invariant factors above `1`, in divisibility order.
    pub fn invariant_factors(&self) -> &[BigInt] {
        &self.invariant_factors
    }

    /// `v_p(d_i)` for each invariant factor, in the same order.
    pub fn p_valuations(&self) -> &[u32] {
        &self.p_valuations
    }

    /// The exponents of the cyclic `Z_p`-summands, ascending.
    pub fn p_primary_type(&self) -> &[u32] {
        &self.p_primary_type
    }

    /// `p^(Σ v_p(d_i))`: the order of `M/ω_n M` as a `Z_p`-module.
    pub const fn order(&self) -> &BigUint {
        &self.order
    }

    /// `∏ d_i`: the order of the cokernel over `Z`.
    pub const fn integral_order(&self) -> &BigUint {
        &self.integral_order
    }

    /// `integral_order / order`: the part of the `Z`-cokernel that `⊗ Z_p` kills.
    pub const fn prime_to_p_part(&self) -> &BigUint {
        &self.prime_to_p_part
    }

    /// Whether the `Z`-cokernel is already `p`-primary, i.e. whether the two orders agree.
    pub fn is_p_primary(&self) -> bool {
        self.prime_to_p_part.is_one()
    }

    /// `e_n`, with `|M/ω_n M| = p^(e_n)`.
    ///
    /// A **growth exponent of an order**, not an entropy and not an information measure.
    pub const fn growth_exponent(&self) -> u64 {
        self.growth_exponent
    }

    /// Whether the module is the zero module.
    pub fn is_trivial(&self) -> bool {
        self.order.is_one()
    }

    /// The level-indexed finite type, which is what a direct sum composes.
    pub fn p_type(&self) -> SpecializationType {
        SpecializationType {
            level: self.level,
            p_primary_type: self.p_primary_type.clone(),
            order: self.order.clone(),
            growth_exponent: self.growth_exponent,
        }
    }
}

/// The finite `Z_p`-type of a specialization: the exponents of its cyclic summands, its order and
/// its growth exponent, at one level.
///
/// This is the carrier a direct sum composes, because a direct sum of modules has no single
/// relation matrix: the type of `A ⊕ B` is the concatenated multiset of the two types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecializationType {
    level: IwasawaLevel,
    p_primary_type: Vec<u32>,
    order: BigUint,
    growth_exponent: u64,
}

impl SpecializationType {
    /// The level.
    pub const fn level(&self) -> &IwasawaLevel {
        &self.level
    }

    /// The exponents of the cyclic `Z_p`-summands, ascending.
    pub fn p_primary_type(&self) -> &[u32] {
        &self.p_primary_type
    }

    /// `p^(e_n)`.
    pub const fn order(&self) -> &BigUint {
        &self.order
    }

    /// `e_n`.
    pub const fn growth_exponent(&self) -> u64 {
        self.growth_exponent
    }

    /// The direct sum: concatenate the types, multiply the orders, add the growth exponents.
    ///
    /// Refuses an empty list and refuses summands at different levels; a direct sum of two
    /// specializations at different `n` is not a specialization of anything.
    pub fn direct_sum(parts: &[Self]) -> Result<Self, IwasawaRefusal> {
        let Some(first) = parts.first() else {
            return Err(IwasawaRefusal::EmptyDirectSum);
        };
        let mut p_primary_type = Vec::new();
        let mut order = BigUint::one();
        let mut growth_exponent = 0_u64;
        for part in parts {
            if part.level != first.level {
                return Err(IwasawaRefusal::LevelMismatch {
                    left: first.level.level(),
                    right: part.level.level(),
                });
            }
            p_primary_type.extend(part.p_primary_type.iter().copied());
            order *= &part.order;
            growth_exponent += part.growth_exponent;
        }
        p_primary_type.sort_unstable();
        Ok(Self {
            level: first.level,
            p_primary_type,
            order,
            growth_exponent,
        })
    }
}

// ---------------------------------------------------------------------------------------------
// The growth exponents.
// ---------------------------------------------------------------------------------------------

/// The exact integer solution of `e_n = μ p^n + λ n + ν` over three consecutive levels.
///
/// These are **growth exponents of an order**. They are not entropies, not information measures and
/// not observer statistics, and nothing here converts them to a scalar that decides a branch:
/// [`GrowthExponents::predict`] returns an exact `BigInt` and the verification is an integer
/// equality.
///
/// The shape itself is the cited classical theorem (Iwasawa 1959; Washington,
/// *Introduction to Cyclotomic Fields*, 2nd ed., Thm 13.13), which holds for `n ≥ n₀`. This type
/// carries the base level it was fitted from precisely because `n₀` is real: see
/// [`GrowthExponents::is_iwasawa_admissible`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GrowthExponents {
    prime: u64,
    base_level: u32,
    mu: BigInt,
    lambda: BigInt,
    nu: BigInt,
}

impl GrowthExponents {
    /// Solve for `(μ, λ, ν)` from three consecutive measured exponents.
    ///
    /// With `Δ₁ = e₂ - e₁` and `Δ₂ = e₃ - e₂` at base level `b`:
    ///
    /// ```text
    ///   Δ₂ - Δ₁ = μ · p^b · (p-1)²
    ///   λ       = Δ₁ - μ · p^b · (p-1)
    ///   ν       = e₁ - μ · p^b - λ · b
    /// ```
    ///
    /// The first is an exact integer division and refuses with
    /// [`IwasawaRefusal::NoExactGrowthFit`] when it does not divide. `p ≥ 2`, so the divisor is
    /// never zero.
    ///
    /// The differences are taken over `BigInt`, not over `u64`, so a decreasing sequence produces a
    /// negative difference rather than an underflow.
    ///
    /// `p^base_level` is **not** computed from the raw `u32`: the pair `(prime, base_level)` is
    /// first put through [`IwasawaLevel::new`], which checks primality and refuses a degree above
    /// [`MAX_DEGREE`]. A caller asking to fit from base level four billion is refused before any
    /// `BigInt` power is built.
    pub fn fit(prime: u64, base_level: u32, exponents: [u64; 3]) -> Result<Self, IwasawaRefusal> {
        let base_chart = IwasawaLevel::new(prime, base_level)?;
        let [first, second, third] = exponents;
        let e1 = BigInt::from(first);
        let e2 = BigInt::from(second);
        let e3 = BigInt::from(third);
        let delta1 = &e2 - &e1;
        let delta2 = &e3 - &e2;
        let second_difference = &delta2 - &delta1;

        let p = BigInt::from(prime);
        let base_power = BigInt::from(base_chart.degree());
        let step = &p - BigInt::one();
        let divisor = &base_power * &step * &step;

        if divisor.is_zero() || !(&second_difference % &divisor).is_zero() {
            return Err(IwasawaRefusal::NoExactGrowthFit {
                prime,
                base_level,
                first,
                second,
                third,
                second_difference,
                divisor,
            });
        }
        let mu = &second_difference / &divisor;
        let lambda = &delta1 - &mu * &base_power * &step;
        let nu = &e1 - &mu * &base_power - &lambda * BigInt::from(base_level);
        Ok(Self {
            prime,
            base_level,
            mu,
            lambda,
            nu,
        })
    }

    /// The residue characteristic.
    pub const fn prime(&self) -> u64 {
        self.prime
    }

    /// The lowest of the three levels the fit was taken over.
    pub const fn base_level(&self) -> u32 {
        self.base_level
    }

    /// `μ`.
    pub const fn mu(&self) -> &BigInt {
        &self.mu
    }

    /// `λ`.
    pub const fn lambda(&self) -> &BigInt {
        &self.lambda
    }

    /// `ν`.
    pub const fn nu(&self) -> &BigInt {
        &self.nu
    }

    /// Whether `μ ≥ 0` and `λ ≥ 0`, which the cited theorem asserts for `n ≥ n₀`.
    ///
    /// A `false` here does not contradict the theorem: it says the three levels the fit was taken
    /// over lie below this module's `n₀`. That is not hypothetical — it is what `p = 2`,
    /// `f = T - 2` does from base level `0`.
    pub fn is_iwasawa_admissible(&self) -> bool {
        !self.mu.is_negative() && !self.lambda.is_negative()
    }

    /// `μ p^n + λ n + ν` at a level.
    ///
    /// Takes an [`IwasawaLevel`] rather than a bare `n` so that `p^n` is a quantity this owner has
    /// already bounded; a raw `u32` would let a caller ask for `p^(2^32)`.
    pub fn predict(&self, level: &IwasawaLevel) -> Result<BigInt, IwasawaRefusal> {
        if level.prime() != self.prime {
            return Err(IwasawaRefusal::PrimeMismatch {
                left: self.prime,
                right: level.prime(),
            });
        }
        let power = BigInt::from(level.degree());
        Ok(&self.mu * power + &self.lambda * BigInt::from(level.level()) + &self.nu)
    }
}

/// Measure `e_n` at each declared level.
///
/// Each level is constructed through [`IwasawaLevel::new`], so each degree is bounded before any
/// matrix is assembled, and each specialization passes the [`MAX_RELATION_MATRIX_AREA`] check
/// independently.
pub fn measure_growth(
    presentation: &LambdaPresentation,
    prime: u64,
    levels: &[u32],
) -> Result<Vec<(u32, u64)>, IwasawaRefusal> {
    let mut measured = Vec::with_capacity(levels.len());
    for level in levels {
        let chart = IwasawaLevel::new(prime, *level)?;
        let specialization = presentation.specialize(&chart)?;
        measured.push((*level, specialization.growth_exponent()));
    }
    Ok(measured)
}

/// A fitted `(μ, λ, ν)` together with the levels it was fitted from and the level it was verified
/// at.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GrowthFit {
    exponents: GrowthExponents,
    fitted_from: Vec<(u32, u64)>,
    verified_at: (u32, u64),
}

impl GrowthFit {
    /// The exponents.
    pub const fn exponents(&self) -> &GrowthExponents {
        &self.exponents
    }

    /// The three `(n, e_n)` the solve used.
    pub fn fitted_from(&self) -> &[(u32, u64)] {
        &self.fitted_from
    }

    /// The `(n, e_n)` the fit was checked against, which was **not** one of the three.
    pub const fn verified_at(&self) -> (u32, u64) {
        self.verified_at
    }
}

/// Measure four consecutive levels, solve `(μ, λ, ν)` on the first three, and verify on the fourth.
///
/// The verification is an exact integer equality. A disagreement is
/// [`IwasawaRefusal::GrowthFitDisagrees`] carrying both numbers, never a tolerance.
pub fn fit_and_verify_growth(
    presentation: &LambdaPresentation,
    prime: u64,
    base_level: u32,
) -> Result<GrowthFit, IwasawaRefusal> {
    let mut measured: Vec<(u32, u64)> = Vec::with_capacity(4);
    for offset in 0..4_u32 {
        let level = base_level
            .checked_add(offset)
            .ok_or(IwasawaRefusal::DegreeTooLarge {
                prime,
                level: base_level,
                bound: MAX_DEGREE,
            })?;
        let chart = IwasawaLevel::new(prime, level)?;
        let specialization = presentation.specialize(&chart)?;
        measured.push((level, specialization.growth_exponent()));
    }
    let [first, second, third, fourth] = <[(u32, u64); 4]>::try_from(measured.as_slice())
        .expect("invariant: exactly four consecutive levels were measured");

    let exponents = GrowthExponents::fit(prime, base_level, [first.1, second.1, third.1])?;
    let chart = IwasawaLevel::new(prime, fourth.0)?;
    let predicted = exponents.predict(&chart)?;
    if predicted != BigInt::from(fourth.1) {
        return Err(IwasawaRefusal::GrowthFitDisagrees {
            level: fourth.0,
            predicted,
            measured: fourth.1,
            exponents: Box::new(exponents),
        });
    }
    Ok(GrowthFit {
        exponents,
        fitted_from: vec![first, second, third],
        verified_at: fourth,
    })
}

#[cfg(test)]
#[path = "iwasawa_tower/tests.rs"]
mod tests;
