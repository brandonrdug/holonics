//! **One certified rank / kernel / solve, reached through bounded prime charts.**
//!
//! [definition] A rational map `A : X → Y` is read here by clearing denominators with recorded
//! nonzero row scales, taking its image in a family of bounded prime arithmetic charts, lifting
//! those images by Chinese remainder, reconstructing the rationals the consumer is owed, and
//! **verifying the reconstruction against the caller's own `A` over ℚ before returning**. The
//! reconstruction does not own the return; the verification does. Nothing below is returned on
//! the strength of a modulus.
//!
//! # Why a prime chart
//!
//! [proved-standard] Rational Gauss–Jordan over `Rat = BigRational` grows in the **coefficients**,
//! not in the shape — a rational
//! elimination writes minors of the input as its intermediate entries, and their bit width grows
//! linearly in the rank while the operation count grows cubically, so the cost grows as the fourth
//! power with a `BigRational` normalisation (a gcd) at every write. A prime chart removes exactly
//! that factor: every intermediate entry is one machine word.
//!
//! # The four returns, and the certificate each owes
//!
//! [definition] Everything this module returns is derived from **one** primitive,
//! [`certified_kernel`], because the four returns the consumers ask for are one object:
//!
//! | return | how it is read off the certificate |
//! |---|---|
//! | rank | [`KernelCertificate::rank`] |
//! | kernel basis | [`KernelCertificate::kernel`], in the canonical free-coordinate normalisation |
//! | reduced row echelon form | [`KernelCertificate::reduced_rows`] — `R[i][p_j] = δ_ij`, `R[i][f] = −N_f[p_i]` |
//! | preimage fibre | [`certified_kernel`] of the augmented `[A | b]`; see [`certified_fibre`] |
//!
//! The RREF is **determined** by the kernel together with the pivot set, so it costs no further
//! reconstruction: `R` is the unique matrix in canonical echelon form whose row space annihilates
//! the kernel. That identity is what makes one primitive enough.
//!
//! ## What the certificate proves, and by which inequality
//!
//! [proved-derived] A returned [`KernelCertificate`] carries both halves of `rank_ℚ A = r`, and
//! [`KernelCertificate::verify`] checks both against the caller's own matrix:
//!
//! - **`rank_ℚ A ≥ r`** — the `r × r` minor of the integral presentation `B = diag(s) A` on the
//!   recorded rows and pivot columns has a **nonzero determinant in one prime chart**. A matrix
//!   with rank below `r` has every `r × r` minor zero over ℤ, hence zero in every chart.
//! - **`rank_ℚ A ≤ r`** — `n − r` vectors `N_f` are exhibited with `A N = 0` **checked over ℚ**
//!   and with `N_f[f'] = δ_{ff'}` on the free coordinates, which makes them independent by
//!   construction rather than by a count. Zero or duplicated vectors cannot pass that check.
//!
//! Together these are an equality, and the kernel is then a **basis** rather than a subset.
//!
//! ## The pivot set is certified too, and this is the part a rank alone would miss
//!
//! [proved-derived] `kernel_basis` and `reduced_row_echelon` do not return *a* basis and *an*
//! echelon form; they return the ones the leftmost-greedy pivot set determines. A certificate that
//! fixed only `ker A` would not fix those: on `A = [1 1]`, both `(−1, 1)` and `(1, −1)` are bases
//! carrying a unit on their own free coordinate, under the two different pivot sets `{0}` and `{1}`.
//! So the verification adds one structural clause:
//!
//! > **`N_f[p] = 0` for every pivot `p > f`.**
//!
//! With `N` a basis of `ker A` that is the identity on the free coordinates, that clause is
//! equivalent to `P` being the leftmost-greedy pivot set. Forward: it says each free column `f` is
//! a combination of pivot columns strictly left of `f`, so `f` is not greedy. Backward, for a
//! pivot `p`: a relation expressing `col_p` through strictly earlier columns is a kernel vector `v`
//! with `v_p = 1` supported below `p`; writing `v = Σ a_f N_f` and restricting to the free
//! coordinates forces `a_f = 0` for `f > p`, and every remaining `N_f` is supported strictly below
//! `p`, so `v_p = 0` — a contradiction. Hence no pivot is redundant and no free column is missed,
//! and the returned basis and echelon form are **the** ones the existing API names.
//!
//! # Bad primes and the pivot profile
//!
//! [definition] Reduction mod `p` can only **lose** rank, never gain it, so an image whose rank is
//! below the running maximum is a bad prime and is named in
//! [`KernelCertificate::refused_moduli`] rather than silently dropped. Equal rank does not imply an
//! equal pivot profile — `A = [[p, 1], [0, 0]]` has rational profile `{0}` and mod-`p` profile
//! `{1}` at the same rank 1 — so images are grouped by profile and only one profile's images are
//! lifted together. A profile that survives to a passing verification was the rational one; a
//! profile that does not is refused by the verification and the search continues. **No
//! goodness heuristic decides a return here.**
//!
//! # Where this runs, and what a thread does not make independent
//!
//! [established-bounded] One prime chart's reduction is a **sequence of dependent pivots**: pivot
//! `k + 1` reads the rows pivot `k` wrote. Allocating threads does not make that sequence
//! independent and this module does not pretend otherwise — [`ImageCost::dependency_span`] records
//! the pivot count as the serial span of one image, and it is unchanged by any placement.
//! What *is* independent is the family of images: they share an immutable
//! [`IntegralPresentation`] and each owns its own output, which is the hardware law's
//! shared-input, disjoint-output pattern, so batches of images run on the CPU lanes at once.
//! A pivot sweep is not a shared linear local operator (its multiplier differs per row and it is
//! bilinear in two data words), so the device's section kernel does not realize it.
//!
//! `holonics::ratio::ring::ModularWords` is the ring this module computes in. At the
//! `MERSENNE61` modulus `2^61 − 1`, its `add` and `mul` use the same portable code that the CUDA
//! section kernel compiles for nvptx. [`PrimeChart::mersenne61`] is the starting chart every
//! reconstruction takes; later charts descend through smaller primes.
//!
//! # What this composes
//!
//! - **Rational reconstruction** is `crate::ratio::polynomial::rational_reconstruction` — Wang's
//!   bounded form, already used by that owner's multi-modular polynomial lift. This module calls it.
//! - **Chinese remainder**: the bulk lift hoists the Bézout coefficient out of the per-entry loop
//!   (one modular inverse per round instead of one extended gcd per entry).
//! - **Primality** is `crate::ratio::primality::is_prime` — deterministic Miller–Rabin over
//!   the first twelve prime bases, exact for every `u64` (below `ψ₁₂`). This module calls it; it declares no base set.
//! - **The ring** is [`crate::ratio::ring::ModularWords`], as above.

use crate::ratio::{Rat, gcd};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use thiserror::Error;

use crate::ratio::ring::{ExactRing, ModularWords};

use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};

// ===============================================================================================
// 0. ceilings and refusals
// ===============================================================================================

/// **The ceiling on the word population of one prime image.**
///
/// [definition] One image materialises `rows × columns` machine words and is checked against this
/// ceiling *before* the allocation. It is the same `2^26` the contact assembly declares, and it
/// bounds the same thing: the arithmetic one reading is allowed to perform in one body.
pub(crate) const DECLARED_IMAGE_EXTENT_CEILING: usize = 1 << 26;

/// **The ceiling on the number of prime charts one reconstruction may consume.**
///
/// [definition] Each chart contributes just under 61 bits to the lifted modulus, so this ceiling
/// admits a reconstruction of about `62_000` bits of numerator and denominator together —
/// past the Hadamard bound of any matrix that also fits
/// [`DECLARED_IMAGE_EXTENT_CEILING`] with word-sized entries. A reconstruction that exhausts it
/// refuses by name rather than running longer.
pub(crate) const DECLARED_PRIME_CEILING: usize = 1024;

/// **The floor below which a chart modulus is refused.**
///
/// [definition] A chart contributes `log2 p` bits per image; a small prime buys almost nothing per
/// pass over the material and multiplies the number of passes. The floor is `2^32`, so every
/// admitted chart carries at least 32 bits.
pub(crate) const DECLARED_PRIME_FLOOR: u64 = 1 << 32;

/// **The ceiling above which a chart modulus is refused**: `2^62`, so that the 128-bit product of
/// two canonical residues cannot leave `u128` and the ring's `mul` is total.
pub(crate) const DECLARED_PRIME_MODULUS_CEILING: u64 = 1 << 62;

/// **How many times a reading may abandon a pivot profile before refusing.**
///
/// [definition] A profile is abandoned only when the exhibited kernel has already passed its exact
/// residual and still fails the leftmost-greedy clause — a bad chart's pivot profile, which is a
/// rare event needing a prime that divides a particular minor while the total rank survives. Four
/// independent occurrences of that in one reading is not a convergence problem; it is a refusal.
pub(crate) const DECLARED_PROFILE_RETRIES: usize = 4;

/// Why a certified reading refuses. Every variant names the clause it enforces; none is a panic.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub(crate) enum PrimeImageRefusal {
    #[error("{what} declares {found} words, past the declared image ceiling of {ceiling}")]
    ImageExtent {
        what: &'static str,
        found: String,
        ceiling: usize,
    },
    #[error(
        "the reconstruction consumed {consumed} prime charts without a verified return; the \
         declared ceiling is {ceiling}"
    )]
    PrimeCeiling { consumed: usize, ceiling: usize },
    #[error("a chart modulus of {modulus} is outside the admitted window [{floor}, {ceiling})")]
    ModulusWindow {
        modulus: u64,
        floor: u64,
        ceiling: u64,
    },
    #[error("a chart modulus of {0} is composite; a chart is a field or it is refused")]
    ModulusNotPrime(u64),
    #[error("no admissible prime chart remains below {0}")]
    PrimesExhausted(u64),
    #[error("{what}: expected {expected}, found {found}")]
    ShapeDisagrees {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error(
        "the exhibited kernel fails `A N = 0` over Q at row {row} of vector {vector}; the \
         reconstruction is refused rather than returned"
    )]
    KernelResidualNonzero { vector: usize, row: usize },
    #[error(
        "the exhibited kernel vector {vector} carries {found} at free coordinate {coordinate} \
         where the canonical normalisation requires {expected}"
    )]
    KernelNormalisation {
        vector: usize,
        coordinate: usize,
        expected: &'static str,
        found: String,
    },
    #[error(
        "the exhibited kernel vector for free column {free} is nonzero at pivot {pivot}, which \
         lies to its right; the declared pivot set is then not the leftmost-greedy one"
    )]
    PivotProfileNotLeftmost { free: usize, pivot: usize },
    #[error(
        "the {rank}x{rank} minor on the declared rows and pivot columns vanishes in chart {modulus}; \
         it certifies no rank at all"
    )]
    MinorVanishes { rank: usize, modulus: u64 },
    #[error(
        "a row scale of a cleared presentation is zero; a scale is invertible or it is not a scale"
    )]
    ZeroRowScale,
    #[error("the exact linear carrier refused: {0}")]
    Carrier(#[from] ExactLinearError),
}

fn bounded_words(
    what: &'static str,
    rows: usize,
    columns: usize,
) -> Result<usize, PrimeImageRefusal> {
    let extent = rows.checked_mul(columns);
    match extent {
        Some(extent) if extent <= DECLARED_IMAGE_EXTENT_CEILING => Ok(extent),
        Some(extent) => Err(PrimeImageRefusal::ImageExtent {
            what,
            found: extent.to_string(),
            ceiling: DECLARED_IMAGE_EXTENT_CEILING,
        }),
        None => Err(PrimeImageRefusal::ImageExtent {
            what,
            found: format!("{rows} x {columns}"),
            ceiling: DECLARED_IMAGE_EXTENT_CEILING,
        }),
    }
}

// ===============================================================================================
// 1. the integral presentation and its decoder
// ===============================================================================================

/// **`B = diag(s) A`: the same map with its denominators cleared, and the scales that clear them.**
///
/// [definition] Row `i` is multiplied by the positive rational `s_i = d_i / g_i`, where `d_i` is the
/// least common denominator of the row and `g_i` the content of the cleared row. Every `s_i` is
/// **nonzero**, so `diag(s)` is invertible and
///
/// ```text
/// ker B = ker A,   rowspace B = rowspace A,   rank B = rank A,   rref B = rref A.
/// ```
///
/// The four readings this module returns are therefore readings of `A` itself and need no decoder.
/// The decoder is retained anyway — [`IntegralPresentation::row_scale`] and
/// [`IntegralPresentation::decoded_row`] — because a *solve* does need it: `A x = b` is
/// `B x = diag(s) b`, and a consumer that presents its target separately must scale it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct IntegralPresentation {
    rows: usize,
    columns: usize,
    entries: Vec<BigInt>,
    /// The narrow reading of `entries`, present exactly when **every** entry fits `i64`. The
    /// modular image then costs one machine remainder per entry instead of a big-integer division.
    narrow: Option<Vec<i64>>,
    row_scales: Vec<Rat>,
}

impl IntegralPresentation {
    /// Clear the denominators of a rational map, recording the scales.
    pub(crate) fn of(matrix: &ExactRatMatrix) -> Result<Self, PrimeImageRefusal> {
        let rows = matrix.rows();
        let columns = matrix.columns();
        bounded_words("an integral presentation", rows, columns)?;
        let mut entries = Vec::with_capacity(rows.saturating_mul(columns));
        let mut row_scales = Vec::with_capacity(rows);
        for row in 0..rows {
            let source = matrix.row(row)?;
            let mut denominator = BigInt::one();
            for entry in source {
                denominator = lcm(&denominator, entry.denom());
            }
            let mut cleared: Vec<BigInt> = source
                .iter()
                .map(|entry| entry.numer() * (&denominator / entry.denom()))
                .collect();
            let mut content = BigInt::zero();
            for value in &cleared {
                content = gcd(&content, value);
            }
            let scale = if content.is_zero() {
                // An all-zero row: the scale is the denominator alone, and it is still invertible.
                Rat::from_integer(denominator.clone())
            } else {
                for value in &mut cleared {
                    *value /= &content;
                }
                Rat::new(denominator.clone(), content.clone())
            };
            if scale.is_zero() {
                return Err(PrimeImageRefusal::ZeroRowScale);
            }
            row_scales.push(scale);
            entries.extend(cleared);
        }
        let narrow = entries
            .iter()
            .map(i64::try_from)
            .collect::<Result<Vec<i64>, _>>()
            .ok();
        Ok(Self {
            rows,
            columns,
            entries,
            narrow,
            row_scales,
        })
    }

    /// `B[row][column]`.
    pub(crate) fn entry(&self, row: usize, column: usize) -> Result<&BigInt, PrimeImageRefusal> {
        self.entries
            .get(row * self.columns + column)
            .ok_or(PrimeImageRefusal::ShapeDisagrees {
                what: "an integral presentation address",
                expected: self.rows * self.columns,
                found: row * self.columns + column,
            })
    }

    #[cfg(test)]
    /// The nonzero scale `s_i` with `B[i] = s_i · A[i]`.
    pub(crate) fn row_scale(&self, row: usize) -> Result<&Rat, PrimeImageRefusal> {
        self.row_scales
            .get(row)
            .ok_or(PrimeImageRefusal::ShapeDisagrees {
                what: "a row scale address",
                expected: self.rows,
                found: row,
            })
    }

    #[cfg(test)]
    /// **The decoder.** `A[i] = B[i] / s_i`, returned exactly.
    pub(crate) fn decoded_row(&self, row: usize) -> Result<Vec<Rat>, PrimeImageRefusal> {
        let scale = self.row_scale(row)?.clone();
        Ok((0..self.columns)
            .map(|column| {
                Rat::from_integer(self.entries[row * self.columns + column].clone()) / &scale
            })
            .collect())
    }

    #[cfg(test)]
    /// **The target of `A x = b` re-presented against `B`**: `diag(s) b`.
    pub(crate) fn scaled_target(&self, target: &[Rat]) -> Result<Vec<Rat>, PrimeImageRefusal> {
        if target.len() != self.rows {
            return Err(PrimeImageRefusal::ShapeDisagrees {
                what: "a target against the presentation it is scaled for",
                expected: self.rows,
                found: target.len(),
            });
        }
        Ok(target
            .iter()
            .zip(&self.row_scales)
            .map(|(value, scale)| value * scale)
            .collect())
    }

    /// The image of `B` in one prime chart, as canonical residues, row-major.
    fn residues(&self, chart: &PrimeChart) -> Vec<u64> {
        let modulus = chart.modulus();
        match &self.narrow {
            Some(narrow) => {
                let signed = modulus as i64;
                narrow
                    .iter()
                    .map(|value| value.rem_euclid(signed) as u64)
                    .collect()
            }
            None => {
                let modulus = BigInt::from(modulus);
                self.entries
                    .iter()
                    .map(|value| {
                        let residue = value % &modulus;
                        let residue = if residue.is_negative() {
                            residue + &modulus
                        } else {
                            residue
                        };
                        u64::try_from(residue).unwrap_or(0)
                    })
                    .collect()
            }
        }
    }

    /// `Σ_j B[row][j] · w[j]`, over the integers, skipping the zeros.
    fn row_pairing(&self, row: usize, weights: &[BigInt]) -> BigInt {
        let base = row * self.columns;
        let mut total = BigInt::zero();
        match &self.narrow {
            Some(narrow) => {
                for column in 0..self.columns {
                    let coefficient = narrow[base + column];
                    if coefficient == 0 || weights[column].is_zero() {
                        continue;
                    }
                    total += &weights[column] * coefficient;
                }
            }
            None => {
                for column in 0..self.columns {
                    let coefficient = &self.entries[base + column];
                    if coefficient.is_zero() || weights[column].is_zero() {
                        continue;
                    }
                    total += &weights[column] * coefficient;
                }
            }
        }
        total
    }
}

/// `floor(sqrt(value))` for a nonnegative integer, by Newton descent from a bit-length seed.
///
/// Founded here rather than composed because the crate declares no `num-integer` dependency and
/// therefore has no `Roots::sqrt` in scope; the reconstruction window needs exactly this and
/// nothing else of that trait.
fn integer_square_root(value: &BigInt) -> BigInt {
    if value.is_negative() || value.is_zero() {
        return BigInt::zero();
    }
    if value.bits() <= 2 {
        return BigInt::one();
    }
    let mut standing = BigInt::one() << (value.bits().div_ceil(2) as usize);
    loop {
        let next = (&standing + value / &standing) >> 1u32;
        if next >= standing {
            break;
        }
        standing = next;
    }
    standing
}

fn lcm(left: &BigInt, right: &BigInt) -> BigInt {
    if left.is_zero() || right.is_zero() {
        return BigInt::one();
    }
    let divisor = gcd(left, right);
    (left * right).abs() / divisor
}

// ===============================================================================================
// 2. the bounded arithmetic chart
// ===============================================================================================

/// **One bounded arithmetic chart: a prime, decided, carrying the exact ratio ring.**
///
/// [definition] The modulus is decided prime by `crate::ratio::primality::is_prime` —
/// deterministic Miller–Rabin over the first twelve prime bases, exact for every `u64` (below `ψ₁₂`) — and is held inside
/// the admitted window `[2^32, 2^62)` so that the 128-bit product of two canonical residues cannot
/// leave `u128`. A chart is a **field**, which is what the elimination below needs and what a
/// composite modulus would not supply.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PrimeChart {
    ring: ModularWords,
}

impl PrimeChart {
    /// A declared chart. The declaration is never trusted: window and primality are both checked.
    pub(crate) fn declared(modulus: u64) -> Result<Self, PrimeImageRefusal> {
        if !(DECLARED_PRIME_FLOOR..DECLARED_PRIME_MODULUS_CEILING).contains(&modulus) {
            return Err(PrimeImageRefusal::ModulusWindow {
                modulus,
                floor: DECLARED_PRIME_FLOOR,
                ceiling: DECLARED_PRIME_MODULUS_CEILING,
            });
        }
        if !crate::ratio::primality::is_prime(modulus) {
            return Err(PrimeImageRefusal::ModulusNotPrime(modulus));
        }
        let ring = ModularWords::new(modulus).map_err(|_| PrimeImageRefusal::ModulusWindow {
            modulus,
            floor: DECLARED_PRIME_FLOOR,
            ceiling: DECLARED_PRIME_MODULUS_CEILING,
        })?;
        Ok(Self { ring })
    }

    /// The Mersenne prime chart `2^61 − 1`, whose reduction shares the portable section arithmetic.
    pub(crate) fn mersenne61() -> Result<Self, PrimeImageRefusal> {
        Self::declared(ModularWords::MERSENNE61.modulus())
    }

    pub(crate) fn modulus(&self) -> u64 {
        self.ring.modulus()
    }

    fn add(&self, left: u64, right: u64) -> u64 {
        self.ring.add(left, right).unwrap_or(0)
    }

    fn mul(&self, left: u64, right: u64) -> u64 {
        self.ring.mul(left, right).unwrap_or(0)
    }

    fn sub(&self, left: u64, right: u64) -> u64 {
        self.add(left, self.modulus() - right % self.modulus())
    }

    fn power(&self, base: u64, mut exponent: u64) -> u64 {
        let mut standing = base % self.modulus();
        let mut accumulated = 1 % self.modulus();
        while exponent > 0 {
            if exponent & 1 == 1 {
                accumulated = self.mul(accumulated, standing);
            }
            standing = self.mul(standing, standing);
            exponent >>= 1;
        }
        accumulated
    }

    /// `x^{-1}` by Fermat, which is exact because the chart is a field.
    fn invert(&self, value: u64) -> u64 {
        self.power(value, self.modulus() - 2)
    }
}

/// The admissible charts at or below a declared start, in descending order.
///
/// [definition] Deterministic and reproducible: the first chart is always
/// [`PrimeChart::mersenne61`]'s `2^61 − 1`, and every later one is the next prime below its
/// predecessor. Nothing is sampled.
///
/// **Extended one batch at a time, never to the budget.** The budget is a Hadamard-sized upper
/// bound on how many charts a reading *could* need; deciding every one of them up front costs a
/// deterministic Miller–Rabin per odd candidate, and a reading that reconstructs after one batch
/// would have paid for hundreds of charts it never reduced. The cost of the charts a reading
/// actually decided is [`ImageCost::charts_decided`], accounted apart from the image work.
fn extend_charts(charts: &mut Vec<PrimeChart>, wanted: usize) -> Result<(), PrimeImageRefusal> {
    if charts.is_empty() && wanted > 0 {
        charts.push(PrimeChart::mersenne61()?);
    }
    let mut candidate = charts.last().map_or(0, PrimeChart::modulus);
    while charts.len() < wanted {
        if candidate <= DECLARED_PRIME_FLOOR + 1 {
            return Err(PrimeImageRefusal::PrimesExhausted(candidate));
        }
        candidate -= if candidate % 2 == 0 { 1 } else { 2 };
        if crate::ratio::primality::is_prime(candidate) {
            charts.push(PrimeChart::declared(candidate)?);
        }
    }
    Ok(())
}

/// The first `count` admissible charts, decided at once.
///
/// No reading takes charts this way — [`certified_kernel_over`] extends one batch at a time — so
/// this is the tests' entry, kept beside the law it exercises rather than duplicated there.
#[cfg(test)]
fn descending_charts(count: usize) -> Result<Vec<PrimeChart>, PrimeImageRefusal> {
    let mut charts = Vec::with_capacity(count);
    extend_charts(&mut charts, count)?;
    Ok(charts)
}

// ===============================================================================================
// 3. one prime image
// ===============================================================================================

/// **The image of `B` in one chart, reduced.** Forward elimination with row exchange, then
/// back-substitution — a **dependent** sequence of `rank` pivots, which no thread allocation
/// shortens.
#[derive(Clone, Debug, PartialEq, Eq)]
struct PrimeImage {
    modulus: u64,
    rank: usize,
    pivot_columns: Vec<usize>,
    /// The original row index chosen at each pivot, in pivot order.
    pivot_rows: Vec<usize>,
    /// `det B[pivot_rows][pivot_columns]` in this chart — the product of the forward pivots, which
    /// equals that determinant because the transform onto the chosen rows is unit lower triangular.
    minor_determinant: u64,
    /// `R[i][f]` for `i < rank` and `f` a free column, row-major over the free columns.
    free_block: Vec<u64>,
    /// The ring multiplications this image performed.
    multiplications: u64,
}

impl PrimeImage {
    fn reduce(presentation: &IntegralPresentation, chart: &PrimeChart) -> Self {
        let rows = presentation.rows;
        let columns = presentation.columns;
        let mut data = presentation.residues(chart);
        let mut order: Vec<usize> = (0..rows).collect();
        let mut pivot_columns = Vec::new();
        let mut pivot_rows = Vec::new();
        let mut minor_determinant = 1 % chart.modulus();
        let mut multiplications = 0u64;
        let mut at = 0usize;

        for column in 0..columns {
            if at >= rows {
                break;
            }
            let Some(found) = (at..rows).find(|row| data[row * columns + column] != 0) else {
                continue;
            };
            if found != at {
                for offset in 0..columns {
                    data.swap(found * columns + offset, at * columns + offset);
                }
                order.swap(found, at);
            }
            let pivot = data[at * columns + column];
            minor_determinant = chart.mul(minor_determinant, pivot);
            let inverse = chart.invert(pivot);
            for offset in column..columns {
                let address = at * columns + offset;
                data[address] = chart.mul(data[address], inverse);
            }
            multiplications += (columns - column) as u64;
            for row in (at + 1)..rows {
                let factor = data[row * columns + column];
                if factor == 0 {
                    continue;
                }
                for offset in column..columns {
                    let above = data[at * columns + offset];
                    if above == 0 {
                        continue;
                    }
                    let address = row * columns + offset;
                    data[address] = chart.sub(data[address], chart.mul(factor, above));
                }
                multiplications += (columns - column) as u64;
            }
            pivot_columns.push(column);
            pivot_rows.push(order[at]);
            at += 1;
        }

        let rank = pivot_columns.len();
        // Back-substitution: clear above every pivot, right to left.
        for index in (0..rank).rev() {
            let column = pivot_columns[index];
            for row in 0..index {
                let factor = data[row * columns + column];
                if factor == 0 {
                    continue;
                }
                for offset in column..columns {
                    let above = data[index * columns + offset];
                    if above == 0 {
                        continue;
                    }
                    let address = row * columns + offset;
                    data[address] = chart.sub(data[address], chart.mul(factor, above));
                }
                multiplications += (columns - column) as u64;
            }
        }

        let free: Vec<usize> = (0..columns)
            .filter(|column| !pivot_columns.contains(column))
            .collect();
        let mut free_block = Vec::with_capacity(rank * free.len());
        for row in 0..rank {
            for column in &free {
                free_block.push(data[row * columns + column]);
            }
        }

        Self {
            modulus: chart.modulus(),
            rank,
            pivot_columns,
            pivot_rows,
            minor_determinant,
            free_block,
            multiplications,
        }
    }
}

/// Why one chart's image was not lifted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BadChart {
    /// The image lost rank: `rank_p < max_p rank_p ≤ rank_ℚ`.
    RankBelowMaximum { found: usize, maximum: usize },
    /// The image reached the maximum rank under a different pivot profile.
    PivotProfileDisagrees,
}

// ===============================================================================================
// 4. what a reading cost, and where it ran
// ===============================================================================================

/// **The cost of a certified reading, with the five stages accounted separately.**
///
/// [definition] The fields are public for the same reason [`crate::ratio::work::ExactWork`]'s are:
/// this is a **receipt**, not a value anything decides on. Nothing in this module or its consumers
/// accepts an `ImageCost`, and a [`KernelCertificate`] has no public constructor at all, so a
/// fabricated cost cannot enter a certificate; everything that decides — the rank, the pivot set,
/// the kernel, the minor — is private and is re-checked by [`KernelCertificate::verify`].
///
/// No field here is a duration: as for [`crate::ratio::work::ExactWork`], a cost is measured in
/// work, and a wall-clock reading belongs in a receipt beside the command, never inside the value.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ImageCost {
    /// Preparation: entries whose denominator was cleared.
    pub prepared_entries: u64,
    /// Preparation: prime charts decided — one deterministic Miller–Rabin per odd candidate below
    /// the previous chart. Accounted apart from the image work because it is a cost of the
    /// *reconstruction's* budget and not of the material.
    pub charts_decided: usize,
    /// Image work: ring multiplications summed over every image that was computed, including the
    /// images later refused as bad charts.
    pub image_multiplications: u64,
    /// Image work: how many charts were reduced.
    pub images_reduced: usize,
    /// Reconstruction: entries lifted by Chinese remainder, summed over the rounds.
    pub lifted_entries: u64,
    /// Reconstruction: how many times a full rational reconstruction of the free block was
    /// attempted, including the attempts that did not reconstruct.
    pub reconstruction_attempts: usize,
    /// Reconstruction: entries that reconstructed into the returned kernel.
    pub reconstructed_entries: u64,
    /// Verification: integer multiply-adds spent on `A N = 0` and on the minor determinant.
    pub verification_multiplications: u64,
    /// Readout: rationals written into the returned kernel.
    pub readout_entries: u64,
    /// **The serial span of one image**: its pivot count. Unchanged by any placement, because a
    /// sequence of dependent pivots is not made independent by allocating more threads.
    pub dependency_span: u64,
}

// ===============================================================================================
// 5. the certificate
// ===============================================================================================

/// **The one certificate under rank, kernel, echelon form and solve.**
///
/// [proved-derived; implemented-exact] Every field is private, so a certificate is one this owner
/// issued and verified. [`Self::verify`] re-checks the whole certificate against a caller's own
/// matrix, so a reuse re-validates rather than trusts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct KernelCertificate {
    rows: usize,
    columns: usize,
    rank: usize,
    pivot_columns: Vec<usize>,
    free_columns: Vec<usize>,
    minor_modulus: u64,
    minor_rows: Vec<usize>,
    minor_determinant: u64,
    image_moduli: Vec<u64>,
    refused_moduli: Vec<(u64, BadChart)>,
    kernel: Vec<Vec<Rat>>,
    cost: ImageCost,
}

impl KernelCertificate {
    pub(crate) fn rank(&self) -> usize {
        self.rank
    }

    pub(crate) fn rows(&self) -> usize {
        self.rows
    }

    pub(crate) fn columns(&self) -> usize {
        self.columns
    }

    /// The leftmost-greedy pivot columns, certified as such by [`Self::verify`].
    pub(crate) fn pivot_columns(&self) -> &[usize] {
        &self.pivot_columns
    }

    #[cfg(test)]
    pub(crate) fn free_columns(&self) -> &[usize] {
        &self.free_columns
    }

    /// The exhibited basis of `ker A`, one vector per free column in the canonical normalisation.
    pub(crate) fn kernel(&self) -> &[Vec<Rat>] {
        &self.kernel
    }

    #[cfg(test)]
    /// The chart whose nonzero minor gives `rank_ℚ A ≥ rank`, and that minor's rows.
    pub(crate) fn minor(&self) -> (u64, &[usize], u64) {
        (self.minor_modulus, &self.minor_rows, self.minor_determinant)
    }

    #[cfg(test)]
    /// The charts computed and then refused, with the reason. Retained, never dropped.
    pub(crate) fn refused_moduli(&self) -> &[(u64, BadChart)] {
        &self.refused_moduli
    }

    pub(crate) fn cost(&self) -> &ImageCost {
        &self.cost
    }

    /// **The reduced row echelon form, determined by this certificate and costing no further
    /// reconstruction.**
    ///
    /// [proved-derived] `R` is the unique canonical-echelon matrix whose row space annihilates the
    /// kernel: `R[i][p_j] = δ_ij` and `R[i][f] = −N_f[p_i]`, with `rows − rank` zero rows beneath.
    /// Row-space equivalence to `A` follows from the certificate rather than from a rank match:
    /// `A N = 0` and `R N = 0` place both row spaces inside `N^⊥`, which has dimension
    /// `columns − (columns − rank) = rank`; `A` reaches that dimension because its rank is
    /// certified, and `R`'s rows are independent because of the canonical pivot pattern. Two
    /// subspaces of one space, both of its full dimension, are it.
    pub(crate) fn reduced_rows(&self) -> Vec<Vec<Rat>> {
        let mut rows = vec![vec![Rat::zero(); self.columns]; self.rows];
        for (index, pivot) in self.pivot_columns.iter().enumerate() {
            rows[index][*pivot] = Rat::one();
        }
        for (vector, free) in self.kernel.iter().zip(&self.free_columns) {
            for (index, pivot) in self.pivot_columns.iter().enumerate() {
                rows[index][*free] = -vector[*pivot].clone();
            }
        }
        rows
    }

    #[cfg(test)]
    /// **Check the whole certificate against a caller's own matrix.** Both halves of the rank
    /// equality, the canonical normalisation, the leftmost-greedy pivot clause and the exact
    /// kernel residual. A certificate that does not pass is refused, never repaired.
    pub(crate) fn verify(&self, matrix: &ExactRatMatrix) -> Result<(), PrimeImageRefusal> {
        if matrix.rows() != self.rows {
            return Err(PrimeImageRefusal::ShapeDisagrees {
                what: "a certificate's row population against the matrix it certifies",
                expected: self.rows,
                found: matrix.rows(),
            });
        }
        if matrix.columns() != self.columns {
            return Err(PrimeImageRefusal::ShapeDisagrees {
                what: "a certificate's column population against the matrix it certifies",
                expected: self.columns,
                found: matrix.columns(),
            });
        }
        let presentation = IntegralPresentation::of(matrix)?;
        let chart = PrimeChart::declared(self.minor_modulus)?;
        let mut spent = 0u64;
        verify_minor(
            &presentation,
            &chart,
            &self.minor_rows,
            &self.pivot_columns,
            &mut spent,
        )?;
        verify_kernel(
            &presentation,
            self.rank,
            &self.pivot_columns,
            &self.free_columns,
            &self.kernel,
            &mut spent,
        )
    }
}

/// `rank_ℚ A ≥ r`: the declared minor is nonzero in the declared chart.
fn verify_minor(
    presentation: &IntegralPresentation,
    chart: &PrimeChart,
    minor_rows: &[usize],
    pivot_columns: &[usize],
    spent: &mut u64,
) -> Result<(), PrimeImageRefusal> {
    let rank = pivot_columns.len();
    if minor_rows.len() != rank {
        return Err(PrimeImageRefusal::ShapeDisagrees {
            what: "a declared minor's row population against its rank",
            expected: rank,
            found: minor_rows.len(),
        });
    }
    if rank == 0 {
        return Ok(());
    }
    let modulus = chart.modulus();
    let signed = modulus as i64;
    let mut minor = vec![0u64; rank * rank];
    for (at, row) in minor_rows.iter().enumerate() {
        if *row >= presentation.rows {
            return Err(PrimeImageRefusal::ShapeDisagrees {
                what: "a declared minor row address",
                expected: presentation.rows,
                found: *row,
            });
        }
        for (offset, column) in pivot_columns.iter().enumerate() {
            if *column >= presentation.columns {
                return Err(PrimeImageRefusal::ShapeDisagrees {
                    what: "a declared minor column address",
                    expected: presentation.columns,
                    found: *column,
                });
            }
            let entry = presentation.entry(*row, *column)?;
            minor[at * rank + offset] = match &presentation.narrow {
                Some(_) => i64::try_from(entry)
                    .map(|value| value.rem_euclid(signed) as u64)
                    .unwrap_or(0),
                None => {
                    let big = BigInt::from(modulus);
                    let residue = entry % &big;
                    let residue = if residue.is_negative() {
                        residue + &big
                    } else {
                        residue
                    };
                    u64::try_from(residue).unwrap_or(0)
                }
            };
        }
    }
    // An independent determinant, computed from the caller's matrix rather than read off the sweep.
    let mut determinant = 1 % modulus;
    for at in 0..rank {
        let Some(found) = (at..rank).find(|row| minor[row * rank + at] != 0) else {
            return Err(PrimeImageRefusal::MinorVanishes { rank, modulus });
        };
        if found != at {
            for offset in 0..rank {
                minor.swap(found * rank + offset, at * rank + offset);
            }
            determinant = chart.sub(0, determinant);
        }
        let pivot = minor[at * rank + at];
        determinant = chart.mul(determinant, pivot);
        let inverse = chart.invert(pivot);
        for row in (at + 1)..rank {
            let factor = chart.mul(minor[row * rank + at], inverse);
            if factor == 0 {
                continue;
            }
            for offset in at..rank {
                let above = minor[at * rank + offset];
                if above == 0 {
                    continue;
                }
                let address = row * rank + offset;
                minor[address] = chart.sub(minor[address], chart.mul(factor, above));
            }
            *spent += (rank - at) as u64;
        }
    }
    if determinant == 0 {
        return Err(PrimeImageRefusal::MinorVanishes { rank, modulus });
    }
    Ok(())
}

/// `rank_ℚ A ≤ r`, the canonical normalisation, and the leftmost-greedy pivot clause.
fn verify_kernel(
    presentation: &IntegralPresentation,
    rank: usize,
    pivot_columns: &[usize],
    free_columns: &[usize],
    kernel: &[Vec<Rat>],
    spent: &mut u64,
) -> Result<(), PrimeImageRefusal> {
    let columns = presentation.columns;
    if pivot_columns.len() != rank {
        return Err(PrimeImageRefusal::ShapeDisagrees {
            what: "a certificate's pivot population against its rank",
            expected: rank,
            found: pivot_columns.len(),
        });
    }
    if free_columns.len() != columns - rank || kernel.len() != columns - rank {
        return Err(PrimeImageRefusal::ShapeDisagrees {
            what: "a certificate's kernel population against its nullity",
            expected: columns - rank,
            found: kernel.len(),
        });
    }
    // **Two passes, and the order is the point.** An under-converged reconstruction produces
    // rationals that are simply wrong, and those fail the *residual*. A reconstruction that has
    // converged and still fails the *leftmost* clause is a different fault entirely: the kernel is
    // genuine and the declared pivot set is not the rational one, which is a bad chart's pivot
    // profile rather than a shortage of charts. Checking every residual before any leftmost clause
    // is what lets [`certified_kernel_over`] tell those two apart — one wants more charts, the
    // other wants a different profile — instead of answering both by running longer.
    for (at, values) in kernel.iter().enumerate() {
        let free = &free_columns[at];
        if values.len() != columns {
            return Err(PrimeImageRefusal::ShapeDisagrees {
                what: "a kernel vector's width against the map's domain",
                expected: columns,
                found: values.len(),
            });
        }
        // The canonical normalisation: the identity on the free coordinates. This is what makes
        // the exhibited population independent by construction; a zero or duplicated vector
        // cannot satisfy it.
        for other in free_columns {
            let expected_one = other == free;
            let value = &values[*other];
            if expected_one && !value.is_one() {
                return Err(PrimeImageRefusal::KernelNormalisation {
                    vector: at,
                    coordinate: *other,
                    expected: "1",
                    found: value.to_string(),
                });
            }
            if !expected_one && !value.is_zero() {
                return Err(PrimeImageRefusal::KernelNormalisation {
                    vector: at,
                    coordinate: *other,
                    expected: "0",
                    found: value.to_string(),
                });
            }
        }
        // `A N = 0` over Q, taken on the integral presentation, which has the same kernel.
        let mut denominator = BigInt::one();
        for value in values.iter() {
            denominator = lcm(&denominator, value.denom());
        }
        let weights: Vec<BigInt> = values
            .iter()
            .map(|value| value.numer() * (&denominator / value.denom()))
            .collect();
        for row in 0..presentation.rows {
            let pairing = presentation.row_pairing(row, &weights);
            *spent += columns as u64;
            if !pairing.is_zero() {
                return Err(PrimeImageRefusal::KernelResidualNonzero { vector: at, row });
            }
        }
    }
    for (at, values) in kernel.iter().enumerate() {
        let free = &free_columns[at];
        for pivot in pivot_columns {
            if pivot > free && !values[*pivot].is_zero() {
                return Err(PrimeImageRefusal::PivotProfileNotLeftmost {
                    free: *free,
                    pivot: *pivot,
                });
            }
        }
    }
    Ok(())
}

// ===============================================================================================
// 6. the certified reading
// ===============================================================================================

/// **The certified rank, kernel and pivot profile of a rational map.**
///
/// [definition] The images are independent: each reads the same immutable integral presentation
/// and owns its own output, so batches of them run on the CPU's declared lanes at once (the
/// hardware law's shared-input, disjoint-output pattern).
pub(crate) fn certified_kernel(
    matrix: &ExactRatMatrix,
) -> Result<KernelCertificate, PrimeImageRefusal> {
    let rows = matrix.rows();
    let columns = matrix.columns();
    bounded_words("a certified reading", rows, columns)?;

    let mut cost = ImageCost::default();
    let presentation = IntegralPresentation::of(matrix)?;
    cost.prepared_entries = (rows as u64).saturating_mul(columns as u64);

    if columns == 0 || rows == 0 {
        return Ok(KernelCertificate {
            rows,
            columns,
            rank: 0,
            pivot_columns: Vec::new(),
            free_columns: (0..columns).collect(),
            minor_modulus: PrimeChart::mersenne61()?.modulus(),
            minor_rows: Vec::new(),
            minor_determinant: 1,
            image_moduli: Vec::new(),
            refused_moduli: Vec::new(),
            kernel: (0..columns)
                .map(|free| {
                    let mut vector = vec![Rat::zero(); columns];
                    vector[free] = Rat::one();
                    vector
                })
                .collect(),
            cost,
        });
    }

    // The declared prime budget: enough charts to carry a Hadamard-sized numerator and denominator
    // for this shape, capped by the declared ceiling. `min(rows, columns)` bounds the rank, and a
    // minor of that rank has at most `rank · (entry_bits + log2 rank / 2)` bits; the reconstruction
    // needs twice that, plus a round of slack. This is a **budget**, not a sufficiency proof: the
    // verification decides the return, and running out of budget is a named refusal.
    let entry_bits = presentation
        .entries
        .iter()
        .map(|entry| entry.bits())
        .max()
        .unwrap_or(1)
        .max(1);
    let bound_rank = rows.min(columns) as u64;
    let minor_bits = bound_rank.saturating_mul(entry_bits + 32);
    let needed =
        usize::try_from(minor_bits.saturating_mul(2) / 60 + 4).unwrap_or(DECLARED_PRIME_CEILING);
    let budget = needed.clamp(2, DECLARED_PRIME_CEILING);

    let mut charts: Vec<PrimeChart> = Vec::new();
    let lanes = cpu_lanes().min(budget).max(1);

    let mut lifted: Option<CrtAccumulator> = None;
    let mut chosen: Option<ChosenProfile> = None;
    let mut maximum_rank = 0usize;
    let mut refused: Vec<(u64, BadChart)> = Vec::new();
    let mut image_moduli: Vec<u64> = Vec::new();
    let mut next_attempt = 1usize;
    let mut consumed = 0usize;
    let mut abandoned = 0usize;

    while consumed < budget {
        let batch_end = (consumed + lanes).min(budget);
        extend_charts(&mut charts, batch_end)?;
        cost.charts_decided = charts.len();
        let batch = &charts[consumed..batch_end];
        // Independent images: each reads the same immutable presentation and owns its output.
        let images = reduce_batch(&presentation, batch, lanes);
        consumed = batch_end;
        cost.images_reduced += images.len();

        for image in images {
            cost.image_multiplications = cost
                .image_multiplications
                .saturating_add(image.multiplications);
            if image.rank > maximum_rank {
                // A strictly better chart supersedes everything lifted so far: every earlier image
                // lost rank and was a bad prime, which is only visible now.
                for modulus in image_moduli.drain(..) {
                    refused.push((
                        modulus,
                        BadChart::RankBelowMaximum {
                            found: maximum_rank,
                            maximum: image.rank,
                        },
                    ));
                }
                maximum_rank = image.rank;
                lifted = None;
                chosen = None;
                next_attempt = 1;
            } else if image.rank < maximum_rank {
                refused.push((
                    image.modulus,
                    BadChart::RankBelowMaximum {
                        found: image.rank,
                        maximum: maximum_rank,
                    },
                ));
                continue;
            }
            match &chosen {
                Some(profile) if profile.pivot_columns != image.pivot_columns => {
                    refused.push((image.modulus, BadChart::PivotProfileDisagrees));
                    continue;
                }
                _ => {}
            }
            if chosen.is_none() {
                let free: Vec<usize> = (0..columns)
                    .filter(|column| !image.pivot_columns.contains(column))
                    .collect();
                chosen = Some(ChosenProfile {
                    rank: image.rank,
                    pivot_columns: image.pivot_columns.clone(),
                    free_columns: free,
                    minor_modulus: image.modulus,
                    minor_rows: image.pivot_rows.clone(),
                    minor_determinant: image.minor_determinant,
                });
                lifted = Some(CrtAccumulator::new(image.free_block.len()));
            }
            let Some(accumulator) = lifted.as_mut() else {
                continue;
            };
            accumulator.absorb(&image.free_block, image.modulus);
            cost.lifted_entries = cost
                .lifted_entries
                .saturating_add(image.free_block.len() as u64);
            image_moduli.push(image.modulus);
            if let Some(profile) = &chosen {
                cost.dependency_span = profile.rank as u64;
            }
        }

        let (Some(accumulator), Some(profile)) = (lifted.as_ref(), chosen.as_ref()) else {
            continue;
        };
        if image_moduli.len() < next_attempt {
            continue;
        }
        // A doubling schedule: a reconstruction attempt costs an extended gcd per entry, so
        // attempting after every chart would spend most of the reading on attempts that cannot
        // succeed. Doubling spends at most twice the final attempt in total.
        next_attempt = image_moduli.len().saturating_mul(2).max(1);
        cost.reconstruction_attempts += 1;
        let Some(free_block) = accumulator.reconstruct() else {
            continue;
        };
        let kernel = canonical_kernel(
            columns,
            &profile.pivot_columns,
            &profile.free_columns,
            &free_block,
        );
        let mut spent = 0u64;
        let chart = PrimeChart::declared(profile.minor_modulus)?;
        // The minor is recomputed from the caller's own matrix, never read off the sweep, so the
        // `rank >= r` half is checkable without trusting the image that proposed it.
        let minor = verify_minor(
            &presentation,
            &chart,
            &profile.minor_rows,
            &profile.pivot_columns,
            &mut spent,
        );
        let verdict = minor.and_then(|()| {
            verify_kernel(
                &presentation,
                profile.rank,
                &profile.pivot_columns,
                &profile.free_columns,
                &kernel,
                &mut spent,
            )
        });
        match verdict {
            Ok(()) => {}
            // The kernel is genuine and the declared pivot set is not the rational one, or the
            // declared minor vanishes: a bad chart's **profile**, not a shortage of charts.
            // Abandon it, name its charts, and re-derive from the next batch — running longer on
            // a wrong profile would never return.
            Err(
                PrimeImageRefusal::PivotProfileNotLeftmost { .. }
                | PrimeImageRefusal::MinorVanishes { .. },
            ) if abandoned < DECLARED_PROFILE_RETRIES => {
                abandoned += 1;
                for modulus in image_moduli.drain(..) {
                    refused.push((modulus, BadChart::PivotProfileDisagrees));
                }
                chosen = None;
                lifted = None;
                next_attempt = 1;
                continue;
            }
            // Everything else — a residual that does not vanish — is a reconstruction that has not
            // converged, and the answer to that is more charts.
            Err(_) => continue,
        }
        cost.verification_multiplications = cost.verification_multiplications.saturating_add(spent);
        cost.reconstructed_entries = free_block.len() as u64;
        cost.readout_entries = (kernel.len() as u64).saturating_mul(columns as u64);
        return Ok(KernelCertificate {
            rows,
            columns,
            rank: profile.rank,
            pivot_columns: profile.pivot_columns.clone(),
            free_columns: profile.free_columns.clone(),
            minor_modulus: profile.minor_modulus,
            minor_rows: profile.minor_rows.clone(),
            minor_determinant: profile.minor_determinant,
            image_moduli,
            refused_moduli: refused,
            kernel,
            cost,
        });
    }

    Err(PrimeImageRefusal::PrimeCeiling {
        consumed,
        ceiling: DECLARED_PRIME_CEILING,
    })
}

/// **The complete affine preimage of a declared target, certified.**
///
/// `Some((particular, kernel))` is the fibre `x_0 + ker A`, with `A x_0 = b` implied by the
/// certificate of the augmented map: the canonical kernel vector on the augmented column is
/// `(−x_0, 1)`, so `A x_0 = b` is one clause of `[A | b] N = 0`, already checked over ℚ.
/// `None` is an **exact incompatibility**: the augmented column is a pivot of `[A | b]`, whose
/// pivot set restricted to the first `columns` is the pivot set of `A` (greedy on a prefix is
/// greedy), so `rank [A | b] = rank A + 1` and `b ∉ image A`. Both ranks are certified by the same
/// returned certificate.
pub(crate) fn certified_fibre(
    matrix: &ExactRatMatrix,
    target: &[Rat],
) -> Result<(Option<(Vec<Rat>, Vec<Vec<Rat>>)>, KernelCertificate), PrimeImageRefusal> {
    let columns = matrix.columns();
    if target.len() != matrix.rows() {
        return Err(PrimeImageRefusal::ShapeDisagrees {
            what: "a target against the map it is a target of",
            expected: matrix.rows(),
            found: target.len(),
        });
    }
    let mut augmented = matrix.to_rows();
    for (row, value) in augmented.iter_mut().zip(target) {
        row.push(value.clone());
    }
    let augmented = ExactRatMatrix::shaped(matrix.rows(), columns + 1, augmented)?;
    let certificate = certified_kernel(&augmented)?;
    if certificate.pivot_columns.contains(&columns) {
        return Ok((None, certificate));
    }
    let mut particular = vec![Rat::zero(); columns];
    let mut kernel = Vec::with_capacity(certificate.kernel.len().saturating_sub(1));
    for (vector, free) in certificate.kernel.iter().zip(&certificate.free_columns) {
        if *free == columns {
            for (at, value) in vector.iter().take(columns).enumerate() {
                particular[at] = -value.clone();
            }
        } else {
            kernel.push(vector.iter().take(columns).cloned().collect());
        }
    }
    Ok((Some((particular, kernel)), certificate))
}

/// The one pivot profile a reconstruction lifts against, with the minor that certifies its rank.
#[derive(Clone, Debug)]
struct ChosenProfile {
    rank: usize,
    pivot_columns: Vec<usize>,
    free_columns: Vec<usize>,
    minor_modulus: u64,
    minor_rows: Vec<usize>,
    minor_determinant: u64,
}

/// The canonical basis the free block determines.
fn canonical_kernel(
    columns: usize,
    pivot_columns: &[usize],
    free_columns: &[usize],
    free_block: &[Rat],
) -> Vec<Vec<Rat>> {
    let width = free_columns.len();
    let mut kernel = Vec::with_capacity(width);
    for (at, free) in free_columns.iter().enumerate() {
        let mut vector = vec![Rat::zero(); columns];
        vector[*free] = Rat::one();
        for (index, pivot) in pivot_columns.iter().enumerate() {
            vector[*pivot] = -free_block[index * width + at].clone();
        }
        kernel.push(vector);
    }
    kernel
}

/// The CPU lanes the host declares about itself; one when it declares nothing.
fn cpu_lanes() -> usize {
    std::thread::available_parallelism().map_or(1, usize::from)
}

/// Reduce a batch of charts, one image per lane, sharing the immutable presentation.
fn reduce_batch(
    presentation: &IntegralPresentation,
    charts: &[PrimeChart],
    lanes: usize,
) -> Vec<PrimeImage> {
    if charts.len() <= 1 || lanes <= 1 {
        return charts
            .iter()
            .map(|chart| PrimeImage::reduce(presentation, chart))
            .collect();
    }
    std::thread::scope(|scope| {
        let handles: Vec<_> = charts
            .iter()
            .map(|chart| scope.spawn(move || PrimeImage::reduce(presentation, chart)))
            .collect();
        handles
            .into_iter()
            // A panicking image is resumed, not swallowed into a rank-zero placeholder: a typed
            // refusal is what a *declared limit* owes, and a panic here is neither.
            .map(|handle| match handle.join() {
                Ok(image) => image,
                Err(payload) => std::panic::resume_unwind(payload),
            })
            .collect()
    })
}

// ===============================================================================================
// 7. the lift and the reconstruction
// ===============================================================================================

/// **The incremental Chinese-remainder lift of one entry population.**
///
/// [definition] The Chinese remainder law with the Bézout coefficient hoisted: every entry in one
/// round shares the same modulus pair, so the inverse of `M mod p` is computed once per round
/// rather than once per entry.
#[derive(Clone, Debug)]
struct CrtAccumulator {
    residues: Vec<BigInt>,
    modulus: BigInt,
}

impl CrtAccumulator {
    fn new(extent: usize) -> Self {
        Self {
            residues: vec![BigInt::zero(); extent],
            modulus: BigInt::one(),
        }
    }

    fn absorb(&mut self, image: &[u64], modulus: u64) {
        if self.modulus.is_one() {
            self.residues = image.iter().map(|value| BigInt::from(*value)).collect();
            self.modulus = BigInt::from(modulus);
            return;
        }
        let chart = ModularWords::new(modulus).ok();
        let Some(chart) = chart else { return };
        let standing = {
            let big = BigInt::from(modulus);
            let residue = &self.modulus % &big;
            u64::try_from(if residue.is_negative() {
                residue + &big
            } else {
                residue
            })
            .unwrap_or(0)
        };
        if standing == 0 {
            return;
        }
        let inverse = {
            let mut accumulated = 1u64 % modulus;
            let mut base = standing;
            let mut exponent = modulus - 2;
            while exponent > 0 {
                if exponent & 1 == 1 {
                    accumulated = chart.mul(accumulated, base).unwrap_or(0);
                }
                base = chart.mul(base, base).unwrap_or(0);
                exponent >>= 1;
            }
            accumulated
        };
        let big_modulus = BigInt::from(modulus);
        for (at, residue) in self.residues.iter_mut().enumerate() {
            let current = {
                let value = &*residue % &big_modulus;
                u64::try_from(if value.is_negative() {
                    value + &big_modulus
                } else {
                    value
                })
                .unwrap_or(0)
            };
            let wanted = image.get(at).copied().unwrap_or(0) % modulus;
            let difference = chart.add(wanted, modulus - current % modulus).unwrap_or(0);
            let delta = chart.mul(difference, inverse).unwrap_or(0);
            if delta != 0 {
                *residue += &self.modulus * BigInt::from(delta);
            }
        }
        self.modulus *= big_modulus;
    }

    /// Rational reconstruction of every entry in the symmetric balanced window, or `None` on the
    /// first entry that does not reconstruct — an abort, not a partial return.
    fn reconstruct(&self) -> Option<Vec<Rat>> {
        let bound = integer_square_root(&((&self.modulus - BigInt::one()) / BigInt::from(2u32)));
        if bound.is_zero() {
            return None;
        }
        let mut reconstructed = Vec::with_capacity(self.residues.len());
        for residue in &self.residues {
            let (numerator, denominator) = crate::ratio::polynomial::rational_reconstruction(
                residue,
                &self.modulus,
                &bound,
                &bound,
            )?;
            if denominator.is_zero() {
                return None;
            }
            reconstructed.push(Rat::new(numerator, denominator));
        }
        Some(reconstructed)
    }
}

#[cfg(test)]
mod tests;
