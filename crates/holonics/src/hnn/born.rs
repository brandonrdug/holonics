//! **The wave read by the Born rule: a finitely correlated (quantum hidden Markov) receiver on the
//! receiving ring's register** (Decision 33; rebuild step 4, #73; Lean `HNN/BornFace`).
//!
//! [definition] The computational object is the helical pair interaction; this owner is its
//! receiving parametron read quantum-mechanically. Of the winding guide's six general objects it
//! touches three: the **helix** (the register's ray is the ring's phase, carried as a Gaussian
//! integer vector whose binary exponent is its carry), the **pair** (each digit's reception is the
//! pair of operators `A_(ℓ,0), A_(ℓ,1)` meeting the state), and **faces and placement** (the Born
//! face on the dyadic partition of the unit cell). The tube is the passage, one cell per tick; the
//! tower thread is the digit prefix (the dyadic cell a digit descends); no cell holonomy is claimed.
//!
//! ```text
//! state      ρ = ψψ†/‖ψ‖²,  ψ ∈ ℤ[i]^χ on its mantissa (Lean born_pure_stays_pure)       the retained quotient
//! mass       T_c = Tr(A_c ρ A_c†) = ‖A_c ψ‖²/‖ψ‖²
//! split      p(b | ρ) = T_b/(T_0 + T_1)                           zero denominator refused  (born_face_normalized)
//! executed   q̂_0 = ⟦T̃_0/(T̃_0 + T̃_1)⟧ on 2^(−M), clamped to [2^(−M), 1 − 2^(−M)],  q̂_1 = 1 − q̂_0
//! cell       q̂(c) = ∏_i q̂_i(c_i): a dyadic partition of the unit cell   (LandmarkTree.cell_faces_partition)
//! reception  ψ ← A_b ψ  (ρ ← A_b ρ A_b†/Tr(A_b ρ A_b†))           the collapse is the receipt (born_update_trace_one)
//! tick       ρ ← U ρ U†  with U = I between cells                  (born_unitary_invariant, born_tick_absorbed)
//! covector   ∂ log p(b)/∂A_c = G_c = (2/Z)(q_c/p_c − 1) A_c ρ,  Z = T_0 + T_1        (born_covector_eq)
//! deposit    H′ = H + ψ̂ψ̂†,   A_c ← A_c + ½(q_c/p̂_c − 1)(A_c ψ̂)(H′⁻¹ ψ̂)†        the normal prox step, γ = Z/4
//! ```
//!
//! [definition; agent-inferred] **The state is pure and stays pure.** Each digit has one operator
//! per outcome, so reception maps a pure density to a pure density, `A ψψ† A† = (Aψ)(Aψ)†` (Lean
//! `born_pure_stays_pure`), and so does the tick. The register opens at the ring's harmonic mode
//! `ψ_0 = (1, …, 1)`, the constant (dormant) mode of a closed ring (`HNN/Ring.ring_harmonic_mode_singular`),
//! so `ρ` is carried as the ray of `ψ`: `2χ` integers, with `O(χ²)` work a digit. A mixed opening is a
//! Bayesian mixture of pure runs (each weighted by its own evidence), at `χ` times the work; it is
//! not declared.
//!
//! [definition; agent-inferred, from the mathematics] **The tick between cells is the identity.**
//! The declared ring's Cayley tick (`HNN/Ring`) keeps the storage form `Q = diag(K, C)` of its
//! realified pair `(u, w)`, not a Hilbert metric on a register of width `χ`: `Q` is only
//! semidefinite on a closed ring (`C` and `K` share the harmonic mode, where the closed tick's
//! denominator is singular, `ring_harmonic_mode_singular`), and campaign 1 declares no resonator
//! material at all. And any fixed unitary tick is absorbed exactly by the first digit's learned
//! operators: `Tr(A UρU† A†) = Tr((AU)ρ(AU)†)` and the updated states agree (Lean
//! `born_tick_absorbed`), while the prox step's Frobenius metric is invariant under `A ↦ AU`. A
//! declared tick adds no face the operators cannot reach; it would change only the opening.
//!
//! [definition; agent-inferred] **The emission.** A cell is its `B = ⌈log₂|A|⌉` odometer digits,
//! most significant first. Two emissions are declared ([`Emission`]):
//! - `Position`: digit `i` has the operators `A_(i,0), A_(i,1)` (the brief's form, `B` pairs); the
//!   register must then also carry the cell's digit prefix;
//! - `Dyadic`: digit `i` of class `c` is read at its dyadic cell `h = 2^i + ⌊c/2^(B−i)⌋` (the tree's
//!   forced split, `2^B − 1` pairs founded at first arrival). A register of width `χ` carries at
//!   most `log₂ χ` bits of accessible information (Holevo), so reading the prefix from the operator's
//!   address leaves the register's capacity to the context; at `χ = 1` this emission is an order-0
//!   dyadic face.
//!
//! A digit whose dyadic cell's upper half holds no class of the chart is forced (face 1, no
//! reception).
//!
//! [definition; agent-inferred] **The opening operators** (no literal): each pair opens at
//! `A_(ℓ,b) = W_χ D_(ℓ,b)`, the normalized Walsh–Hadamard matrix (the characters of the digits'
//! group `(ℤ/2)^j`, `χ = 2^j`: `W/2^(j/2)` for even `j`, `(1 + i)W/2^((j+1)/2)` for odd `j`, an
//! exactly unitary dyadic Gaussian matrix) times a diagonal of signs from the declared sign
//! generator (`hnn::constitution::declared_sign`, kind `4` for `Position`, `5` for `Dyadic`). Both
//! operators are unitary, so `A_0†A_0 = A_1†A_1 = I` and every digit's opening split is exactly `½`
//! at every state (the uniform dyadic split); the signs break the symmetry between the outcomes, and
//! the dense `W` makes superpositions from the first reception.
//!
//! [definition; agent-inferred] **The learning** (the normal law's prox step, Lean
//! `HNN/Normal.normal_prox_step_complex`, on its lattices). Per locus the Gram of its feature `ψ̂`
//! opens at the unit prior, `H_0 = I` (campaign 1's), with unit sample weight. The step is Fisher
//! scoring: the split's Fisher information along a unit direction of the amplitude `a_c = A_c ψ̂` is
//! `(4/Z)(1 − p_c) ≤ 4/Z`, so `γ = Z/4`, and `(Z/4) G_c H′⁻¹ = ½(q_c/p_c − 1)(A_c ψ̂)(H′⁻¹ψ̂)†`.
//! Its first-order move of the split's logit is `h (q_0 − p_0)/(p_0 p_1)`, Newton's step for the log
//! loss times the leverage `h = ψ̂†H′⁻¹ψ̂`; the observed amplitude grows by `1 + ½h(1 − p)/p` along
//! `ψ̂` and the other shrinks by `1 − ½h`, which at `p = 1/(2n)` and `h = 1/(n + 1)` doubles the
//! amplitude, the KT face's own move. The coefficient reads the face at its executed lattice point
//! `p̂` (the chart of `p` at `2^(−M)`, whose residual is the face's rounding), so it is bounded by
//! `2^(M−1)`: a digit the executed face floors moves by the step the code paid for.
//!
//! [definition; agent-inferred] **The lattices** (Decisions 22 and 24; every width derived from the
//! declaration, [`BornWidths::derived`]):
//! - **the face** on `2^(−M)`, `M` the least with `2^M ≥ 3 B L_R (2n* + 2)`: a face of at least
//!   `1/(2n* + 2)` (the least a learner of `n*` arrivals assigns) is rounded within a quarter grain a
//!   cell (`LandmarkTree.digit_log_residual`), and a digit costs at most `M` bits;
//! - **the state's mantissa** `S = M + 3 + ⌈j/2⌉`: the pair's amplitudes are rebased jointly to `S`
//!   bits for the face (the largest real part in `[2^(S−1), 2^S)`), which moves the split by at
//!   most `√χ 2^(1−S) ≤ 2^(−M−2)`; the next state is the observed amplitude rebased alone, its ray
//!   moved by at most `√(χ/2) 2^(1−S)`;
//! - **the operators** on `2^(−L_A)`, `L_A = M + 3 + j`: an entry's unit moves an opening amplitude
//!   (`√Z = √2`) by less than a `2^(−M−2)` share; each deposit carries its remainder at the clock's
//!   refining precision `2^(−L_A−k_m)`, `k_m = 2⌊log₂ m⌋ + 1` (Lean `HNN/LatticeDeposit`), so
//!   applied + carried + released is the exact executed update and the releases since the locus's
//!   founding stay below half a unit;
//! - **the Gram** on `2^(−L_H)`, `L_H = ⌈log₂(2 L_R χ)⌉` (Decision 22's rule for a width-`χ` Gram:
//!   within `χ 2^(−L_H) ≤ 1/(2L_R)` of the exact statistic, so positive definite), its increment
//!   `ψψ†/‖ψ‖²` split exactly at the refining lattice;
//! - **the covector's charts** (Decision 24's chart-based covector): the amplitude `A_c ψ`, the
//!   solve `H′⁻¹ψ` and the coefficient `½(q_c/p̂_c − 1)/‖ψ‖²` each read on `C = M + 4 + j`
//!   significant bits (relative residual `2^(1−C)` each), their product an exact dyadic that the
//!   carry splits;
//! - **the solve** `v̂ ≈ H′⁻¹ψ` on `2^(−F)` in `ψ`'s units, `F = C + j + 3`, certified by its own
//!   residual `r = ψ − H′v̂`, computed exactly, `‖r‖∞ ≤ 2^(−C)‖ψ‖∞`; it starts from the carried
//!   preconditioner `X̂ ≈ H′⁻¹` (on `2^(−F)`, updated by the exact rank-one Sherman–Morrison step on
//!   its chart, refreshed by Newton–Schulz from the scaled identity only when a refinement stops
//!   halving the residual) and refines `v̂ ← v̂ + X̂r` until certified.
//!
//! Every product is formed in `i128` within the bounds these widths give; the operator entries are
//! refused past `2^62` and a locus past the declared population (the Gram's bound).
//!
//! | Law | Lean `HNN/BornFace` | Rust |
//! |---|---|---|
//! | the digit split is nonnegative and normalized; the cell faces partition the unit cell | `born_face_normalized`; `HNN/LandmarkTree.{executed_split_laws, cell_faces_partition}` | [`born_split`], [`Born::face`] |
//! | reception keeps a density, trace one | `born_update_trace_one` | [`Born::read`] |
//! | the pure state stays pure | `born_pure_stays_pure` | the carried ray `ψ` |
//! | the future faces factor through `ρ` (the retention quotient) | `born_state_future_sufficient` over `Foundation/Standing.StandingLaw` | [`Born`] holds `ψ` and the constitution only |
//! | the tick keeps trace and positivity, and a fixed tick is absorbed by the operators | `born_unitary_invariant`, `born_tick_absorbed` | the identity tick |
//! | the amplitudes cancel where a nonnegative receiver cannot | `born_interference_zero` | [`born_split`] (the floored zero) |
//! | the covector of the trace ratio | `born_covector_eq` | [`Born::deposit`] (its chart) |
//! | the prox step | `HNN/Normal.normal_prox_step_complex` | [`Born::deposit`] |
//! | the carry at the refining precision | `HNN/LatticeDeposit.{lattice_deposit_accounting, release_bounded_since_founding}` | [`Born::deposit`] |
//!
//! [established-bounded; measured] **On the standing cut** (notebook `hnn_born`, development cells
//! only, prequential): the best Born face, `Dyadic` at `χ = 128`, reads `4 + 3/16 + ε` bits a cell
//! against the landmark tree's `3 + 10/16 + ε`, and no member of the declared family (both
//! emissions, `χ ≤ 256`) lowers Decision 30's mixture below the tree; the mixture telescopes to
//! `½W_T + ½W_B`, so it codes below the tree only where the Born face alone does.
//!
//! [established-bounded; measured] **Weighed locally** (Decision 34; the notebook `hnn_landmark`'s
//! retired `local` mode, commit `d2a2e0db`): the Born face's digit split
//! ([`DigitOperand::numerator`], read causally at each digit) was the external face of the landmark
//! tree's node-local law (retired, its realization at commit `89460425`, its law in Lean
//! `HNN/LocalWeighing`) and is one face of the switching mixture
//! (`hnn::receiving::Mixture::switching`). Its oracle against
//! the tree on the development cells is large at the digit and cell grains (`−3499 + 10/16 + ε` and
//! `−1531 + 9/16 + ε` bits at `Dyadic` `χ = 128`) and small at the dyadic-cell grain
//! (`−46 + 3/16 + ε`). Both local laws code below the tree on the development cells, charged
//! (`−52 + 11/16 + ε` with `χ = 1` at each landmark, `−98 + 9/16 + ε` with `χ = 256` across epochs),
//! and above it held out (`+17 + 3/16 + ε`, `+11 + 4/16 + ε`).
//!
//! [open] Owed in #62: the per-digit residuals (the face's rounding, the joint and the state's
//! rebase, the covector's charts, the solve's certificate) composed over the passage into a bound
//! against the never-rounded receiver, as for the tree and the word; the convergence of the
//! Fisher-scored prox step; Glasser et al.'s separation in general.

use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};
use rayon::prelude::*;

use crate::hnn::HnnError;
use crate::hnn::constitution::{declared_sign, gamma_length};
use crate::hnn::landmark::odometer_digits;
use crate::ratio::Rat;

/// A Gaussian integer on a carrier word, `(re, im)`.
pub type Word = (i64, i64);
/// A Gaussian integer on a wide word, `(re, im)`.
pub type Wide = (i128, i128);

/// The operator entries' carrier bound: an entry's real and imaginary parts stay below `2^62`.
const OPERATOR_BOUND: i128 = 1 << 62;

/// The sign generator's kind of the register's operator pairs, per emission.
const SIGN_KIND: [u64; 2] = [4, 5];

// -------------------------------------------------------------------------------------------
// the declaration and its widths

/// [definition] **Where a digit's operators live** (module header, "The emission").
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Emission {
    /// Digit `i` has the pair `A_(i,0), A_(i,1)`.
    Position,
    /// Digit `i` of class `c` is read at its dyadic cell `h = 2^i + ⌊c/2^(B−i)⌋`.
    Dyadic,
}

impl Emission {
    fn index(self) -> usize {
        match self {
            Self::Position => 0,
            Self::Dyadic => 1,
        }
    }
}

/// [definition] **A declared Born receiver**: the exterior chart `|A|`, the register's width
/// `χ = 2^j`, the emission, the declared population `n*` (the passage its widths hold within) and
/// the receiver's grain `L_R`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BornDeclaration {
    pub alphabet: usize,
    pub width: usize,
    pub emission: Emission,
    pub population: u64,
    pub grain: u64,
}

/// [definition; agent-inferred] **The derived widths** (module header, "The lattices").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BornWidths {
    /// `B`, the odometer digits of a cell.
    pub digits: u64,
    /// `j = log₂ χ`.
    pub order: u32,
    /// `M`, the face's lattice.
    pub face: u32,
    /// `S`, the state's mantissa.
    pub state: u32,
    /// `L_A`, the operators' lattice.
    pub operator: u32,
    /// `L_H`, the Gram's lattice.
    pub gram: u32,
    /// `C`, the covector charts' significant bits and the solve's target `2^(−C)`.
    pub chart: u32,
    /// `F`, the solve's and the preconditioner's lattice.
    pub solve: u32,
}

/// `⌈log₂ x⌉` of a positive integer (zero at one).
fn ceil_log2(x: u128) -> u32 {
    if x <= 1 {
        0
    } else {
        128 - (x - 1).leading_zeros()
    }
}

impl BornWidths {
    /// **The widths a declaration derives** (module header). Refused at a width that is not a
    /// power of two, an alphabet below two, or widths whose products would pass `i128`.
    pub fn derived(declaration: &BornDeclaration) -> Result<Self, HnnError> {
        let width = declaration.width;
        if width == 0 || !width.is_power_of_two() {
            return Err(HnnError::Shape {
                what: "a register width χ = 2^j",
                expected: width.next_power_of_two(),
                found: width,
            });
        }
        if declaration.alphabet < 2 || declaration.population == 0 || declaration.grain == 0 {
            return Err(HnnError::NonpositiveDeclaration);
        }
        let order = width.trailing_zeros();
        let digits = odometer_digits(declaration.alphabet);
        let floor = 2 * u128::from(declaration.population) + 2;
        let face = ceil_log2(3 * u128::from(digits) * u128::from(declaration.grain) * floor).max(1);
        let state = face + 3 + order.div_ceil(2);
        let operator = face + 3 + order;
        let gram = ceil_log2(2 * u128::from(declaration.grain) * width as u128);
        let chart = face + 4 + order;
        let solve = chart + order + 3;
        let widths = Self {
            digits,
            order,
            face,
            state,
            operator,
            gram,
            chart,
            solve,
        };
        widths.admitted(declaration.population)?;
        Ok(widths)
    }

    /// **The `i128` bounds** of every product the receiver forms (module header): the read
    /// `A ψ`, the face's traces over `2^(M+1)`, the covector's triple product, the Gram's increment
    /// at the finest refining precision, and the solve's residual at the population's Gram.
    fn admitted(&self, population: u64) -> Result<(), HnnError> {
        let log_width = self.order + 1;
        let precision = gamma_length(population.max(1));
        let gram_bits = ceil_log2(u128::from(population) + 2) + self.gram + self.order.div_ceil(2);
        let checks = [
            62 + self.state + log_width + 1,
            2 * self.state + log_width + 2 + self.face + 1,
            3 * self.chart + 3,
            2 * self.state + 1 + self.gram + precision + 1,
            gram_bits + (self.state + 2 + self.order.div_ceil(2) + self.solve) + log_width,
            (self.solve + 2) + (self.chart + 1) + log_width,
        ];
        if checks.iter().any(|&bits| bits > 126) || self.operator >= 62 || self.solve >= 60 {
            return Err(HnnError::Carrier {
                what: "the Born receiver's derived widths pass the 128-bit carrier",
            });
        }
        Ok(())
    }
}

// -------------------------------------------------------------------------------------------
// exact integer steps

/// The nearest integer of `x/2^s`, ties upward (`s ≥ 0`).
fn round_shift(x: i128, s: u32) -> i128 {
    if s == 0 {
        x
    } else {
        (x + (1i128 << (s - 1))) >> s
    }
}

/// The nearest integer of `num/den` (`den > 0`), ties upward: the Ratio's `div_rem`.
fn div_round(num: i128, den: i128) -> i128 {
    let (q, r) = (num.div_euclid(den), num.rem_euclid(den));
    if 2 * r >= den { q + 1 } else { q }
}

/// `x·2^e` for a signed exponent: exact when `e ≥ 0`, the nearest integer (ties upward) otherwise.
fn scale(x: i128, e: i32) -> i128 {
    if e >= 0 {
        x << e
    } else {
        round_shift(x, (-e) as u32)
    }
}

/// The bits of the largest real or imaginary part of a wide vector.
fn wide_bits(vector: &[Wide]) -> u32 {
    vector
        .iter()
        .map(|&(re, im)| re.unsigned_abs().max(im.unsigned_abs()))
        .max()
        .map_or(0, |largest| 128 - largest.leading_zeros())
}

/// **A vector's chart on `bits` significant bits**: each part rounded at the common shift that
/// puts the largest part below `2^bits` (no shift when it already is), with that shift.
fn chart(vector: &[Wide], bits: u32) -> (Vec<Wide>, u32) {
    let shift = wide_bits(vector).saturating_sub(bits);
    (
        vector
            .iter()
            .map(|&(re, im)| (round_shift(re, shift), round_shift(im, shift)))
            .collect(),
        shift,
    )
}

/// **A positive ratio's chart** `num/den ≈ m·2^e` with `m ∈ [2^(bits−1), 2^bits]`, the nearest
/// (ties upward) at that exponent.
fn ratio_chart(num: &BigUint, den: &BigUint, bits: u32) -> (i128, i32) {
    let exponent = i64::try_from(den.bits()).expect("bits")
        - i64::try_from(num.bits()).expect("bits")
        + i64::from(bits);
    let (numerator, denominator) = if exponent >= 0 {
        (num << (exponent as usize), den.clone())
    } else {
        (num.clone(), den << ((-exponent) as usize))
    };
    let mantissa = (numerator * 2u32 + &denominator) / (denominator * 2u32);
    (
        mantissa.to_i128().expect("a chart mantissa of `bits` bits"),
        -(exponent as i32),
    )
}

fn mul(a: Wide, b: Wide) -> Wide {
    (a.0 * b.0 - a.1 * b.1, a.0 * b.1 + a.1 * b.0)
}

/// `a · conj(b)`.
fn mul_conj(a: Wide, b: Wide) -> Wide {
    (a.0 * b.0 + a.1 * b.1, a.1 * b.0 - a.0 * b.1)
}

fn wide(word: Word) -> Wide {
    (i128::from(word.0), i128::from(word.1))
}

/// `M v` for a `χ × χ` word matrix and a wide vector, exact.
fn apply(matrix: &[Word], vector: &[Wide]) -> Vec<Wide> {
    let n = vector.len();
    (0..n)
        .map(|row| {
            matrix[row * n..(row + 1) * n].iter().zip(vector).fold(
                (0i128, 0i128),
                |sum, (&entry, &x)| {
                    let p = mul(wide(entry), x);
                    (sum.0 + p.0, sum.1 + p.1)
                },
            )
        })
        .collect()
}

/// The largest real or imaginary part of a wide vector, as a magnitude.
fn wide_max(vector: &[Wide]) -> u128 {
    vector
        .iter()
        .map(|&(re, im)| re.unsigned_abs().max(im.unsigned_abs()))
        .max()
        .unwrap_or(0)
}

/// `‖x‖²`, exact.
fn norm_sq(vector: &[Wide]) -> u128 {
    vector
        .iter()
        .map(|&(re, im)| (re * re + im * im) as u128)
        .sum()
}

// -------------------------------------------------------------------------------------------
// the split

/// [definition] **One digit's Born split at a state** (module header): the exact images
/// `a_c = A_c ψ`, the traces `T̃_c` of the pair jointly rebased to `S` bits, and the executed
/// numerator `n = ⟦2^M T̃_0/(T̃_0 + T̃_1)⟧` in `[1, 2^M − 1]`, so `q̂_0 = n/2^M`, `q̂_1 = 1 − q̂_0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BornSplit {
    pub amplitudes: [Vec<Wide>; 2],
    pub traces: [u128; 2],
    pub numerator: u64,
}

impl BornSplit {
    /// The executed face of outcome `b`, exact on `2^(−M)`.
    pub fn face(&self, b: usize, face_bits: u32) -> Rat {
        let scale = 1u64 << face_bits;
        let numerator = if b == 0 {
            self.numerator
        } else {
            scale - self.numerator
        };
        Rat::new(numerator.into(), scale.into())
    }
}

/// **The Born split of a digit** at state `ψ` with operators `A_0, A_1` on any lattice (both on
/// one, `χ × χ` row-major): exact images, the joint rebase to `state_bits`, and the executed
/// numerator on `2^(−face_bits)`. Refused at a zero denominator (both images zero).
pub fn born_split(
    operators: [&[Word]; 2],
    state: &[Word],
    face_bits: u32,
    state_bits: u32,
) -> Result<BornSplit, HnnError> {
    let psi: Vec<Wide> = state.iter().map(|&x| wide(x)).collect();
    let amplitudes = [apply(operators[0], &psi), apply(operators[1], &psi)];
    let bits = wide_bits(&amplitudes[0]).max(wide_bits(&amplitudes[1]));
    let shift = bits.saturating_sub(state_bits);
    let traces = [0, 1].map(|b| {
        amplitudes[b]
            .iter()
            .map(|&(re, im)| {
                let (re, im) = (round_shift(re, shift), round_shift(im, shift));
                (re * re + im * im) as u128
            })
            .sum::<u128>()
    });
    let total = traces[0] + traces[1];
    if total == 0 {
        return Err(HnnError::BornZero {
            what: "a digit whose two images vanish: the split's denominator is zero",
        });
    }
    let scaled = traces[0] << (face_bits + 1);
    let nearest = (scaled + total) / (2 * total);
    let top = (1u128 << face_bits) - 1;
    let numerator = nearest.clamp(1, top) as u64;
    Ok(BornSplit {
        amplitudes,
        traces,
        numerator,
    })
}

/// The state's rebase: the observed image, its largest real or imaginary part moved into
/// `[2^(S−1), 2^S)` (a right shift rounds, ties upward; a left shift is exact). Refused at zero.
fn rebase_state(image: &[Wide], state_bits: u32) -> Result<(Vec<Word>, bool), HnnError> {
    let bits = wide_bits(image);
    if bits == 0 {
        return Err(HnnError::BornZero {
            what: "the observed digit's image is zero: the density's update has no trace",
        });
    }
    if bits <= state_bits {
        let left = state_bits - bits;
        return Ok((
            image
                .iter()
                .map(|&(re, im)| ((re << left) as i64, (im << left) as i64))
                .collect(),
            false,
        ));
    }
    let mut shift = bits - state_bits;
    let mut rounded: Vec<Wide> = image
        .iter()
        .map(|&(re, im)| (round_shift(re, shift), round_shift(im, shift)))
        .collect();
    if wide_bits(&rounded) > state_bits {
        shift += 1;
        rounded = image
            .iter()
            .map(|&(re, im)| (round_shift(re, shift), round_shift(im, shift)))
            .collect();
    }
    Ok((
        rounded
            .into_iter()
            .map(|(re, im)| (re as i64, im as i64))
            .collect(),
        true,
    ))
}

// -------------------------------------------------------------------------------------------
// a locus: one digit's operator pair, its Gram, its preconditioner and its clock

#[derive(Clone, Debug, PartialEq, Eq)]
struct Locus {
    /// `A_(ℓ,0), A_(ℓ,1)` on `2^(−L_A)`, `χ × χ` row-major.
    operators: [Vec<Word>; 2],
    /// Their carried remainders on `2^(−L_A−k)`.
    remainders: [Vec<Word>; 2],
    /// The Gram `H` on `2^(−L_H)`, Hermitian.
    gram: Vec<Word>,
    /// Its carried remainder on `2^(−L_H−k)`.
    gram_remainder: Vec<Word>,
    /// The preconditioner `X̂ ≈ H⁻¹` on `2^(−F)`, Hermitian.
    preconditioner: Vec<Word>,
    /// The deposit clock `m`.
    clock: u64,
    /// `k_m` of the last deposit: the remainders' refining precision.
    precision: u32,
}

/// [definition] **One digit's operands for its deposit**: the locus it was read at, the state it
/// read, its exact images, its executed numerator and the observed outcome. Transient: a cell's
/// operands are consumed by its deposit and released.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DigitOperand {
    pub locus: usize,
    pub state: Vec<Word>,
    pub amplitudes: [Vec<Wide>; 2],
    pub numerator: u64,
    pub observed: usize,
}

/// [definition] **A cell's reception**: its executed face (exact, on `2^(−BM)`) and its digits'
/// operands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reception {
    pub face: Rat,
    pub digits: Vec<DigitOperand>,
}

/// [definition] **One locus's deposit receipt**: the solve's refinement steps, whether the
/// preconditioner was refreshed, and the solve's certificate `‖r‖∞/‖ψ‖∞`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct DepositReceipt {
    refinements: u32,
    refreshed: bool,
    certificate: Rat,
}

/// [definition] **The receiver's executed-chart receipts** over its passage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BornReport {
    /// Cells deposited.
    pub deposits: u64,
    /// Locus deposits (one a digit read).
    pub locus_deposits: u64,
    /// Solve refinement steps in all, and the most in one deposit.
    pub refinements: u64,
    pub most_refinements: u32,
    /// Preconditioner refreshes by Newton–Schulz.
    pub refreshes: u64,
    /// The largest certified solve residual `‖r‖∞/‖ψ‖∞`.
    pub largest_certificate: Rat,
    /// State rebases that rounded (a right shift).
    pub state_rebases: u64,
    /// Digits read.
    pub digits: u64,
}

impl Default for BornReport {
    fn default() -> Self {
        Self {
            deposits: 0,
            locus_deposits: 0,
            refinements: 0,
            most_refinements: 0,
            refreshes: 0,
            largest_certificate: Rat::zero(),
            state_rebases: 0,
            digits: 0,
        }
    }
}

impl Locus {
    /// **The opening locus** (module header, "The opening operators"): `W_χ D_(ℓ,b)`, `H = I`,
    /// `X̂ = I`, clock zero.
    fn open(widths: &BornWidths, width: usize, emission: Emission, index: usize) -> Self {
        let j = widths.order;
        let exponent = widths.operator - j.div_ceil(2);
        let unit = 1i64 << exponent;
        let odd = j % 2 == 1;
        let operators = [0usize, 1].map(|b| {
            let code = (SIGN_KIND[emission.index()] << 40) + ((index as u64) << 20) + b as u64;
            let signs: Vec<i64> = (0..width as u64)
                .map(|l| {
                    if declared_sign(code, l, l) > Rat::zero() {
                        1
                    } else {
                        -1
                    }
                })
                .collect();
            let mut matrix = vec![(0i64, 0i64); width * width];
            for k in 0..width {
                for l in 0..width {
                    let walsh = if (k & l).count_ones() % 2 == 0 { 1 } else { -1 };
                    let entry = walsh * signs[l] * unit;
                    matrix[k * width + l] = if odd { (entry, entry) } else { (entry, 0) };
                }
            }
            matrix
        });
        let identity = |bits: u32| {
            let mut matrix = vec![(0i64, 0i64); width * width];
            for k in 0..width {
                matrix[k * width + k] = (1i64 << bits, 0);
            }
            matrix
        };
        Self {
            operators,
            remainders: [vec![(0, 0); width * width], vec![(0, 0); width * width]],
            gram: identity(widths.gram),
            gram_remainder: vec![(0, 0); width * width],
            preconditioner: identity(widths.solve),
            clock: 0,
            precision: gamma_length(0),
        }
    }

    /// **Deposit one digit's covector** (module header, "The learning"): the clock advances, the
    /// Gram takes `ψψ†/‖ψ‖²` at the refining lattice, the preconditioner its Sherman–Morrison
    /// step, the solve `v̂ ≈ H′⁻¹ψ` is certified, and each operator takes
    /// `½(q_c/p̂_c − 1)(A_c ψ)v̂†/‖ψ‖²` through its charts and the carry.
    fn deposit(
        &mut self,
        operand: &DigitOperand,
        widths: &BornWidths,
        population: u64,
    ) -> Result<DepositReceipt, HnnError> {
        let n = operand.state.len();
        if self.clock >= population {
            return Err(HnnError::PopulationReached { population });
        }
        self.clock += 1;
        let k = gamma_length(self.clock);
        let refine = k - self.precision;
        for remainder in self
            .remainders
            .iter_mut()
            .chain(std::iter::once(&mut self.gram_remainder))
        {
            for entry in remainder.iter_mut() {
                *entry = (entry.0 << refine, entry.1 << refine);
            }
        }
        self.precision = k;
        let psi: Vec<Wide> = operand.state.iter().map(|&x| wide(x)).collect();
        let norm = norm_sq(&psi) as i128;

        // The Gram: H ← H + ψψ†/‖ψ‖², split exactly at 2^(−L_H−k), the remainder carried.
        let fine = widths.gram + k;
        for i in 0..n {
            for l in i..n {
                let numerator = mul_conj(psi[i], psi[l]);
                let increment = (
                    div_round(numerator.0 << fine, norm),
                    div_round(numerator.1 << fine, norm),
                );
                let index = i * n + l;
                let carried = (
                    i128::from(self.gram_remainder[index].0) + increment.0,
                    i128::from(self.gram_remainder[index].1) + increment.1,
                );
                let applied = (round_shift(carried.0, k), round_shift(carried.1, k));
                let remainder = (carried.0 - (applied.0 << k), carried.1 - (applied.1 << k));
                let entry = (
                    i128::from(self.gram[index].0) + applied.0,
                    i128::from(self.gram[index].1) + applied.1,
                );
                self.gram[index] = (entry.0 as i64, entry.1 as i64);
                self.gram_remainder[index] = (remainder.0 as i64, remainder.1 as i64);
                if l != i {
                    self.gram[l * n + i] = (entry.0 as i64, -entry.1 as i64);
                    self.gram_remainder[l * n + i] = (remainder.0 as i64, -remainder.1 as i64);
                }
            }
        }

        // The preconditioner's Sherman–Morrison step X̂ ← X̂ − uu†/(‖ψ‖² + ψ†u), u = X̂ψ.
        let u = apply(&self.preconditioner, &psi);
        let quadratic: i128 = psi.iter().zip(&u).map(|(&p, &x)| mul_conj(x, p).0).sum();
        let denominator = (norm << widths.solve) + quadratic;
        let mut refreshed = false;
        if denominator > 0 {
            let (charted, shift) = chart(&u, widths.chart);
            let (gain, exponent) = ratio_chart(
                &(BigUint::one() << (2 * shift) as usize),
                &BigUint::from(denominator as u128),
                widths.chart,
            );
            for i in 0..n {
                for l in i..n {
                    let term = mul_conj(charted[i], charted[l]);
                    let term = (
                        scale(term.0 * gain, exponent),
                        scale(term.1 * gain, exponent),
                    );
                    let index = i * n + l;
                    let entry = (
                        i128::from(self.preconditioner[index].0) - term.0,
                        i128::from(self.preconditioner[index].1) - term.1,
                    );
                    self.preconditioner[index] = (entry.0 as i64, entry.1 as i64);
                    if l != i {
                        self.preconditioner[l * n + i] = (entry.0 as i64, -entry.1 as i64);
                    }
                }
            }
        } else {
            self.refresh(widths, n)?;
            refreshed = true;
        }

        // The certified solve H′v̂ = ψ.
        let (solution, refinements, certificate, again) = self.solve(&psi, widths)?;
        refreshed |= again;

        // The covector through its charts, then the carry at 2^(−L_A−k).
        let (solution_chart, solution_shift) = chart(&solution, widths.chart);
        let norm_big = BigUint::from(norm as u128);
        let scale_face = 1u64 << widths.face;
        let executed = [operand.numerator, scale_face - operand.numerator];
        for c in 0..2 {
            let (amplitude, amplitude_shift) = chart(&operand.amplitudes[c], widths.chart);
            // ½(q_c/p̂_c − 1)/‖ψ‖²: observed (p̂_(c′)/p̂_c)/(2‖ψ‖²), unobserved −1/(2‖ψ‖²).
            let (numerator, denominator, sign) = if c == operand.observed {
                (
                    BigUint::from(executed[1 - c]),
                    BigUint::from(executed[c]) * &norm_big * 2u32,
                    1i128,
                )
            } else {
                (BigUint::one(), &norm_big * 2u32, -1i128)
            };
            let (gain, gain_exponent) = ratio_chart(&numerator, &denominator, widths.chart);
            let gain = sign * gain;
            let exponent = gain_exponent + amplitude_shift as i32 + solution_shift as i32
                - widths.solve as i32
                + k as i32;
            let operator = &mut self.operators[c];
            let remainder = &mut self.remainders[c];
            for (row, &left) in amplitude.iter().enumerate() {
                if left == (0, 0) {
                    continue;
                }
                for (column, &right) in solution_chart.iter().enumerate() {
                    let product = mul_conj(left, right);
                    let update = (
                        scale(product.0 * gain, exponent),
                        scale(product.1 * gain, exponent),
                    );
                    let index = row * n + column;
                    let carried = (
                        i128::from(remainder[index].0) + update.0,
                        i128::from(remainder[index].1) + update.1,
                    );
                    let applied = (round_shift(carried.0, k), round_shift(carried.1, k));
                    let rest = (carried.0 - (applied.0 << k), carried.1 - (applied.1 << k));
                    let entry = (
                        i128::from(operator[index].0) + applied.0,
                        i128::from(operator[index].1) + applied.1,
                    );
                    if entry.0.abs() >= OPERATOR_BOUND || entry.1.abs() >= OPERATOR_BOUND {
                        return Err(HnnError::Carrier {
                            what: "a Born operator entry past 2^62",
                        });
                    }
                    operator[index] = (entry.0 as i64, entry.1 as i64);
                    remainder[index] = (rest.0 as i64, rest.1 as i64);
                }
            }
        }
        Ok(DepositReceipt {
            refinements,
            refreshed,
            certificate,
        })
    }

    /// **The certified solve** `H′v̂ = ψ` on `2^(−F)`: from `X̂ψ`, refined by `v̂ ← v̂ + X̂ r̃`
    /// (`r̃` the residual's chart) until `‖r‖∞ ≤ 2^(−C)‖ψ‖∞`, each step halving the residual or the
    /// preconditioner refreshed once; refused past that.
    fn solve(
        &mut self,
        psi: &[Wide],
        widths: &BornWidths,
    ) -> Result<(Vec<Wide>, u32, Rat, bool), HnnError> {
        let scale_bits = widths.gram + widths.solve;
        let limit = wide_max(psi) << (scale_bits - widths.chart);
        let mut refreshed = false;
        loop {
            let mut solution = apply(&self.preconditioner, psi);
            let mut residual = self.residual(psi, &solution, scale_bits);
            let mut size = wide_max(&residual);
            let mut steps = 0u32;
            while size > limit {
                let (charted, shift) = chart(&residual, widths.chart);
                let correction = apply(&self.preconditioner, &charted);
                let back = scale_bits as i32 - shift as i32;
                for (x, &d) in solution.iter_mut().zip(&correction) {
                    x.0 += scale(d.0, -back);
                    x.1 += scale(d.1, -back);
                }
                let next = self.residual(psi, &solution, scale_bits);
                let next_size = wide_max(&next);
                steps += 1;
                if 2 * next_size > size {
                    break;
                }
                residual = next;
                size = next_size;
            }
            if size <= limit {
                let certificate =
                    Rat::new(size.into(), (wide_max(psi) << scale_bits).max(1).into());
                return Ok((solution, steps, certificate, refreshed));
            }
            if refreshed {
                return Err(HnnError::Carrier {
                    what: "the Born solve did not certify after the preconditioner's refresh",
                });
            }
            self.refresh(widths, psi.len())?;
            refreshed = true;
        }
    }

    /// `r = ψ 2^(L_H+F) − H v̂` in the solve's integer units (scale `2^(−(L_H+F))`).
    fn residual(&self, psi: &[Wide], solution: &[Wide], scale_bits: u32) -> Vec<Wide> {
        let image = apply(&self.gram, solution);
        psi.iter()
            .zip(image)
            .map(|(&p, h)| ((p.0 << scale_bits) - h.0, (p.1 << scale_bits) - h.1))
            .collect()
    }

    /// **The preconditioner's refresh**: Newton–Schulz `X ← X(2I − HX)` from the scaled identity
    /// `2^(−p)I`, `2^p ≥ ‖H‖∞` (the carried Gram is Hermitian positive definite, so the residual's
    /// spectrum lies in `[0, 1)` and squares each step), until `‖I − HX‖∞ ≤ 2^(−C/2)`.
    fn refresh(&mut self, widths: &BornWidths, n: usize) -> Result<(), HnnError> {
        let rows = row_sums(&self.gram, n);
        let p = ceil_log2(rows.max(1)).saturating_sub(widths.gram);
        let mut matrix = vec![(0i64, 0i64); n * n];
        for k in 0..n {
            matrix[k * n + k] = (1i64 << (widths.solve - p.min(widths.solve)), 0);
        }
        let unit = 1i128 << (widths.gram + widths.solve);
        let target = unit >> widths.chart.div_ceil(2);
        let steps = p + ceil_log2(u128::from(widths.chart)) + 8;
        for _ in 0..steps {
            let product = mat_mul(&self.gram, &matrix, n);
            let residual: Vec<Wide> = product
                .iter()
                .enumerate()
                .map(|(index, &(re, im))| {
                    let diagonal = if index / n == index % n { unit } else { 0 };
                    (diagonal - re, -im)
                })
                .collect();
            let norm = (0..n)
                .map(|row| {
                    residual[row * n..(row + 1) * n]
                        .iter()
                        .map(|&(re, im)| re.unsigned_abs() + im.unsigned_abs())
                        .sum::<u128>()
                })
                .max()
                .unwrap_or(0);
            if norm <= target as u128 {
                self.preconditioner = matrix;
                return Ok(());
            }
            let correction = mat_mul_wide(&matrix, &residual, n);
            let shift = widths.gram + widths.solve;
            let mut next = vec![(0i64, 0i64); n * n];
            for i in 0..n {
                for l in i..n {
                    let index = i * n + l;
                    let entry = (
                        i128::from(matrix[index].0) + round_shift(correction[index].0, shift),
                        i128::from(matrix[index].1) + round_shift(correction[index].1, shift),
                    );
                    next[index] = (entry.0 as i64, entry.1 as i64);
                    next[l * n + i] = (entry.0 as i64, -entry.1 as i64);
                }
            }
            matrix = next;
        }
        Err(HnnError::Carrier {
            what: "the Born preconditioner's Newton–Schulz refresh did not certify",
        })
    }
}

/// The largest absolute row sum of a word matrix's parts, `max_i Σ_l |re| + |im|`.
fn row_sums(matrix: &[Word], n: usize) -> u128 {
    (0..n)
        .map(|row| {
            matrix[row * n..(row + 1) * n]
                .iter()
                .map(|&(re, im)| u128::from(re.unsigned_abs()) + u128::from(im.unsigned_abs()))
                .sum::<u128>()
        })
        .max()
        .unwrap_or(0)
}

/// `A B` of two word matrices, exact.
fn mat_mul(a: &[Word], b: &[Word], n: usize) -> Vec<Wide> {
    let b: Vec<Wide> = b.iter().map(|&x| wide(x)).collect();
    mat_mul_wide(a, &b, n)
}

/// `A B` of a word matrix and a wide one, exact within the widths' bounds.
fn mat_mul_wide(a: &[Word], b: &[Wide], n: usize) -> Vec<Wide> {
    let mut product = vec![(0i128, 0i128); n * n];
    for i in 0..n {
        for m in 0..n {
            let left = wide(a[i * n + m]);
            if left == (0, 0) {
                continue;
            }
            for l in 0..n {
                let p = mul(left, b[m * n + l]);
                let entry = &mut product[i * n + l];
                entry.0 += p.0;
                entry.1 += p.1;
            }
        }
    }
    product
}

// -------------------------------------------------------------------------------------------
// the receiver

/// The carried values of a founded locus, read by the tests.
#[cfg(test)]
pub(crate) struct LocusView<'a> {
    pub operators: [&'a [Word]; 2],
    pub remainders: [&'a [Word]; 2],
    pub gram: &'a [Word],
    pub gram_remainder: &'a [Word],
    pub clock: u64,
    pub precision: u32,
}

/// [definition] **The Born receiver** (module header): its declaration and widths, the operator
/// loci founded at first arrival, the register's ray `ψ` (the retained density), and the executed
/// charts' receipts. It holds the current operators, statistics and state and no list of cells.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Born {
    declaration: BornDeclaration,
    widths: BornWidths,
    loci: Vec<Option<Box<Locus>>>,
    state: Vec<Word>,
    report: BornReport,
}

impl Born {
    /// **The opening receiver**: no locus founded, the register at the harmonic mode
    /// `ψ_0 = (1, …, 1)` on its mantissa's top octave.
    pub fn new(declaration: BornDeclaration) -> Result<Self, HnnError> {
        let widths = BornWidths::derived(&declaration)?;
        let loci = match declaration.emission {
            Emission::Position => widths.digits as usize,
            Emission::Dyadic => 1usize << widths.digits,
        };
        let state = vec![(1i64 << (widths.state - 1), 0); declaration.width];
        Ok(Self {
            declaration,
            widths,
            loci: vec![None; loci],
            state,
            report: BornReport::default(),
        })
    }

    pub fn declaration(&self) -> &BornDeclaration {
        &self.declaration
    }

    pub fn widths(&self) -> BornWidths {
        self.widths
    }

    pub fn report(&self) -> &BornReport {
        &self.report
    }

    /// The register's ray `ψ` (the retained density `ψψ†/‖ψ‖²`).
    pub fn state(&self) -> &[Word] {
        &self.state
    }

    /// The founded loci.
    pub fn founded(&self) -> usize {
        self.loci.iter().filter(|locus| locus.is_some()).count()
    }

    /// **The stored bits**: every founded locus's words (the operators and their remainders, the
    /// Gram and its remainder, the preconditioner) at 64 bits a part, and the register's.
    pub fn bits(&self) -> u64 {
        let n = self.declaration.width as u64;
        let per_locus = 7 * n * n * 128 + 2 * 64;
        self.founded() as u64 * per_locus + n * 128
    }

    /// The digits a class opens: each digit's locus and outcome, or `None` for a forced digit
    /// (its dyadic cell's upper half holds no class of the chart).
    fn digits(&self, class: usize) -> Result<Vec<Option<(usize, usize)>>, HnnError> {
        let alphabet = self.declaration.alphabet;
        if class >= alphabet {
            return Err(HnnError::CellOutside {
                code: class,
                alphabet,
            });
        }
        let b = self.widths.digits as usize;
        Ok((0..b)
            .map(|i| {
                let prefix = class >> (b - i);
                let upper = (prefix << (b - i)) + (1 << (b - i - 1));
                if upper >= alphabet {
                    return None;
                }
                let outcome = (class >> (b - 1 - i)) & 1;
                let locus = match self.declaration.emission {
                    Emission::Position => i,
                    Emission::Dyadic => (1 << i) + prefix,
                };
                Some((locus, outcome))
            })
            .collect())
    }

    /// **The split of a locus at a state**: its founded operators, borrowed, or the opening pair
    /// an unfounded locus reads.
    fn split(&self, locus: usize, state: &[Word]) -> Result<BornSplit, HnnError> {
        let (face_bits, state_bits) = (self.widths.face, self.widths.state);
        match &self.loci[locus] {
            Some(founded) => born_split(
                [&founded.operators[0], &founded.operators[1]],
                state,
                face_bits,
                state_bits,
            ),
            None => {
                let opening = Locus::open(
                    &self.widths,
                    self.declaration.width,
                    self.declaration.emission,
                    locus,
                )
                .operators;
                born_split([&opening[0], &opening[1]], state, face_bits, state_bits)
            }
        }
    }

    /// **Read a cell** at the current standing (Decision 29: before its own deposit): each digit's
    /// split at the state the earlier digits left, the state received digit by digit
    /// (`ψ ← A_b ψ`, rebased), and the cell's executed face, with the digits' operands.
    pub fn read(&mut self, class: usize) -> Result<Reception, HnnError> {
        let digits = self.digits(class)?;
        let face_bits = self.widths.face;
        let mut numerator = BigUint::one();
        let mut exponent = 0u64;
        let mut operands = Vec::with_capacity(digits.len());
        for (locus, outcome) in digits.into_iter().flatten() {
            let split = self.split(locus, &self.state)?;
            let executed = if outcome == 0 {
                split.numerator
            } else {
                (1u64 << face_bits) - split.numerator
            };
            numerator *= executed;
            exponent += u64::from(face_bits);
            let (next, rounded) = rebase_state(&split.amplitudes[outcome], self.widths.state)?;
            self.report.digits += 1;
            self.report.state_rebases += u64::from(rounded);
            operands.push(DigitOperand {
                locus,
                state: std::mem::replace(&mut self.state, next),
                amplitudes: split.amplitudes,
                numerator: split.numerator,
                observed: outcome,
            });
        }
        let face = Rat::new(
            numerator.into(),
            (BigUint::one() << exponent as usize).into(),
        );
        Ok(Reception {
            face,
            digits: operands,
        })
    }

    /// **The executed face of a class** at the current standing, changing nothing (the state is
    /// walked on a copy).
    pub fn face(&self, class: usize) -> Result<Rat, HnnError> {
        let face_bits = self.widths.face;
        let mut state = self.state.clone();
        let mut face = Rat::one();
        for (locus, outcome) in self.digits(class)?.into_iter().flatten() {
            let split = self.split(locus, &state)?;
            face *= split.face(outcome, face_bits);
            state = rebase_state(&split.amplitudes[outcome], self.widths.state)?.0;
        }
        Ok(face)
    }

    /// The carried values of a founded locus (the tests' reading): its operators and their
    /// remainders, its Gram and remainder, its clock and precision `k_m`.
    #[cfg(test)]
    pub(crate) fn locus(&self, locus: usize) -> Option<LocusView<'_>> {
        self.loci[locus].as_ref().map(|founded| LocusView {
            operators: [&founded.operators[0], &founded.operators[1]],
            remainders: [&founded.remainders[0], &founded.remainders[1]],
            gram: &founded.gram,
            gram_remainder: &founded.gram_remainder,
            clock: founded.clock,
            precision: founded.precision,
        })
    }

    /// The opening operators of a locus (the tests' reading).
    #[cfg(test)]
    pub(crate) fn opening(&self, locus: usize) -> [Vec<Word>; 2] {
        Locus::open(
            &self.widths,
            self.declaration.width,
            self.declaration.emission,
            locus,
        )
        .operators
    }

    /// **Deposit a cell's reception** (module header, "The learning"): each digit's covector at
    /// its locus, founding the locus at first arrival. A cell's digits reach distinct loci, so
    /// their deposits touch disjoint state and run together (the hardware law); the receipts are
    /// folded in digit order.
    pub fn deposit(&mut self, reception: Reception) -> Result<(), HnnError> {
        let widths = self.widths;
        let (width, emission, population) = (
            self.declaration.width,
            self.declaration.emission,
            self.declaration.population,
        );
        let mut slots: Vec<Option<&DigitOperand>> = vec![None; self.loci.len()];
        for operand in &reception.digits {
            if slots[operand.locus].replace(operand).is_some() {
                return Err(HnnError::Shape {
                    what: "one digit a locus in a cell",
                    expected: 1,
                    found: 2,
                });
            }
        }
        let receipts: Vec<Result<DepositReceipt, HnnError>> = self
            .loci
            .par_iter_mut()
            .zip(slots.par_iter())
            .enumerate()
            .filter_map(|(index, (locus, slot))| {
                slot.map(|operand| {
                    let founded = locus.get_or_insert_with(|| {
                        Box::new(Locus::open(&widths, width, emission, index))
                    });
                    founded.deposit(operand, &widths, population)
                })
            })
            .collect();
        for receipt in receipts {
            let receipt = receipt?;
            self.report.locus_deposits += 1;
            self.report.refinements += u64::from(receipt.refinements);
            self.report.most_refinements = self.report.most_refinements.max(receipt.refinements);
            self.report.refreshes += u64::from(receipt.refreshed);
            if receipt.certificate > self.report.largest_certificate {
                self.report.largest_certificate = receipt.certificate;
            }
        }
        self.report.deposits += 1;
        Ok(())
    }

    /// **Receive a cell**: read it at the current standing, then deposit it; the executed face it
    /// was scored at.
    pub fn receive(&mut self, class: usize) -> Result<Rat, HnnError> {
        let reception = self.read(class)?;
        let face = reception.face.clone();
        self.deposit(reception)?;
        Ok(face)
    }
}
