//! **The moment tower: modes driven by the encoding, read through rectifying contacts, level over
//! level** (#405, #404).
//!
//! [definition; agent-inferred, October 23] Why it is built. On GSM8K the receiving tree, the
//! passage and the node lock code 1.64 bits a character, and their samples babble. The
//! mathematics thread's field reading (record
//! `2026-10-23_CODE_LENGTH_IS_A_FIELD_ITS_FLOOR_IS_THE_DARK_ENERGY_TERM…`) fits that lens a floor
//! of about 1.2 bits a byte that its learning approaches and cannot pass, and answer prose sits on
//! it after a quarter of the passage. A count of exact contexts cannot generalize from one context
//! to a similar one; sharpening its draw only loops. The keyed modes (`hnn::keyed_modes`), 32
//! diagonal modes read linearly at the cell grain, added nothing: a cell's two bits name no class
//! of the codec, and a linear read takes no conjunction. The mathematics thread's §2 names what a
//! selective state-space model does instead: diagonal transports, with the conjunction taken by a
//! nonlinear read between levels, the tower. This owner is that tower at the codec's own classes.
//!
//! ```text
//! encoding   x⁰_t = E(u_t)                                   the class's face, located
//! level ℓ    h_t = λ ⊙ h_(t−1) + γ ⊙ B x^ℓ_t                 N complex modes: λ the navigator's turn
//!                                                            and boost, B the push (the source moment),
//!                                                            γ = √(1 − |λ|²) its passive scale
//!            r_t = Re(C h_t)                                 the modes' receiving face
//!            r̂_t = r_t / ‖r_t‖_rms                           read as a ratio to its own power
//!            v_t = max(W₁ r̂_t + b₁, 0)                       rectifying contacts (they conduct one way)
//!            x^(ℓ+1)_t = x^ℓ_t + W₂ v_t + b₂
//! face       z_t = U x^L_t + c,   p̂_t(a) = 2^(z_a) / Σ_b 2^(z_b)
//! covector   δz = p̂_t − [· = u_(t+1)]                         the comparison's descent covector, in bits
//! adjoint    G_h(t) = (Cᵀδr)⁻ + conj(λ) G_h(t+1)              the reverse scan inside one section
//!            G_λ = Σ_t conj(h_(t−1)) G_h(t) − (λ/γ) Σ_t Re(conj(G_h(t)) B x_t)
//!            G_B = Σ_t γ G_h(t) x^ℓ_tᵀ
//! deposit    θ ← θ − 2^(−k) m / (√v + 2^(−32))               m, v the covector's first and second moments
//!                                                            over sections (`1 − 2^(−3)`, `1 − 2^(−8)`);
//!                                                            a move in its chart (ln(1 − |λ|), arg λ)
//! certificate the section reread from its opening states under the deposit codes strictly fewer
//!            bits (an exact comparison of the products of its faces); else the step halves, until
//!            it is certified or has released below every family's grain (then nothing is
//!            deposited)
//! ```
//!
//! **Passivity.** With `γ = √(1 − |λ|²)` a mode's state under a unit white push keeps unit
//! power whatever its decay, and under any push `|h| ≤ γ/(1 − |λ|) max|B x| = √((1 + |λ|)/(1 − |λ|))
//! max|B x| ≤ 2^(13/2) max|B x|` inside the margin. Without it, a decay moved toward the margin
//! raised the state's gain as `1/(1 − |λ|)` (measured: five-fold over nine sections, then past the
//! contact's carrier in the next).
//!
//! **The contacts read a ratio.** A contact conducts on the direction of the modes' face, not its
//! power: `r̂ = r / ‖r‖_rms`, with the adjoint `∂r = (∂r̂ − r̂ ⟨r̂, ∂r̂⟩/d) / ‖r‖_rms`. Read on its
//! power, the drive followed the face's scale (some 50 units on the 1,000-problem passage), a step
//! of the contacts moved it by tens of units, and the first level's contacts stopped conducting: 251
//! of 256 changed no weight in the second pass, so no covector reached its modes (measured).
//!
//! **The read's carrier.** The ratio read makes the forward blind to the read's scale `‖C‖`, so
//! the covector of `C` is orthogonal to `C` and every normalized step lengthens it (the step's
//! effective rate on the read falls as `1/‖C‖`). The raw read `r = Re(C h)` is therefore carried in
//! 64 bits before the ratio is taken. Measured: on all 6,726 GSM8K problems the second level's
//! largest `‖r‖_rms` grew from 739 to 1,795 face units over passes 3 and 4, and a held-out read
//! after pass 4 passed the 32-bit carrier (a typed refusal).
//!
//! **What a section holds.** The forward's temporaries of its own cells, for the reverse scan, and
//! the streams' opening states, for the reread. They are released when the section closes (the
//! Athena alpha plan's §A2.4: the reverse pairs the forward prefix operands with the backward
//! covectors, inside the section only). What continues is the material and each stream's mode state.
//!
//! **Exact integers, grains declared.** Every quantity is an integer numerator on a declared dyadic
//! grain: a face (`x`, `r`, `v`, `z`) on `2^(−16)`, the material on `2^(−24)`, the moves `λ` on
//! `2^(−30)` with `|λ| ≤ 1 − 2^(−12)`, a mode's state on `2^(−24)`, a covector on `2^(−24)` in
//! `i64` (a slow mode's covector accumulates over a section's reverse scan; measured, it outgrew
//! `i32` in the second pass on 1,000 GSM8K problems). Each
//! product's remainder below its grain is released to the nearest numerator. A sum is checked
//! against its carrier before it is formed: an `i64` sum widens to `i128` where its terms could
//! reach `2^62`, and a released value that outgrows its carrier is a typed refusal, never a wrap.
//! `2^(z)` is the dyadic square-root navigator's face ([`Exponential`]). Integer sums are
//! associative, so the streams' covectors summed in any order give the same bits.
//!
//! **Modality.** The tower reads classes of a declared alphabet and nothing else. A text, image,
//! acoustic or motor boundary chart supplies the classes (bytes, for text).
//!
//! **Not claimed.** The nonlinearity of the completed model is in the state (a parametron's lock);
//! here it sits between levels, the classical selective model's place. The certified step is
//! descent on its own section, not on the passage.
use crate::hnn::keyed_modes::{dyadic_turn, ln2_face, release, Exponential};
use crate::hnn::passage::log2_face;
use num_bigint::BigUint;
use rayon::prelude::*;

/// A face's grain, `2^(−16)`.
pub const FACE_BITS: u32 = 16;
/// The material's grain, `2^(−24)`.
pub const MATERIAL_BITS: u32 = 24;
/// The moves' grain, `2^(−30)`.
pub const MOVE_BITS: u32 = 30;
/// A mode's state grain, `2^(−24)`.
pub const STATE_BITS: u32 = 24;
/// A covector's grain, `2^(−24)`.
pub const COVECTOR_BITS: u32 = 24;
/// The deposit's covector grain, `2^(−32)`, and its ε.
pub const STEP_BITS: u32 = 32;
/// The moves' margin inside the unit disk, `|λ| ≤ 1 − 2^(−12)`: a mode's memory reaches some
/// 4,096 classes (agent-inferred: past a GSM8K problem of some 520 bytes, inside the passage).
pub const MARGIN: u32 = 12;
/// A code reading's grain, `2^(−20)` bits.
pub const READ_BITS: u32 = 20;
/// The first moment's rate, `2^(−3)`, and the second's, `2^(−8)` (agent-inferred: the classical
/// 0.9 and 0.999 read as dyadic rates; the second at `2^(−8)` so a pass of a few hundred sections
/// renews it).
const FIRST_RATE: u32 = 3;
const SECOND_RATE: u32 = 8;
const UNIT_BITS: u32 = 62;

/// Refusals of the tower's law.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TowerError {
    #[error("tower refused: {0}")]
    Refused(&'static str),
}

type Result<T> = std::result::Result<T, TowerError>;

fn refuse<T>(why: &'static str) -> Result<T> {
    Err(TowerError::Refused(why))
}

fn fit32(x: i128, what: &'static str) -> Result<i32> {
    i32::try_from(x).map_err(|_| TowerError::Refused(what))
}

fn fit64(x: i128) -> Result<i64> {
    i64::try_from(x).map_err(|_| TowerError::Refused("a released value outgrew its 64-bit carrier"))
}

/// [definition; agent-inferred] **The tower's declared law**: an alphabet of `A` classes, a face
/// width `d`, `N` complex modes and `f` rectifying contacts a level, and `L` levels.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TowerDeclaration {
    pub alphabet: usize,
    pub width: usize,
    pub modes: usize,
    pub contacts: usize,
    pub levels: usize,
}

/// Where each family of the material sits in the one vector, and its grain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LevelLayout {
    move_re: usize,
    move_im: usize,
    push_re: usize,
    push_im: usize,
    read_re: usize,
    read_im: usize,
    contact: usize,
    contact_bias: usize,
    ret: usize,
    ret_bias: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Layout {
    encoding: usize,
    levels: Vec<LevelLayout>,
    readout: usize,
    readout_bias: usize,
    len: usize,
    /// `(start, length, the family's grain)`, in order.
    families: Vec<(usize, usize, u32)>,
}

impl Layout {
    fn new(d: &TowerDeclaration) -> Self {
        let (a, w, n, f) = (d.alphabet, d.width, d.modes, d.contacts);
        let mut at = 0usize;
        let mut families = Vec::new();
        let mut take = |len: usize, grain: u32| {
            let start = at;
            at += len;
            families.push((start, len, grain));
            start
        };
        let encoding = take(a * w, FACE_BITS);
        let mut levels = Vec::with_capacity(d.levels);
        for _ in 0..d.levels {
            levels.push(LevelLayout {
                move_re: take(n, MOVE_BITS),
                move_im: take(n, MOVE_BITS),
                push_re: take(n * w, MATERIAL_BITS),
                push_im: take(n * w, MATERIAL_BITS),
                read_re: take(w * n, MATERIAL_BITS),
                read_im: take(w * n, MATERIAL_BITS),
                contact: take(f * w, MATERIAL_BITS),
                contact_bias: take(f, FACE_BITS),
                ret: take(w * f, MATERIAL_BITS),
                ret_bias: take(w, FACE_BITS),
            });
        }
        let readout = take(a * w, MATERIAL_BITS);
        let readout_bias = take(a, FACE_BITS);
        Self { encoding, levels, readout, readout_bias, len: at, families }
    }
}

/// [definition; agent-inferred] **The located material**: every family as one vector of integer
/// numerators on its grain (`Layout`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tower {
    pub declaration: TowerDeclaration,
    pub theta: Vec<i32>,
    layout: Layout,
    exponential: Exponential,
}

/// [definition; agent-inferred] **A stream's continuing state**: each level's modes on
/// `2^(−24)`, `(re, im)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TowerState {
    pub modes: Vec<Vec<(i64, i64)>>,
}

/// One cell's face: each class's mass `2^(z_a − z_max)` on `2^(−62)`, and their sum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TowerFace {
    pub masses: Vec<u128>,
    pub total: u128,
}

impl TowerFace {
    /// The class's code, `−log₂ p̂(a)`, on `2^(−20)` bits.
    pub fn code(&self, class: usize) -> i64 {
        let p = (self.masses[class] << UNIT_BITS) / self.total;
        -(log2_face(p.max(1), READ_BITS) as i64)
    }

    /// The face read at one base-four cell of a byte (the exterior byte chart: four cells, high
    /// first): the masses of the bytes whose first `phase` cells are `prefix`, split by the cell at
    /// `phase`. Exact sums of the byte masses; their total is the prefix's mass.
    pub fn cell_masses(&self, prefix: usize, phase: usize) -> Result<[u128; 4]> {
        if self.masses.len() != 256 || phase > 3 || prefix >> (2 * phase) != 0 {
            return refuse("a cell face needs a byte face and a prefix inside its phase");
        }
        let low = 6 - 2 * phase as u32;
        let mut cells = [0u128; 4];
        for d in 0..4 {
            let first = ((prefix << 2) | d) << low;
            cells[d] = self.masses[first..first + (1usize << low)].iter().sum();
        }
        Ok(cells)
    }
}

/// `max |w|` over a family.
fn reach(w: &[i32]) -> u64 {
    w.iter().map(|v| v.unsigned_abs() as u64).max().unwrap_or(0)
}

/// `out[o] = release(Σ_i w[o·cols + i] x[i] + bias[o] · 2^bias_shift, shift)`, in `i64` where the
/// terms' bound allows and in `i128` otherwise.
fn affine(w: &[i32], wmax: u64, cols: usize, x: &[i32], bias: Option<&[i32]>, bias_shift: u32, shift: u32, out: &mut [i64]) -> Result<()> {
    let xmax = reach(x);
    let narrow = (wmax as u128) * (xmax as u128) * (cols as u128 + 1) < (1u128 << 62);
    for (o, slot) in out.iter_mut().enumerate() {
        let row = &w[o * cols..(o + 1) * cols];
        let mut sum: i128 = if narrow {
            row.iter().zip(x).map(|(a, b)| *a as i64 * *b as i64).sum::<i64>() as i128
        } else {
            row.iter().zip(x).map(|(a, b)| *a as i128 * *b as i128).sum::<i128>()
        };
        if let Some(b) = bias {
            sum += (b[o] as i128) << bias_shift;
        }
        *slot = fit64(release(sum, shift))?;
    }
    Ok(())
}

/// `out[i] = release(Σ_o w[o·cols + i] y[o], shift)`: the transposed read, `y` a covector (carried
/// in `i64`: the reverse scan accumulates a slow mode's covector over the section).
fn transposed(w: &[i32], wmax: u64, cols: usize, y: &[i64], shift: u32, out: &mut [i64]) -> Result<()> {
    let ymax = reach64(y);
    let rows = y.len();
    let narrow = (wmax as u128) * (ymax as u128) * (rows as u128 + 1) < (1u128 << 62);
    if narrow {
        let mut acc = vec![0i64; cols];
        for (o, &yo) in y.iter().enumerate() {
            if yo == 0 {
                continue;
            }
            let row = &w[o * cols..(o + 1) * cols];
            for (a, &wv) in acc.iter_mut().zip(row) {
                *a += wv as i64 * yo;
            }
        }
        for (slot, a) in out.iter_mut().zip(acc) {
            *slot = fit64(release(a as i128, shift))?;
        }
    } else {
        let mut acc = vec![0i128; cols];
        for (o, &yo) in y.iter().enumerate() {
            let row = &w[o * cols..(o + 1) * cols];
            for (a, &wv) in acc.iter_mut().zip(row) {
                *a += wv as i128 * yo as i128;
            }
        }
        for (slot, a) in out.iter_mut().zip(acc) {
            *slot = fit64(release(a, shift))?;
        }
    }
    Ok(())
}

/// `g[o·cols + i] += y[o] x[i]`: a covector's outer product with a face, at their summed grain.
fn outer(g: &mut [i128], cols: usize, y: &[i64], x: &[i32]) {
    let narrow = (reach64(y) as u128) * (reach(x) as u128) < (1u128 << 62);
    for (o, &yo) in y.iter().enumerate() {
        if yo == 0 {
            continue;
        }
        let row = &mut g[o * cols..(o + 1) * cols];
        if narrow {
            for (a, &xv) in row.iter_mut().zip(x) {
                *a += (yo * xv as i64) as i128;
            }
        } else {
            for (a, &xv) in row.iter_mut().zip(x) {
                *a += yo as i128 * xv as i128;
            }
        }
    }
}

/// `max |y|` over a covector.
fn reach64(y: &[i64]) -> u64 {
    y.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0)
}

fn to32(v: &[i64], what: &'static str) -> Result<Vec<i32>> {
    v.iter().map(|&x| fit32(x as i128, what)).collect()
}

/// One level's forward temporaries at one cell.
#[derive(Clone, Debug, Default)]
struct LevelCell {
    input: Vec<i32>,
    /// `B x` before the mode's `γ`, on the state's grain.
    push: Vec<(i64, i64)>,
    state: Vec<(i64, i64)>,
    state_face: Vec<i32>,
    /// `r̂`, the contacts' input, on `2^(−16)`.
    read: Vec<i32>,
    /// `‖r‖_rms` on `2^(−16)` (zero when the face is zero).
    read_scale: i128,
    drive: Vec<i32>,
    conduct: Vec<i32>,
}

/// One cell's forward temporaries.
#[derive(Clone, Debug, Default)]
struct Cell {
    levels: Vec<LevelCell>,
    top: Vec<i32>,
    face: TowerFace,
}

impl Default for TowerFace {
    fn default() -> Self {
        Self { masses: Vec::new(), total: 1 }
    }
}

/// The reaches of every family, read once a section.
#[derive(Clone, Debug)]
struct Reaches {
    levels: Vec<[u64; 6]>,
    readout: u64,
    /// Each level's `γ_k = √(1 − |λ_k|²)` on `2^(−30)`.
    gammas: Vec<Vec<i128>>,
}

/// `x / k` to the nearest integer, half away from zero.
fn div_nearest(x: i128, k: i128) -> i128 {
    if x >= 0 { (x + k / 2) / k } else { -((-x + k / 2) / k) }
}

/// `e^(a + i b)` on `2^(−30)`, `a`, `b` on `2^(−30)`: the series summed until its term releases
/// to zero at the grain.
fn exp_series(a: i128, b: i128) -> (i128, i128) {
    let mut term = (1i128 << MOVE_BITS, 0i128);
    let mut sum = term;
    let mut k = 1i128;
    loop {
        let re = release(term.0 * a - term.1 * b, MOVE_BITS);
        let im = release(term.0 * b + term.1 * a, MOVE_BITS);
        term = (div_nearest(re, k), div_nearest(im, k));
        if term == (0, 0) {
            return sum;
        }
        sum = (sum.0 + term.0, sum.1 + term.1);
        k += 1;
    }
}

/// `r̂ = r / ‖r‖_rms` on `2^(−16)` and `‖r‖_rms` on `2^(−16)`, `r` on `2^(−16)`; a zero face reads
/// as zero.
fn ratio_to_power(r: &[i64]) -> Result<(Vec<i32>, i128)> {
    let power: i128 = r.iter().map(|&v| v as i128 * v as i128).sum();
    let scale = ((power / r.len() as i128) as u128).isqrt() as i128;
    if scale == 0 {
        return Ok((vec![0; r.len()], 0));
    }
    let read = r.iter().map(|&v| fit32(div_nearest((v as i128) << FACE_BITS, scale), "a read's ratio outgrew its 32-bit carrier")).collect::<Result<_>>()?;
    Ok((read, scale))
}

/// The adjoint of [`ratio_to_power`]: `∂r = (∂r̂ − r̂ ⟨r̂, ∂r̂⟩/d) / ‖r‖_rms`, covectors on
/// `2^(−24)`.
fn ratio_adjoint(read: &[i32], scale: i128, cov: &[i64]) -> Result<Vec<i64>> {
    if scale == 0 {
        return Ok(vec![0; cov.len()]);
    }
    let dot: i128 = read.iter().zip(cov).map(|(&a, &b)| a as i128 * b as i128).sum(); // 2^(−40)
    let mean = div_nearest(dot, read.len() as i128);
    read.iter()
        .zip(cov)
        .map(|(&a, &b)| fit64(div_nearest((b as i128 - release(mean * a as i128, 2 * FACE_BITS)) << FACE_BITS, scale)))
        .collect()
}

/// `|λ|` on `2^(−30)` and `γ = √(1 − |λ|²)` on `2^(−30)`.
fn modulus_and_gamma(re: i128, im: i128) -> (i128, i128) {
    let n = re * re + im * im;
    let modulus = (n as u128).isqrt() as i128;
    let gamma = (((1i128 << (2 * MOVE_BITS)) - n).max(0) as u128).isqrt() as i128;
    (modulus, gamma)
}

impl Tower {
    /// **The founding configuration** (agent-inferred, October 23), read from a declared exterior
    /// key stream (`keys`, consumed four bytes a key, each a signed 32-bit integer read as a
    /// uniform draw on `[−1, 1)`): the encoding uniform on `[−1, 1)`; each level's modes on a
    /// scale ladder `ρ = 1 − 2^(−s)` for `s = 1..=S` and a turn ladder `j·π/J`, `J = N/S` (the
    /// odometer's mixed radix and a closing ring's characters), the push by `1/√d` (the step
    /// scales it by the mode's `γ`, so a mode's state opens at the face's scale), the read by `1/√N`, the contacts
    /// by `√(6/d)` (a rectifier passes half its drive); the return and the readout at zero, so the
    /// tower opens on the flat face (birth at zero) and each level on the identity.
    pub fn found(declaration: TowerDeclaration, keys: &[u8]) -> Result<Self> {
        let d = declaration;
        if d.alphabet < 2 || d.width == 0 || d.modes == 0 || d.contacts == 0 || d.levels == 0 {
            return refuse("a tower needs two classes and a nonempty width, bank, contacts and levels");
        }
        let layout = Layout::new(&d);
        let mut theta = vec![0i32; layout.len];
        let mut cursor = 0usize;
        let mut draw = || -> Result<i64> {
            let word = keys.get(cursor..cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the founding reads"))?;
            cursor += 4;
            Ok(i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i64)
        };
        // A uniform draw on [−r, r) with r = num/den on the grain 2^(−bits).
        let mut uniform = |slice: &mut [i32], num: u128, den: u128, bits: u32| -> Result<()> {
            for v in slice.iter_mut() {
                let k = draw()? as i128; // on 2^(−31), in [−1, 1)
                let scaled = (k * ((num << bits) / den) as i128) >> 31;
                *v = fit32(scaled, "a founded value outgrew its 32-bit carrier")?;
            }
            Ok(())
        };
        let e = layout.encoding;
        uniform(&mut theta[e..e + d.alphabet * d.width], 1, 1, FACE_BITS)?;
        let turns = turn_ladder(d.modes);
        let sqrt_width = (d.width as u128).isqrt().max(1);
        for lv in &layout.levels {
            for k in 0..d.modes {
                let s = (k / turns) as u32 + 1;
                let j = (k % turns) as u64;
                let rho = (1i128 << MOVE_BITS) - (1i128 << (MOVE_BITS - s.min(MARGIN)));
                // The turn by j·π/turns: turns is a power of two by the ladder's declaration.
                let n = turns.trailing_zeros();
                let rot = dyadic_turn(j, n, MOVE_BITS);
                let re = release(rot.re * rho, MOVE_BITS);
                let im = release(rot.im * rho, MOVE_BITS);
                theta[lv.move_re + k] = fit32(re, "a founded move outgrew its 32-bit carrier")?;
                theta[lv.move_im + k] = fit32(im, "a founded move outgrew its 32-bit carrier")?;
                // The push at 1/√d; the step scales it by the mode's γ = √(1 − |λ|²).
                let row = lv.push_re + k * d.width;
                uniform(&mut theta[row..row + d.width], 1, sqrt_width, MATERIAL_BITS)?;
                let row = lv.push_im + k * d.width;
                uniform(&mut theta[row..row + d.width], 1, sqrt_width, MATERIAL_BITS)?;
            }
            let sqrt_modes = (d.modes as u128).isqrt().max(1);
            uniform(&mut theta[lv.read_re..lv.read_re + d.width * d.modes], 1, sqrt_modes, MATERIAL_BITS)?;
            uniform(&mut theta[lv.read_im..lv.read_im + d.width * d.modes], 1, sqrt_modes, MATERIAL_BITS)?;
            // √(6/d) as (√6·2^16)/(√d·2^16), each square root on 2^(−16).
            let six = (6u128 << 32).isqrt();
            let dd = ((d.width as u128) << 32).isqrt();
            uniform(&mut theta[lv.contact..lv.contact + d.contacts * d.width], six, dd, MATERIAL_BITS)?;
        }
        Ok(Self { declaration: d, theta, layout, exponential: Exponential::new(FACE_BITS) })
    }

    /// The rested state: every mode at zero.
    pub fn rest(&self) -> TowerState {
        TowerState { modes: vec![vec![(0, 0); self.declaration.modes]; self.declaration.levels] }
    }

    fn reaches(&self) -> Reaches {
        let t = &self.theta;
        let d = &self.declaration;
        let levels = self
            .layout
            .levels
            .iter()
            .map(|lv| {
                [
                    reach(&t[lv.push_re..lv.push_re + d.modes * d.width]),
                    reach(&t[lv.push_im..lv.push_im + d.modes * d.width]),
                    reach(&t[lv.read_re..lv.read_re + d.width * d.modes]),
                    reach(&t[lv.read_im..lv.read_im + d.width * d.modes]),
                    reach(&t[lv.contact..lv.contact + d.contacts * d.width]),
                    reach(&t[lv.ret..lv.ret + d.width * d.contacts]),
                ]
            })
            .collect();
        let gammas = self
            .layout
            .levels
            .iter()
            .map(|lv| (0..d.modes).map(|k| modulus_and_gamma(t[lv.move_re + k] as i128, t[lv.move_im + k] as i128).1).collect())
            .collect();
        Reaches { levels, readout: reach(&t[self.layout.readout..self.layout.readout + d.alphabet * d.width]), gammas }
    }

    /// One cell forward: the class `u` arrives, every level's modes move, and the face of the next
    /// class is read. The temporaries are returned for the reverse scan.
    fn step(&self, state: &mut TowerState, u: usize, reaches: &Reaches) -> Result<Cell> {
        let d = &self.declaration;
        let (w, n, f) = (d.width, d.modes, d.contacts);
        if u >= d.alphabet {
            return refuse("a class outside the declared alphabet");
        }
        let t = &self.theta;
        let e = self.layout.encoding + u * w;
        let mut x: Vec<i32> = t[e..e + w].to_vec();
        let mut levels = Vec::with_capacity(d.levels);
        let mut buf = vec![0i64; w.max(n).max(f)];
        for (l, lv) in self.layout.levels.iter().enumerate() {
            let r = &reaches.levels[l];
            // The push, on 2^(−40) released to the state's 2^(−24).
            let mut push_re = vec![0i64; n];
            let mut push_im = vec![0i64; n];
            affine(&t[lv.push_re..lv.push_re + n * w], r[0], w, &x, None, 0, MATERIAL_BITS + FACE_BITS - STATE_BITS, &mut push_re)?;
            affine(&t[lv.push_im..lv.push_im + n * w], r[1], w, &x, None, 0, MATERIAL_BITS + FACE_BITS - STATE_BITS, &mut push_im)?;
            let modes = &mut state.modes[l];
            let gammas = &reaches.gammas[l];
            let mut face = vec![0i32; 2 * n];
            for k in 0..n {
                let (hr, hi) = modes[k];
                let (lr, li) = (t[lv.move_re + k] as i128, t[lv.move_im + k] as i128);
                let pr = release(gammas[k] * push_re[k] as i128, MOVE_BITS);
                let pi = release(gammas[k] * push_im[k] as i128, MOVE_BITS);
                let nr = fit64(release(lr * hr as i128 - li * hi as i128, MOVE_BITS) + pr)?;
                let ni = fit64(release(lr * hi as i128 + li * hr as i128, MOVE_BITS) + pi)?;
                modes[k] = (nr, ni);
                face[k] = fit32(release(nr as i128, STATE_BITS - FACE_BITS), "a mode's face outgrew its 32-bit carrier")?;
                face[n + k] = fit32(release(ni as i128, STATE_BITS - FACE_BITS), "a mode's face outgrew its 32-bit carrier")?;
            }
            // The read Re(C h) = C_re h_re − C_im h_im, on 2^(−40) released to 2^(−16).
            let mut read_a = vec![0i64; w];
            let mut read_b = vec![0i64; w];
            affine(&t[lv.read_re..lv.read_re + w * n], r[2], n, &face[..n], None, 0, 0, &mut read_a)?;
            affine(&t[lv.read_im..lv.read_im + w * n], r[3], n, &face[n..], None, 0, 0, &mut read_b)?;
            // The raw read is carried in 64 bits: only its direction reaches the contacts, so its
            // scale is a gauge, and the normalized step lets it grow (see "The read's carrier").
            let raw: Vec<i64> = read_a
                .iter()
                .zip(&read_b)
                .map(|(a, b)| fit64(release(*a as i128 - *b as i128, MATERIAL_BITS)))
                .collect::<Result<_>>()?;
            let (read, read_scale) = ratio_to_power(&raw)?;
            let drive_buf = &mut buf[..f];
            affine(&t[lv.contact..lv.contact + f * w], r[4], w, &read, Some(&t[lv.contact_bias..lv.contact_bias + f]), MATERIAL_BITS, MATERIAL_BITS, drive_buf)?;
            let drive = to32(drive_buf, "a contact drive outgrew its 32-bit carrier")?;
            let conduct: Vec<i32> = drive.iter().map(|&a| a.max(0)).collect();
            let mut ret = vec![0i64; w];
            affine(&t[lv.ret..lv.ret + w * f], r[5], f, &conduct, Some(&t[lv.ret_bias..lv.ret_bias + w]), MATERIAL_BITS, MATERIAL_BITS, &mut ret)?;
            let next: Vec<i32> = x.iter().zip(&ret).map(|(a, b)| fit32(*a as i128 + *b as i128, "the residual stream outgrew its 32-bit carrier")).collect::<Result<_>>()?;
            let state_copy = modes.clone();
            let push = push_re.into_iter().zip(push_im).collect();
            levels.push(LevelCell { input: std::mem::replace(&mut x, next), push, state: state_copy, state_face: face, read, read_scale, drive, conduct });
        }
        let a = d.alphabet;
        let mut z = vec![0i64; a];
        let ro = self.layout.readout;
        let rb = self.layout.readout_bias;
        affine(&t[ro..ro + a * w], reaches.readout, w, &x, Some(&t[rb..rb + a]), MATERIAL_BITS, MATERIAL_BITS, &mut z)?;
        let zmax = *z.iter().max().expect("a nonempty alphabet");
        let masses: Vec<u128> = z.iter().map(|&v| self.exponential.below_one((v - zmax) as i128)).collect();
        let total = masses.iter().sum();
        Ok(Cell { levels, top: x, face: TowerFace { masses, total } })
    }

    /// The face of the next class after `u` arrives, and the state moved.
    pub fn advance(&self, state: &mut TowerState, u: usize) -> Result<TowerFace> {
        let reaches = self.reaches();
        Ok(self.step(state, u, &reaches)?.face)
    }

    /// A section's forward: `classes[0..T]` arrive, `classes[1..=T]` are coded.
    fn forward(&self, state: &mut TowerState, classes: &[usize], reaches: &Reaches) -> Result<Vec<Cell>> {
        classes[..classes.len() - 1].iter().map(|&u| self.step(state, u, reaches)).collect()
    }

    /// The reverse scan of one stream's section: the covector of every family, on its natural
    /// grain (material `2^(−40)`, faces and biases `2^(−24)`, moves `2^(−48)`).
    fn reverse(&self, opening: &TowerState, cells: &[Cell], classes: &[usize]) -> Result<Vec<i128>> {
        let d = &self.declaration;
        let (w, n, f, a) = (d.width, d.modes, d.contacts, d.alphabet);
        let t = &self.theta;
        let reaches = self.reaches();
        let mut g = vec![0i128; self.layout.len];
        let cells_n = cells.len();
        // The face's covector and the top's.
        let mut dx: Vec<Vec<i64>> = Vec::with_capacity(cells_n);
        let ro = self.layout.readout;
        let rb = self.layout.readout_bias;
        for (i, cell) in cells.iter().enumerate() {
            let target = classes[i + 1];
            let face = &cell.face;
            let dz: Vec<i64> = (0..a)
                .map(|c| {
                    let p = ((face.masses[c] << COVECTOR_BITS) + face.total / 2) / face.total;
                    p as i64 - if c == target { 1i64 << COVECTOR_BITS } else { 0 }
                })
                .collect();
            outer(&mut g[ro..ro + a * w], w, &dz, &cell.top);
            for (slot, &v) in g[rb..rb + a].iter_mut().zip(&dz) {
                *slot += v as i128;
            }
            let mut back = vec![0i64; w];
            transposed(&t[ro..ro + a * w], reaches.readout, w, &dz, MATERIAL_BITS, &mut back)?;
            dx.push(back);
        }
        for l in (0..d.levels).rev() {
            let lv = self.layout.levels[l];
            let r = &reaches.levels[l];
            let mut read_cov: Vec<Vec<(i64, i64)>> = Vec::with_capacity(cells_n);
            for (i, cell) in cells.iter().enumerate() {
                let lc = &cell.levels[l];
                let dy = &dx[i];
                outer(&mut g[lv.ret..lv.ret + w * f], f, dy, &lc.conduct);
                for (slot, &v) in g[lv.ret_bias..lv.ret_bias + w].iter_mut().zip(dy) {
                    *slot += v as i128;
                }
                let mut dv = vec![0i64; f];
                transposed(&t[lv.ret..lv.ret + w * f], r[5], f, dy, MATERIAL_BITS, &mut dv)?;
                let da: Vec<i64> = dv.iter().zip(&lc.drive).map(|(&v, &drive)| if drive > 0 { v } else { 0 }).collect();
                outer(&mut g[lv.contact..lv.contact + f * w], w, &da, &lc.read);
                for (slot, &v) in g[lv.contact_bias..lv.contact_bias + f].iter_mut().zip(&da) {
                    *slot += v as i128;
                }
                let mut dr = vec![0i64; w];
                transposed(&t[lv.contact..lv.contact + f * w], r[4], w, &da, MATERIAL_BITS, &mut dr)?;
                let dread = ratio_adjoint(&lc.read, lc.read_scale, &dr)?;
                outer(&mut g[lv.read_re..lv.read_re + w * n], n, &dread, &lc.state_face[..n]);
                let neg: Vec<i64> = dread.iter().map(|v| -v).collect();
                outer(&mut g[lv.read_im..lv.read_im + w * n], n, &neg, &lc.state_face[n..]);
                let mut hre = vec![0i64; n];
                let mut him = vec![0i64; n];
                transposed(&t[lv.read_re..lv.read_re + w * n], r[2], n, &dread, MATERIAL_BITS, &mut hre)?;
                transposed(&t[lv.read_im..lv.read_im + w * n], r[3], n, &neg, MATERIAL_BITS, &mut him)?;
                read_cov.push(hre.into_iter().zip(him).collect());
            }
            // The reverse scan of the modes: G_h(t) = read covector + conj(λ) G_h(t+1).
            let mut carried: Vec<(i64, i64)> = vec![(0, 0); n];
            let mut gh_all: Vec<Vec<(i64, i64)>> = vec![Vec::new(); cells_n];
            for i in (0..cells_n).rev() {
                let mut gh = Vec::with_capacity(n);
                for k in 0..n {
                    let (lr, li) = (t[lv.move_re + k] as i128, t[lv.move_im + k] as i128);
                    let (cr, ci) = (carried[k].0 as i128, carried[k].1 as i128);
                    let re = fit64(read_cov[i][k].0 as i128 + release(lr * cr + li * ci, MOVE_BITS))?;
                    let im = fit64(read_cov[i][k].1 as i128 + release(lr * ci - li * cr, MOVE_BITS))?;
                    gh.push((re, im));
                }
                carried = gh.clone();
                gh_all[i] = gh;
            }
            let gammas = &reaches.gammas[l];
            // S_k = Σ_t Re(conj(G_h) B x): the covector of the mode's γ, on 2^(−48).
            let mut through_gamma = vec![0i128; n];
            for (i, cell) in cells.iter().enumerate() {
                let lc = &cell.levels[l];
                let previous: &[(i64, i64)] = if i == 0 { &opening.modes[l] } else { &cells[i - 1].levels[l].state };
                let gh = &gh_all[i];
                for k in 0..n {
                    let (hr, hi) = (previous[k].0 as i128, previous[k].1 as i128);
                    let (gr, gi) = (gh[k].0 as i128, gh[k].1 as i128);
                    g[lv.move_re + k] += hr * gr + hi * gi;
                    g[lv.move_im + k] += hr * gi - hi * gr;
                    through_gamma[k] += gr * lc.push[k].0 as i128 + gi * lc.push[k].1 as i128;
                }
                let gre: Vec<i64> = gh.iter().zip(gammas).map(|(v, &c)| fit64(release(c * v.0 as i128, MOVE_BITS))).collect::<Result<_>>()?;
                let gim: Vec<i64> = gh.iter().zip(gammas).map(|(v, &c)| fit64(release(c * v.1 as i128, MOVE_BITS))).collect::<Result<_>>()?;
                outer(&mut g[lv.push_re..lv.push_re + n * w], w, &gre, &lc.input);
                outer(&mut g[lv.push_im..lv.push_im + n * w], w, &gim, &lc.input);
                let mut back_re = vec![0i64; w];
                let mut back_im = vec![0i64; w];
                transposed(&t[lv.push_re..lv.push_re + n * w], r[0], w, &gre, MATERIAL_BITS, &mut back_re)?;
                transposed(&t[lv.push_im..lv.push_im + n * w], r[1], w, &gim, MATERIAL_BITS, &mut back_im)?;
                let next: Vec<i64> = dx[i]
                    .iter()
                    .zip(back_re.iter().zip(&back_im))
                    .map(|(v, (a, b))| fit64(*v as i128 + *a as i128 + *b as i128))
                    .collect::<Result<_>>()?;
                dx[i] = next;
            }
            // ∂γ/∂λ = −λ/γ.
            for k in 0..n {
                let (lr, li) = (t[lv.move_re + k] as i128, t[lv.move_im + k] as i128);
                g[lv.move_re + k] -= div_nearest(lr * through_gamma[k], gammas[k]);
                g[lv.move_im + k] -= div_nearest(li * through_gamma[k], gammas[k]);
            }
        }
        let e = self.layout.encoding;
        for (i, dxi) in dx.iter().enumerate() {
            let u = classes[i];
            for (slot, &v) in g[e + u * w..e + (u + 1) * w].iter_mut().zip(dxi) {
                *slot += v as i128;
            }
        }
        Ok(g)
    }

    /// The covector on the deposit's grain `2^(−32)` from each family's natural grain.
    fn to_step_grain(&self, g: &mut [i128]) {
        for lv in &self.layout.levels {
            for k in [lv.move_re, lv.move_im] {
                for v in &mut g[k..k + self.declaration.modes] {
                    *v = release(*v, 2 * COVECTOR_BITS - STEP_BITS);
                }
            }
        }
        for &(start, len, grain) in &self.layout.families {
            if grain == MOVE_BITS {
                continue;
            }
            for v in &mut g[start..start + len] {
                *v = if grain == MATERIAL_BITS {
                    release(*v, COVECTOR_BITS + FACE_BITS - STEP_BITS)
                } else {
                    *v << (STEP_BITS - COVECTOR_BITS)
                };
            }
        }
    }

    /// The material as text.
    pub fn to_text(&self) -> String {
        let d = &self.declaration;
        let mut s = format!("moment-tower-v1 {} {} {} {} {}\n", d.alphabet, d.width, d.modes, d.contacts, d.levels);
        s.push_str(&self.theta.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" "));
        s.push('\n');
        s
    }

    /// The material from its text, refused unless it restores whole.
    pub fn from_text(text: &str) -> Result<Self> {
        let mut lines = text.lines();
        let head: Vec<&str> = lines.next().unwrap_or("").split(' ').collect();
        if head.len() != 6 || head[0] != "moment-tower-v1" {
            return refuse("not a moment tower's text");
        }
        let num = |s: &str| s.parse::<usize>().map_err(|_| TowerError::Refused("a declaration that is not a count"));
        let declaration = TowerDeclaration { alphabet: num(head[1])?, width: num(head[2])?, modes: num(head[3])?, contacts: num(head[4])?, levels: num(head[5])? };
        let layout = Layout::new(&declaration);
        let theta: Vec<i32> = lines
            .next()
            .unwrap_or("")
            .split(' ')
            .map(|s| s.parse::<i32>().map_err(|_| TowerError::Refused("material that is not an integer")))
            .collect::<Result<_>>()?;
        if theta.len() != layout.len || lines.next().is_some() {
            return refuse("material of the wrong extent");
        }
        Ok(Self { declaration, theta, layout, exponential: Exponential::new(FACE_BITS) })
    }
}

/// The turn ladder's count `J` for `N` modes: the largest power of two up to eight that divides
/// `N` (agent-inferred: eight turns of the half circle when the bank allows); the scale ladder has
/// `N/J` rungs.
fn turn_ladder(modes: usize) -> usize {
    let mut turns = 1usize;
    while turns < 8 && modes % (turns * 2) == 0 {
        turns *= 2;
    }
    turns
}

/// The exact comparison of two sections' codes: does `new` code strictly fewer bits than `old`?
/// `Π p_new > Π p_old`, over the products of their faces' numerators and denominators.
fn fewer_bits(old: &[(u128, u128)], new: &[(u128, u128)]) -> bool {
    fn product(v: &[u128]) -> BigUint {
        match v.len() {
            0 => BigUint::from(1u8),
            1 => BigUint::from(v[0]),
            n => product(&v[..n / 2]) * product(&v[n / 2..]),
        }
    }
    let (om, ot): (Vec<u128>, Vec<u128>) = old.iter().cloned().unzip();
    let (nm, nt): (Vec<u128>, Vec<u128>) = new.iter().cloned().unzip();
    product(&nm) * product(&ot) > product(&om) * product(&nt)
}

/// [definition; agent-inferred] **The learner**: the tower, the covector's moments and the
/// deposits' receipts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TowerLearner {
    pub tower: Tower,
    first: Vec<i128>,
    second: Vec<i128>,
    opened: bool,
    /// The step's rate, `2^(−k)`.
    pub rate_bits: u32,
    /// The last section's swell per level, on `2^(−16)`: `max |x|`, `max |h|` (its face), `max
    /// ‖r‖_rms`, `max |W₁ r̂ + b₁|` over every stream's cells. A reading for the receipt, not material.
    pub swell: Vec<[u64; 4]>,
}

/// A section's receipt: its code before and after (on `2^(−20)` bits), the halvings the
/// certificate took, and whether a deposit was admitted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SectionReceipt {
    pub cells: usize,
    pub code_before: i64,
    pub code_after: i64,
    pub halvings: u32,
    pub deposited: bool,
}

impl TowerLearner {
    pub fn new(tower: Tower, rate_bits: u32) -> Self {
        let len = tower.theta.len();
        Self { tower, first: vec![0; len], second: vec![0; len], opened: false, rate_bits, swell: Vec::new() }
    }

    /// The swell and the reaches as one line: per level `x h r a` (faces, `2^(−16)`) and `push read
    /// contact return` (material, `2^(−24)`), then the readout's reach and `max |λ|` on `2^(−30)`.
    pub fn swell_line(&self) -> String {
        let reaches = self.tower.reaches();
        let mut line = String::new();
        for (l, r) in reaches.levels.iter().enumerate() {
            let s = self.swell.get(l).copied().unwrap_or([0; 4]);
            let lv = self.tower.layout.levels[l];
            let lambda = (0..self.tower.declaration.modes)
                .map(|k| {
                    let (re, im) = (self.tower.theta[lv.move_re + k] as i128, self.tower.theta[lv.move_im + k] as i128);
                    ((re * re + im * im) as u128).isqrt()
                })
                .max()
                .unwrap_or(0);
            line.push_str(&format!(
                "L{l} x={} h={} r={} a={} push={} read={} contact={} return={} lambda={} ",
                s[0], s[1], s[2], s[3], r[0].max(r[1]), r[2].max(r[3]), r[4], r[5], lambda
            ));
        }
        line.push_str(&format!("readout={}", reaches.readout));
        line
    }

    /// One section over parallel streams: each stream's classes `[0..=T]` from its carried state.
    /// The streams' covectors are summed, the moments move, the step is certified by the reread,
    /// and each stream's state continues under the material the section ends with.
    pub fn section(&mut self, states: &mut [TowerState], classes: &[&[usize]]) -> Result<SectionReceipt> {
        if states.len() != classes.len() || classes.iter().any(|c| c.len() < 2) {
            return refuse("a section needs one carried state and two classes a stream");
        }
        let tower = &self.tower;
        let reaches = tower.reaches();
        let opening: Vec<TowerState> = states.to_vec();
        let forwards: Vec<(Vec<Cell>, TowerState)> = opening
            .par_iter()
            .zip(classes.par_iter())
            .map(|(open, c)| {
                let mut s = open.clone();
                let cells = tower.forward(&mut s, c, &reaches)?;
                Ok((cells, s))
            })
            .collect::<Result<_>>()?;
        self.swell = (0..tower.declaration.levels)
            .map(|l| {
                let mut m = [0u64; 4];
                for lc in forwards.iter().flat_map(|(cells, _)| cells.iter().map(move |c| &c.levels[l])) {
                    m[0] = m[0].max(reach(&lc.input));
                    m[1] = m[1].max(reach(&lc.state_face));
                    m[2] = m[2].max(lc.read_scale as u64);
                    m[3] = m[3].max(reach(&lc.drive));
                }
                m
            })
            .collect();
        let faces_old: Vec<(u128, u128)> = forwards
            .iter()
            .zip(classes)
            .flat_map(|((cells, _), c)| cells.iter().enumerate().map(move |(i, cell)| (cell.face.masses[c[i + 1]], cell.face.total)))
            .collect();
        let code_before: i64 = forwards
            .iter()
            .zip(classes)
            .map(|((cells, _), c)| cells.iter().enumerate().map(|(i, cell)| cell.face.code(c[i + 1])).sum::<i64>())
            .sum();
        let gradients: Vec<Vec<i128>> = opening
            .par_iter()
            .zip(forwards.par_iter())
            .zip(classes.par_iter())
            .map(|((open, (cells, _)), c)| tower.reverse(open, cells, c))
            .collect::<Result<_>>()?;
        let mut g = vec![0i128; tower.theta.len()];
        for gs in &gradients {
            for (a, b) in g.iter_mut().zip(gs) {
                *a += *b;
            }
        }
        tower.to_step_grain(&mut g);
        tower.to_move_chart(&mut g);
        // The moments.
        if !self.opened {
            self.first.clone_from(&g);
            self.second = g
                .iter()
                .map(|v| v.checked_mul(*v).ok_or(TowerError::Refused("a covector's square outgrew its 128-bit carrier")))
                .collect::<Result<_>>()?;
            self.opened = true;
        } else {
            for ((m, v), gv) in self.first.iter_mut().zip(self.second.iter_mut()).zip(&g) {
                let square = gv.checked_mul(*gv).ok_or(TowerError::Refused("a covector's square outgrew its 128-bit carrier"))?;
                *m += release(*gv - *m, FIRST_RATE);
                *v += release(square - *v, SECOND_RATE);
            }
        }
        // The proposed step on each family's grain.
        let mut step = vec![0i128; g.len()];
        for &(start, len, grain) in &self.tower.layout.families {
            for i in start..start + len {
                let root = (self.second[i].max(0) as u128).isqrt() as i128 + 1;
                let num = self.first[i] << grain;
                let q = (num >> self.rate_bits) / root;
                step[i] = q;
            }
        }
        // The certificate halves a refused step until it is certified or has released below every
        // family's grain; then the section deposits nothing.
        let mut halvings = 0u32;
        loop {
            let mut candidate = self.tower.clone();
            let mut moved = false;
            for &(start, len, grain) in &self.tower.layout.families {
                if grain == MOVE_BITS {
                    continue;
                }
                for i in start..start + len {
                    let released = release(step[i], halvings);
                    moved |= released != 0;
                    candidate.theta[i] = fit32(candidate.theta[i] as i128 - released, "a deposited parameter outgrew its 32-bit carrier")?;
                }
            }
            moved |= candidate.move_by_chart(&step, halvings)?;
            if !moved {
                for (s, (_, end)) in states.iter_mut().zip(forwards) {
                    *s = end;
                }
                return Ok(SectionReceipt { cells: faces_old.len(), code_before, code_after: code_before, halvings, deposited: false });
            }
            candidate.project();
            let creaches = candidate.reaches();
            let rereads: Vec<(Vec<Cell>, TowerState)> = opening
                .par_iter()
                .zip(classes.par_iter())
                .map(|(open, c)| {
                    let mut s = open.clone();
                    let cells = candidate.forward(&mut s, c, &creaches)?;
                    Ok((cells, s))
                })
                .collect::<Result<_>>()?;
            let faces_new: Vec<(u128, u128)> = rereads
                .iter()
                .zip(classes)
                .flat_map(|((cells, _), c)| cells.iter().enumerate().map(move |(i, cell)| (cell.face.masses[c[i + 1]], cell.face.total)))
                .collect();
            if fewer_bits(&faces_old, &faces_new) {
                let code_after: i64 = rereads
                    .iter()
                    .zip(classes)
                    .map(|((cells, _), c)| cells.iter().enumerate().map(|(i, cell)| cell.face.code(c[i + 1])).sum::<i64>())
                    .sum();
                for (s, (_, end)) in states.iter_mut().zip(rereads) {
                    *s = end;
                }
                self.tower = candidate;
                return Ok(SectionReceipt { cells: faces_old.len(), code_before, code_after, halvings, deposited: true });
            }
            halvings += 1;
        }
    }

    /// The learner as text: the tower, then the moments.
    pub fn to_text(&self) -> String {
        let mut s = self.tower.to_text();
        s.push_str(&format!("moments {} {}\n", self.rate_bits, self.opened as u8));
        s.push_str(&self.first.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" "));
        s.push('\n');
        s.push_str(&self.second.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" "));
        s.push('\n');
        s
    }

    pub fn from_text(text: &str) -> Result<Self> {
        let lines: Vec<&str> = text.lines().collect();
        if lines.len() != 5 {
            return refuse("a learner's text has five lines");
        }
        let tower = Tower::from_text(&format!("{}\n{}\n", lines[0], lines[1]))?;
        let head: Vec<&str> = lines[2].split(' ').collect();
        if head.len() != 3 || head[0] != "moments" {
            return refuse("not a learner's moments");
        }
        let rate_bits = head[1].parse::<u32>().map_err(|_| TowerError::Refused("a rate that is not a count"))?;
        let opened = head[2] == "1";
        let parse = |l: &str| -> Result<Vec<i128>> {
            l.split(' ').map(|s| s.parse::<i128>().map_err(|_| TowerError::Refused("a moment that is not an integer"))).collect()
        };
        let first = parse(lines[3])?;
        let second = parse(lines[4])?;
        if first.len() != tower.theta.len() || second.len() != tower.theta.len() {
            return refuse("moments of the wrong extent");
        }
        Ok(Self { tower, first, second, opened, rate_bits, swell: Vec::new() })
    }
}

impl Tower {
    /// [definition; agent-inferred, October 23] **A move's deposit chart.** A move `λ = ρ e^(iφ)`
    /// is stepped in `(ν, φ)` with `ν = ln(1 − ρ)`: the logarithm of its distance to the unit
    /// circle (to first order its dissipation a tick) and its turn. A Cartesian step of the rate
    /// `2^(−7)` moves `ρ` by up to 0.008 a section, so it crosses the 0.026 between `ρ = 0.974` and
    /// the margin in about three (measured, second pass on 1,000 GSM8K problems: `ρ` went from 0.974
    /// to 0.991 in nine sections and the state's face five-fold, then past its carrier); in the
    /// chart a step changes `1 − ρ` by the factor `e^(±2^(−k))`. The covector on `2^(−32)` becomes
    /// `g_ν = −(1 − ρ) ⟨λ/ρ, g⟩`, `g_φ = λ_re g_im − λ_im g_re`; at `ρ = 0` the chart's direction is
    /// the real axis.
    fn to_move_chart(&self, g: &mut [i128]) {
        let one = 1i128 << MOVE_BITS;
        for lv in &self.layout.levels {
            for k in 0..self.declaration.modes {
                let (re, im) = (self.theta[lv.move_re + k] as i128, self.theta[lv.move_im + k] as i128);
                let (gr, gi) = (g[lv.move_re + k], g[lv.move_im + k]);
                let (modulus, _) = modulus_and_gamma(re, im);
                let radial = if modulus == 0 { gr } else { div_nearest(re * gr + im * gi, modulus) };
                g[lv.move_re + k] = -release((one - modulus) * radial, MOVE_BITS);
                g[lv.move_im + k] = release(re * gi - im * gr, MOVE_BITS);
            }
        }
    }

    /// Every move stepped in its chart by `(Δν, Δφ)` released `halvings` coarser: `1 − ρ ← (1 − ρ)
    /// e^(−Δν)`, `φ ← φ − Δφ`, then projected inside the margin. Whether any move moved.
    fn move_by_chart(&mut self, step: &[i128], halvings: u32) -> Result<bool> {
        let one = 1i128 << MOVE_BITS;
        let mut moved = false;
        for lv in self.layout.levels.clone() {
            for k in 0..self.declaration.modes {
                let dn = release(step[lv.move_re + k], halvings);
                let dp = release(step[lv.move_im + k], halvings);
                if dn == 0 && dp == 0 {
                    continue;
                }
                moved = true;
                let (re, im) = (self.theta[lv.move_re + k] as i128, self.theta[lv.move_im + k] as i128);
                let (modulus, _) = modulus_and_gamma(re, im);
                let distance = release((one - modulus) * exp_series(-dn, 0).0, MOVE_BITS);
                let target = one - distance;
                let unit = if modulus == 0 { (one, 0) } else { (div_nearest(re * one, modulus), div_nearest(im * one, modulus)) };
                let (c, sn) = exp_series(0, -dp);
                let ur = release(unit.0 * c - unit.1 * sn, MOVE_BITS);
                let ui = release(unit.0 * sn + unit.1 * c, MOVE_BITS);
                self.theta[lv.move_re + k] = fit32(release(target * ur, MOVE_BITS), "a deposited move outgrew its 32-bit carrier")?;
                self.theta[lv.move_im + k] = fit32(release(target * ui, MOVE_BITS), "a deposited move outgrew its 32-bit carrier")?;
            }
        }
        Ok(moved)
    }

    /// Every move back inside its disk, `|λ| ≤ 1 − 2^(−12)`.
    fn project(&mut self) {
        let radius = (1i128 << MOVE_BITS) - (1i128 << (MOVE_BITS - MARGIN));
        for lv in self.layout.levels.clone() {
            for k in 0..self.declaration.modes {
                let (re, im) = (self.theta[lv.move_re + k] as i128, self.theta[lv.move_im + k] as i128);
                let n = re * re + im * im;
                if n > radius * radius {
                    let modulus = (n as u128).isqrt() as i128 + 1;
                    self.theta[lv.move_re + k] = (re * radius / modulus) as i32;
                    self.theta[lv.move_im + k] = (im * radius / modulus) as i32;
                }
            }
        }
    }

    /// A frozen reading: the code of `classes[1..]` from the state, on `2^(−20)` bits, the state
    /// moved.
    pub fn read(&self, state: &mut TowerState, classes: &[usize]) -> Result<i64> {
        Ok(self.read_cells(state, classes)?.iter().sum())
    }

    /// Each cell's code: entry `i` is the face after `classes[i]` read at `classes[i + 1]`, on
    /// `2^(−READ_BITS)` bits, so a receiver can sum it over any partition of the passage.
    pub fn read_cells(&self, state: &mut TowerState, classes: &[usize]) -> Result<Vec<i64>> {
        let reaches = self.reaches();
        let mut codes = Vec::with_capacity(classes.len().saturating_sub(1));
        for i in 0..classes.len().saturating_sub(1) {
            let cell = self.step(state, classes[i], &reaches)?;
            codes.push(cell.face.code(classes[i + 1]));
        }
        Ok(codes)
    }
}

/// [definition; agent-inferred, October 23] **The tower joined to a cell-grain face.** The route
/// (`hnn::keyed_modes`) reads base-four cells; the tower reads bytes. At a cell of phase `k` the
/// tower's face is its byte face summed over the cell's prefix ([`TowerFace::cell_masses`]), and
/// its news over the route's face `r` is `f_d = log₂ t̂(d) − log₂ r̂(d)`. The joined face is
///
/// ```text
/// p̂(d) ∝ r_d 2^(α_k f_d)            (= r̂^(1−α) t̂^α: the geometric join of the two faces)
/// ```
///
/// with one weight per phase on `2^(−16)`, opened at `½` (no evidence favours either face). The
/// weight's covector at a cell is `E_p̂[f] − f_actual` bits and its curvature `ln 2 · Var_p̂(f)`;
/// a section closes with the lock's Newton step on its cumulative curvature from a prior of one,
/// `α ← α − G / (ln 2 (1 + Σ C))`, projected into `|α| ≤ 2^4`. The code is convex in `α`, so
/// the step descends (the lock's certificate, `hnn::keyed_modes`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellJoin {
    /// `α_k` on `2^(−16)`.
    pub weights: [i64; 4],
    /// The section's covector per phase on `2^(−20)` bits.
    gradient: [i128; 4],
    /// The cumulative curvature per phase on `2^(−40)`, the prior `2^40` included.
    curvature: [i128; 4],
    exponential: Exponential,
}

/// The join's weight grain, `2^(−16)`.
pub const JOIN_BITS: u32 = 16;
/// The join's weight reach, `|α| ≤ 2^4`.
const JOIN_REACH: i64 = 1 << (JOIN_BITS + 4);

/// One joined cell: the joined face, and the news it was read with.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JoinedCell {
    pub masses: [u128; 4],
    pub total: u128,
    /// `f_d` on `2^(−20)` bits.
    pub news: [i64; 4],
}

impl JoinedCell {
    /// `−log₂ p̂(d)` on `2^(−20)` bits.
    pub fn code(&self, d: usize) -> i64 {
        code_of(self.masses[d], self.total)
    }
}

/// `m / t` on `2^(−62)`, at least one grain; a total past `2^64` is re-based so the shift fits.
fn unit_of(m: u128, t: u128) -> u128 {
    let shift = (128 - t.leading_zeros()).saturating_sub(64);
    (((m >> shift) << UNIT_BITS) / (t >> shift).max(1)).clamp(1, 1u128 << UNIT_BITS)
}

/// `−log₂(m / t)` on `2^(−20)` bits, for any face's mass and total.
pub fn code_of(m: u128, t: u128) -> i64 {
    -(log2_face(unit_of(m, t), READ_BITS) as i64)
}

impl Default for CellJoin {
    fn default() -> Self {
        Self::new([1 << (JOIN_BITS - 1); 4])
    }
}

impl CellJoin {
    pub fn new(weights: [i64; 4]) -> Self {
        Self { weights, gradient: [0; 4], curvature: [1i128 << 40; 4], exponential: Exponential::new(JOIN_BITS) }
    }

    /// The joined face at a cell of `phase`, from the route's masses and the tower's cell masses.
    pub fn face(&self, route: &[u128], tower: &[u128; 4], phase: usize) -> Result<JoinedCell> {
        if route.len() != 4 || phase > 3 {
            return refuse("a joined cell has four classes and a phase below four");
        }
        let rt: u128 = route.iter().sum();
        let tt: u128 = tower.iter().sum();
        if rt == 0 || tt == 0 {
            return refuse("a joined cell needs both faces with mass");
        }
        let unit = unit_of;
        let mut news = [0i64; 4];
        for d in 0..4 {
            news[d] = (log2_face(unit(tower[d], tt), READ_BITS) - log2_face(unit(route[d], rt), READ_BITS)) as i64;
        }
        let alpha = self.weights[phase] as i128;
        let w: Vec<i128> = news.iter().map(|&f| release(alpha * f as i128, READ_BITS)).collect();
        let top = *w.iter().max().expect("four classes");
        let mut masses = [0u128; 4];
        for d in 0..4 {
            // r̂_d on 2^(−62) times 2^(w_d − w_max) on 2^(−62).
            masses[d] = ((unit(route[d], rt) * self.exponential.below_one(w[d] - top)) >> UNIT_BITS).max(1);
        }
        let total = masses.iter().sum();
        Ok(JoinedCell { masses, total, news })
    }

    /// The cell's actual class reaches the weight of its phase: its covector and curvature.
    pub fn receive(&mut self, cell: &JoinedCell, actual: usize, phase: usize) {
        // p̂_d on 2^(−30).
        let p: Vec<i128> = cell.masses.iter().map(|&m| (((m << 30) + cell.total / 2) / cell.total) as i128).collect();
        let mean: i128 = p.iter().zip(&cell.news).map(|(&p, &f)| p * f as i128).sum(); // 2^(−50)
        let second: i128 = p.iter().zip(&cell.news).map(|(&p, &f)| p * (f as i128) * (f as i128)).sum(); // 2^(−70)
        let mean20 = release(mean, 30);
        self.gradient[phase] += mean20 - cell.news[actual] as i128;
        let variance = release(second, 30) - mean20 * mean20; // 2^(−40)
        self.curvature[phase] += variance.max(0) * ln2_face() >> 30;
    }

    /// The section closes: each phase's weight takes its Newton step, and the covector reopens.
    pub fn step(&mut self) {
        for k in 0..4 {
            let g = self.gradient[k];
            self.gradient[k] = 0;
            if g == 0 {
                continue;
            }
            // Δα on 2^(−16) = G 2^(−20) / (ln 2 · H 2^(−40)) · 2^16 = G 2^36 / (ln 2 · H)
            //                = G 2^(36+30) / (ln2_face · H).
            let num = (g as i128) << 36;
            let den = (ln2_face() * self.curvature[k]) >> 30;
            let delta = if den > 0 { num / den } else { 0 };
            let delta = delta.clamp(-(2 * JOIN_REACH) as i128, (2 * JOIN_REACH) as i128) as i64;
            self.weights[k] = (self.weights[k] - delta).clamp(-JOIN_REACH, JOIN_REACH);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn keys(n: usize) -> Vec<u8> {
        // A fixed exterior key stream for the fixtures: the bytes of a counter's squares.
        (0..n as u64).flat_map(|i| (i.wrapping_mul(2654435761) ^ (i * i)).to_be_bytes()[4..].to_vec()).collect()
    }

    fn tiny() -> Tower {
        let declaration = TowerDeclaration { alphabet: 4, width: 4, modes: 2, contacts: 4, levels: 2 };
        let mut tower = Tower::found(declaration, &keys(4096)).expect("founded");
        // Open the readout and the returns away from zero so every family carries a covector.
        let k = keys(8192);
        let mut i = 1000;
        let layout = tower.layout.clone();
        let mut fill = |theta: &mut Vec<i32>, start: usize, len: usize| {
            for v in &mut theta[start..start + len] {
                *v = (i32::from_be_bytes([k[4 * i], k[4 * i + 1], k[4 * i + 2], k[4 * i + 3]]) >> 8) / 4;
                i += 1;
            }
        };
        fill(&mut tower.theta, layout.readout, 16);
        for lv in &layout.levels {
            fill(&mut tower.theta, lv.ret, 16);
        }
        tower
    }

    fn code(tower: &Tower, classes: &[usize]) -> i64 {
        let mut s = tower.rest();
        tower.read(&mut s, classes).expect("read")
    }

    #[test]
    fn text_restores_exactly() {
        let tower = tiny();
        assert_eq!(Tower::from_text(&tower.to_text()).expect("restored"), tower);
        let mut learner = TowerLearner::new(tower, 6);
        let seq: Vec<usize> = (0..17).map(|i| i % 4).collect();
        let mut states = vec![learner.tower.rest()];
        learner.section(&mut states, &[&seq]).expect("section");
        let restored = TowerLearner::from_text(&learner.to_text()).expect("restored");
        assert_eq!(restored.tower, learner.tower);
        assert_eq!(restored.to_text(), learner.to_text());
    }

    #[test]
    fn the_covector_matches_the_code_difference() {
        let tower = tiny();
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
        let opening = tower.rest();
        let reaches = tower.reaches();
        let mut s = opening.clone();
        let cells = tower.forward(&mut s, &classes, &reaches).expect("forward");
        let mut g = tower.reverse(&opening, &cells, &classes).expect("reverse");
        tower.to_step_grain(&mut g);
        // Which contacts conduct at every cell: the covector is the derivative on the passage's own
        // side of every kink, so a perturbation that moves a contact across its kink is not read.
        let conducting = |t: &Tower| -> Vec<bool> {
            let mut s = t.rest();
            let cells = t.forward(&mut s, &classes, &t.reaches()).expect("forward");
            cells.iter().flat_map(|c| c.levels.iter().flat_map(|l| l.drive.iter().map(|&a| a > 0)).collect::<Vec<_>>()).collect()
        };
        let base = conducting(&tower);
        // Every family: its parameters by covector, largest first, the first whose ±2^(−7) units
        // keep every contact on its side.
        let mut checked = 0;
        for &(start, len, grain) in &tower.layout.families {
            let mut order: Vec<usize> = (start..start + len).collect();
            order.sort_by_key(|&i| std::cmp::Reverse(g[i].abs()));
            for i in order {
                let gi = g[i];
                if gi.abs() < 1i128 << (STEP_BITS - 6) {
                    break; // below 1/64 bit a unit the difference over ±2^(−7) units nears the reading's grain
                }
                let h = 1i32 << (grain - 7);
                let mut plus = tower.clone();
                plus.theta[i] += h;
                let mut minus = tower.clone();
                minus.theta[i] -= h;
                if conducting(&plus) != base || conducting(&minus) != base {
                    continue;
                }
                // (L(θ+h) − L(θ−h)) / 2h against g, both in bits a unit on 2^(−32).
                let diff = (code(&plus, &classes) - code(&minus, &classes)) as i128; // on 2^(−20)
                let numeric = (diff << (STEP_BITS - READ_BITS)) * (1i128 << grain) / (2 * h as i128);
                let error = (numeric - gi).abs();
                assert!(error * 10 <= gi.abs(), "family at {start} grain {grain}, parameter {i}: covector {gi} against {numeric}");
                checked += 1;
                break;
            }
        }
        assert!(checked * 4 >= tower.layout.families.len() * 3, "only {checked} families carried a readable covector");
    }

    #[test]
    fn the_move_chart_covector_matches_its_step() {
        let tower = tiny();
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
        let opening = tower.rest();
        let reaches = tower.reaches();
        let mut s = opening.clone();
        let cells = tower.forward(&mut s, &classes, &reaches).expect("forward");
        let mut g = tower.reverse(&opening, &cells, &classes).expect("reverse");
        tower.to_step_grain(&mut g);
        tower.to_move_chart(&mut g);
        // Each chart coordinate of each level: the mode with the largest covector, stepped by ±2^(−7).
        let mut checked = 0;
        for lv in &tower.layout.levels {
            for slot in [lv.move_re, lv.move_im] {
                let (i, gi) = (slot..slot + tower.declaration.modes).map(|i| (i, g[i])).max_by_key(|(_, v)| v.abs()).expect("modes");
                if gi.abs() < 1i128 << (STEP_BITS - 6) {
                    continue;
                }
                let h = 1i128 << (MOVE_BITS - 7);
                let mut step = vec![0i128; g.len()];
                step[i] = h;
                let mut minus = tower.clone();
                minus.move_by_chart(&step, 0).expect("chart step");
                step[i] = -h;
                let mut plus = tower.clone();
                plus.move_by_chart(&step, 0).expect("chart step");
                let diff = (code(&plus, &classes) - code(&minus, &classes)) as i128;
                let numeric = (diff << (STEP_BITS - READ_BITS)) * (1i128 << MOVE_BITS) / (2 * h);
                assert!((numeric - gi).abs() * 10 <= gi.abs(), "chart coordinate at {i}: covector {gi} against {numeric}");
                checked += 1;
            }
        }
        assert!(checked >= 2, "only {checked} chart coordinates carried a readable covector");
    }

    #[test]
    fn the_cell_faces_split_the_byte_face_exactly() {
        let masses: Vec<u128> = (0..256u128).map(|b| 1 + (b * b) % 97).collect();
        let total = masses.iter().sum();
        let face = TowerFace { masses: masses.clone(), total };
        // The first cell's masses sum to the face's total; each later phase splits its prefix's mass.
        assert_eq!(face.cell_masses(0, 0).expect("cell").iter().sum::<u128>(), total);
        for byte in [0usize, 77, 200, 255] {
            let mut prefix = 0;
            let mut mass = total;
            for phase in 0..4 {
                let cells = face.cell_masses(prefix, phase).expect("cell");
                assert_eq!(cells.iter().sum::<u128>(), mass);
                let d = (byte >> (6 - 2 * phase)) & 3;
                mass = cells[d];
                prefix = (prefix << 2) | d;
            }
            assert_eq!(mass, masses[byte]);
        }
        assert!(face.cell_masses(4, 1).is_err());
    }

    #[test]
    fn the_join_reads_the_route_at_zero_and_moves_toward_the_face_that_codes_less() {
        let route = [400u128, 300, 200, 100];
        let tower = [10u128, 10, 10, 970];
        let at_zero = CellJoin::new([0; 4]).face(&route, &tower, 0).expect("joined");
        for d in 0..4 {
            // r̂ on 2^(−62) timed by 2^0: the route's own face.
            assert_eq!(at_zero.masses[d], unit_of(route[d], 1000), "{at_zero:?}");
        }
        // The class the tower favours keeps arriving: the weight of its phase grows past ½.
        let mut join = CellJoin::default();
        for _ in 0..8 {
            for _ in 0..64 {
                let cell = join.face(&route, &tower, 2).expect("joined");
                join.receive(&cell, 3, 2);
            }
            join.step();
        }
        assert!(join.weights[2] > 1 << (JOIN_BITS - 1), "{:?}", join.weights);
        assert_eq!(join.weights[0], 1 << (JOIN_BITS - 1));
        let cell = join.face(&route, &tower, 2).expect("joined");
        assert!(cell.code(3) < code_of(route[3], 1000));
    }

    #[test]
    fn a_section_learns_a_repeating_passage() {
        let declaration = TowerDeclaration { alphabet: 4, width: 8, modes: 4, contacts: 8, levels: 1 };
        let tower = Tower::found(declaration, &keys(4096)).expect("founded");
        let mut learner = TowerLearner::new(tower, 5);
        let passage: Vec<usize> = (0..4096).map(|i| [0, 1, 2, 1, 3][i % 5]).collect();
        let mut states = vec![learner.tower.rest(), learner.tower.rest()];
        let mut last = SectionReceipt { cells: 0, code_before: 0, code_after: 0, halvings: 0, deposited: false };
        for section in 0..60 {
            let a = &passage[section * 32..section * 32 + 33];
            let b = &passage[2048 + section * 32..2048 + section * 32 + 33];
            last = learner.section(&mut states, &[a, b]).expect("section");
            // The certificate compares the exact products; the reading releases each cell to
            // 2^(−20) bits, so a certified step below that grain can read as a tie.
            assert!(!last.deposited || last.code_after <= last.code_before + last.cells as i64, "section {section}: {last:?}");
        }
        // Under a quarter of a bit a class (the flat face codes two bits).
        assert!(last.code_after * 4 < (last.cells as i64) << READ_BITS, "{last:?}");
    }
}
