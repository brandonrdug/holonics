//! **The step's parts meet through the receiving face's metric** (#404; the coarse-level record's
//! §17, `2026-10-30_THE_COARSE_LEVEL_HEADS_FOR_THE_TRACE_OF_WHAT_COMES_NEXT_AND_THE_FINE_LEVELS_READ_ITS_HEADING`).
//!
//! [definition; agent-inferred, October 30, the law derived in the unified-theory thread] A refused
//! step is read in five parts (the record's §13: the descent, the heading's read, the readout with
//! its bias, the clocked levels' material, and the rest). Each part stepped alone changes every
//! compared face's base-2 logits by `δz⁽ⁱ⁾`, and the code's curvature in those logits is the face's
//! Fisher form `ln 2 (diag p − p pᵀ)` (atlas `receiver.fisher-certificate`). Pulled back through
//! the parts (`hnn.witness-plane`'s Gauss–Newton form), it is the meeting form
//!
//! ```text
//! c_t⁽ⁱ⁾ = Σ_c p_tc δz_tc⁽ⁱ⁾          G = Σ_t G_t,   G_t⁽ⁱʲ⁾ = Σ_c p_tc δz_tc⁽ⁱ⁾ δz_tc⁽ʲ⁾ − c_t⁽ⁱ⁾ c_t⁽ʲ⁾
//! g_i = Σ_t (c_t⁽ⁱ⁾ − δz_(t,target)⁽ⁱ⁾)   m(α) = Σ_i α_i g_i + ½ ln 2 · αᵀ G α,   α* = argmin over [0, 1]⁵ of m
//! ```
//!
//! `G_t` is the covariance of two parts' logit changes under the face, so `G` is positive
//! semidefinite by construction: the probabilities are partitioned on `2^(−32)` to sum to one
//! exactly, and every product is carried whole. The box's minimum is solved exactly over its
//! `3⁵` faces ([`box_minimum`]).

use super::*;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::Rat;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

/// The parts a refused step is read in: the descent, the heading's read, the readout and its bias,
/// the clocked levels' own material, and every other family.
pub const PARTS: usize = 5;

/// The grain of a face's partitioned probabilities, `2^(−32)`.
const MASS_BITS: u32 = 32;

/// The grain of an applied scale, `2^(−32)`.
pub const SCALE_BITS: u32 = 32;

/// The largest logit change the form reads, `2^24` on `2^(−16)` (256 bits): past it a cell's
/// products would leave their 128-bit carrier, so the form refuses.
const CHANGE_BITS: u32 = 24;

/// The grain of `g`, `2^(−48)` bits: a probability on `2^(−32)` times a logit on `2^(−16)`.
const SLOPE_BITS: u32 = MASS_BITS + FACE_BITS;

/// The grain of `G`, `2^(−96)`: two probabilities and two logits.
const FORM_BITS: u32 = 2 * SLOPE_BITS;

/// The grain a reading of `G` is released to, `2^(−64)`.
const READING_BITS: u32 = 64;

/// [definition; agent-inferred, October 30] **A refused step's meeting form**, read at the halving
/// the section first refused: each part's first-order change of the arrivals' code (`g`, on
/// `2^(−48)` bits) and the form (`gram`, on `2^(−96)`), summed over every compared cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MeetingForm {
    pub g: [i128; PARTS],
    pub gram: [[BigInt; PARTS]; PARTS],
}

/// [agent-inferred, October 30] **One trial of the meeting form** ([`SectionReceipt::meeting`]):
/// the halving it stepped at, the form it was solved on (`g` on `2^(−48)` bits and the form
/// released to `2^(−64)`, both at the form's own halving), the scales it applied (on `2^(−32)`), the
/// model's change at them and at the trial's halving (on `2^(−20)` bits, the code's grain), the
/// actual change of the arrivals' code (none where the model predicted no fall and nothing was
/// read), and whether the step was accepted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MeetingReading {
    pub halvings: u32,
    pub g: [i128; PARTS],
    pub gram: [[i128; PARTS]; PARTS],
    pub scales: [u64; PARTS],
    pub model: i64,
    pub change: Option<i64>,
    pub accepted: bool,
}

/// A face's masses partitioned on `2^(−32)` so they sum to one exactly: each mass's floor, then
/// the remaining grains one each to the largest remainders, ties to the lower class.
fn partitioned(masses: &[u128], total: u128) -> Vec<i128> {
    let unit = 1u128 << MASS_BITS;
    let mut p: Vec<i128> = Vec::with_capacity(masses.len());
    let mut rest: Vec<(u128, usize)> = Vec::with_capacity(masses.len());
    let mut given = 0u128;
    for (c, &m) in masses.iter().enumerate() {
        // `m ≤ total < 2^70`, so `m · 2^32` stays within 128 bits.
        let scaled = m * unit;
        p.push((scaled / total) as i128);
        given += scaled / total;
        rest.push((scaled % total, c));
    }
    let short = (unit - given) as usize;
    rest.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
    for &(_, c) in rest.iter().take(short) {
        p[c] += 1;
    }
    p
}

/// `x` released `bits` coarser, to the nearest, half away from zero.
fn release_big(x: &BigInt, bits: u32) -> BigInt {
    if bits == 0 {
        return x.clone();
    }
    let half = BigInt::one() << (bits - 1);
    if x.is_negative() { -((-x + half) >> bits) } else { (x + half) >> bits }
}

/// [definition; agent-inferred, October 30] **The meeting form** of the parts' logit changes:
/// `opening` holds every compared cell's face logits at the opening (the alphabet's entries, in
/// the faces' order) and `parts[i]` the same cells' logits with part `i` stepped alone; `targets`
/// the class each compared cell is compared with. The opening's probabilities are the face the
/// tower forms from its logits, partitioned on `2^(−32)`.
pub fn form(tower: &Tower, opening: &[i64], parts: &[Vec<i64>], targets: &[usize]) -> Result<MeetingForm> {
    let a = tower.declaration.alphabet;
    let cells = targets.len();
    if parts.len() != PARTS || opening.len() != cells * a || parts.iter().any(|z| z.len() != cells * a) || targets.iter().any(|&t| t >= a) {
        return refuse("a meeting form reads every compared cell's logits, at the opening and under each part");
    }
    let limit = 1i128 << CHANGE_BITS;
    type Cell = ([i128; PARTS], [[i128; PARTS]; PARTS]);
    let cell = |t: usize| -> Result<Cell> {
        let zo = &opening[t * a..(t + 1) * a];
        let zmax = *zo.iter().max().expect("a nonempty alphabet");
        let masses: Vec<u128> = zo.iter().map(|&v| tower.exponential.below_one((v - zmax) as i128)).collect();
        let total: u128 = masses.iter().sum();
        let p = partitioned(&masses, total);
        let mut changes: Vec<Vec<i128>> = Vec::with_capacity(PARTS);
        for z in parts {
            let row: Vec<i128> = z[t * a..(t + 1) * a].iter().zip(zo).map(|(&x, &o)| x as i128 - o as i128).collect();
            if row.iter().any(|v| v.abs() >= limit) {
                return refuse("a part moved a face's logit past the meeting form's reach");
            }
            changes.push(row);
        }
        let mut c = [0i128; PARTS];
        let mut s = [[0i128; PARTS]; PARTS];
        for (class, &pc) in p.iter().enumerate() {
            if pc == 0 {
                continue;
            }
            for i in 0..PARTS {
                let di = changes[i][class];
                if di == 0 {
                    continue;
                }
                let weighted = pc * di;
                c[i] += weighted;
                for j in i..PARTS {
                    s[i][j] += weighted * changes[j][class];
                }
            }
        }
        let target = targets[t];
        let g: [i128; PARTS] = std::array::from_fn(|i| c[i] - (changes[i][target] << MASS_BITS));
        let mut cov = [[0i128; PARTS]; PARTS];
        for i in 0..PARTS {
            for j in i..PARTS {
                let v = (s[i][j] << MASS_BITS) - c[i] * c[j];
                cov[i][j] = v;
                cov[j][i] = v;
            }
        }
        Ok((g, cov))
    };
    let zero = || ([0i128; PARTS], std::array::from_fn::<[BigInt; PARTS], PARTS, _>(|_| std::array::from_fn(|_| BigInt::zero())));
    let (g, gram) = (0..cells)
        .into_par_iter()
        .map(cell)
        .try_fold(zero, |(mut g, mut gram), r| -> Result<_> {
            let (gc, cov) = r?;
            for i in 0..PARTS {
                g[i] = g[i].checked_add(gc[i]).ok_or(TowerError::Refused("a part's slope outgrew its 128-bit carrier"))?;
                for j in 0..PARTS {
                    gram[i][j] += cov[i][j];
                }
            }
            Ok((g, gram))
        })
        .try_reduce(zero, |(mut g, mut gram), (g2, gram2)| {
            for i in 0..PARTS {
                g[i] = g[i].checked_add(g2[i]).ok_or(TowerError::Refused("a part's slope outgrew its 128-bit carrier"))?;
                for j in 0..PARTS {
                    gram[i][j] += &gram2[i][j];
                }
            }
            Ok((g, gram))
        })?;
    Ok(MeetingForm { g, gram })
}

impl MeetingForm {
    /// The model at `k` halvings past the form's own, in bits: the slopes `g / 2^k` and the
    /// curvature `ln 2 · G / 4^k` (the parts stepped `2^(−k)` as far).
    pub fn model(&self, k: u32) -> (Vec<Rat>, Vec<Vec<Rat>>) {
        let ln2 = BigInt::from(ln2_face());
        let slope_den = BigInt::one() << (SLOPE_BITS + k);
        let form_den = BigInt::one() << (FORM_BITS + 30 + 2 * k);
        let g = self.g.iter().map(|&v| Rat::new(BigInt::from(v), slope_den.clone())).collect();
        let curvature = self.gram.iter().map(|row| row.iter().map(|v| Rat::new(v * &ln2, form_den.clone())).collect()).collect();
        (g, curvature)
    }

    /// The form as a reading: `g` and the form released to `2^(−64)`.
    pub fn reading(&self) -> Result<([i128; PARTS], [[i128; PARTS]; PARTS])> {
        let mut gram = [[0i128; PARTS]; PARTS];
        for i in 0..PARTS {
            for j in 0..PARTS {
                gram[i][j] = i128::try_from(release_big(&self.gram[i][j], FORM_BITS - READING_BITS)).map_err(|_| TowerError::Refused("a meeting form's reading outgrew its 128-bit carrier"))?;
            }
        }
        Ok((self.g, gram))
    }
}

/// `m(α) = Σ_i α_i g_i + ½ αᵀ K α`.
pub fn model_at(g: &[Rat], curvature: &[Vec<Rat>], alpha: &[Rat]) -> Rat {
    let n = g.len();
    let mut m = Rat::zero();
    for i in 0..n {
        m += &alpha[i] * &g[i];
        let mut row = Rat::zero();
        for j in 0..n {
            row += &curvature[i][j] * &alpha[j];
        }
        m += &alpha[i] * row / Rat::from_integer(BigInt::from(2));
    }
    m
}

/// [definition; agent-inferred, October 30] **The box's minimum**: `argmin over [0, 1]ⁿ of
/// m(α) = Σ α_i g_i + ½ αᵀ K α` for `K` positive semidefinite, solved exactly over the box's `3ⁿ`
/// faces in order (each coordinate held at zero, held at one, or free). On a face the free
/// coordinates solve `K_FF α_F = −(g_F + K_FU 1)`; a face whose block is singular, or whose solution
/// leaves the box, is passed over, and the least `m` is kept, the first face in order on a tie. At a
/// vertex of the minimizers the free block is nonsingular (a null direction of it would be a null
/// direction of `K` along which `m` is flat, so the vertex would not be one), so the least face is
/// the minimum.
pub fn box_minimum(g: &[Rat], curvature: &[Vec<Rat>]) -> Result<Vec<Rat>> {
    let n = g.len();
    if curvature.len() != n || curvature.iter().any(|r| r.len() != n) {
        return refuse("a box's model is square in its scales");
    }
    let mut best: Option<(Rat, Vec<Rat>)> = None;
    let faces = 3usize.pow(n as u32);
    for face in 0..faces {
        let mut state = vec![0u8; n];
        let mut code = face;
        for s in state.iter_mut() {
            *s = (code % 3) as u8;
            code /= 3;
        }
        let free: Vec<usize> = (0..n).filter(|&i| state[i] == 2).collect();
        let mut alpha: Vec<Rat> = state.iter().map(|&s| if s == 1 { Rat::one() } else { Rat::zero() }).collect();
        if !free.is_empty() {
            let block = ExactRatMatrix::new(free.iter().map(|&i| free.iter().map(|&j| curvature[i][j].clone()).collect()).collect()).map_err(|_| TowerError::Refused("a box's face block is not a matrix"))?;
            let Ok(inverse) = block.inverse() else { continue };
            let rhs: Vec<Rat> = free
                .iter()
                .map(|&i| {
                    let mut r = -g[i].clone();
                    for j in (0..n).filter(|&j| state[j] == 1) {
                        r -= &curvature[i][j];
                    }
                    r
                })
                .collect();
            let solved = inverse.apply(&rhs).map_err(|_| TowerError::Refused("a box's face solve is not square"))?;
            if solved.iter().any(|v| v.is_negative() || *v > Rat::one()) {
                continue;
            }
            for (&i, v) in free.iter().zip(solved) {
                alpha[i] = v;
            }
        }
        let m = model_at(g, curvature, &alpha);
        if best.as_ref().is_none_or(|(b, _)| m < *b) {
            best = Some((m, alpha));
        }
    }
    Ok(best.expect("the box's vertices are faces").1)
}

/// The scales released to `2^(−32)`, to the nearest (half up), each within `[0, 2^32]`.
pub fn released_scales(alpha: &[Rat]) -> Result<[u64; PARTS]> {
    if alpha.len() != PARTS {
        return refuse("one scale a part");
    }
    let unit = BigInt::one() << SCALE_BITS;
    let mut out = [0u64; PARTS];
    for (o, a) in out.iter_mut().zip(alpha) {
        let two = BigInt::from(2);
        let twice: BigInt = a.numer() * &unit * &two + a.denom();
        let v: BigInt = twice / (a.denom() * &two);
        let v = v.max(BigInt::zero()).min(unit.clone());
        *o = u64::try_from(v).expect("a scale within [0, 2^32]");
    }
    Ok(out)
}

/// The released scales as rationals.
pub fn scales_as_rat(scales: &[u64; PARTS]) -> Vec<Rat> {
    scales.iter().map(|&s| Rat::new(BigInt::from(s), BigInt::one() << SCALE_BITS)).collect()
}

/// A step entry scaled by a released scale, to the nearest.
pub fn scaled(step: i128, scale: u64) -> Result<i128> {
    let product = step.checked_mul(scale as i128).ok_or(TowerError::Refused("a scaled step outgrew its 128-bit carrier"))?;
    Ok(release(product, SCALE_BITS))
}

/// The model's change on the code's grain `2^(−20)` bits, to the nearest.
pub fn on_code_grain(m: &Rat) -> Result<i64> {
    let scaled = m * Rat::from_integer(BigInt::one() << READ_BITS);
    let two = BigInt::from(2);
    let twice: BigInt = scaled.numer() * &two;
    let den: BigInt = scaled.denom() * &two;
    let v: BigInt = if twice.is_negative() { -((-twice + scaled.denom()) / den) } else { (twice + scaled.denom()) / den };
    i64::try_from(v).map_err(|_| TowerError::Refused("a model's change outgrew its 64-bit carrier"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(n: i64, d: i64) -> Rat {
        Rat::new(BigInt::from(n), BigInt::from(d))
    }

    /// The optimality conditions of the box's minimum: a free scale stationary, a scale at zero
    /// with a nonnegative slope, at one with a nonpositive one.
    fn optimal(g: &[Rat], k: &[Vec<Rat>], alpha: &[Rat]) -> bool {
        (0..g.len()).all(|i| {
            let mut r = g[i].clone();
            for j in 0..g.len() {
                r += &k[i][j] * &alpha[j];
            }
            if alpha[i].is_zero() {
                !r.is_negative()
            } else if alpha[i] == Rat::one() {
                !r.is_positive()
            } else {
                r.is_zero()
            }
        })
    }

    /// The face probabilities sum to one exactly and stay within a grain of the face.
    #[test]
    fn the_partition_sums_to_one_and_stays_within_a_grain() {
        let masses = [3u128 << 60, 1, 7 << 40, 5 << 61, 2];
        let total: u128 = masses.iter().sum();
        let p = partitioned(&masses, total);
        assert_eq!(p.iter().sum::<i128>(), 1i128 << MASS_BITS);
        for (c, &m) in masses.iter().enumerate() {
            let exact = Rat::new(BigInt::from(m) << MASS_BITS, BigInt::from(total));
            let diff = (Rat::from_integer(BigInt::from(p[c])) - exact).abs();
            assert!(diff < Rat::one(), "class {c}");
        }
    }

    /// The box's minimum meets its optimality conditions on instances whose free blocks are
    /// singular, at a vertex, inside, and on an edge; and on a square of two parts that descend
    /// alone and rise together it takes the part whose descent survives the other's.
    #[test]
    fn the_box_minimum_meets_its_optimality_conditions() {
        let instances: Vec<(Vec<Rat>, Vec<Vec<Rat>>)> = vec![
            (vec![rat(-1, 1), rat(-1, 1)], vec![vec![rat(1, 1), rat(1, 1)], vec![rat(1, 1), rat(1, 1)]]),
            (vec![rat(-3, 1), rat(-5, 2)], vec![vec![rat(1, 1), rat(0, 1)], vec![rat(0, 1), rat(2, 1)]]),
            (vec![rat(-1, 3), rat(-1, 4)], vec![vec![rat(2, 1), rat(1, 1)], vec![rat(1, 1), rat(3, 1)]]),
            (vec![rat(1, 1), rat(-1, 1)], vec![vec![rat(1, 1), rat(0, 1)], vec![rat(0, 1), rat(1, 1)]]),
            (vec![rat(0, 1), rat(0, 1)], vec![vec![rat(0, 1), rat(0, 1)], vec![rat(0, 1), rat(0, 1)]]),
            // Two parts that rise together (m(1, 1) = 7/2) while the first alone descends.
            (vec![rat(-3, 1), rat(-2, 1)], vec![vec![rat(4, 1), rat(4, 1)], vec![rat(4, 1), rat(5, 1)]]),
        ];
        for (g, k) in &instances {
            let alpha = box_minimum(g, k).unwrap();
            assert!(optimal(g, k, &alpha), "g {g:?}: α {alpha:?}");
        }
        // The square: α* = (3/4, 0), m = −9/8, below both parts alone and the whole step.
        let (g, k) = &instances[5];
        let alpha = box_minimum(g, k).unwrap();
        assert_eq!(alpha, vec![rat(3, 4), rat(0, 1)]);
        assert_eq!(model_at(g, k, &alpha), rat(-9, 8));
        assert!(model_at(g, k, &[rat(1, 1), rat(1, 1)]) > Rat::zero());
    }

    /// The released scales round to the nearest grain within the box, and a scaled step to the
    /// nearest of its own.
    #[test]
    fn the_scales_release_to_their_grain() {
        let s = released_scales(&[rat(1, 1), rat(0, 1), rat(1, 3), rat(1, 2), rat(2, 3)]).unwrap();
        assert_eq!(s, [1 << 32, 0, 1431655765, 1 << 31, 2863311531]);
        assert_eq!(scaled(1000, 1 << 31).unwrap(), 500);
        assert_eq!(scaled(-3, 1 << 31).unwrap(), -2);
        assert_eq!(on_code_grain(&rat(-9, 8)).unwrap(), -(9i64 << 20) / 8);
    }
}
