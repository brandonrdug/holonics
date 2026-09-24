//! **The reaction: a modulated skew interconnection with a separate passive resistance.**
//!
//! [definition; agent-inferred] The learned reaction of a native receiver reads its current `s`
//! and a contrast `c`. A complex-bilinear `c ⊗ s` block cannot be power-neutral for every complex
//! `c`: neutrality for `c` and `i c` forces each slice to zero
//! (`Holon/Reaction.lean::bilinear_reaction_workless_iff_zero`, from
//! `Holon/Reaction.lean::eq_zero_of_herm_zero`). The power-neutral reaction is instead
//! real-bilinear, `J(c) = Σ_r c_r A_r` over the REAL coordinates `c_r` of `c` (`Re c_k`, `Im c_k`),
//! with every slice skew-Hermitian in the current's unit pairing, so `Re⟨s, J(c)s⟩ = 0` for every
//! `c` (`Holon/Reaction.lean::skewReaction_workless`, `Holon/Reaction.lean::re_herm_skew`). The
//! linear self-relation of the reaction is held passive (its Hermitian part `⪯ 0`, the resistive
//! part, whose power is `−dissipation`).
//!
//! This module supplies the two exact projections a deposit applies to a learned coefficient
//! matrix held at a dyadic grain (integers in units `2^-grain`), so the stored map remains the
//! executed law exactly:
//!
//! 1. [`skew_hermitian_at_grain`]: the skew-Hermitian part `½(W − Wᴴ)`
//!    (`Holon/Reaction.lean::skewPart`, the Frobenius-orthogonal projection,
//!    `Holon/Reaction.lean::skewPart_orthogonal`), rounded on the strict upper triangle and
//!    completed by `A_ji = −conj(A_ij)`, `A_ii ∈ iℤ`. The result is **exactly** skew-Hermitian at
//!    the grain; it differs from `skewPart W` by at most half a grain unit per real coordinate, and
//!    it fixes an already skew-Hermitian matrix (`Holon/Reaction.lean::skewPart_of_skew`).
//! 2. [`passive_complex_at_grain`]: the certified congruence clip of
//!    [`crate::deposition::project_passive`] (`Holon/Deposition.lean::projectPassiveCongruence_passive`)
//!    applied to the realification, then averaged over the complex structure `J` (`R̄ = ½(R + JᵀRJ)`)
//!    so the removed part is complex-linear, rounded to the grain and enlarged by `n` grain units on
//!    the diagonal (`n·ulp ≥ ‖rounding‖₂`), and re-certified by inertia. It fixes passive relations.
//!    [agent-inferred; formal obligation #62] The averaging step — for `L` with `Jᵀ(sym L)J = sym L`
//!    and `sym(L − R) ⪯ 0`, also `sym(L − R̄) ⪯ 0` — is argued in the comment of
//!    [`passive_complex_at_grain`]; its Lean counterpart is owed.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use crate::geometry::Rat;

use crate::deposition::project_passive;
use crate::exact_linear::ExactRatMatrix;
use crate::holon::HolonError;
use crate::inertia::{Inertia, inertia};
use crate::scalar::{matrix, symmetric_part};

/// One complex coefficient at a grain: `(re, im)` integers in units `2^-grain`.
pub type GridComplex = (BigInt, BigInt);

fn square_shape(w: &[Vec<GridComplex>]) -> Result<usize, HolonError> {
    let n = w.len();
    for row in w {
        if row.len() != n {
            return Err(HolonError::Shape {
                what: "reaction slice",
                expected: n,
                found: row.len(),
            });
        }
    }
    Ok(n)
}

/// `Σ |re|² + |im|²` in grain² units.
pub fn frobenius_square(w: &[Vec<GridComplex>]) -> BigInt {
    w.iter().flatten().map(|(re, im)| re * re + im * im).sum()
}

/// `Σ |re| + |im|` in grain units: dominates every entrywise-monotone norm used by the carrier.
pub fn l1(w: &[Vec<GridComplex>]) -> BigInt {
    w.iter().flatten().map(|(re, im)| re.abs() + im.abs()).sum()
}

/// Whether `Wᴴ = −W` exactly.
pub fn is_skew_hermitian(w: &[Vec<GridComplex>]) -> bool {
    let n = w.len();
    (0..n).all(|i| {
        w[i].len() == n && (0..n).all(|j| w[j][i].0 == -&w[i][j].0 && w[j][i].1 == w[i][j].1)
    })
}

/// [definition] The exact skew-Hermitian projection at a grain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SkewProjection {
    /// Exactly skew-Hermitian.
    pub projected: Vec<Vec<GridComplex>>,
    /// `W − projected`: the Hermitian part and the half-unit rounding.
    pub removed: Vec<Vec<GridComplex>>,
}

/// Project one slice onto the skew-Hermitian matrices, exactly at its grain (see the module header).
pub fn skew_hermitian_at_grain(w: &[Vec<GridComplex>]) -> Result<SkewProjection, HolonError> {
    let n = square_shape(w)?;
    let half = |v: BigInt| Rat::new(v, BigInt::from(2)).floor().to_integer();
    let zero = (BigInt::zero(), BigInt::zero());
    let mut projected = vec![vec![zero.clone(); n]; n];
    for i in 0..n {
        // A skew-Hermitian diagonal is purely imaginary.
        projected[i][i] = (BigInt::zero(), w[i][i].1.clone());
        for j in i + 1..n {
            // ½(a − conj b) = ½((a_r − b_r) + i(a_i + b_i)); floor at the grain.
            let re = half(&w[i][j].0 - &w[j][i].0);
            let im = half(&w[i][j].1 + &w[j][i].1);
            projected[j][i] = (-&re, im.clone());
            projected[i][j] = (re, im);
        }
    }
    let removed = (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    (
                        &w[i][j].0 - &projected[i][j].0,
                        &w[i][j].1 - &projected[i][j].1,
                    )
                })
                .collect()
        })
        .collect();
    Ok(SkewProjection { projected, removed })
}

/// The realification on interleaved `(re, im)` coordinates: `z = x + iy ↦ [[x, −y], [y, x]]`
/// (`Holon/Reaction.lean::realify`, up to the coordinate order).
pub fn realify(w: &[Vec<GridComplex>]) -> Result<ExactRatMatrix, HolonError> {
    let n = square_shape(w)?;
    Ok(matrix(2 * n, 2 * n, |r, c| {
        let (x, y) = &w[r / 2][c / 2];
        let value = match (r % 2, c % 2) {
            (0, 0) | (1, 1) => x.clone(),
            (0, 1) => -y,
            _ => y.clone(),
        };
        Rat::from_integer(value)
    })?)
}

/// [definition] The exact passive projection of a complex relation at a grain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComplexPassiveProjection {
    /// `W − removed`, with `Re⟨s, W' s⟩ ≤ 0` for every complex `s` (certified by inertia).
    pub projected: Vec<Vec<GridComplex>>,
    /// Hermitian, positive semidefinite (certified), at the grain.
    pub removed: Vec<Vec<GridComplex>>,
    /// `n₊` of the Hermitian part before projection (realified count / 2).
    pub removed_rank: usize,
    /// The diagonal enlargement paid for rounding the removed part to the grain (grain units).
    pub shift: BigInt,
    /// Inertia of the realified symmetric part of `projected`: `positive == 0`.
    pub certified: Inertia,
}

fn round_nearest(value: &Rat) -> BigInt {
    // floor(x + ½), deterministic.
    let half = Rat::new(BigInt::one(), BigInt::from(2));
    (value + half).floor().to_integer()
}

/// Project a complex relation onto the passive cone, exactly at its grain.
///
/// [agent-inferred] Let `L` be the realification and `R ⪰ 0` the certified congruence clip, so
/// `sym(L − R) ⪯ 0`. `J` (multiplication by `i`) is orthogonal and commutes with `sym L` because
/// `L` is complex-linear. For every `e`, `⟨e,(L − R̄)e⟩ = ½⟨e,(L − R)e⟩ + ½⟨Je,(L − R)Je⟩ ≤ 0`
/// with `R̄ = ½(R + JᵀRJ) ⪰ 0` complex-linear. Rounding `R̄` Hermitian-symmetrically to the grain
/// errs by at most `½` per real coordinate, `‖E‖₂ ≤ ‖E‖_F ≤ n` grain units, so removing
/// `round(R̄) + n·I` keeps `sym ⪯ 0`. The result is re-certified by exact inertia, not trusted.
pub fn passive_complex_at_grain(
    w: &[Vec<GridComplex>],
) -> Result<ComplexPassiveProjection, HolonError> {
    let n = square_shape(w)?;
    let l = realify(w)?;
    let before = inertia(&symmetric_part(&l)?);
    if before.positive == 0 {
        return Ok(ComplexPassiveProjection {
            projected: w.to_vec(),
            removed: vec![vec![(BigInt::zero(), BigInt::zero()); n]; n],
            removed_rank: 0,
            shift: BigInt::zero(),
            certified: before,
        });
    }
    let clip = project_passive(&l)?;
    let r = crate::scalar::form_matrix(&clip.removed);
    let j = matrix(2 * n, 2 * n, |row, column| {
        if row / 2 != column / 2 {
            Rat::zero()
        } else {
            match (row % 2, column % 2) {
                (1, 0) => Rat::one(),
                (0, 1) => -Rat::one(),
                _ => Rat::zero(),
            }
        }
    })?;
    let twirled = r
        .add(&j.transpose()?.multiply(&r)?.multiply(&j)?)?
        .scaled(&Rat::new(BigInt::one(), BigInt::from(2)));
    let at = |row: usize, column: usize| twirled.get(row, column).cloned();
    let shift = BigInt::from(n);
    let mut removed = vec![vec![(BigInt::zero(), BigInt::zero()); n]; n];
    for a in 0..n {
        removed[a][a] = (round_nearest(&at(2 * a, 2 * a)?) + &shift, BigInt::zero());
        for b in a + 1..n {
            let re = round_nearest(&at(2 * a, 2 * b)?);
            let im = round_nearest(&at(2 * a + 1, 2 * b)?);
            removed[b][a] = (re.clone(), -&im);
            removed[a][b] = (re, im);
        }
    }
    let projected: Vec<Vec<GridComplex>> = (0..n)
        .map(|a| {
            (0..n)
                .map(|b| (&w[a][b].0 - &removed[a][b].0, &w[a][b].1 - &removed[a][b].1))
                .collect()
        })
        .collect();
    let certified = inertia(&symmetric_part(&realify(&projected)?)?);
    if certified.positive != 0 {
        return Err(HolonError::NotPassive { inertia: certified });
    }
    let removed_form = inertia(&symmetric_part(&realify(&removed)?)?);
    if removed_form.negative != 0 {
        return Err(HolonError::NotPassive {
            inertia: removed_form,
        });
    }
    Ok(ComplexPassiveProjection {
        projected,
        removed,
        removed_rank: before.positive / 2,
        shift,
        certified,
    })
}

/// Project a complex relation onto the passive cone by the **minimal certified scalar shift**
/// `W' = W − τ I`, `τ` the least grain integer with `herm W − τ I ⪯ 0` (exact inertia bisection
/// between `0` and the Gershgorin bound).
///
/// [agent-inferred; measured] This is the linear-block projection the power-neutral reaction
/// uses. Like [`passive_complex_at_grain`] it is certified passive and fixes a passive relation;
/// unlike it, what it removes is bounded by the active part itself, `‖τI‖₂ = τ ≤ λ_max(herm W)₊ +
/// 1` grain unit, and it keeps the skew part. The certified congruence clip removes
/// `P⁻ᵀ max(D,0) P⁻¹`, which depends on the elimination order and is unbounded relative to
/// `λ_max(herm W)` when the congruence is ill-conditioned: on the learned native reaction blocks it
/// removed a part `~10⁴` times the block (`research/records`, the power-neutral reaction return),
/// leaving a large dissipative block that the explicit incident word amplifies.
pub fn passive_shift_at_grain(
    w: &[Vec<GridComplex>],
) -> Result<ComplexPassiveProjection, HolonError> {
    let n = square_shape(w)?;
    let symmetric = symmetric_part(&realify(w)?)?;
    let before = inertia(&symmetric);
    if before.positive == 0 {
        return Ok(ComplexPassiveProjection {
            projected: w.to_vec(),
            removed: vec![vec![(BigInt::zero(), BigInt::zero()); n]; n],
            removed_rank: 0,
            shift: BigInt::zero(),
            certified: before,
        });
    }
    let passive_at = |tau: &BigInt| -> Result<bool, HolonError> {
        let shifted = crate::scalar::form_matrix(&symmetric)
            .subtract(&ExactRatMatrix::identity(2 * n)?.scaled(&Rat::from_integer(tau.clone())))?;
        Ok(inertia(&crate::scalar::matrix_form(&shifted)?).positive == 0)
    };
    // Gershgorin: λ_max ≤ max_i Σ_j |S_ij|.
    let bound = (0..2 * n)
        .map(|i| {
            (0..2 * n)
                .map(|j| symmetric.at(i, j).abs())
                .fold(Rat::zero(), |a, b| a + b)
        })
        .fold(Rat::zero(), |a, b| if b > a { b } else { a })
        .ceil()
        .to_integer();
    let (mut lo, mut hi) = (BigInt::zero(), bound);
    if !passive_at(&hi)? {
        return Err(HolonError::NotPassive { inertia: before });
    }
    // Invariant: lo is active (λ_max > lo), hi is passive.
    while &hi - &lo > BigInt::one() {
        let mid: BigInt = (&lo + &hi) >> 1usize;
        if passive_at(&mid)? {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    let tau = hi;
    let mut removed = vec![vec![(BigInt::zero(), BigInt::zero()); n]; n];
    let mut projected = w.to_vec();
    for a in 0..n {
        removed[a][a].0 = tau.clone();
        projected[a][a].0 -= &tau;
    }
    let certified = inertia(&symmetric_part(&realify(&projected)?)?);
    if certified.positive != 0 {
        return Err(HolonError::NotPassive { inertia: certified });
    }
    Ok(ComplexPassiveProjection {
        projected,
        removed,
        removed_rank: before.positive / 2,
        shift: tau,
        certified,
    })
}

/// `Re⟨s, W s⟩ = Σ_ij Re(conj(s_i) W_ij s_j)` over ℚ: the power a relation draws at `s`.
pub fn hermitian_power(w: &[Vec<GridComplex>], s: &[(Rat, Rat)]) -> Rat {
    let mut total = Rat::zero();
    for (i, row) in w.iter().enumerate() {
        for (j, (x, y)) in row.iter().enumerate() {
            let (x, y) = (Rat::from_integer(x.clone()), Rat::from_integer(y.clone()));
            // W_ij s_j
            let (vr, vi) = (&x * &s[j].0 - &y * &s[j].1, &x * &s[j].1 + &y * &s[j].0);
            // Re(conj(s_i) v)
            total += &s[i].0 * vr + &s[i].1 * vi;
        }
    }
    total
}

#[cfg(test)]
mod tests {
    use super::*;

    fn grid(rows: &[&[(i64, i64)]]) -> Vec<Vec<GridComplex>> {
        rows.iter()
            .map(|r| {
                r.iter()
                    .map(|(a, b)| (BigInt::from(*a), BigInt::from(*b)))
                    .collect()
            })
            .collect()
    }

    fn lcg(seed: &mut u64) -> i64 {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((*seed >> 33) % 2001) as i64 - 1000
    }

    fn random(n: usize, seed: &mut u64) -> Vec<Vec<GridComplex>> {
        (0..n)
            .map(|_| {
                (0..n)
                    .map(|_| (BigInt::from(lcg(seed)), BigInt::from(lcg(seed))))
                    .collect()
            })
            .collect()
    }

    /// `Holon/Reaction.lean::skewReaction_workless` at the grain: every modulated sum of exactly
    /// skew-Hermitian slices does no work, exactly, for random real-coordinate contrasts.
    #[test]
    fn projected_slices_are_power_neutral_for_every_contrast() {
        let mut seed = 7;
        let slices: Vec<_> = (0..4)
            .map(|_| {
                skew_hermitian_at_grain(&random(6, &mut seed))
                    .unwrap()
                    .projected
            })
            .collect();
        assert!(slices.iter().all(|a| is_skew_hermitian(a)));
        for _ in 0..20 {
            let c: Vec<BigInt> = (0..4).map(|_| BigInt::from(lcg(&mut seed))).collect();
            let j: Vec<Vec<GridComplex>> = (0..6)
                .map(|a| {
                    (0..6)
                        .map(|b| {
                            let mut z = (BigInt::zero(), BigInt::zero());
                            for (k, slice) in slices.iter().enumerate() {
                                z.0 += &c[k] * &slice[a][b].0;
                                z.1 += &c[k] * &slice[a][b].1;
                            }
                            z
                        })
                        .collect()
                })
                .collect();
            let s: Vec<(Rat, Rat)> = (0..6)
                .map(|_| {
                    (
                        Rat::new(lcg(&mut seed).into(), 7.into()),
                        Rat::new(lcg(&mut seed).into(), 3.into()),
                    )
                })
                .collect();
            assert!(hermitian_power(&j, &s).is_zero());
        }
    }

    /// `Holon/Reaction.lean::skewPart_of_skew`: a skew-Hermitian slice is fixed; the removed part
    /// of a Hermitian slice is the whole slice.
    #[test]
    fn the_skew_projection_fixes_skew_and_removes_hermitian() {
        let mut seed = 11;
        let skew = skew_hermitian_at_grain(&random(5, &mut seed))
            .unwrap()
            .projected;
        let again = skew_hermitian_at_grain(&skew).unwrap();
        assert_eq!(again.projected, skew);
        assert!(frobenius_square(&again.removed).is_zero());
        let hermitian = grid(&[&[(3, 0), (1, 2)], &[(1, -2), (-4, 0)]]);
        let p = skew_hermitian_at_grain(&hermitian).unwrap();
        assert!(frobenius_square(&p.projected).is_zero());
        assert_eq!(p.removed, hermitian);
    }

    /// The minimal scalar shift: passive, certified, minimal (`τ − 1` is still active), fixes a
    /// passive relation, keeps the skew part, and removes no more than the Gershgorin bound.
    #[test]
    fn the_minimal_shift_is_passive_minimal_and_bounded() {
        let mut seed = 23;
        for _ in 0..6 {
            let w = random(6, &mut seed);
            let p = passive_shift_at_grain(&w).unwrap();
            assert_eq!(p.certified.positive, 0);
            assert!(p.shift > BigInt::zero());
            let mut less = w.clone();
            for a in 0..6 {
                less[a][a].0 -= &p.shift - BigInt::one();
            }
            assert!(inertia(&symmetric_part(&realify(&less).unwrap()).unwrap()).positive > 0);
            for a in 0..6 {
                for b in 0..6 {
                    if a != b {
                        assert_eq!(p.projected[a][b], w[a][b]);
                    }
                }
            }
            let fixed = passive_shift_at_grain(&p.projected).unwrap();
            assert_eq!(fixed.projected, p.projected);
            assert!(fixed.shift.is_zero());
        }
        // An ill-conditioned block: the congruence clip removes far more than the active part;
        // the shift removes about λ_max(herm W).
        let w = grid(&[&[(1, 0), (1000, 0)], &[(1000, 0), (-1_000_000, 0)]]);
        let clip = passive_complex_at_grain(&w).unwrap();
        let shift = passive_shift_at_grain(&w).unwrap();
        assert!(shift.shift <= BigInt::from(3));
        assert!(l1(&clip.removed) >= l1(&shift.removed));
    }

    /// `Holon/Deposition.lean::projectPassiveCongruence_passive` / `_of_passive` in the complex
    /// chart: the projection is passive for every complex state, certified, fixes a passive
    /// relation, keeps the skew-Hermitian part, and removes a PSD Hermitian part.
    #[test]
    fn the_complex_passive_projection_is_certified_and_fixes_passive() {
        let mut seed = 3;
        for _ in 0..6 {
            let w = random(6, &mut seed);
            let p = passive_complex_at_grain(&w).unwrap();
            assert_eq!(p.certified.positive, 0);
            // Skew part unchanged: removed is Hermitian.
            for a in 0..6 {
                for b in 0..6 {
                    assert_eq!(p.removed[a][b].0, p.removed[b][a].0);
                    assert_eq!(p.removed[a][b].1, -&p.removed[b][a].1);
                }
            }
            for _ in 0..10 {
                let s: Vec<(Rat, Rat)> = (0..6)
                    .map(|_| {
                        (
                            Rat::from_integer(lcg(&mut seed).into()),
                            Rat::from_integer(lcg(&mut seed).into()),
                        )
                    })
                    .collect();
                assert!(hermitian_power(&p.projected, &s) <= Rat::zero());
                assert!(hermitian_power(&p.removed, &s) >= Rat::zero());
            }
            let fixed = passive_complex_at_grain(&p.projected).unwrap();
            assert_eq!(fixed.projected, p.projected);
            assert_eq!(fixed.removed_rank, 0);
        }
    }
}
