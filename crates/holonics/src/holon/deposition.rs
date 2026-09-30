//! **Deposition: the work of a changing constitution, passivity under learning, the passive
//! projection.**
//!
//! [definition] A Holon whose storage `Q` and learned active relation `L` (entering the flow as
//! `(J − R + L) Q x`) change between commits. The committed balance is the word balance at `Θ_k`
//! plus the deposition work `½⟨x⁺, (Q⁺ − Q) x⁺⟩` (`Holon/Deposition.commit_balance`,
//! `Holon/Deposition.deposition_work`), realized by [`crate::holon::law::ReferenceHolon::commit`]. The
//! learned power is the effort form of the rate form, `⟨x, (AᵀQ + QA) x⟩ = 2⟨Qx, L Qx⟩` for
//! `A = LQ` (`Holon/Deposition.learned_rate_form`).
//!
//! [definition] **Passivity-preserving deposition** (`Holon/Deposition.committed_energy_bound`,
//! from `Holon/Deposition.energy_product_bound`): passive words and deposits
//! `Q_(k+1) ⪯ (1 + ε_k) Q_k` bound the committed energy by `∏(1 + ε_k) E_0`. [`CommittedEnergyBound`]
//! certifies each deposit's `ε_k` exactly by inertia and retains only the running product and the
//! initial energy — the quotient the bound needs, never a list of deposits
//! (`Foundation/Standing` retention). The divergence witness
//! (`Holon/Deposition.normal_law_divergence_witness`, `Holon/Deposition.indefiniteBlock`,
//! `Holon/Deposition.divergentState`) grows `×9` per commit.
//!
//! [definition; agent-inferred] **The passive projection, exactly over ℚ.** The Lean
//! `Holon/Deposition.projectPassive` clips the positive eigenvalues of `sym L`
//! (`Holon/Deposition.clipNeg`, spectral theorem over ℝ); those eigenvalues are in general
//! irrational, so that projection has no exact rational value. [`project_passive`] instead clips
//! along an exact congruence `Pᵀ (sym L) P = D` (symmetric elimination with the zero-diagonal
//! branch): `S⁻ = P⁻ᵀ min(D, 0) P⁻¹`, `L' = L − (sym L − S⁻)`. It is exact and satisfies the two
//! properties the bound consumes — `⟨e, L' e⟩ ≤ 0` for every `e`
//! (`Holon/Deposition.projectPassive_passive`) and `L' = L` for passive `L`
//! (`Holon/Deposition.projectPassive_of_passive`) — so the bound is restored exactly as in
//! `Holon/Deposition.projected_committed_energy_bound`. It removes a positive semidefinite
//! term of rank `n₊(sym L)` and keeps the skew part. It is **not** the Frobenius-nearest projection:
//! it equals `clipNeg` when the congruence is orthogonal (e.g. `sym L` diagonal) and depends on the
//! elimination order otherwise.
//!
//! [definition; agent-inferred, September 29] **The certified step** ([`CertifiedStep`]; the
//! [lessons record](../../../../research/records/2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md),
//! lesson 6). A locus steps along a preconditioned direction `Δ` (the unit step: for a normal law
//! `Δ = G X̂`, the covector that reached the locus read through the solved chart of its metric).
//! Along the ray `η ↦ Θ + ηΔ` the score obeys the quadratic upper model
//! `φ(η) ≤ φ(0) − η a + ½ η² C` with `a = ⟨G, Δ⟩` the first-order decrease of the unit step and `C`
//! a certified bound on its curvature along the whole ray. The step is the largest dyadic
//! `η = 2^k` (`k ∈ ℤ`) with `η C ≤ a` (so `η L ≤ 1` for `L = C/a`, the curvature in the locus's own
//! metric) and `η c ≤ 1` (the lattice's covector bound: one return's weighted covector stays
//! unit-scale, the assumption the lattice rule and the chart rule read). It certifies
//! `φ(η) ≤ φ(0) − ½ η a` (Lean `Holon/Deposition.certified_step_descends`). The alignment `a` is
//! computed, never assumed: `a < 0` is refused, `a = 0` moves nothing. The step reads no codec,
//! alphabet or terrain; what it needs from a machine is `a`, `C` and `c`.
//!
//! [definition; agent-inferred] **The curvature a linear locus reads** (Lean
//! `Holon/Deposition.gauss_newton_curvature`, `joint_cauchy_schwarz`). When a locus's outputs `W f_t`
//! reach a receiver's logits linearly, `z_t = A_t(W f_t)`, through gains `‖A_t u‖ ≤ κ‖u‖`, and the
//! receiver's score has curvature at most `s` in its logits, the curvature of the unit step is
//! `C ≤ B s κ² Σ_t w_t |Δ f_t|²`, `B` the loci stepping together (their logit moves add, and
//! `|Σ_(ℓ<B) u_ℓ|² ≤ B Σ_ℓ |u_ℓ|²`). The gain `κ` is certified by the machine's energy law; a learned
//! map's operator bound is read by the Schur test `‖W‖₂² ≤ ‖W‖₁ ‖W‖_∞` ([`schur_norms`]), exact over
//! `ℚ`, and a square root by its dyadic ceiling ([`sqrt_ceiling`], [`root_ceiling`]).
//!
//! [definition; agent-inferred, September 29] **The tightened certificate** (Lean
//! `Holon/Deposition` §9; `hnn::constitution`, "The tightened certificate"). Two of those bounds
//! are sharpened, each by a proved statement:
//! - **The joint moves** ([`JointReading`]; `joint_move_triangle`, `joint_step_descends`). Families
//!   with logit moves per unit step at most `m_ℓ` move the logits by at most `Σ η_ℓ m_ℓ` (the cross
//!   terms by Cauchy–Schwarz on the joint ray), so each family keeps its own curvature `C_ℓ = s κ² b`
//!   (`B = 1`) and the families hold one joint certificate `s (Σ η_ℓ m_ℓ)² ≤ Σ η_ℓ a_ℓ`, which
//!   descends by `½ Σ η_ℓ a_ℓ` through [`CertifiedStep`]'s law (`certified_step_descends`, the joint
//!   term apportioned by decrease).
//! - **The Gram certificate** ([`spectral_norm`]; `gram_certificate_bound`,
//!   `adjoint_gram_certificate_bound`, `entrywise_error_bound`). `‖X‖₂` is bounded on a dyadic face
//!   of the matrix by a rational `μ` with `μ I − G ⪰ 0` decided by exact inertia on the face's
//!   integer Gram, plus the face's entrywise error; the Schur test is the fallback it sharpens.
//!
//! [proved-derived; formal-checked] **An active element's growth** (Lean
//! `Holon/Deposition.active_element_growth`, [`active_growth`]). An element whose storage obeys
//! `½|s′|² − ½|b|² ≤ ⟨x̄, W c⟩`, `x̄ = ½(b + s′)` (the ring element with its passive part dropped,
//! Lean `HNN/Word.reaction_stage_balance`), with `‖W c‖ ≤ ω|c|`, has `|s′| ≤ |b| + ω|c|`; with
//! `|b|, |c| ≤ r` its energy grows by at most `(2ω + ω²) r²`, the factor `(1 + ω)²` on the share
//! `r²` bounds. A learned active relation that cannot be projected passive (the contrast port is
//! passive only at `W_c = 0`, Lean `HNN/Word.contrastPort_active`) enters the committed energy
//! bound through this growth.
//!
//! [definition; agent-inferred, September 29] **A jump certified by the exact comparison**
//! ([`strictly_better`]; Lean `HNN/Normal.{lock_flip_descends, lock_face_decides}`). A move no
//! curvature bounds, a sheet's half-turn at its node (`hnn::constitution`, "The standing's fold"), is
//! certified by reading the score at both ends exactly: it is taken only when the other end's code
//! enclosure lies strictly below the current one's, so the true scores are strictly ordered and the
//! jump descends. The same comparison is the two-state lock's decision: with the sheets' weights
//! `a = 2^(−ℓ_other)` and `K = 2^(−ℓ_current)`, the lock's face `θ = a/(a + K)` exceeds `½` exactly
//! when `a > K`, exactly when `ℓ_other < ℓ_current`.
//!
//! [definition; agent-inferred, September 29] **The pumped medium's span factor** ([`span_factors`];
//! Lean `Holon/Deposition` §10, `HNN/Floquet.floquet_span_reach`). A medium passive but for its
//! active elements carries a difference over a span of `s` ticks with the energy gain
//! `(1 + ω)^(2(s − 1))` of its contrast ports; a ring that is not certified passive (a pumped
//! resonator) carries it with its certified reach `reach_r(s′)` over the ticks `s′ ≤ s` its state
//! holds it (`hnn::ring::FloquetBound::reach`). The two compose by the product of the maps' bounds
//! (`span_transport_compose`); a difference that passes several such rings within the span is
//! carried by each for at most `s` ticks, so its factor is at most
//! `F(s) = ∏_r max_(s′ ≤ s) reach_r(s′)` (`pumped_span_factor`, the running maximum
//! `runningMax`), which does not fall with `s` (`runningMax_mono`). A certified gain `κ²` sums the
//! span gains over its stations and ticks (`station_tick_gain`, Cauchy–Schwarz over the ticks), each
//! multiplied by `F` of its span; the re-entries of one injection at one station add as amplitudes,
//! so their squared sum is multiplied by `F` of the longest span (`entry_span_gain`). The factor
//! reads no codec, alphabet or terrain; what it needs from a machine is each ring's reach.
//!
//! | Lean | Rust |
//! |---|---|
//! | `HNN/Normal.{lock_flip_descends, lock_face_decides}` | [`strictly_better`] |
//! | `certified_step_descends` | [`CertifiedStep`] |
//! | `gauss_newton_curvature`, `joint_cauchy_schwarz` | the curvature `C` a machine supplies (`hnn::constitution`) |
//! | `joint_move_triangle`, `joint_step_descends` | [`JointReading`] |
//! | `gram_certificate_bound`, `adjoint_gram_certificate_bound`, `entrywise_error_bound` | [`spectral_norm`] |
//! | `active_element_growth`, `active_energy_growth` | [`active_growth`] |
//! | `runningMax`, `le_runningMax`, `runningMax_mono`, `pumped_span_factor`, `span_transport_compose`, `station_tick_gain`, `entry_span_gain` | [`span_factors`], and the gains that read them (`hnn::constitution`) |
//! | `learned_rate_form` | [`learned_rate_form`] |
//! | `energy_product_bound`, `committed_energy_bound` | [`CommittedEnergyBound`] |
//! | `projectPassive`, `projectPassive_passive`, `projectPassive_of_passive` | [`project_passive`] |
//! | `symPart`, `quad_symPart` | [`crate::ratio::linear::vector::symmetric_part`] |
//! | `indefiniteBlock`, `divergentState`, `normal_law_divergence_witness` | [`indefinite_block`], [`divergent_state`] |

use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use crate::holon::HolonError;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::{SymmetricForm, inertia};
use crate::ratio::linear::vector::{dot, form_matrix, matrix, matrix_form, symmetric_part};

/// Both sides of `Holon/Deposition.learned_rate_form`: `⟨x, ((LQ)ᵀQ + Q(LQ)) x⟩` and
/// `2⟨Qx, L Qx⟩`.
pub fn learned_rate_form(
    storage: &SymmetricForm,
    learned: &ExactRatMatrix,
    x: &[Rat],
) -> Result<(Rat, Rat), HolonError> {
    let q = form_matrix(storage);
    let a = learned.multiply(&q)?;
    let rate = a.transpose()?.multiply(&q)?.add(&q.multiply(&a)?)?;
    let qx = q.apply(x)?;
    Ok((
        dot(x, &rate.apply(x)?),
        Rat::from_integer(BigInt::from(2)) * dot(&qx, &learned.apply(&qx)?),
    ))
}

/// [definition] **An exact congruence diagonalization** `Pᵀ S P = D`, `P` invertible: symmetric
/// Gaussian elimination with the zero-diagonal branch. Returns `(P, diag D)`.
pub fn congruence_diagonalization(
    form: &SymmetricForm,
) -> Result<(ExactRatMatrix, Vec<Rat>), HolonError> {
    let n = form.extent();
    let mut a: Vec<Vec<Rat>> = (0..n)
        .map(|r| (0..n).map(|c| form.at(r, c).clone()).collect())
        .collect();
    let mut p: Vec<Vec<Rat>> = (0..n)
        .map(|r| {
            (0..n)
                .map(|c| if r == c { Rat::one() } else { Rat::zero() })
                .collect()
        })
        .collect();
    for k in 0..n {
        if a[k][k].is_zero() {
            if let Some(j) = (k + 1..n).find(|j| !a[*j][*j].is_zero()) {
                a.swap(k, j);
                for row in a.iter_mut() {
                    row.swap(k, j);
                }
                for row in p.iter_mut() {
                    row.swap(k, j);
                }
            } else if let Some(j) = (k + 1..n).find(|j| !a[k][*j].is_zero()) {
                // col_k += col_j and row_k += row_j: A[k][k] becomes 2A[k][j] ≠ 0.
                for row in a.iter_mut() {
                    let add = row[j].clone();
                    row[k] += add;
                }
                let row_j = a[j].clone();
                for (entry, add) in a[k].iter_mut().zip(row_j) {
                    *entry += add;
                }
                for row in p.iter_mut() {
                    let add = row[j].clone();
                    row[k] += add;
                }
            } else {
                continue;
            }
        }
        let pivot = a[k][k].clone();
        for i in k + 1..n {
            let c = &a[i][k] / &pivot;
            if c.is_zero() {
                continue;
            }
            let row_k = a[k].clone();
            for (entry, sub) in a[i].iter_mut().zip(&row_k) {
                *entry -= &c * sub;
            }
            for row in a.iter_mut() {
                let sub = &c * &row[k];
                row[i] -= sub;
            }
            for row in p.iter_mut() {
                let sub = &c * &row[k];
                row[i] -= sub;
            }
        }
    }
    let diagonal: Vec<Rat> = (0..n).map(|k| a[k][k].clone()).collect();
    let p = matrix(n, n, |r, c| p[r][c].clone())?;
    // The congruence is certified, not trusted.
    let check = p.transpose()?.multiply(&form_matrix(form))?.multiply(&p)?;
    if check != ExactRatMatrix::from_diagonal(diagonal.clone())? {
        return Err(HolonError::Singular {
            what: "the congruence certificate",
        });
    }
    Ok((p, diagonal))
}

/// [definition] **The exact passive projection** of an active relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassiveProjection {
    /// `L' = L − removed`, with `⟨e, L' e⟩ ≤ 0`.
    pub projected: ExactRatMatrix,
    /// `sym L − S⁻ = P⁻ᵀ max(D, 0) P⁻¹ ⪰ 0`.
    pub removed: SymmetricForm,
    /// `n₊(sym L)`, the rank of the removed term.
    pub removed_rank: usize,
}

/// Project an active relation onto the passive cone along an exact congruence (see the module
/// header for what is exact and how it relates to the spectral `clipNeg`).
pub fn project_passive(learned: &ExactRatMatrix) -> Result<PassiveProjection, HolonError> {
    let symmetric = symmetric_part(learned)?;
    let (p, diagonal) = congruence_diagonalization(&symmetric)?;
    let n = diagonal.len();
    let positive: Vec<Rat> = diagonal
        .iter()
        .map(|d| {
            if d.is_positive() {
                d.clone()
            } else {
                Rat::zero()
            }
        })
        .collect();
    let removed_rank = positive.iter().filter(|d| !d.is_zero()).count();
    let removed = if removed_rank == 0 {
        ExactRatMatrix::zero(n, n)?
    } else {
        let inverse = p.inverse()?;
        inverse
            .transpose()?
            .multiply(&ExactRatMatrix::from_diagonal(positive)?)?
            .multiply(&inverse)?
    };
    let projected = learned.subtract(&removed)?;
    let clipped = inertia(&symmetric_part(&projected)?);
    if clipped.positive != 0 {
        return Err(HolonError::NotPassive { inertia: clipped });
    }
    Ok(PassiveProjection {
        projected,
        removed: matrix_form(&removed)?,
        removed_rank,
    })
}

/// [definition] **One committed reading of the deposit bound.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundReading {
    /// `∏_(k<n) (1 + ε_k)`.
    pub product: Rat,
    /// `∏ (1 + ε_k) · E_0`.
    pub bound: Rat,
    /// The committed energy `E_n`.
    pub energy: Rat,
    /// `E_n ≤ ∏ (1 + ε_k) E_0`.
    pub holds: bool,
}

/// [definition] **The committed energy bound** (`Holon/Deposition.committed_energy_bound`): the
/// initial energy and the running product `∏(1 + ε_k)`; each deposit's `ε_k` is certified by
/// `(1 + ε_k) Q_k − Q_(k+1) ⪰ 0` before it enters the product.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommittedEnergyBound {
    initial_energy: Rat,
    product: Rat,
    commits: u64,
}

impl CommittedEnergyBound {
    pub fn new(initial_energy: Rat) -> Self {
        Self {
            initial_energy,
            product: Rat::one(),
            commits: 0,
        }
    }

    pub fn product(&self) -> &Rat {
        &self.product
    }

    pub fn commits(&self) -> u64 {
        self.commits
    }

    /// Certify `Q_(k+1) ⪯ (1 + ε) Q_k` with `1 + ε ≥ 0`.
    pub fn certify_deposit(
        before: &SymmetricForm,
        after: &SymmetricForm,
        epsilon: &Rat,
    ) -> Result<(), HolonError> {
        let growth = Rat::one() + epsilon;
        if growth.is_negative() {
            return Err(HolonError::NegativeGrowth);
        }
        let slack = form_matrix(before)
            .scaled(&growth)
            .subtract(&form_matrix(after))?;
        let reading = inertia(&matrix_form(&slack)?);
        if slack.rows() > 0 && reading.negative > 0 {
            return Err(HolonError::DepositExceedsBound { inertia: reading });
        }
        Ok(())
    }

    /// Record one commit: certify the deposit, advance the product, and read the bound against the
    /// committed energy.
    pub fn commit(
        &mut self,
        before: &SymmetricForm,
        after: &SymmetricForm,
        epsilon: &Rat,
        committed_energy: Rat,
    ) -> Result<BoundReading, HolonError> {
        Self::certify_deposit(before, after, epsilon)?;
        self.product = &self.product * (Rat::one() + epsilon);
        self.commits += 1;
        let bound = &self.product * &self.initial_energy;
        Ok(BoundReading {
            product: self.product.clone(),
            holds: committed_energy <= bound,
            bound,
            energy: committed_energy,
        })
    }
}

// -------------------------------------------------------------------------------------------
// the certified step

/// `⌊log₂ q⌋` of a positive rational: the largest `k ∈ ℤ` with `2^k ≤ q`.
fn floor_log2(q: &Rat) -> i64 {
    let (p, r) = (q.numer().magnitude(), q.denom().magnitude());
    let k = p.bits() as i64 - r.bits() as i64;
    let at_least = if k >= 0 {
        *p >= (r << k as usize)
    } else {
        (p << (-k) as usize) >= *r
    };
    if at_least { k } else { k - 1 }
}

/// `x^k` for a natural `k`.
pub fn power(x: &Rat, k: u64) -> Rat {
    let mut result = Rat::one();
    for _ in 0..k {
        result *= x;
    }
    result
}

/// `2^k` for `k ∈ ℤ`.
pub fn dyadic(k: i64) -> Rat {
    if k >= 0 {
        Rat::from_integer(BigInt::one() << k as usize)
    } else {
        Rat::new(BigInt::one(), BigInt::one() << (-k) as usize)
    }
}

/// [definition; agent-inferred] **The certified step** (module header, "The certified step"): the
/// unit step's first-order decrease `a = ⟨G, Δ⟩`, its certified curvature `C` along the ray, the
/// lattice's covector scale `c`, and the largest dyadic `η = 2^k` with `η C ≤ a` and `η c ≤ 1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertifiedStep {
    /// `k`: the step is `2^k`.
    pub exponent: i64,
    /// `η = 2^k`.
    pub step: Rat,
    /// `a = ⟨G, Δ⟩ > 0`.
    pub alignment: Rat,
    /// `C ≥ 0`, the certified curvature of the unit step along the ray.
    pub curvature: Rat,
    /// `c ≥ 0`, the largest weighted covector entry of one return.
    pub covector: Rat,
}

impl CertifiedStep {
    /// **Certify a step**: refused when `a < 0` (the preconditioned direction does not descend the
    /// covector that reached the locus) or when `C` or `c` is negative; `None` when `a = 0` (nothing
    /// descends, nothing moves); otherwise the largest dyadic step both bounds admit.
    pub fn certify(
        alignment: &Rat,
        curvature: &Rat,
        covector: &Rat,
    ) -> Result<Option<Self>, HolonError> {
        if alignment.is_negative() {
            return Err(HolonError::Misaligned {
                alignment: alignment.clone(),
            });
        }
        for (what, value) in [
            ("a step's curvature", curvature),
            ("a covector's scale", covector),
        ] {
            if value.is_negative() {
                return Err(HolonError::Negative {
                    what,
                    value: value.clone(),
                });
            }
        }
        if alignment.is_zero() {
            return Ok(None);
        }
        let bounds: Vec<i64> = [
            (!curvature.is_zero()).then(|| floor_log2(&(alignment / curvature))),
            (!covector.is_zero()).then(|| floor_log2(&(Rat::one() / covector))),
        ]
        .into_iter()
        .flatten()
        .collect();
        // `a > 0` comes from a nonzero covector, so the covector bound is present; a curvature and
        // a covector both zero would leave the step undetermined.
        let exponent = bounds.into_iter().min().ok_or(HolonError::Unsupported {
            what: "a certified step",
            reason: "a positive alignment with neither a curvature nor a covector scale",
        })?;
        Ok(Some(Self {
            exponent,
            step: dyadic(exponent),
            alignment: alignment.clone(),
            curvature: curvature.clone(),
            covector: covector.clone(),
        }))
    }

    /// **Whether a curvature bound read at the step's own ray still certifies it**: `η C′ ≤ a`
    /// (the fixed point a machine iterates when its curvature depends on the steps taken).
    pub fn admits(&self, curvature: &Rat) -> bool {
        &self.step * curvature <= self.alignment
    }

    /// **The step halved** (`k − 1`), the projection a machine takes when the curvature read at the
    /// step's own ray exceeds what the step certified.
    pub fn halved(&self) -> Self {
        Self {
            exponent: self.exponent - 1,
            step: dyadic(self.exponent - 1),
            ..self.clone()
        }
    }

    /// Both bounds at the step: `η C ≤ a` and `η c ≤ 1`.
    pub fn holds(&self) -> bool {
        self.admits(&self.curvature) && &self.step * &self.covector <= Rat::one()
    }

    /// **The certified decrease** `½ η a` (Lean `certified_step_descends`): the score falls by at
    /// least this much along the step.
    pub fn decrease(&self) -> Rat {
        &self.step * &self.alignment / Rat::from_integer(BigInt::from(2))
    }
}

/// **The Schur test's two norms** of a matrix: `‖W‖₁` (the largest absolute column sum) and
/// `‖W‖_∞` (the largest absolute row sum), so `‖W‖₂² ≤ ‖W‖₁ ‖W‖_∞`, exactly over `ℚ`.
pub fn schur_norms(matrix: &ExactRatMatrix) -> (Rat, Rat) {
    let (rows, columns) = (matrix.rows(), matrix.columns());
    let entries = matrix.entries();
    let mut column_sums = vec![Rat::zero(); columns];
    let mut row_max = Rat::zero();
    for i in 0..rows {
        let mut row_sum = Rat::zero();
        for (j, sum) in column_sums.iter_mut().enumerate() {
            let value = &entries[i * columns + j];
            if !value.is_zero() {
                let magnitude = value.abs();
                row_sum += &magnitude;
                *sum += magnitude;
            }
        }
        if row_sum > row_max {
            row_max = row_sum;
        }
    }
    let column_max = column_sums.into_iter().max().unwrap_or_else(Rat::zero);
    (column_max, row_max)
}

/// **The dyadic ceiling of a square root** at grain `2^(−p)`: the least `m·2^(−p)` with
/// `(m·2^(−p))² ≥ x`, for `x ≥ 0`; an upper bound on `√x` within `2^(−p)` of it.
pub fn sqrt_ceiling(x: &Rat, grain: u32) -> Rat {
    if !x.is_positive() {
        return Rat::zero();
    }
    // m = ⌈√(x·4^p)⌉ = ⌈√⌈x·4^p⌉⌉ over the integers.
    let scaled = (x * Rat::from_integer(BigInt::one() << (2 * grain as usize)))
        .ceil()
        .to_integer();
    let magnitude = scaled.magnitude();
    let mut root = magnitude.sqrt();
    if &(&root * &root) < magnitude {
        root += 1u32;
    }
    Rat::new(BigInt::from(root), BigInt::one() << grain as usize)
}

/// **A nonnegative rational's dyadic face at `bits` significant bits**, rounded down (`up = false`)
/// or up: the nearest `m·2^e` below or above `x` with `2^(bits−1) ≤ m < 2^bits`, exact, with zero
/// its own face. A certificate reads its decrease at the floor and its curvature at the ceiling, so
/// `η C⁺ ≤ a⁻` implies `η C ≤ a`, and the products it takes stay within a few hundred bits whatever
/// the exact readings' own (module header, "The certified step").
pub fn significant(x: &Rat, bits: u32, up: bool) -> Rat {
    if !x.is_positive() {
        return Rat::zero();
    }
    let shift = i64::from(bits) - 1 - floor_log2(x);
    let scaled = x * dyadic(shift);
    let mantissa = if up {
        scaled.ceil().to_integer()
    } else {
        scaled.floor().to_integer()
    };
    Rat::from_integer(mantissa) * dyadic(-shift)
}

/// **A dyadic upper root at a relative grain**: the least `m·2^(−p)` with `(m·2^(−p))² ≥ x`, at the
/// grain `p = 32 − ⌊log₂ x⌋/2` (so within `√x · 2^(−31)` of `√x`, whatever its magnitude), for
/// `x ≥ 0` ([`sqrt_ceiling`]).
pub fn root_ceiling(x: &Rat) -> Rat {
    if !x.is_positive() {
        return Rat::zero();
    }
    let grain = (32 - floor_log2(x).div_euclid(2)).max(0);
    sqrt_ceiling(x, u32::try_from(grain).expect("a grain below 2^32"))
}

/// [definition; agent-inferred, September 29] **A certified spectral norm** `ρ ≥ ‖X‖₂` (module
/// header, "The tightened certificate"; Lean `Holon/Deposition.{gram_certificate_bound,
/// adjoint_gram_certificate_bound, entrywise_error_bound}`). `X` is read on a dyadic face: each entry
/// at the grain `2^e`, `e = ⌊log₂ max|x|⌋ − 30`, as the nearest integer `N_ij`, so `X = 2^e N + E`
/// with `|E_ij| ≤ 2^(e−1)` and `‖E‖₂ ≤ 2^(e−1) √(rows · columns)` (zero when the face is exact). The
/// Gram `G` of `N`'s smaller side (`N Nᵀ` or `NᵀN`, whose largest eigenvalue is `‖N‖₂²` either way)
/// is formed over the integers, and a rational `λ` is taken only when `λ I − G ⪰ 0` is decided by
/// exact inertia (Sylvester's law, `ratio::linear::inertia`), so `|Nv|² ≤ λ|v|²` for every `v`; then
/// `ρ = 2^e (√λ + ½ √(rows · columns))` at their dyadic ceilings. The candidates are guessed, never
/// trusted: the Rayleigh quotient of a few power steps from the widest diagonal (a lower bound of the
/// largest eigenvalue) raised by `2^(−6)`, then `2^(−4)`, `2^(−2)`, `2^0`, `2^1`, …; the first the
/// inertia certifies is taken, and the Schur test `‖N‖₁‖N‖_∞` (the bound it sharpens) when none
/// below it is. Zero for the zero matrix.
pub fn spectral_norm(rows: usize, columns: usize, entries: &[Rat]) -> Rat {
    use crate::ratio::linear::vector::integer_dot;
    // The face's grain from the entries' bit lengths (`2^(b(p) − b(q) − 1) ≤ |p/q| < 2^(b(p) − b(q) + 1)`);
    // any grain is sound, the grain sets only the face's precision.
    let Some(widest) = entries
        .iter()
        .filter(|x| !x.is_zero())
        .map(|x| x.numer().bits() as i64 - x.denom().bits() as i64)
        .max()
    else {
        return Rat::zero();
    };
    if rows == 0 || columns == 0 {
        return Rat::zero();
    }
    // The dyadic face: `N_ij` the nearest integer to `x_ij / 2^e`.
    let exponent = widest - 16;
    let unit = dyadic(exponent);
    let mut exact = true;
    let numerators: Vec<BigInt> = entries
        .iter()
        .map(|x| {
            // `x / 2^e = p / q` on the raw pair (no normalization), and its nearest integer.
            let (p, q) = if exponent <= 0 {
                (x.numer() << (-exponent) as usize, x.denom().clone())
            } else {
                (x.numer().clone(), x.denom() << exponent as usize)
            };
            let quotient = &p / &q;
            let remainder = &p - &quotient * &q;
            if remainder.is_zero() {
                return quotient;
            }
            exact = false;
            if remainder.magnitude() * 2u32 >= *q.magnitude() {
                quotient + p.signum()
            } else {
                quotient
            }
        })
        .collect();
    // The Schur test on the face: the bound this sharpens, taken when no candidate below it is
    // certified.
    let mut column_sums = vec![BigInt::zero(); columns];
    let mut row_widest = BigInt::zero();
    for row in numerators.chunks(columns) {
        let mut sum = BigInt::zero();
        for (total, value) in column_sums.iter_mut().zip(row) {
            let magnitude = value.abs();
            sum += &magnitude;
            *total += magnitude;
        }
        if sum > row_widest {
            row_widest = sum;
        }
    }
    let upper = Rat::from_integer(column_sums.into_iter().max().unwrap_or_default() * row_widest);
    // The Gram of the face's smaller side, over the integers.
    let lines: Vec<Vec<BigInt>> = if rows <= columns {
        numerators.chunks(columns).map(<[BigInt]>::to_vec).collect()
    } else {
        (0..columns)
            .map(|j| {
                (0..rows)
                    .map(|i| numerators[i * columns + j].clone())
                    .collect()
            })
            .collect()
    };
    let n = lines.len();
    let mut gram = vec![vec![BigInt::zero(); n]; n];
    for i in 0..n {
        for j in i..n {
            let value = integer_dot(&lines[i], &lines[j]);
            gram[j][i] = value.clone();
            gram[i][j] = value;
        }
    }
    // A lower bound of the largest eigenvalue: the Rayleigh quotient of a few power steps from the
    // widest diagonal entry, each iterate shifted to 64 significant bits (any vector's quotient is a
    // lower bound, so the shift is only a guess's grain).
    let start = (0..n).max_by_key(|&i| gram[i][i].clone()).unwrap_or(0);
    let mut vector: Vec<BigInt> = (0..n)
        .map(|i| {
            if i == start {
                BigInt::one()
            } else {
                BigInt::zero()
            }
        })
        .collect();
    for _ in 0..16 {
        let next: Vec<BigInt> = gram.iter().map(|row| integer_dot(row, &vector)).collect();
        let bits = next.iter().map(BigInt::bits).max().unwrap_or(0);
        let shift = bits.saturating_sub(64);
        vector = next.into_iter().map(|x| x >> shift).collect();
    }
    let applied: Vec<BigInt> = gram.iter().map(|row| integer_dot(row, &vector)).collect();
    let norm = integer_dot(&vector, &vector);
    let diagonal = Rat::from_integer(gram[start][start].clone());
    let lower = if norm.is_zero() {
        diagonal
    } else {
        Rat::new(integer_dot(&vector, &applied), norm).max(diagonal)
    };
    // `λ I − G ⪰ 0`, decided by exact inertia on `λ_num I − λ_den G`.
    let dominates = |lambda: &Rat| -> bool {
        let (numerator, denominator) = (lambda.numer(), lambda.denom());
        let form: Vec<Vec<Rat>> = (0..n)
            .map(|i| {
                (0..n)
                    .map(|j| {
                        let entry = -(denominator * &gram[i][j]);
                        Rat::from_integer(if i == j { entry + numerator } else { entry })
                    })
                    .collect()
            })
            .collect();
        SymmetricForm::from_rows(form).is_ok_and(|form| inertia(&form).negative == 0)
    };
    let mut bound = upper.clone();
    for raise in [-6i64, -4, -2, 0, 1, 2, 3, 4, 5, 6] {
        let candidate = significant(&(&lower * (Rat::one() + dyadic(raise))), 24, true);
        if candidate >= upper {
            break;
        }
        if dominates(&candidate) {
            bound = candidate;
            break;
        }
    }
    let error = if exact {
        Rat::zero()
    } else {
        root_ceiling(&Rat::from_integer(BigInt::from(rows * columns)))
            / Rat::from_integer(BigInt::from(2))
    };
    (root_ceiling(&bound) + error) * unit
}

/// [definition; agent-inferred, September 29] **The joint certificate** (module header, "The
/// tightened certificate"; Lean `Holon/Deposition.{joint_move_triangle, joint_step_descends}`):
/// families stepping together by `η_ℓ`, each with its unit step's first-order decrease `a_ℓ` and a
/// bound `m_ℓ` on its logit move along its whole ray, move the logits by at most `Σ η_ℓ m_ℓ` (the
/// triangle: the cross terms by Cauchy–Schwarz on the joint ray), so the joint curvature term is at
/// most `s(Σ η_ℓ m_ℓ)²`; when it is at most the first-order decrease `Σ η_ℓ a_ℓ`, the score falls by
/// at least `½ Σ η_ℓ a_ℓ` (through `certified_step_descends`, with the joint curvature apportioned to
/// the families by their decreases).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointReading {
    /// `s (Σ η_ℓ m_ℓ)²`: the joint curvature term.
    pub curvature: Rat,
    /// `Σ η_ℓ a_ℓ`: the first-order decrease.
    pub decrease: Rat,
}

impl JointReading {
    /// The reading at a score curvature `s` over `(η_ℓ, a_ℓ, m_ℓ)`.
    pub fn read<'a>(
        curvature: &Rat,
        terms: impl IntoIterator<Item = (&'a Rat, &'a Rat, &'a Rat)>,
    ) -> Self {
        let (mut moves, mut decrease) = (Rat::zero(), Rat::zero());
        for (step, alignment, bound) in terms {
            moves += step * bound;
            decrease += step * alignment;
        }
        Self {
            curvature: curvature * &moves * &moves,
            decrease,
        }
    }

    /// [definition; agent-inferred, September 29] **A score beside the logits' joins the joint
    /// term** (Lean `HNN/BankFace.joint_descends_beside`): a comparison read beside the logits (the
    /// receiving bank's face, `hnn::constitution`, "The bank's learning path") whose own score moves
    /// by at most its first-order decrease plus an endpoint term `Q_b` along the families' rays adds
    /// `Q_b` to the joint curvature term; its decrease is already in each family's alignment. The
    /// joint certificate `s (Σ η m)² + Q_b ≤ Σ η a` then descends by `½ Σ η a`.
    pub fn beside(mut self, term: &Rat) -> Self {
        self.curvature += term;
        self
    }

    /// `s (Σ η m)² ≤ Σ η a` (the beside term included).
    pub fn holds(&self) -> bool {
        self.curvature <= self.decrease
    }

    /// **The certified decrease** `½ Σ η a` (Lean `joint_step_descends`).
    pub fn certified_decrease(&self) -> Rat {
        &self.decrease / Rat::from_integer(BigInt::from(2))
    }
}

/// [definition; agent-inferred, September 29] **The exact comparison that certifies a jump**
/// (module header, "A jump certified by the exact comparison"; Lean
/// `HNN/Normal.{lock_flip_descends, lock_face_decides}`): the other configuration's code
/// enclosure lies strictly below the current one's, `ℓ_other⁺ < ℓ_current⁻`, so every score the
/// two enclosures hold is strictly ordered. Equal or overlapping enclosures decide nothing, and
/// the jump is not taken.
pub fn strictly_better(current: &ExactInterval, other: &ExactInterval) -> bool {
    other.upper < current.lower
}

/// **An active element's growth factor** `(1 + ω)²` (module header; Lean
/// `active_element_growth`, `active_energy_growth`): the most an element with an active relation of
/// operator bound `ω` multiplies the energy share it reads in one step.
pub fn active_growth(bound: &Rat) -> Rat {
    let one_plus = Rat::one() + bound;
    &one_plus * &one_plus
}

/// [definition; agent-inferred, September 29] **The pumped medium's span factors** `F(0..=S)`
/// (module header, "The pumped medium's span factor"; Lean `Holon/Deposition.{runningMax,
/// le_runningMax, runningMax_mono, pumped_span_factor}`): from each ring's reach over the spans
/// `0..=S` (`reaches[r][s]`, each `≥ 0`), `F(s) = ∏_r max_(s′ ≤ s) reach_r(s′)`, exact and
/// nondecreasing in `s`. With no ring every factor is one. Each ring's table must cover the span.
pub fn span_factors(reaches: &[Vec<Rat>], span: usize) -> Vec<Rat> {
    let mut factors = vec![Rat::one(); span + 1];
    for reach in reaches {
        assert!(
            reach.len() > span,
            "a ring's reach covers every span the factor reads"
        );
        let mut running = Rat::zero();
        for (factor, value) in factors.iter_mut().zip(reach) {
            if *value > running {
                running = value.clone();
            }
            *factor *= &running;
        }
    }
    factors
}

/// `diag(1, −1)`, the indefinite normal-law block (`Holon/Deposition.indefiniteBlock`).
pub fn indefinite_block() -> ExactRatMatrix {
    ExactRatMatrix::from_diagonal(vec![Rat::one(), -Rat::one()])
        .expect("a two-entry diagonal is a declared shape")
}

/// `(3ⁿ, 0)` (`Holon/Deposition.divergentState`).
pub fn divergent_state(n: u32) -> Vec<Rat> {
    vec![Rat::from_integer(BigInt::from(3).pow(n)), Rat::zero()]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::integer;
    use crate::ratio::linear::vector::{integer_matrix, ints};
    use crate::ratio::rat;

    #[test]
    fn the_congruence_handles_the_zero_diagonal_branch() {
        let hyperbolic = SymmetricForm::from_integers(&[vec![0, 1], vec![1, 0]]).unwrap();
        let (_, diagonal) = congruence_diagonalization(&hyperbolic).unwrap();
        assert_eq!(diagonal.iter().filter(|d| d.is_positive()).count(), 1);
        assert_eq!(diagonal.iter().filter(|d| d.is_negative()).count(), 1);
    }

    /// `Holon/Deposition.projectPassive_passive`, `Holon/Deposition.projectPassive_of_passive`.
    #[test]
    fn the_projection_is_passive_and_fixes_passive_relations() {
        let learned = integer_matrix(&[&[1, 3, 0], &[-1, -2, 2], &[0, 0, 1]]).unwrap();
        let projection = project_passive(&learned).unwrap();
        assert!(inertia(&symmetric_part(&projection.projected).unwrap()).positive == 0);
        assert_eq!(
            projection.removed_rank,
            inertia(&symmetric_part(&learned).unwrap()).positive
        );
        // The skew part is kept.
        let skew = |m: &ExactRatMatrix| m.subtract(&m.transpose().unwrap()).unwrap();
        assert_eq!(skew(&projection.projected), skew(&learned));
        // A passive relation is fixed.
        let passive = integer_matrix(&[&[-2, 1], &[-1, -1]]).unwrap();
        assert_eq!(project_passive(&passive).unwrap().projected, passive);
        // Diagonal symmetric part: the congruence is orthogonal, so it is the spectral clipNeg.
        assert_eq!(
            project_passive(&indefinite_block()).unwrap().projected,
            ExactRatMatrix::from_diagonal(vec![integer(0), integer(-1)]).unwrap()
        );
    }

    /// `Holon/Deposition.learned_rate_form` on the witness: the rate form `2W` is indefinite.
    #[test]
    fn the_learned_rate_form_is_twice_the_effort_power() {
        let q = SymmetricForm::from_integers(&[vec![2, 1], vec![1, 3]]).unwrap();
        let l = integer_matrix(&[&[1, 4], &[0, -2]]).unwrap();
        let (left, right) = learned_rate_form(&q, &l, &ints(&[3, -1])).unwrap();
        assert_eq!(left, right);
        let identity = SymmetricForm::from_integers(&[vec![1, 0], vec![0, 1]]).unwrap();
        let (up, _) = learned_rate_form(&identity, &indefinite_block(), &ints(&[1, 0])).unwrap();
        let (down, _) = learned_rate_form(&identity, &indefinite_block(), &ints(&[0, 1])).unwrap();
        assert!(up > Rat::zero() && down < Rat::zero());
    }

    #[test]
    fn floor_log2_is_the_largest_dyadic_below() {
        for (q, k) in [
            (integer(1), 0),
            (rat(3, 5), -1),
            (integer(8), 3),
            (integer(7), 2),
            (rat(1, 8), -3),
            (rat(1, 7), -3),
        ] {
            assert_eq!(floor_log2(&q), k, "{q}");
            assert!(dyadic(k) <= q && q < dyadic(k + 1));
        }
    }

    /// `Holon/Deposition.certified_step_descends`: the largest dyadic step under `ηC ≤ a` and
    /// `ηc ≤ 1`, and its half decrease on the exact quadratic model, which the next dyadic breaks.
    #[test]
    fn the_certified_step_is_the_largest_dyadic_under_both_bounds() {
        let (a, curvature) = (integer(3), integer(5));
        let step = CertifiedStep::certify(&a, &curvature, &rat(1, 4))
            .unwrap()
            .unwrap();
        assert_eq!((step.exponent, step.step.clone()), (-1, rat(1, 2)));
        assert!(step.holds());
        assert_eq!(step.decrease(), rat(3, 4));
        let model = |eta: &Rat| -(eta * &a) + eta * eta * &curvature / integer(2);
        assert!(model(&step.step) <= -step.decrease());
        let doubled = dyadic(step.exponent + 1);
        assert!(model(&doubled) > -(&doubled * &a / integer(2)));
        // The covector bound binds when the curvature is zero.
        let bound = CertifiedStep::certify(&a, &Rat::zero(), &integer(3))
            .unwrap()
            .unwrap();
        assert_eq!(bound.step, rat(1, 4));
        // A curvature read at the ray's end past what the step certified halves it.
        assert!(!step.admits(&integer(7)));
        assert!(step.halved().admits(&integer(7)));
        // Misalignment is refused, zero alignment moves nothing, negative bounds are refused.
        assert!(matches!(
            CertifiedStep::certify(&integer(-1), &curvature, &Rat::one()),
            Err(HolonError::Misaligned { .. })
        ));
        assert_eq!(
            CertifiedStep::certify(&Rat::zero(), &curvature, &Rat::one()),
            Ok(None)
        );
        assert!(matches!(
            CertifiedStep::certify(&a, &integer(-1), &Rat::one()),
            Err(HolonError::Negative { .. })
        ));
    }

    /// A dyadic face at a few significant bits encloses its value: `1/3` at 4 bits lies in
    /// `[10/32, 11/32]`, a dyadic value is its own face, and zero stays zero.
    #[test]
    fn the_significant_face_encloses_its_value() {
        assert_eq!(significant(&rat(1, 3), 4, false), rat(10, 32));
        assert_eq!(significant(&rat(1, 3), 4, true), rat(11, 32));
        assert_eq!(significant(&rat(3, 8), 4, true), rat(3, 8));
        assert_eq!(significant(&integer(5), 2, true), integer(6));
        assert_eq!(significant(&integer(5), 2, false), integer(4));
        assert_eq!(significant(&Rat::zero(), 8, true), Rat::zero());
        let x = rat(22, 7);
        assert!(significant(&x, 64, false) <= x && x <= significant(&x, 64, true));
    }

    #[test]
    fn the_square_root_ceiling_is_the_least_dyadic_upper_root() {
        let root = sqrt_ceiling(&integer(2), 4);
        assert_eq!(root, rat(23, 16));
        assert!(&root * &root >= integer(2) && rat(22, 16) * rat(22, 16) < integer(2));
        assert_eq!(sqrt_ceiling(&rat(9, 4), 0), integer(2));
        assert_eq!(sqrt_ceiling(&rat(9, 4), 1), rat(3, 2));
        assert_eq!(sqrt_ceiling(&Rat::zero(), 8), Rat::zero());
    }

    /// The Schur test `‖W‖₂² ≤ ‖W‖₁‖W‖_∞` and the active growth `(1 + ω)²`
    /// (`Holon/Deposition.active_energy_growth`).
    #[test]
    fn the_schur_norms_and_the_active_growth() {
        let w = integer_matrix(&[&[1, -2], &[3, 0]]).unwrap();
        assert_eq!(schur_norms(&w), (integer(4), integer(3)));
        // ‖W‖₂² is the largest root of λ² − 14λ + 36 (WᵀW = [[10, −2], [−2, 4]]); it is below
        // 12 because 12² − 14·12 + 36 > 0 and 12 > 7, the roots' midpoint.
        assert!(integer(144) - integer(168) + integer(36) > Rat::zero());
        assert_eq!(active_growth(&rat(1, 2)), rat(9, 4));
        assert_eq!(active_growth(&Rat::zero()), Rat::one());
    }

    /// `ρ² I − XᵀX ⪰ 0`, decided exactly: the bound [`spectral_norm`] returns certifies `X`.
    fn certifies(x: &ExactRatMatrix, rho: &Rat) -> bool {
        let gram = x.transpose().unwrap().multiply(x).unwrap();
        let n = gram.rows();
        let slack = ExactRatMatrix::identity(n)
            .unwrap()
            .scaled(&(rho * rho))
            .subtract(&gram)
            .unwrap();
        inertia(&matrix_form(&slack).unwrap()).negative == 0
    }

    /// Lean `Holon/Deposition.{gram_certificate_bound, adjoint_gram_certificate_bound,
    /// entrywise_error_bound}`: the certified spectral norm bounds the map, on either side's Gram and
    /// on an inexact face, and sharpens the Schur test where the Schur test is loose.
    #[test]
    fn the_spectral_norm_is_certified_and_sharpens_the_schur_test() {
        // `[[1, −2], [3, 0]]`: `‖W‖₂² = 7 + √13`, below the Schur test's 12.
        let w = integer_matrix(&[&[1, -2], &[3, 0]]).unwrap();
        let rho = spectral_norm(2, 2, w.entries());
        assert!(certifies(&w, &rho));
        let square = &rho * &rho;
        assert!(square < integer(12), "{square}");
        // `ρ² ≥ 7 + √13`: `(ρ² − 7)² ≥ 13` with `ρ² ≥ 7`.
        assert!(
            square >= integer(7) && (&square - integer(7)) * (&square - integer(7)) >= integer(13)
        );
        // A wide and a tall matrix read their smaller side's Gram; both are certified.
        let wide = integer_matrix(&[&[2, -1, 0, 3], &[1, 1, -2, 0]]).unwrap();
        let tall = wide.transpose().unwrap();
        for x in [&wide, &tall] {
            let rho = spectral_norm(x.rows(), x.columns(), x.entries());
            assert!(certifies(x, &rho));
            let (column, row) = schur_norms(x);
            assert!(&rho * &rho <= column * row);
        }
        // An inexact face (a third is not dyadic) adds its entrywise error and stays certified.
        let third = ExactRatMatrix::new(vec![
            vec![rat(1, 3), rat(-2, 7)],
            vec![rat(5, 11), rat(1, 13)],
        ])
        .unwrap();
        assert!(certifies(&third, &spectral_norm(2, 2, third.entries())));
        // The rank-one all-ones block is its own Schur test, reached within the face's grain.
        let ones = integer_matrix(&[&[1, 1, 1], &[1, 1, 1]]).unwrap();
        let rho = spectral_norm(2, 3, ones.entries());
        assert!(certifies(&ones, &rho) && &rho * &rho <= integer(6) * rat(33, 32));
        // Zero is its own bound.
        assert_eq!(
            spectral_norm(2, 2, &[Rat::zero(), Rat::zero(), Rat::zero(), Rat::zero()]),
            Rat::zero()
        );
    }

    /// The relative root ceiling bounds the root from above within `2^(−31)` of it.
    #[test]
    fn the_root_ceiling_is_a_close_upper_root() {
        for x in [integer(2), rat(1, 3), integer(1 << 40), rat(1, 1 << 40)] {
            let root = root_ceiling(&x);
            assert!(&root * &root >= x, "{x}");
            let below = &root * (Rat::one() - dyadic(-30));
            assert!(&below * &below < x, "{x}");
        }
        assert_eq!(root_ceiling(&Rat::zero()), Rat::zero());
    }

    /// Lean `Holon/Deposition.{joint_move_triangle, joint_step_descends}`: the joint certificate
    /// holds where the count `B` would refuse the same steps, and fails when the moves outgrow the
    /// decrease.
    #[test]
    fn the_joint_certificate_reads_the_moves_not_the_count() {
        let s = rat(1, 2);
        // One family with a large decrease and move, and two with small moves.
        let steps = [integer(1), rat(1, 4), rat(1, 4)];
        let alignments = [integer(8), integer(1), integer(1)];
        let bounds = [integer(2), integer(1), integer(1)];
        let joint = JointReading::read(
            &s,
            steps
                .iter()
                .zip(&alignments)
                .zip(&bounds)
                .map(|((e, a), m)| (e, a, m)),
        );
        // `½ (2 + ¼ + ¼)² = 25/8 ≤ 8 + ½`.
        assert_eq!(joint.curvature, rat(25, 8));
        assert_eq!(joint.decrease, rat(17, 2));
        assert!(joint.holds());
        assert_eq!(joint.certified_decrease(), rat(17, 4));
        // Every family at `η = 1`: the count `B = 3` refuses a small one (`η B s m² = 3/2 > a = 1`),
        // while the joint certificate holds (`½ (2 + 1 + 1)² = 8 ≤ 8 + 1 + 1`).
        let wider = [integer(1), integer(1), integer(1)];
        let joint = JointReading::read(
            &s,
            wider
                .iter()
                .zip(&alignments)
                .zip(&bounds)
                .map(|((e, a), m)| (e, a, m)),
        );
        assert!(joint.holds());
        assert!(&wider[1] * integer(3) * &s * &bounds[1] * &bounds[1] > alignments[1]);
        // Moves that outgrow the decrease fail it.
        let far = [integer(4), integer(4), integer(4)];
        assert!(
            !JointReading::read(
                &s,
                far.iter()
                    .zip(&alignments)
                    .zip(&bounds)
                    .map(|((e, a), m)| (e, a, m)),
            )
            .holds()
        );
    }

    #[test]
    fn a_deposit_beyond_its_declared_growth_is_refused() {
        let q = SymmetricForm::from_integers(&[vec![1, 0], vec![0, 1]]).unwrap();
        let grown = SymmetricForm::from_integers(&[vec![2, 0], vec![0, 1]]).unwrap();
        assert!(CommittedEnergyBound::certify_deposit(&q, &grown, &integer(1)).is_ok());
        assert!(matches!(
            CommittedEnergyBound::certify_deposit(&q, &grown, &rat(1, 2)),
            Err(HolonError::DepositExceedsBound { .. })
        ));
        assert_eq!(
            CommittedEnergyBound::certify_deposit(&q, &q, &integer(-2)),
            Err(HolonError::NegativeGrowth)
        );
    }

    /// **The span factor is the product of the rings' running maxima** (Lean
    /// `Holon/Deposition.{pumped_span_factor, runningMax_mono}`): it does not fall as the span
    /// grows, a ring whose reach falls keeps its largest reach so far, and no ring reads one.
    #[test]
    fn the_span_factor_is_the_product_of_running_maxima() {
        assert_eq!(span_factors(&[], 3), vec![Rat::one(); 4]);
        // A growing ring and a ring whose reach falls after its first tick.
        let growing = vec![integer(2), integer(4), integer(8), integer(16)];
        let falling = vec![rat(3, 2), integer(3), rat(5, 4), integer(1)];
        let factors = span_factors(&[growing.clone(), falling], 3);
        assert_eq!(
            factors,
            vec![integer(3), integer(12), integer(24), integer(48)]
        );
        assert!(factors.windows(2).all(|pair| pair[0] <= pair[1]));
        assert_eq!(span_factors(&[growing], 1), vec![integer(2), integer(4)]);
    }
}
