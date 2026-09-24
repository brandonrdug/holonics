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
//! | Lean | Rust |
//! |---|---|
//! | `learned_rate_form` | [`learned_rate_form`] |
//! | `energy_product_bound`, `committed_energy_bound` | [`CommittedEnergyBound`] |
//! | `projectPassive`, `projectPassive_passive`, `projectPassive_of_passive` | [`project_passive`] |
//! | `symPart`, `quad_symPart` | [`crate::ratio::linear::vector::symmetric_part`] |
//! | `indefiniteBlock`, `divergentState`, `normal_law_divergence_witness` | [`indefinite_block`], [`divergent_state`] |

use crate::ratio::Rat;
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
}
