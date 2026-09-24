//! **The storage facet of the quadratic moment** (plan phase 13).
//!
//! [definition] Every chart in this module presents one element relation of the Holon core: the
//! quadratic storage `E(x) = ½⟨x, C x⟩` of the moment
//!
//! ```text
//! C = Σ_s w_s f_s f_sᵀ          (weighted rank-one family; the defining law)
//!   = Bᵀ H B                    (FactoredMomentSection: image incidence and constitutive form)
//!   = Eᵀ (⊕_h μ_h H_root) E     (FactoredConstitutiveSpine: rooted direct sum with multiplicities)
//!   = Σ_(i≤j) c_ij (e_i e_jᵀ + [i≠j] e_j e_iᵀ)   (SparseQuadraticMomentSection: fixed pair carrier)
//! ```
//!
//! and therefore one [`ElementRelation::Storage`] on the factor ports. Its energy is
//! `½ Σ_s w_s ⟨f_s, x⟩²`, so a positive-weight family is passive storage (positive semidefinite);
//! a change of `C` at a fixed configuration is deposition work `½⟨x, (C' − C) x⟩`
//! ([`holonics::element::deposition_work`]). The resident card holds the same object in its own
//! limb layout; its read-back sections are compared against these host charts in the device suite.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Millennium/HolonicQuadraticMomentCondensation.lean::quadraticMoment` | [`weighted_family_moment`] |
//! | `Holon/MomentStorage.lean::storageEnergy_quadraticMoment` | [`QuadraticMomentStorage::stored_energy`] (tested against `½ Σ w ⟨f, x⟩²`) |
//! | `Holon/MomentStorage.lean::storageEnergy_quadraticMoment_nonneg` | [`QuadraticMomentStorage::is_passive`] |
//! | `Holon/Deposition.lean::deposition_work` | [`QuadraticMomentStorage::deposition_work`] |

use holonics::element::{self, ElementRelation};
use holonics::inertia::SymmetricForm;
use holonics::scalar::matrix_form;
use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;

use super::*;
use holonics::exact_linear::ExactRatMatrix;

fn storage_refusal(_: holonics::holon::HolonError) -> FactoredMomentError {
    FactoredMomentError::Shape
}

/// The defining law `C = Σ_s w_s f_s f_sᵀ` of a weighted integral current family on
/// `factor_population` ports.
pub fn weighted_family_moment(
    factor_population: u32,
    family: &[WeightedIntegralCurrent],
) -> Result<ExactRatMatrix, FactoredMomentError> {
    let factors = factor_population as usize;
    if factors == 0 {
        return Err(FactoredMomentError::Shape);
    }
    let mut moment = vec![vec![BigInt::zero(); factors]; factors];
    for current in family {
        if current
            .entries
            .iter()
            .any(|(factor, _)| *factor >= factor_population)
        {
            return Err(FactoredMomentError::Shape);
        }
        let weight = BigInt::from(current.weight.clone());
        for (left, left_coefficient) in &current.entries {
            for (right, right_coefficient) in &current.entries {
                moment[*left as usize][*right as usize] += &weight
                    * BigInt::from(left_coefficient.clone())
                    * BigInt::from(right_coefficient.clone());
            }
        }
    }
    Ok(ExactRatMatrix::new(
        moment
            .into_iter()
            .map(|row| row.into_iter().map(Rat::from_integer).collect())
            .collect(),
    )?)
}

/// [definition] **The storage facet** shared by every host chart of the quadratic moment. A chart
/// supplies only its moment `C`; the element, its energy, passivity and deposition work are the
/// core's.
pub trait QuadraticMomentStorage {
    /// The complete symmetric moment `C` on the factor ports.
    fn moment(&self) -> Result<ExactRatMatrix, FactoredMomentError>;

    /// `C` as a core symmetric form (refuses an asymmetric chart as a reconstruction failure).
    fn storage_form(&self) -> Result<SymmetricForm, FactoredMomentError> {
        matrix_form(&self.moment()?).map_err(|_| FactoredMomentError::Reconstruction)
    }

    /// The core element relation: quadratic storage `½⟨x, C x⟩` on the factor ports.
    fn element(&self) -> Result<ElementRelation, FactoredMomentError> {
        Ok(ElementRelation::Storage {
            form: self.storage_form()?,
        })
    }

    /// `½⟨x, C x⟩`.
    fn stored_energy(&self, x: &[Rat]) -> Result<Rat, FactoredMomentError> {
        element::storage_energy(&self.storage_form()?, x).map_err(storage_refusal)
    }

    /// Whether the storage is passive (`C ⪰ 0`), decided exactly by Sylvester inertia.
    fn is_passive(&self) -> Result<bool, FactoredMomentError> {
        Ok(element::is_positive_semidefinite(&self.storage_form()?))
    }

    /// The deposition work `½⟨x, (C' − C) x⟩` of replacing this storage by `successor` at the
    /// fixed configuration `x`.
    fn deposition_work(
        &self,
        successor: &dyn QuadraticMomentStorage,
        x: &[Rat],
    ) -> Result<Rat, FactoredMomentError> {
        element::deposition_work(&self.storage_form()?, &successor.storage_form()?, x)
            .map_err(storage_refusal)
    }
}

impl QuadraticMomentStorage for FactoredMomentSection {
    /// `Bᵀ H B`.
    fn moment(&self) -> Result<ExactRatMatrix, FactoredMomentError> {
        self.validate_admitted()?;
        Ok(self
            .incidence
            .transpose()?
            .multiply(&self.constitutive)?
            .multiply(&self.incidence)?)
    }
}

impl QuadraticMomentStorage for FactoredConstitutiveSpine {
    /// `Eᵀ (⊕_h μ_h H_root) E`.
    fn moment(&self) -> Result<ExactRatMatrix, FactoredMomentError> {
        self.reconstruct_moment()
    }
}

impl QuadraticMomentStorage for SparseQuadraticMomentSection {
    /// The symmetric fill of the upper pair coefficients.
    fn moment(&self) -> Result<ExactRatMatrix, FactoredMomentError> {
        self.validate()?;
        let factors = self.factor_population as usize;
        let mut moment = vec![vec![Rat::zero(); factors]; factors];
        for (pair, coefficient) in self.pairs.iter().zip(&self.coefficients) {
            let value = Rat::from_integer(BigInt::from(coefficient.clone()));
            moment[pair.left as usize][pair.right as usize] = value.clone();
            moment[pair.right as usize][pair.left as usize] = value;
        }
        Ok(ExactRatMatrix::new(moment)?)
    }
}
