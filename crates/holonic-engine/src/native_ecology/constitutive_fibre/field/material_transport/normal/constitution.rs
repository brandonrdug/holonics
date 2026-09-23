//! **Constitution facet** of the normal Holon (plan phase 9): the one element relation `W H = B`.
//!
//! [definition] The normal law is an element relation on the coefficient configuration `W`
//! (targets × sources, complex): its storage is the accumulated source Gram `H ⪰ I` (realified,
//! [`NormalConstitution::storage_form`]), its source is the cross moment `B`, and its stored
//! energy at the applied coefficients is `½ Σ_r Re(w_r H w_r*)`. An observation deposits into
//! `H`, `B` and `C`; the work that deposit does at the successor's coefficients is the core
//! deposition work `½⟨x, (Q' − Q) x⟩` (`holonic_core::element::deposition_work`,
//! `Holon/Deposition.lean::deposition_work`). The resident chart of this relation is
//! [`ResidentNormalMaterial`]; this type is its exact host reading, and
//! [`NativeNormalMaterialObjective`] the reading of its normal objective.
use super::*;
use crate::inertia::SymmetricForm;
use holonic_core::element::ElementRelation;

#[derive(Clone, Debug, Serialize)]
pub struct NormalConstitution {
    pub material: NativeFieldMaterialTransportState,
    pub source_normal: Vec<Vec<ExactComplexWaveCurrent>>,
    pub cross_source: Vec<Vec<ExactComplexWaveCurrent>>,
    pub source_normal_error: Rat,
    pub cross_source_error: Rat,
    pub target_energy: Rat,
    pub target_energy_error: Rat,
    pub normal_residual_upper: Rat,
}

/// Immutable nonzero coefficient prior for a normal chart.  `cross_source` is
/// `B_0 = W_0 H_0` and `target_energy` is `C_0 = ||W_0||²`; the observed
/// `target_energy` retained in a state remains Q_data.  Keeping this operand
/// separate prevents a prior from being reported as an observation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
pub struct NativeNormalPrior {
    pub cross_source: Vec<Vec<ExactComplexWaveCurrent>>,
    pub target_energy: Rat,
}

impl NativeNormalPrior {
    pub fn from_coefficients(
        coefficients: Vec<Vec<ExactComplexWaveCurrent>>,
    ) -> Result<Self, ConstitutiveFibreError> {
        if coefficients.is_empty()
            || coefficients
                .iter()
                .any(|row| row.len() != coefficients[0].len())
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let target_energy = coefficients
            .iter()
            .flatten()
            .map(ExactComplexWaveCurrent::norm_square)
            .sum();
        Ok(Self {
            cross_source: coefficients,
            target_energy,
        })
    }

    pub fn source_complex(&self) -> usize {
        self.cross_source.first().map_or(0, Vec::len)
    }
    pub fn targets(&self) -> usize {
        self.cross_source.len()
    }
}

impl NormalConstitution {
    /// Evaluate the normal objective with a supplied immutable prior.  The resident
    /// state carries total H/B, while its Q_data remains the observed/proxy-target
    /// energy; this method forms B-B0 and adds C0 only for the objective.
    pub fn objective_with_prior(
        &self,
        prior: &NativeNormalPrior,
    ) -> Result<NativeNormalMaterialObjective, ConstitutiveFibreError> {
        if prior.targets() != self.cross_source.len()
            || prior.source_complex() != self.source_normal.len()
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut data = self.clone();
        for (row, p) in data.cross_source.iter_mut().zip(&prior.cross_source) {
            for (value, prior_value) in row.iter_mut().zip(p) {
                *value = value.subtract(prior_value);
            }
        }
        data.target_energy += &prior.target_energy;
        data.objective()
    }

    /// Validate the prior's dimensions and the retained H-I/B-B0 split without
    /// conflating its C0 with Q_data.  Source-family uncertainty remains separate.
    pub fn validate_prior(&self, prior: &NativeNormalPrior) -> Result<(), ConstitutiveFibreError> {
        if prior.targets() != self.cross_source.len()
            || prior.source_complex() != self.source_normal.len()
            || self
                .source_normal
                .iter()
                .any(|row| row.len() != self.source_normal.len())
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        // Validate the observed source geometry as H-I. A nonzero prior does
        // not require a fresh chart after observations have accumulated.
        for i in 0..self.source_normal.len() {
            for j in 0..self.source_normal.len() {
                if self.source_normal[i][j] != self.source_normal[j][i].conjugate() {
                    return Err(ConstitutiveFibreError::Uncertain);
                }
            }
            let observed_diagonal = &self.source_normal[i][i].real - Rat::one();
            if observed_diagonal.is_negative() {
                return Err(ConstitutiveFibreError::Uncertain);
            }
        }
        Ok(())
    }

    /// Decode the signed numerical normal residual from its retained exact factors.
    /// Source/target family uncertainty remains in the separate normal and cross-source bounds.
    pub fn normal_residual(
        &self,
    ) -> Result<Vec<Vec<ExactComplexWaveCurrent>>, ConstitutiveFibreError> {
        let m = self.source_normal.len();
        if m == 0
            || self.source_normal.iter().any(|r| r.len() != m)
            || self.material.coefficients.len() != self.cross_source.len()
            || self
                .material
                .coefficients
                .iter()
                .chain(&self.cross_source)
                .any(|r| r.len() != m)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(self
            .material
            .coefficients
            .iter()
            .zip(&self.cross_source)
            .map(|(row, b)| {
                (0..m)
                    .map(|j| {
                        row.iter()
                            .zip(&self.source_normal)
                            .fold(ExactComplexWaveCurrent::zero(), |sum, (a, h)| {
                                sum.add(&a.multiply(&h[j]))
                            })
                            .subtract(&b[j])
                    })
                    .collect()
            })
            .collect())
    }

    /// Observe a state returned by `inspect_normal_material_state`. Its exact accumulated
    /// Gram and every admitted source Gram are at least I. No inverse, raw-source replay,
    /// source-centre selection for learning, or native coefficient change occurs here.
    pub fn objective(&self) -> Result<NativeNormalMaterialObjective, ConstitutiveFibreError> {
        if [
            &self.source_normal_error,
            &self.cross_source_error,
            &self.target_energy_error,
        ]
        .iter()
        .any(|q| q.is_negative())
        {
            return Err(invalid("negative objective family bound"));
        }
        let residual = self.normal_residual()?;
        let two = Rat::from_integer(2.into());
        let mut norm_square = Rat::zero();
        let mut norm_upper = Rat::zero();
        let mut cross_norm_upper = Rat::zero();
        let mut paired = Rat::zero();
        let mut residual_square = Rat::zero();
        for ((m, b), r) in self
            .material
            .coefficients
            .iter()
            .flatten()
            .zip(self.cross_source.iter().flatten())
            .zip(residual.iter().flatten())
        {
            norm_square += m.norm_square();
            norm_upper += m.real.abs() + m.imaginary.abs();
            cross_norm_upper += b.real.abs() + b.imaginary.abs();
            // M H = B + R: avoids a second matrix multiplication for the objective.
            paired += m.multiply(&r.subtract(b).conjugate()).real;
            residual_square += r.norm_square();
        }
        let prior = &norm_square / &two;
        let attained = (&self.target_energy + paired) / &two;
        let data = &attained - &prior;
        if data.is_negative() || attained.is_negative() {
            return Err(invalid(
                "objective incompatible with accumulated unit-prior geometry",
            ));
        }
        let gap = &residual_square / &two;
        let lower = (&attained - &gap).max(Rat::zero());
        let family_error = (&norm_square * &self.source_normal_error
            + &two * &norm_upper * &self.cross_source_error
            + &self.target_energy_error)
            / &two;
        // Both minimizers have norm <= ||B_nominal||_F + EB. L1 is an exact upper bound.
        let k = cross_norm_upper + &self.cross_source_error;
        let minimum_error = (&k * &k * &self.source_normal_error
            + &two * &k * &self.cross_source_error
            + &self.target_energy_error)
            / &two;
        let around = |value: &Rat, error: &Rat| crate::ExactInterval {
            lower: (value - error).max(Rat::zero()),
            upper: value + error,
        };
        Ok(NativeNormalMaterialObjective {
            family_data_term: around(&data, &family_error),
            family_regularized_objective: around(&attained, &family_error),
            family_minimum: crate::ExactInterval {
                lower: (&lower - &minimum_error).max(Rat::zero()),
                upper: &attained + &minimum_error,
            },
            nominal_minimum: crate::ExactInterval {
                lower,
                upper: attained.clone(),
            },
            nominal_data_term: data,
            prior_term: prior,
            nominal_regularized_objective: attained,
            normal_residual_squared: residual_square,
            solve_gap_upper: gap,
        })
    }
}

/// Compatibility name of [`NormalConstitution`].
pub type NativeNormalMaterialState = NormalConstitution;

impl NormalConstitution {
    /// The realified Hermitian source Gram `R(H)`: block `[[Re, Im], [−Im, Re]]` per entry on
    /// the interleaved `(Re w_j, Im w_j)` coordinates, so `Re(w H w*) = xᵀ R(H) x`.
    pub fn storage_form(&self) -> Result<SymmetricForm, ConstitutiveFibreError> {
        let m = self.source_normal.len();
        if m == 0 || self.source_normal.iter().any(|row| row.len() != m) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let rows = (0..2 * m)
            .map(|i| {
                (0..2 * m)
                    .map(|j| {
                        let z = &self.source_normal[i / 2][j / 2];
                        match (i % 2, j % 2) {
                            (0, 0) | (1, 1) => z.real.clone(),
                            (0, 1) => z.imaginary.clone(),
                            _ => -z.imaginary.clone(),
                        }
                    })
                    .collect()
            })
            .collect();
        SymmetricForm::from_rows(rows).map_err(invalid)
    }
    /// The element relation of the normal law in the core: storage on the coefficient rows.
    pub fn element(&self) -> Result<ElementRelation, ConstitutiveFibreError> {
        Ok(ElementRelation::Storage {
            form: self.storage_form()?,
        })
    }
    /// The applied coefficients `W`, one realified interleaved row per target.
    pub fn coefficient_rows(&self) -> Vec<Vec<Rat>> {
        self.material
            .coefficients
            .iter()
            .map(|row| {
                row.iter()
                    .flat_map(|z| [z.real.clone(), z.imaginary.clone()])
                    .collect()
            })
            .collect()
    }
    /// Stored energy of the constitution at its applied coefficients, `½ Σ_r Re(w_r H w_r*)`.
    pub fn stored_energy(&self) -> Result<Rat, ConstitutiveFibreError> {
        let form = self.storage_form()?;
        self.coefficient_rows()
            .iter()
            .map(|x| holonic_core::element::storage_energy(&form, x).map_err(invalid))
            .sum()
    }
    /// Deposition work of the change `self → successor` at the successor's coefficients:
    /// `Σ_r ½⟨x'_r, (R(H') − R(H)) x'_r⟩` (`holonic_core::element::deposition_work`).
    pub fn deposition_work(&self, successor: &Self) -> Result<Rat, ConstitutiveFibreError> {
        let (before, after) = (self.storage_form()?, successor.storage_form()?);
        successor
            .coefficient_rows()
            .iter()
            .map(|x| holonic_core::element::deposition_work(&before, &after, x).map_err(invalid))
            .sum()
    }
}
