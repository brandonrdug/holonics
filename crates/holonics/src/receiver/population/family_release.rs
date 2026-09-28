//! Family-ancestral release operands for a request-conditioned population face.
//!
//! The Bayesian consumer chooses a family once at the request-conditioned standing, then follows
//! that family's `P_f` along the whole response. Its mixture identity is
//! `Σ_f w_f P_f(y) = P_population(y)`. Interval family selection refuses a draw whenever the
//! charged posterior bounds leave its family unresolved; that refusal means this released
//! submeasure does not yet prove equality of the full distributions.

use crate::ratio::Rat;
use crate::ratio::algebraic::{ExactInterval, ExactValueError};
use crate::receiver::population::{Population, PopulationError};
use num_traits::{One, Zero};
use thiserror::Error;

use super::sampling::{CertifiedClass, SamplingError, select_class};

/// A normalized exact class selected from the face of one already chosen family.
pub fn select_family_class(face: &[Rat], draw: &Rat) -> Result<CertifiedClass, FamilyReleaseError> {
    if face.is_empty() {
        return Err(FamilyReleaseError::EmptyFace);
    }
    let mut total = Rat::zero();
    let mut intervals = Vec::with_capacity(face.len());
    for (class, mass) in face.iter().enumerate() {
        if mass < &Rat::zero() {
            return Err(FamilyReleaseError::NegativeMass {
                class,
                mass: mass.clone(),
            });
        }
        total += mass;
        intervals.push(ExactInterval::point(mass.clone()));
    }
    if total != Rat::one() {
        return Err(FamilyReleaseError::NotNormalized { total });
    }
    Ok(select_class(&intervals, draw)?)
}

/// Errors while forming or selecting a family-ancestral release operand.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum FamilyReleaseError {
    #[error("a family face must contain at least one class")]
    EmptyFace,
    #[error("family face class {class} has negative mass {mass}")]
    NegativeMass { class: usize, mass: Rat },
    #[error("family face sums to {total}, not exactly one")]
    NotNormalized { total: Rat },
    #[error("exact class selection was refused: {0:?}")]
    Sampling(SamplingError),
    #[error("population face was refused: {0}")]
    Population(String),
    #[error("population posterior interval was invalid: {0}")]
    Exact(String),
}

impl From<SamplingError> for FamilyReleaseError {
    fn from(error: SamplingError) -> Self {
        Self::Sampling(error)
    }
}

impl From<PopulationError> for FamilyReleaseError {
    fn from(error: PopulationError) -> Self {
        Self::Population(error.to_string())
    }
}

impl From<ExactValueError> for FamilyReleaseError {
    fn from(error: ExactValueError) -> Self {
        Self::Exact(error.to_string())
    }
}

impl Population {
    /// The request-conditioned posterior enclosure of each declared family.
    ///
    /// This uses the same charged likelihood bounds and normalized total as `face`. Dead
    /// families remain in declaration order with point-zero mass. Each living family's
    /// normalized charged-weight bounds are converted outward to an exact rational enclosure;
    /// its cell face is read separately when following that selected family.
    pub fn family_posterior_face(&self) -> Result<Vec<ExactInterval>, FamilyReleaseError> {
        let charged = self.charged_bounds();
        let (total_lower, total_upper) = Self::total(&charged, 0..charged.len());
        if total_lower.is_zero() {
            return Err(PopulationError::Extinct { cell: self.cells }.into());
        }

        self.members
            .iter()
            .zip(charged.iter())
            .map(|(member, (charged_lower, charged_upper))| {
                if member.died.is_some() {
                    return Ok(ExactInterval::point(Rat::zero()));
                }
                let weight_lower = charged_lower.over(&total_upper, false).to_rat(false);
                let weight_upper = charged_upper
                    .over(&total_lower, true)
                    .to_rat(true)
                    .min(Rat::one());
                Ok(ExactInterval::new(weight_lower, weight_upper)?)
            })
            .collect()
    }

    /// Certify one family index at `draw` when every compatible posterior face selects it.
    pub fn select_family(&self, draw: &Rat) -> Result<CertifiedClass, FamilyReleaseError> {
        Ok(select_class(&self.family_posterior_face()?, draw)?)
    }
}
