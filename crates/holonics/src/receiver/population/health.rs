//! Exact health readings scoped to a population's receiving class face.
//!
//! Given interval enclosures of the family posterior and exact normalized family class faces,
//! this module bounds the L1 variation of the mixed receiving face. For a column-stochastic
//! family-to-class map `A`, `||A(w - v)||₁ ≤ ||w - v||₁`; any two normalized posterior vectors
//! inside the supplied intervals differ by at most `Σ_f (upper_f - lower_f)` in L1.
//!
//! This receipt counts supplied [`CertifiedClass`] draw decisions and refuses a class-face
//! enclosure whose every coordinate is `[0, 1]`. It is an exact receiving-face reading only. It
//! does **not** certify a solver radius, robust count over an unsampled face, Bayesian-update
//! contraction, numerical field solve, or compatible-source fibre, and it does not close F5.
//! The computational object is the helical pair's receiving face; this touches faces and
//! placement and the continuing tower thread, with the helix, pair, cell holonomy and tube kept
//! attached.

use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;
use crate::receiver::population::Population;
use crate::receiver::population::sampling::CertifiedClass;
use num_traits::{One, Zero};
use thiserror::Error;

/// Exact L1 readings for variation of a mixed population receiving face.
///
/// The bounds are dimensionless probability-mass readings. `family_posterior_l1_variation_bound`
/// bounds the change in the mixed class face between any two normalized family posterior vectors
/// enclosed by the supplied posterior intervals. The operator bound and factor state the
/// stochastic family-to-class map's L1 nonexpansiveness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PopulationReceivingFaceHealth {
    pub family_posterior_l1_variation_bound: Rat,
    pub family_to_class_l1_operator_bound: Rat,
    pub family_to_class_nonexpansive_factor: Rat,
    /// Number of `CertifiedClass` draw-decision receipts supplied by the caller.
    pub certified_draw_decision_count: usize,
}

/// Invalid exact operands or a class face too broad to release from.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum PopulationReceivingFaceHealthError {
    #[error("the population's current face could not be read: {0}")]
    Population(String),
    #[error("the family posterior face is empty")]
    EmptyFamilyPosterior,
    #[error(
        "posterior has {posterior_families} families but the class map has {class_map_families}"
    )]
    FamilyCountMismatch {
        posterior_families: usize,
        class_map_families: usize,
    },
    #[error("the family posterior interval at index {family} is outside [0, 1]")]
    InvalidPosteriorInterval { family: usize },
    #[error("the posterior interval at index {family} is reversed")]
    ReversedPosteriorInterval { family: usize },
    #[error("family posterior intervals do not enclose a normalized face")]
    PosteriorIntervalsDoNotEncloseOne,
    #[error("the family-to-class map is empty")]
    EmptyFamilyClassMap,
    #[error("family {family} has no class face")]
    EmptyFamilyClassFace { family: usize },
    #[error("family {family} has {actual} classes; expected {expected}")]
    FamilyClassCountMismatch {
        family: usize,
        expected: usize,
        actual: usize,
    },
    #[error("family {family}, class {class} has mass outside [0, 1]")]
    InvalidFamilyClassMass { family: usize, class: usize },
    #[error("family {family}'s class face sums to {total}, not exactly one")]
    FamilyClassFaceNotNormalized { family: usize, total: Rat },
    #[error("the receiving class face enclosure is empty")]
    EmptyClassFaceEnclosure,
    #[error("receiving class-face intervals do not enclose a normalized face")]
    ClassFaceEnclosureDoesNotEncloseOne,
    #[error("receiving class face enclosure has {actual} classes; expected {expected}")]
    ClassFaceCountMismatch { expected: usize, actual: usize },
    #[error("receiving class-face interval at index {class} is outside [0, 1]")]
    InvalidClassFaceInterval { class: usize },
    #[error("the receiving class-face interval at index {class} is reversed")]
    ReversedClassFaceInterval { class: usize },
    #[error("every receiving class is enclosed by [0, 1], so the face covers the whole simplex")]
    SimplexCoveringClassFace,
}

impl Population {
    /// Read this population's actual next face, posterior and family faces through the same
    /// standing before any reception. Dead families have point-zero posterior; a canonical
    /// one-hot column fills their unused face slot without contributing to the mixture.
    pub fn receiving_face_health(
        &self,
    ) -> Result<PopulationReceivingFaceHealth, PopulationReceivingFaceHealthError> {
        let source = |error: String| PopulationReceivingFaceHealthError::Population(error);
        let posterior = self
            .family_posterior_face()
            .map_err(|e| source(e.to_string()))?;
        let face = self.face().map_err(|e| source(e.to_string()))?;
        let mut dead_face = vec![Rat::zero(); self.alphabet];
        dead_face[0] = Rat::one();
        let family_faces = self
            .members
            .iter()
            .map(|member| {
                if member.died.is_some() {
                    Ok(dead_face.clone())
                } else {
                    member.family.face().map_err(|e| source(e.to_string()))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        population_receiving_face_health(&posterior, &family_faces, &face, &[])
    }
}

/// Build an exact receiving-face health receipt from the posterior enclosure, each family's
/// fixed exact class face, the population class-face enclosure, and already certified draw
/// decisions.
///
/// The family faces are the columns of a nonnegative stochastic map. Its induced L1 operator
/// norm is therefore exactly one (and its nonexpansive factor is one). The posterior interval
/// widths provide the mixture-face variation bound. This calculation does not check whether a
/// `CertifiedClass` was produced from this same face; it reports only the count of receipts the
/// caller supplies.
pub fn population_receiving_face_health(
    family_posterior: &[ExactInterval],
    family_class_faces: &[Vec<Rat>],
    class_face_enclosure: &[ExactInterval],
    certified_draws: &[CertifiedClass],
) -> Result<PopulationReceivingFaceHealth, PopulationReceivingFaceHealthError> {
    if family_posterior.is_empty() {
        return Err(PopulationReceivingFaceHealthError::EmptyFamilyPosterior);
    }
    if family_posterior.len() != family_class_faces.len() {
        return Err(PopulationReceivingFaceHealthError::FamilyCountMismatch {
            posterior_families: family_posterior.len(),
            class_map_families: family_class_faces.len(),
        });
    }

    let mut posterior_lower = Rat::zero();
    let mut posterior_upper = Rat::zero();
    let mut variation_bound = Rat::zero();
    for (family, interval) in family_posterior.iter().enumerate() {
        if interval.lower > interval.upper {
            return Err(PopulationReceivingFaceHealthError::ReversedPosteriorInterval { family });
        }
        if interval.lower < Rat::zero() || interval.upper > Rat::one() {
            return Err(PopulationReceivingFaceHealthError::InvalidPosteriorInterval { family });
        }
        posterior_lower += &interval.lower;
        posterior_upper += &interval.upper;
        variation_bound += &interval.upper - &interval.lower;
    }
    if posterior_lower > Rat::one() || posterior_upper < Rat::one() {
        return Err(PopulationReceivingFaceHealthError::PosteriorIntervalsDoNotEncloseOne);
    }

    let class_count = family_class_faces
        .first()
        .ok_or(PopulationReceivingFaceHealthError::EmptyFamilyClassMap)?
        .len();
    if class_count == 0 {
        return Err(PopulationReceivingFaceHealthError::EmptyFamilyClassFace { family: 0 });
    }
    for (family, face) in family_class_faces.iter().enumerate() {
        if face.is_empty() {
            return Err(PopulationReceivingFaceHealthError::EmptyFamilyClassFace { family });
        }
        if face.len() != class_count {
            return Err(
                PopulationReceivingFaceHealthError::FamilyClassCountMismatch {
                    family,
                    expected: class_count,
                    actual: face.len(),
                },
            );
        }
        let mut total = Rat::zero();
        for (class, mass) in face.iter().enumerate() {
            if mass < &Rat::zero() || mass > &Rat::one() {
                return Err(PopulationReceivingFaceHealthError::InvalidFamilyClassMass {
                    family,
                    class,
                });
            }
            total += mass;
        }
        if total != Rat::one() {
            return Err(
                PopulationReceivingFaceHealthError::FamilyClassFaceNotNormalized { family, total },
            );
        }
    }

    if class_face_enclosure.is_empty() {
        return Err(PopulationReceivingFaceHealthError::EmptyClassFaceEnclosure);
    }
    if class_face_enclosure.len() != class_count {
        return Err(PopulationReceivingFaceHealthError::ClassFaceCountMismatch {
            expected: class_count,
            actual: class_face_enclosure.len(),
        });
    }
    let mut covers_simplex = true;
    let mut class_lower_total = Rat::zero();
    let mut class_upper_total = Rat::zero();
    for (class, interval) in class_face_enclosure.iter().enumerate() {
        if interval.lower > interval.upper {
            return Err(PopulationReceivingFaceHealthError::ReversedClassFaceInterval { class });
        }
        if interval.lower < Rat::zero() || interval.upper > Rat::one() {
            return Err(PopulationReceivingFaceHealthError::InvalidClassFaceInterval { class });
        }
        class_lower_total += &interval.lower;
        class_upper_total += &interval.upper;
        covers_simplex &= interval.lower.is_zero() && interval.upper.is_one();
    }
    if class_lower_total > Rat::one() || class_upper_total < Rat::one() {
        return Err(PopulationReceivingFaceHealthError::ClassFaceEnclosureDoesNotEncloseOne);
    }
    if covers_simplex {
        return Err(PopulationReceivingFaceHealthError::SimplexCoveringClassFace);
    }

    Ok(PopulationReceivingFaceHealth {
        family_posterior_l1_variation_bound: variation_bound,
        family_to_class_l1_operator_bound: Rat::one(),
        family_to_class_nonexpansive_factor: Rat::one(),
        certified_draw_decision_count: certified_draws.len(),
    })
}
