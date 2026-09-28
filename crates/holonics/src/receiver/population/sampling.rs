//! Exact inverse-CDF path selection for a receiving face.
//!
//! This is an exterior boundary certificate: it selects a class only when every exact face
//! compatible with the supplied interval face selects that same class. If uncertainty retains
//! probability mass across the draw, selection is refused and the exact crossing bounds are
//! returned. The result does not establish equality of distributions or certify a text release.

use crate::ratio::Rat;
use crate::ratio::algebraic::{ExactInterval, ExactValueError};
use num_traits::{One, Zero};

/// Exact bounds at a potentially crossed inverse-CDF boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrossingBounds {
    /// Zero-based class whose interval may contain the draw's inverse-CDF boundary.
    pub class: usize,
    /// Upper bound on cumulative mass strictly before `class`.
    pub prior_upper: Rat,
    /// Lower bound on cumulative mass through `class`.
    pub through_lower: Rat,
}

/// Exact certificate that all compatible faces choose one class.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertifiedClass {
    pub class: usize,
    pub prior_upper: Rat,
    pub through_lower: Rat,
}

/// Validation or unresolved-fibre refusal for exact class selection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SamplingError {
    EmptyFace,
    NegativeMass {
        class: usize,
        bound: Rat,
    },
    MassAboveOne {
        class: usize,
        bound: Rat,
    },
    InvalidNormalization {
        lower_total: Rat,
        upper_total: Rat,
    },
    DrawOutOfRange {
        draw: Rat,
    },
    UnresolvedFibre {
        draw: Rat,
        crossings: Vec<CrossingBounds>,
    },
    Interval(ExactValueError),
}

/// Certify inverse-CDF selection for every exact normalized face enclosed by `face`.
///
/// For class `i`, the certificate is `Σ_(j<i) upper_j ≤ u < Σ_(j≤i) lower_j`.
/// This sufficient condition deliberately refuses a draw when the unresolved fibre could
/// place the cumulative boundary on either side of `u`; that mass remains unresolved.
pub fn select_class(face: &[ExactInterval], draw: &Rat) -> Result<CertifiedClass, SamplingError> {
    if face.is_empty() {
        return Err(SamplingError::EmptyFace);
    }
    if draw < &Rat::zero() || draw >= &Rat::one() {
        return Err(SamplingError::DrawOutOfRange { draw: draw.clone() });
    }

    let mut lower_total = Rat::zero();
    let mut upper_total = Rat::zero();
    for (class, mass) in face.iter().enumerate() {
        if mass.lower < Rat::zero() {
            return Err(SamplingError::NegativeMass {
                class,
                bound: mass.lower.clone(),
            });
        }
        if mass.upper > Rat::one() {
            return Err(SamplingError::MassAboveOne {
                class,
                bound: mass.upper.clone(),
            });
        }
        lower_total += &mass.lower;
        upper_total += &mass.upper;
    }
    if lower_total > Rat::one() || upper_total < Rat::one() {
        return Err(SamplingError::InvalidNormalization {
            lower_total,
            upper_total,
        });
    }

    let mut lower_prefix = Rat::zero();
    let mut upper_prefix = Rat::zero();
    let mut crossings = Vec::new();
    for (class, mass) in face.iter().enumerate() {
        let prior_upper = upper_prefix.clone();
        let through_lower = &lower_prefix + &mass.lower;
        if &prior_upper <= draw && draw < &through_lower {
            return Ok(CertifiedClass {
                class,
                prior_upper,
                through_lower,
            });
        }
        if &lower_prefix <= draw && draw < &(&upper_prefix + &mass.upper) {
            crossings.push(CrossingBounds {
                class,
                prior_upper,
                through_lower: through_lower.clone(),
            });
        }
        lower_prefix = through_lower;
        upper_prefix += &mass.upper;
    }
    Err(SamplingError::UnresolvedFibre {
        draw: draw.clone(),
        crossings,
    })
}
