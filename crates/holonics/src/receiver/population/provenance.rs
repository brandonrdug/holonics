//! Exact attribution of a receiving face to its declared navigator families.
//!
//! Contributions are interval products of the same charged-weight bounds and family faces used
//! by `Population::face`. They attribute mass to a family, not to one producing key or causal
//! path; those relations remain explicit missing terms in each receipt.

use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;
use crate::receiver::population::{Declaration, KeyReadout, Population, PopulationError, Readout};
use num_traits::{One, Zero};

/// Provenance relations not established by a family-level mixture contribution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MissingProducerTerm {
    /// A family's share is not attributed to an individual producing key (or key fibre).
    KeyToContributionRelation,
    /// The relation from this contribution to a causally producing source/request is absent.
    CausalSourceRelation,
}

/// One family's interval contribution to a class of the population's receiving face.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaceContribution {
    pub family_index: usize,
    pub label: String,
    pub declaration: Declaration,
    /// The actual surviving key fibre when this family exposes a `Readout::Keys`.
    pub key_readout: Option<KeyReadout>,
    /// Exact enclosure of `w_f · P_f(class)` using the receiving face's outward arithmetic.
    pub contribution: ExactInterval,
    /// A dead member has zero contribution; a living member may also contribute exact zero.
    pub died_at: Option<usize>,
    /// These remain missing even when a family exposes a key readout: no per-contribution
    /// producing key or causal source relation is proved by the mixture decomposition.
    pub missing_producer_terms: [MissingProducerTerm; 2],
}

impl Population {
    /// Return exact family contributions to one class, retaining dead families as explicit zero
    /// contributors. Their sum and `Population::face` both enclose the same exact mixture; their
    /// outward-rounding enclosures need not contain one another.
    pub fn face_contributors(
        &self,
        class: usize,
    ) -> Result<Vec<FaceContribution>, PopulationError> {
        if class >= self.alphabet {
            return Err(PopulationError::CellOutside {
                cell: class,
                alphabet: self.alphabet,
            });
        }
        let charged = self.charged_bounds();
        let (total_lower, total_upper) = Self::total(&charged, 0..charged.len());
        if total_lower.is_zero() {
            return Err(PopulationError::Extinct { cell: self.cells });
        }

        self.members
            .iter()
            .zip(charged.iter())
            .enumerate()
            .map(|(family_index, (member, (charged_lower, charged_upper)))| {
                let contribution = if member.died.is_some() {
                    ExactInterval::point(Rat::zero())
                } else {
                    let weight_lower = charged_lower.over(&total_upper, false);
                    let weight_upper = charged_upper.over(&total_lower, true);
                    let probability = member.family.face()?[class].clone();
                    let face_lower = super::Bound::of_rat(&probability, false);
                    let face_upper = super::Bound::of_rat(&probability, true);
                    let lower = weight_lower.times(&face_lower, false);
                    let upper = weight_upper.times(&face_upper, true);
                    let lower = lower.to_rat(false);
                    let upper = upper.to_rat(true).min(Rat::one());
                    ExactInterval::new(lower, upper)?
                };
                let key_readout = match member.family.readout() {
                    Readout::Keys(keys) => Some(keys),
                    _ => None,
                };
                Ok(FaceContribution {
                    family_index,
                    label: member.family.label(),
                    declaration: member.family.declaration(),
                    key_readout,
                    contribution,
                    died_at: member.died,
                    missing_producer_terms: [
                        MissingProducerTerm::KeyToContributionRelation,
                        MissingProducerTerm::CausalSourceRelation,
                    ],
                })
            })
            .collect()
    }
}
