#![allow(unused_imports)]

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::receiver_history_compression::{
    AddressedFactoredIntegralReceiverComplex, FactoredIntegralReceiverForm,
    SparseIntegralFunctional,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WeightedIntegralCurrent {
    pub weight: BigUint,
    pub entries: Vec<(u32, BigUint)>,
}

/// One addressed diagonal incidence in an ordered multiplicative chronology.  The sparse
/// section is an exact native current; an exterior port or byte name is not part of this type.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedDiagonalCurrentStep {
    pub source_state: u32,
    pub target_state: u32,
    pub entries: Vec<(u32, BigUint)>,
}

/// One coordinate of the symmetric quadratic current.  The canonical order is a storage chart;
/// it identifies the two presentations of one symmetric moment entry without identifying the
/// ordered source-pair occurrences retained by the foundation fibre.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SymmetricFactorPair {
    pub left: u32,
    pub right: u32,
}

impl SymmetricFactorPair {
    pub(crate) fn new(left: u32, right: u32) -> Self {
        if left <= right {
            Self { left, right }
        } else {
            Self {
                left: right,
                right: left,
            }
        }
    }
}

/// Fixed generator-closed pair carrier.  Every `(generator, source_pair)` incidence has exactly
/// one target coordinate. `multiplicity` is two only when a distinct source pair collapses onto
/// one target diagonal; it is not a tunable coefficient.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SparseQuadraticMomentAction {
    pub schema: String,
    pub factor_population: u32,
    pub generator_population: u32,
    pub pairs: Vec<SymmetricFactorPair>,
    pub generator_targets: Vec<Vec<u32>>,
    pub target_pair_coordinates: Vec<u32>,
    pub multiplicities: Vec<u8>,
}

/// The hot exact current on one fixed pair carrier.  Recurrence changes only these coefficients;
/// it neither appends history words nor derives a new factor frame.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SparseQuadraticMomentSection {
    pub schema: String,
    pub factor_population: u32,
    pub generation: u64,
    pub pairs: Vec<SymmetricFactorPair>,
    pub coefficients: Vec<BigUint>,
}

/// Cold testimony joining the source occurrence family to the native pair-current quotient.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SparseQuadraticMomentFoundation {
    pub schema: String,
    pub action: SparseQuadraticMomentAction,
    pub section: SparseQuadraticMomentSection,
    pub reconstruction_fibre: Vec<WeightedIntegralCurrent>,
}

/// One nonzero coefficient of a bilinear receiver after exact contraction onto the pair carrier.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SparseQuadraticPairReceiverTerm {
    pub pair_coordinate: u32,
    pub coefficient: BigInt,
}

/// A receiver-local sparse contraction frame.  The original addressed receiver complex remains
/// cold reconstruction testimony; equal pair contributions are summed only inside their declared
/// receiver occurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SparseQuadraticPairReceiverFrame {
    pub schema: String,
    pub factor_population: u32,
    pub pair_population: u32,
    pub receiver_population: u32,
    pub receiver_term_offsets: Vec<u64>,
    pub terms: Vec<SparseQuadraticPairReceiverTerm>,
}

/// The hot current section.  Its image rank is derived from the entering incidence and is never
/// supplied by a caller.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FactoredMomentSection {
    pub schema: String,
    pub factor_population: u32,
    pub image_rank: u32,
    /// Ordered factor columns forming one nonsingular minor of `incidence`. This is a compact
    /// full-row-rank certificate, not a preferred cross-moment or semantic factor taxonomy.
    pub basis_factors: Vec<u32>,
    /// Integral image incidence `B`, shape `image_rank × factor_population`.
    pub incidence: ExactRatMatrix,
    /// The constitutive form `H` on the derived image, shape `image_rank × image_rank`.
    pub constitutive: ExactRatMatrix,
}

/// Exterior reconstruction testimony for one foundation.  It does not enter the section's hot
/// transport closure.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FactoredMomentFoundation {
    pub schema: String,
    pub source_population: u32,
    /// Each entering current row expressed through the canonical image incidence.
    pub source_to_image: ExactRatMatrix,
    pub reconstruction_fibre: Vec<WeightedIntegralCurrent>,
    pub section: FactoredMomentSection,
}

/// One addressed plural-generator passage.  Row `(generator, source_image)` of
/// `generator_source_to_target_image` retains the complete boundary map into the newly derived
/// target image; it is not a count or a digest of the join.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FactoredMomentPassage {
    pub schema: String,
    pub factor_population: u32,
    pub generator_population: u32,
    pub source_image_rank: u32,
    pub target_image_rank: u32,
    /// The complete source section at this occurrence.  Serial composition joins this object to
    /// the preceding passage's target; equal ranks or equal digests are not a joining witness.
    pub source: FactoredMomentSection,
    /// The complete plural factor-leg incidence in generator-major order.
    pub generator_targets: Vec<Vec<u32>>,
    pub generator_source_to_target_image: ExactRatMatrix,
    pub target: FactoredMomentSection,
}

/// The productive constitutive chart of an ordered passage history.  The compact target image is
/// still retained by [`FactoredMomentSection`] for refactorization and reconstruction; this spine
/// carries the same moment as one rooted constitutive form and an addressed effective incidence.
/// Its row address is `(history, root_coordinate)`, so no dense successor constitution has to be
/// squared into every later receiver contraction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactoredConstitutiveSpine {
    pub schema: String,
    pub factor_population: u32,
    pub root_rank: u32,
    pub history_population: u32,
    pub root_constitutive: ExactRatMatrix,
    pub effective_incidence: ExactRatMatrix,
    /// Exact ordered-history multiplicity carried by each distinct incidence block.  Equal
    /// realizations are one productive block but never lose the population which reached it.
    pub history_weights: Vec<BigUint>,
    /// Complete candidate-history boundary maps retained by each exact action descent.
    pub reconstruction_fibre: Vec<FactoredHistoryQuotientPassage>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactoredHistoryQuotientPassage {
    pub source_history_population: u32,
    pub generator_population: u32,
    pub presented_history_population: u32,
    pub target_history_population: u32,
    pub candidate_to_target: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum FactoredMomentError {
    #[error("the factored moment incidence, current, or generator has a malformed extent")]
    Shape,
    #[error("the factored moment image collapsed to zero")]
    ZeroImage,
    #[error("the factored moment chart failed its exact reconstruction certificate")]
    Reconstruction,
    #[error("the canonical moment chart is not integral at the requested apparatus boundary")]
    NonIntegralChart,
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
}
