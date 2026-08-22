//! Local cultivation on a generator-native receiver/history ecology.
//!
//! A receiver difference does not authorize a global parameter sweep.  It names one native port
//! and one already-retained ordered word.  The return rides that word in reverse composition order
//! and deposits a factorized exact morphology at the addressed port.  The first admitted species
//! is a rank-one metric reflection:
//!
//! ```text
//! R = I + u v^T,          R^T G R = G,          R^2 = I.
//! ```
//!
//! The rank is measured from `u v^T`; it is never a caller aperture.  `G` is a receiver metric,
//! not an assumption that a bare transpose is an adjoint.  Validation computes
//! `G^-1 R^T G` and requires the reflection itself, which is its inverse in this regime.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use relational_geometry::Rat;

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::generator_native_rest::{GeneratorNativeRest, GeneratorNativeRestError};
use crate::receiver_exact_compression::InputId;
use crate::receiver_history_compression::NativeStateId;

pub const CULTIVATED_HISTORY_SCHEMA: &str = "holonics.m4.receiver-history-cultivation.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PredecessorNativeIdentity {
    pub sha256: String,
    pub extent: u64,
}

impl PredecessorNativeIdentity {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        Self {
            sha256: format!("{:x}", Sha256::digest(bytes)),
            extent: bytes.len() as u64,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RankOneMetricMorphology {
    pub left: Vec<Rat>,
    pub right: Vec<Rat>,
    pub receiver_metric: ExactRatMatrix,
    /// One exact coordinate rebase.  Repeated action transports the seed factor through its whole
    /// symmetry orbit; the orbit extent is derived by closure, not declared separately.
    pub coordinate_transport: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CultivatedReceiverHistoryRest {
    pub schema: String,
    pub predecessor: PredecessorNativeIdentity,
    pub port: NativeStateId,
    pub leader_word: Vec<InputId>,
    pub leader_endpoint: NativeStateId,
    pub morphology: RankOneMetricMorphology,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CausalAdjointReceipt {
    pub port: NativeStateId,
    pub leader_word: Vec<InputId>,
    pub return_word: Vec<InputId>,
    pub leader_endpoint: NativeStateId,
    pub ambient_dimension: usize,
    pub orbit_extent: usize,
    pub measured_delta_ranks: Vec<usize>,
    pub reflections: Vec<ExactRatMatrix>,
    pub metric_adjoints: Vec<ExactRatMatrix>,
    pub metric_square_held: bool,
    pub involution_held: bool,
    pub zero_morphology_foil_separated_at: (usize, usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MountedCultivatedHistory {
    base: GeneratorNativeRest,
    rest: CultivatedReceiverHistoryRest,
    receipt: CausalAdjointReceipt,
}

impl CultivatedReceiverHistoryRest {
    pub fn seal(
        predecessor_bytes: &[u8],
        port: NativeStateId,
        leader_word: Vec<InputId>,
        morphology: RankOneMetricMorphology,
    ) -> Result<(Self, CausalAdjointReceipt), HistoryCultivationError> {
        let base = GeneratorNativeRest::read(predecessor_bytes)?;
        let leader_endpoint = base.conduct_word(port, &leader_word)?;
        let rest = Self {
            schema: CULTIVATED_HISTORY_SCHEMA.to_owned(),
            predecessor: PredecessorNativeIdentity::from_bytes(predecessor_bytes),
            port,
            leader_word,
            leader_endpoint,
            morphology,
        };
        let receipt = rest.validate_against(&base)?;
        Ok((rest, receipt))
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, HistoryCultivationError> {
        serde_json::to_vec(self).map_err(|error| HistoryCultivationError::Wire(error.to_string()))
    }

    pub fn mount(
        bytes: &[u8],
        predecessor_bytes: &[u8],
    ) -> Result<MountedCultivatedHistory, HistoryCultivationError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| HistoryCultivationError::Wire(error.to_string()))?;
        if rest.schema != CULTIVATED_HISTORY_SCHEMA {
            return Err(HistoryCultivationError::Schema(rest.schema));
        }
        let actual = PredecessorNativeIdentity::from_bytes(predecessor_bytes);
        if rest.predecessor != actual {
            return Err(HistoryCultivationError::PredecessorDrift {
                expected: rest.predecessor,
                actual,
            });
        }
        let base = GeneratorNativeRest::read(predecessor_bytes)?;
        let receipt = rest.validate_against(&base)?;
        Ok(MountedCultivatedHistory {
            base,
            rest,
            receipt,
        })
    }

    fn validate_against(
        &self,
        base: &GeneratorNativeRest,
    ) -> Result<CausalAdjointReceipt, HistoryCultivationError> {
        if self.schema != CULTIVATED_HISTORY_SCHEMA {
            return Err(HistoryCultivationError::Schema(self.schema.clone()));
        }
        let endpoint = base.conduct_word(self.port, &self.leader_word)?;
        if endpoint != self.leader_endpoint {
            return Err(HistoryCultivationError::LeaderEndpoint {
                declared: self.leader_endpoint,
                returned: endpoint,
            });
        }
        let dimension = self.morphology.left.len();
        if dimension == 0
            || self.morphology.right.len() != dimension
            || self.morphology.coordinate_transport.len() != dimension
            || self.morphology.receiver_metric.rows() != dimension
            || self.morphology.receiver_metric.columns() != dimension
        {
            return Err(HistoryCultivationError::MorphologyShape);
        }
        let permutation = &self.morphology.coordinate_transport;
        let mut seen = vec![false; dimension];
        for coordinate in permutation {
            let Some(slot) = seen.get_mut(*coordinate) else {
                return Err(HistoryCultivationError::CoordinateTransport);
            };
            if *slot {
                return Err(HistoryCultivationError::CoordinateTransport);
            }
            *slot = true;
        }
        let permutation_matrix = permutation_matrix(permutation)?;
        if permutation_matrix
            .transpose()?
            .multiply(&self.morphology.receiver_metric)?
            .multiply(&permutation_matrix)?
            != self.morphology.receiver_metric
        {
            return Err(HistoryCultivationError::CoordinateMetricDefect);
        }
        let identity = ExactRatMatrix::identity(dimension)?;
        let metric_inverse = self.morphology.receiver_metric.inverse()?;
        let mut left = self.morphology.left.clone();
        let mut right = self.morphology.right.clone();
        let seed = (left.clone(), right.clone());
        let mut factors = Vec::new();
        loop {
            if factors
                .iter()
                .any(|candidate| candidate == &(left.clone(), right.clone()))
            {
                if (left, right) != seed || factors.len() != dimension {
                    return Err(HistoryCultivationError::CoordinateOrbit(factors.len()));
                }
                break;
            }
            factors.push((left.clone(), right.clone()));
            left = permute(&left, permutation);
            right = permute(&right, permutation);
        }
        let mut measured_delta_ranks = Vec::with_capacity(factors.len());
        let mut reflections = Vec::with_capacity(factors.len());
        let mut metric_adjoints = Vec::with_capacity(factors.len());
        let mut separator = None;
        for (left_values, right_values) in &factors {
            let left = ExactRatMatrix::new(
                left_values
                    .iter()
                    .cloned()
                    .map(|entry| vec![entry])
                    .collect(),
            )?;
            let right = ExactRatMatrix::new(vec![right_values.clone()])?;
            let delta = left.multiply(&right)?;
            let rank = delta.rank()?;
            if rank != 1 {
                return Err(HistoryCultivationError::MorphologyRank(rank));
            }
            measured_delta_ranks.push(rank);
            if separator.is_none() {
                separator = delta
                    .entries()
                    .iter()
                    .position(|entry| entry != &Rat::from_integer(0.into()))
                    .map(|ordinal| (ordinal / dimension, ordinal % dimension));
            }
            let reflection = identity.add(&delta)?;
            let metric_square = reflection
                .transpose()?
                .multiply(&self.morphology.receiver_metric)?
                .multiply(&reflection)?;
            if metric_square != self.morphology.receiver_metric {
                return Err(HistoryCultivationError::MetricDefect);
            }
            if reflection.multiply(&reflection)? != identity {
                return Err(HistoryCultivationError::NotInvolutive);
            }
            let metric_adjoint = metric_inverse
                .multiply(&reflection.transpose()?)?
                .multiply(&self.morphology.receiver_metric)?;
            if metric_adjoint != reflection {
                return Err(HistoryCultivationError::AdjointDefect);
            }
            reflections.push(reflection);
            metric_adjoints.push(metric_adjoint);
        }
        let separator = separator.ok_or(HistoryCultivationError::MorphologyRank(0))?;
        let mut return_word = self.leader_word.clone();
        return_word.reverse();
        Ok(CausalAdjointReceipt {
            port: self.port,
            leader_word: self.leader_word.clone(),
            return_word,
            leader_endpoint: endpoint,
            ambient_dimension: dimension,
            orbit_extent: factors.len(),
            measured_delta_ranks,
            reflections,
            metric_adjoints,
            metric_square_held: true,
            involution_held: true,
            zero_morphology_foil_separated_at: separator,
        })
    }
}

impl MountedCultivatedHistory {
    pub fn base(&self) -> &GeneratorNativeRest {
        &self.base
    }

    pub fn rest(&self) -> &CultivatedReceiverHistoryRest {
        &self.rest
    }

    pub fn receipt(&self) -> &CausalAdjointReceipt {
        &self.receipt
    }

    /// Exact serial admission/control face.  Production conduct is expected to enact this same
    /// factorized law on the resident apparatus and compare the returned consequence.
    pub fn apply_exact(
        &self,
        orbit_member: usize,
        input: &[Rat],
    ) -> Result<Vec<Rat>, HistoryCultivationError> {
        if input.len() != self.receipt.ambient_dimension {
            return Err(HistoryCultivationError::InputShape);
        }
        self.receipt
            .reflections
            .get(orbit_member)
            .ok_or(HistoryCultivationError::OrbitMember(orbit_member))?
            .apply(input)
            .map_err(HistoryCultivationError::from)
    }

    pub fn conduct_native_word(
        &self,
        start: NativeStateId,
        word: &[InputId],
    ) -> Result<NativeStateId, HistoryCultivationError> {
        self.base
            .conduct_word(start, word)
            .map_err(HistoryCultivationError::from)
    }

    /// Targeted ablation removes only the local morphology.  The predecessor ecology is retained
    /// by ownership and remains available for unrelated native conduct.
    pub fn ablate(self) -> AblatedHistoryRest {
        AblatedHistoryRest {
            base: self.base,
            removed_port: self.rest.port,
            removed_predecessor: self.rest.predecessor,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AblatedHistoryRest {
    base: GeneratorNativeRest,
    removed_port: NativeStateId,
    removed_predecessor: PredecessorNativeIdentity,
}

impl AblatedHistoryRest {
    pub fn conduct_native_word(
        &self,
        start: NativeStateId,
        word: &[InputId],
    ) -> Result<NativeStateId, HistoryCultivationError> {
        self.base
            .conduct_word(start, word)
            .map_err(HistoryCultivationError::from)
    }

    pub fn apply_exact(
        &self,
        _orbit_member: usize,
        _input: &[Rat],
    ) -> Result<Vec<Rat>, HistoryCultivationError> {
        Err(HistoryCultivationError::Ablated {
            port: self.removed_port,
            predecessor: self.removed_predecessor.clone(),
        })
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum HistoryCultivationError {
    #[error(transparent)]
    Native(#[from] GeneratorNativeRestError),
    #[error("cultivated receiver-history wire refused: {0}")]
    Wire(String),
    #[error("unknown cultivated receiver-history schema {0}")]
    Schema(String),
    #[error("the cultivated rest's predecessor moved: expected {expected:?}, actual {actual:?}")]
    PredecessorDrift {
        expected: PredecessorNativeIdentity,
        actual: PredecessorNativeIdentity,
    },
    #[error("the leader endpoint moved: declared {declared:?}, returned {returned:?}")]
    LeaderEndpoint {
        declared: NativeStateId,
        returned: NativeStateId,
    },
    #[error("the local morphology, metric and input carrier do not share one positive extent")]
    MorphologyShape,
    #[error("the coordinate transport is not a permutation of the morphology carrier")]
    CoordinateTransport,
    #[error("the coordinate transport does not preserve the declared receiver metric")]
    CoordinateMetricDefect,
    #[error("the coordinate orbit closed after {0} members instead of covering the carrier")]
    CoordinateOrbit(usize),
    #[error("the measured morphology rank is {0}, not one")]
    MorphologyRank(usize),
    #[error("the candidate does not preserve its declared receiver metric")]
    MetricDefect,
    #[error("the candidate is not an involution")]
    NotInvolutive,
    #[error("the declared metric adjoint is not the returned inverse reflection")]
    AdjointDefect,
    #[error("the held-out input left the cultivated carrier")]
    InputShape,
    #[error("orbit member {0} is outside the cultivated symmetry family")]
    OrbitMember(usize),
    #[error("targeted ablation removed the local morphology at {port:?} from {predecessor:?}")]
    Ablated {
        port: NativeStateId,
        predecessor: PredecessorNativeIdentity,
    },
    #[error("exact linear cultivation refused: {0}")]
    ExactLinear(String),
}

impl From<ExactLinearError> for HistoryCultivationError {
    fn from(error: ExactLinearError) -> Self {
        Self::ExactLinear(error.to_string())
    }
}

fn permute(values: &[Rat], transport: &[usize]) -> Vec<Rat> {
    transport
        .iter()
        .map(|source| values[*source].clone())
        .collect()
}

fn permutation_matrix(transport: &[usize]) -> Result<ExactRatMatrix, ExactLinearError> {
    let dimension = transport.len();
    ExactRatMatrix::new(
        transport
            .iter()
            .copied()
            .map(|source| {
                (0..dimension)
                    .map(|column| Rat::from_integer(i64::from(column == source).into()))
                    .collect()
            })
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generator_native_rest::{GeneratorNativeRest, NativeGenerator};
    use crate::receiver_history_compression::NativeTransport;

    fn predecessor() -> Vec<u8> {
        GeneratorNativeRest::new(
            vec![NativeStateId(0), NativeStateId(1)],
            Vec::new(),
            vec![NativeGenerator {
                generator: InputId(0),
                transport: vec![
                    NativeTransport {
                        from: NativeStateId(0),
                        to: NativeStateId(1),
                    },
                    NativeTransport {
                        from: NativeStateId(1),
                        to: NativeStateId(1),
                    },
                ],
            }],
        )
        .expect("base")
        .canonical_bytes()
        .expect("bytes")
    }

    fn integer(value: i64) -> Rat {
        Rat::from_integer(value.into())
    }

    #[test]
    fn a_metric_reflection_seals_remounts_and_ablates_locally() {
        let base = predecessor();
        let morphology = RankOneMetricMorphology {
            left: vec![integer(1), integer(0)],
            right: vec![integer(-2), integer(0)],
            receiver_metric: ExactRatMatrix::identity(2).expect("metric"),
            coordinate_transport: vec![1, 0],
        };
        let (rest, receipt) = CultivatedReceiverHistoryRest::seal(
            &base,
            NativeStateId(0),
            vec![InputId(0)],
            morphology,
        )
        .expect("seal");
        assert_eq!(receipt.measured_delta_ranks, vec![1, 1]);
        assert_eq!(receipt.return_word, vec![InputId(0)]);
        let bytes = rest.canonical_bytes().expect("wire");
        let mounted = CultivatedReceiverHistoryRest::mount(&bytes, &base).expect("mount");
        assert_eq!(
            mounted
                .apply_exact(0, &[integer(3), integer(5)])
                .expect("apply"),
            vec![integer(-3), integer(5)]
        );
        let ablated = mounted.ablate();
        assert!(ablated.apply_exact(0, &[integer(3), integer(5)]).is_err());
        assert_eq!(
            ablated
                .conduct_native_word(NativeStateId(0), &[InputId(0)])
                .expect("base conduct"),
            NativeStateId(1)
        );
    }
}
