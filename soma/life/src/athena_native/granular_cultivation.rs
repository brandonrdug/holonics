//! Scale-natural fine morphology cultivated over an already-admitted Athena body.
//!
//! The predecessor is moved into this successor unchanged.  Exterior octets cross only while the
//! later organ is cultivated; rested state retains sparse oriented boundary-port incidence and
//! complete affine-factor support, never strings, words, token classes, or source payloads.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{BufReader, Read},
    path::Path,
};

use holonic_engine::{
    receiver_exact_compression::ItemId,
    receiver_history_compression::{NativeStateId, ReceiverHistoryCompression},
};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::exchange_world_tube::{
    ContinuationAperture, ContinuationFamily, MessageAddress, VisibleMessageFace,
    VisibleMessageProjection,
};

use super::membrane_cultivation::MembraneDifferenceStanding;
use super::{
    AffineLaboratoryCellWithdrawal, AffineLaboratoryCultivatedAthenaRest, AthenaMembraneStanding,
    GranularAthenaMembraneStanding, GranularFactorAction, GranularFactorGenerator,
    GranularFactorReceiver, LaboratoryCellAffineSection, LaboratoryFactorCycleCorrespondence,
    NativeGranularPotential, NativeGranularPotentialBuilder, ReceiverHistoryRealizationPassage,
    RecurrentReturnedAffineDifferenceWithdrawal, RecurrentReturnedAffineLaboratoryAthenaRest,
    RecurrentReturnedAffinePredecessor, ReturnedAffineLaboratoryAthenaRest,
    SituatedCultivationBranch, SituatedDifferenceSection,
};

pub const GRANULAR_ATHENA_REST_SCHEMA: &str = "soma-life.granular-athena-rest.v9";
pub const GRANULAR_FACTOR_LINEAGE_SCHEMA: &str = "soma-life.granular-factor-lineage-projection.v2";
pub const GRANULAR_CULTIVATION_WITHDRAWAL_SCHEMA: &str =
    "soma-life.granular-cultivation-withdrawal.v9";
pub const GRANULAR_SOURCE_NEUTRAL_COMPOSITION_SCHEMA: &str =
    "soma-life.granular-source-neutral-composition.v1";

/// Cold projection of the exact L1 source-to-affine-factor correspondence.
///
/// This testimony is consumed during cultivation and is not a hot inference organ. It exists
/// because the admitted L5 receiver intentionally condensed family identity out of its relational
/// occurrence chart; repeated message surfaces cannot reconstruct this join.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularFactorLineageProjection {
    schema: String,
    source_product_schema: String,
    source_product_wire_sha256: String,
    predecessor_rest_wire_sha256: String,
    factor_sources: Vec<Vec<u64>>,
    factor_action: GranularFactorAction,
    identity_sha256: String,
}

#[derive(Deserialize)]
struct ExchangeProductLineageWire {
    schema: String,
    predecessor_rest_wire_sha256: String,
    native_action: ReceiverHistoryCompression,
    native_covers: Vec<ExchangeCoverLineageWire>,
}

#[derive(Deserialize)]
struct ExchangeCoverLineageWire {
    native: NativeStateId,
    source_reconstruction_fibre: BTreeSet<ItemId>,
}

impl GranularFactorLineageProjection {
    pub fn read_product(path: &Path) -> Result<Self, GranularCultivationError> {
        let product: ExchangeProductLineageWire = serde_json::from_reader(BufReader::new(
            File::open(path)
                .map_err(|error| GranularCultivationError::Exterior(error.to_string()))?,
        ))
        .map_err(|error| GranularCultivationError::Exterior(error.to_string()))?;
        product
            .native_action
            .validate()
            .map_err(|error| GranularCultivationError::Exterior(error.to_string()))?;
        let source_product_wire_sha256 = sha256_file(path)?;
        let factor_sources = product
            .native_covers
            .iter()
            .map(|cover| {
                cover
                    .source_reconstruction_fibre
                    .iter()
                    .map(|source| source.0)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let factor_action =
            factor_action_from_product(&product.native_action, &product.native_covers)?;
        let mut projection = Self {
            schema: GRANULAR_FACTOR_LINEAGE_SCHEMA.to_owned(),
            source_product_schema: product.schema,
            source_product_wire_sha256,
            predecessor_rest_wire_sha256: product.predecessor_rest_wire_sha256,
            factor_sources,
            factor_action,
            identity_sha256: String::new(),
        };
        projection.identity_sha256 = projection.rederived_identity()?;
        projection.validate()?;
        Ok(projection)
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn factor_population(&self) -> usize {
        self.factor_sources.len()
    }

    pub fn factor_action(&self) -> &GranularFactorAction {
        &self.factor_action
    }

    fn source_factors(&self) -> Result<BTreeMap<u64, u32>, GranularCultivationError> {
        let mut sources = BTreeMap::new();
        for (factor, fibre) in self.factor_sources.iter().enumerate() {
            let factor = u32::try_from(factor).map_err(|_| {
                GranularCultivationError::Exterior("factor extent overflow".to_owned())
            })?;
            for source in fibre {
                if sources.insert(*source, factor).is_some() {
                    return Err(GranularCultivationError::Exterior(
                        "one L1 source occurs in two affine factor fibres".to_owned(),
                    ));
                }
            }
        }
        Ok(sources)
    }

    fn validate(&self) -> Result<(), GranularCultivationError> {
        let sources = self.source_factors()?;
        if self.schema != GRANULAR_FACTOR_LINEAGE_SCHEMA
            || self.source_product_schema != "soma-life.exchange-situated-product.v2"
            || !is_digest(&self.source_product_wire_sha256)
            || !is_digest(&self.predecessor_rest_wire_sha256)
            || self.factor_sources.is_empty()
            || self.factor_sources.iter().any(Vec::is_empty)
            || sources.is_empty()
            || self.factor_action.validate().is_err()
            || self.factor_action.native_states.len() != self.factor_sources.len()
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(GranularCultivationError::Exterior(
                "the L1 factor-lineage projection is malformed".to_owned(),
            ));
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, GranularCultivationError> {
        digest_json(&(
            GRANULAR_FACTOR_LINEAGE_SCHEMA,
            &self.source_product_schema,
            &self.source_product_wire_sha256,
            &self.predecessor_rest_wire_sha256,
            &self.factor_sources,
            &self.factor_action,
        ))
    }
}

fn factor_action_from_product(
    native: &ReceiverHistoryCompression,
    covers: &[ExchangeCoverLineageWire],
) -> Result<GranularFactorAction, GranularCultivationError> {
    let native_states = covers.iter().map(|cover| cover.native).collect::<Vec<_>>();
    let factor_by_native = native_states
        .iter()
        .copied()
        .enumerate()
        .map(|(factor, native)| {
            u32::try_from(factor)
                .map(|factor| (native, factor))
                .map_err(|_| {
                    GranularCultivationError::Exterior("factor extent overflow".to_owned())
                })
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;
    if factor_by_native.len() != covers.len()
        || native
            .native_population
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            != native_states.iter().copied().collect::<BTreeSet<_>>()
    {
        return Err(GranularCultivationError::Exterior(
            "the L1 native action and affine factor population differ".to_owned(),
        ));
    }
    let factor_sources = covers
        .iter()
        .map(|cover| (cover.native, &cover.source_reconstruction_fibre))
        .collect::<BTreeMap<_, _>>();
    if native
        .reconstruction_fibres
        .iter()
        .any(|fibre| factor_sources.get(&fibre.native).copied() != Some(&fibre.sources))
    {
        return Err(GranularCultivationError::Exterior(
            "the L1 action and affine reconstruction fibres do not commute".to_owned(),
        ));
    }
    let receiver_factors = native_states
        .iter()
        .map(|state| {
            let mut factors = native
                .receiver_factors
                .iter()
                .filter(|factor| factor.native == *state)
                .map(|factor| GranularFactorReceiver {
                    receiver: factor.receiver,
                    observation: factor.observation,
                })
                .collect::<Vec<_>>();
            factors.sort();
            factors
        })
        .collect::<Vec<_>>();
    let mut generators = native
        .generators
        .iter()
        .map(|square| {
            let native_targets = square
                .native
                .iter()
                .map(|edge| (edge.from, edge.to))
                .collect::<BTreeMap<_, _>>();
            let targets = native_states
                .iter()
                .map(|state| {
                    native_targets
                        .get(state)
                        .and_then(|target| factor_by_native.get(target))
                        .copied()
                        .ok_or_else(|| {
                            GranularCultivationError::Exterior(format!(
                                "generator {} does not descend on native factor {}",
                                square.generator.0, state.0
                            ))
                        })
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(GranularFactorGenerator {
                generator: square.generator,
                targets,
                source_square_identity_sha256: digest_json(&(
                    "soma-life.granular-source-generator-square.v1",
                    square,
                ))?,
            })
        })
        .collect::<Result<Vec<_>, GranularCultivationError>>()?;
    generators.sort_by_key(|generator| generator.generator);
    let action = GranularFactorAction {
        native_states,
        receiver_factors,
        generators,
        source_action_identity_sha256: digest_json(&(
            "soma-life.granular-source-action.v1",
            native,
        ))?,
    };
    action
        .validate()
        .map_err(|error| GranularCultivationError::Exterior(error.to_string()))?;
    Ok(action)
}

#[derive(Debug, Error)]
pub enum GranularCultivationError {
    #[error("the predecessor Athena body is malformed: {0}")]
    Predecessor(String),
    #[error("the exterior cultivation occurrence is malformed: {0}")]
    Exterior(String),
    #[error("the fine incidence carrier refused cultivation: {0}")]
    Granular(String),
    #[error("the granular Athena rest is malformed: {0}")]
    Wire(String),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularCultivationReceipt {
    pub predecessor_rest_identity_sha256: String,
    pub cultivated_rest_identity_sha256: String,
    pub cultivation_lineage_sha256: String,
    pub affine_factor_population: usize,
    pub delivered_occurrence_population: u64,
    pub caused_octet_population: u64,
    pub boundary_port_population: usize,
    pub causal_grain_population: usize,
    pub source_payload_retained: bool,
    pub word_or_token_class_authored: bool,
}

/// Exact receipt for moving an already source-neutral fine organ onto another compatible
/// continuation body.  This is composition, not another exposure: the old body is returned by
/// withdrawal, the organ is consumed, and no exterior source occurrence is consulted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularSourceNeutralCompositionReceipt {
    pub schema: String,
    pub inherited_rest_identity_sha256: String,
    pub inherited_predecessor_identity_sha256: String,
    pub inherited_cultivation_lineage_sha256: String,
    pub inherited_organ_identity_sha256: String,
    pub receiving_body_identity_sha256: String,
    pub composed_rest_identity_sha256: String,
    pub composition_lineage_sha256: String,
    pub affine_factor_population: usize,
    pub boundary_port_population: usize,
    pub causal_grain_population: usize,
    pub source_occurrence_consulted: bool,
    pub source_payload_retained: bool,
}

/// One continuing Athena owner after a later fine-incidence morphology has been cultivated.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularAthenaRest<Body> {
    schema: String,
    predecessor_rest_identity_sha256: String,
    cultivation_lineage_sha256: String,
    body: Body,
    granular: NativeGranularPotential,
    identity_sha256: String,
}

pub type GranularAffineAthenaRest = GranularAthenaRest<AffineLaboratoryCultivatedAthenaRest>;
pub type GranularReturnedAffineAthenaRest = GranularAthenaRest<ReturnedAffineLaboratoryAthenaRest>;
pub type RecurrentGranularReturnedAffineAthenaRest =
    GranularAthenaRest<RecurrentReturnedAffineLaboratoryAthenaRest>;

#[derive(Debug, PartialEq, Eq)]
pub enum RecurrentGranularReturnedAffinePredecessor {
    First(GranularReturnedAffineAthenaRest),
    Recurrent(RecurrentGranularReturnedAffineAthenaRest),
}

impl RecurrentGranularReturnedAffinePredecessor {
    pub fn identity(&self) -> &str {
        match self {
            Self::First(rest) => rest.identity(),
            Self::Recurrent(rest) => rest.identity(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct RecurrentGranularReturnedAffineDifferenceWithdrawal {
    original_rest_identity_sha256: String,
    body: RecurrentReturnedAffineDifferenceWithdrawal,
}

#[derive(Debug, PartialEq, Eq)]
pub struct RecurrentGranularRelationalCellWithdrawal {
    original_rest_identity_sha256: String,
    body: AffineLaboratoryCellWithdrawal,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GranularCultivationWithdrawal {
    schema: String,
    original_rest_identity_sha256: String,
    predecessor_rest_identity_sha256: String,
    cultivation_lineage_sha256: String,
    granular: NativeGranularPotential,
}

impl GranularCultivationWithdrawal {
    pub fn read(bytes: &[u8]) -> Result<Self, GranularCultivationError> {
        let withdrawal: Self = serde_json::from_slice(bytes)
            .map_err(|error| GranularCultivationError::Wire(error.to_string()))?;
        withdrawal.validate()?;
        Ok(withdrawal)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, GranularCultivationError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| GranularCultivationError::Wire(error.to_string()))
    }

    pub fn successor_identity(&self) -> &str {
        &self.original_rest_identity_sha256
    }

    pub fn predecessor_identity(&self) -> &str {
        &self.predecessor_rest_identity_sha256
    }

    pub fn cultivation_lineage_identity(&self) -> &str {
        &self.cultivation_lineage_sha256
    }

    fn validate(&self) -> Result<(), GranularCultivationError> {
        self.granular
            .validate()
            .map_err(|error| GranularCultivationError::Granular(error.to_string()))?;
        if self.schema != GRANULAR_CULTIVATION_WITHDRAWAL_SCHEMA
            || !is_digest(&self.original_rest_identity_sha256)
            || !is_digest(&self.predecessor_rest_identity_sha256)
            || !is_digest(&self.cultivation_lineage_sha256)
        {
            return Err(GranularCultivationError::Wire(
                "the granular cultivation withdrawal lost its lineage".to_owned(),
            ));
        }
        Ok(())
    }
}

impl GranularAffineAthenaRest {
    pub fn cultivate(
        body: AffineLaboratoryCultivatedAthenaRest,
        aperture: &ContinuationAperture,
        world: &VisibleMessageProjection,
        lineage: &GranularFactorLineageProjection,
    ) -> Result<(Self, GranularCultivationReceipt), GranularCultivationError> {
        cultivate_granular(body, aperture, world, lineage)
    }
}

impl GranularReturnedAffineAthenaRest {
    pub fn cultivate_returned(
        body: ReturnedAffineLaboratoryAthenaRest,
        aperture: &ContinuationAperture,
        world: &VisibleMessageProjection,
        lineage: &GranularFactorLineageProjection,
    ) -> Result<(Self, GranularCultivationReceipt), GranularCultivationError> {
        cultivate_granular(body, aperture, world, lineage)
    }

    /// Move the already cultivated fine organ with the one affine body across a later returned
    /// difference. No source material or duplicate granular body survives beside the successor.
    pub fn deposit_additional_returned_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<RecurrentGranularReturnedAffineAthenaRest, GranularCultivationError> {
        self.validate()?;
        self.deposit_additional_returned_difference_admitted(difference)
    }

    pub(super) fn deposit_additional_returned_difference_admitted(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<RecurrentGranularReturnedAffineAthenaRest, GranularCultivationError> {
        let Self {
            schema,
            predecessor_rest_identity_sha256: _,
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256: _,
        } = self;
        let body = body
            .deposit_additional_returned_difference_admitted(difference)
            .map_err(|error| GranularCultivationError::Predecessor(error.to_string()))?;
        let mut rest = GranularAthenaRest {
            schema,
            predecessor_rest_identity_sha256: body.identity().to_owned(),
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity();
        rest.validate()?;
        Ok(rest)
    }
}

impl RecurrentGranularReturnedAffineAthenaRest {
    pub fn deposit_additional_returned_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self, GranularCultivationError> {
        self.validate()?;
        self.deposit_additional_returned_difference_admitted(difference)
    }

    pub(super) fn deposit_additional_returned_difference_admitted(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self, GranularCultivationError> {
        let Self {
            schema,
            predecessor_rest_identity_sha256: _,
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256: _,
        } = self;
        let body = body
            .deposit_additional_returned_difference_admitted(difference)
            .map_err(|error| GranularCultivationError::Predecessor(error.to_string()))?;
        let mut rest = Self {
            schema,
            predecessor_rest_identity_sha256: body.identity().to_owned(),
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity();
        rest.validate()?;
        Ok(rest)
    }

    pub fn withdraw_relational_cell(
        self,
        cell_address: &str,
    ) -> Result<(Self, RecurrentGranularRelationalCellWithdrawal), GranularCultivationError> {
        self.validate()?;
        let (rest, withdrawal) = self.withdraw_relational_cell_from_admitted(cell_address)?;
        rest.validate()?;
        Ok((rest, withdrawal))
    }

    /// Continue from an exact rest returned by `read` or an invariant-preserving owner without
    /// repeating the complete ecology admission at every nested wrapper.
    pub fn withdraw_relational_cell_from_admitted(
        self,
        cell_address: &str,
    ) -> Result<(Self, RecurrentGranularRelationalCellWithdrawal), GranularCultivationError> {
        let Self {
            schema,
            predecessor_rest_identity_sha256: _,
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256,
        } = self;
        let (body, withdrawal) = body
            .withdraw_relational_cell_from_admitted(cell_address)
            .map_err(|error| GranularCultivationError::Predecessor(error.to_string()))?;
        let mut rest = Self {
            schema,
            predecessor_rest_identity_sha256: body.identity().to_owned(),
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity();
        Ok((
            rest,
            RecurrentGranularRelationalCellWithdrawal {
                original_rest_identity_sha256: identity_sha256,
                body: withdrawal,
            },
        ))
    }

    pub fn restore_relational_cell(
        self,
        withdrawal: RecurrentGranularRelationalCellWithdrawal,
    ) -> Result<Self, GranularCultivationError> {
        self.validate()?;
        let rest = self.restore_relational_cell_from_admitted(withdrawal)?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn restore_relational_cell_from_admitted(
        self,
        withdrawal: RecurrentGranularRelationalCellWithdrawal,
    ) -> Result<Self, GranularCultivationError> {
        let Self {
            schema,
            predecessor_rest_identity_sha256: _,
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256: _,
        } = self;
        let body = body
            .restore_relational_cell_from_admitted(withdrawal.body)
            .map_err(|error| GranularCultivationError::Predecessor(error.to_string()))?;
        let mut rest = Self {
            schema,
            predecessor_rest_identity_sha256: body.identity().to_owned(),
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity();
        if rest.identity_sha256 != withdrawal.original_rest_identity_sha256 {
            return Err(GranularCultivationError::Wire(
                "granular sibling restoration did not recover the exact recurrent successor"
                    .to_owned(),
            ));
        }
        Ok(rest)
    }

    pub fn withdraw_latest_returned_difference(
        self,
    ) -> Result<
        (
            RecurrentGranularReturnedAffinePredecessor,
            RecurrentGranularReturnedAffineDifferenceWithdrawal,
        ),
        GranularCultivationError,
    > {
        self.validate()?;
        let (predecessor, withdrawal) = self.withdraw_latest_returned_difference_from_admitted()?;
        match &predecessor {
            RecurrentGranularReturnedAffinePredecessor::First(rest) => rest.validate()?,
            RecurrentGranularReturnedAffinePredecessor::Recurrent(rest) => rest.validate()?,
        }
        Ok((predecessor, withdrawal))
    }

    pub fn withdraw_latest_returned_difference_from_admitted(
        self,
    ) -> Result<
        (
            RecurrentGranularReturnedAffinePredecessor,
            RecurrentGranularReturnedAffineDifferenceWithdrawal,
        ),
        GranularCultivationError,
    > {
        let Self {
            schema,
            predecessor_rest_identity_sha256: _,
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256,
        } = self;
        let (body, withdrawal) = body
            .withdraw_latest_returned_difference_from_admitted()
            .map_err(|error| GranularCultivationError::Predecessor(error.to_string()))?;
        let predecessor = match body {
            RecurrentReturnedAffinePredecessor::First(body) => {
                let mut rest = GranularAthenaRest {
                    schema,
                    predecessor_rest_identity_sha256: body.identity().to_owned(),
                    cultivation_lineage_sha256,
                    body,
                    granular,
                    identity_sha256: String::new(),
                };
                rest.identity_sha256 = rest.rederived_identity();
                RecurrentGranularReturnedAffinePredecessor::First(rest)
            }
            RecurrentReturnedAffinePredecessor::Recurrent(body) => {
                let mut rest = GranularAthenaRest {
                    schema,
                    predecessor_rest_identity_sha256: body.identity().to_owned(),
                    cultivation_lineage_sha256,
                    body,
                    granular,
                    identity_sha256: String::new(),
                };
                rest.identity_sha256 = rest.rederived_identity();
                RecurrentGranularReturnedAffinePredecessor::Recurrent(rest)
            }
        };
        Ok((
            predecessor,
            RecurrentGranularReturnedAffineDifferenceWithdrawal {
                original_rest_identity_sha256: identity_sha256,
                body: withdrawal,
            },
        ))
    }

    pub fn restore_latest_returned_difference(
        predecessor: RecurrentGranularReturnedAffinePredecessor,
        withdrawal: RecurrentGranularReturnedAffineDifferenceWithdrawal,
    ) -> Result<Self, GranularCultivationError> {
        let rest = Self::restore_latest_returned_difference_from_admitted(predecessor, withdrawal)?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn restore_latest_returned_difference_from_admitted(
        predecessor: RecurrentGranularReturnedAffinePredecessor,
        withdrawal: RecurrentGranularReturnedAffineDifferenceWithdrawal,
    ) -> Result<Self, GranularCultivationError> {
        let predecessor_identity = predecessor.identity().to_owned();
        let (schema, cultivation_lineage_sha256, body, granular) = match predecessor {
            RecurrentGranularReturnedAffinePredecessor::First(rest) => {
                let GranularAthenaRest {
                    schema,
                    predecessor_rest_identity_sha256: _,
                    cultivation_lineage_sha256,
                    body,
                    granular,
                    identity_sha256: _,
                } = rest;
                (
                    schema,
                    cultivation_lineage_sha256,
                    RecurrentReturnedAffinePredecessor::First(body),
                    granular,
                )
            }
            RecurrentGranularReturnedAffinePredecessor::Recurrent(rest) => {
                let GranularAthenaRest {
                    schema,
                    predecessor_rest_identity_sha256: _,
                    cultivation_lineage_sha256,
                    body,
                    granular,
                    identity_sha256: _,
                } = rest;
                (
                    schema,
                    cultivation_lineage_sha256,
                    RecurrentReturnedAffinePredecessor::Recurrent(body),
                    granular,
                )
            }
        };
        let body = RecurrentReturnedAffineLaboratoryAthenaRest::
            restore_latest_returned_difference_from_admitted(body, withdrawal.body)
        .map_err(|error| GranularCultivationError::Predecessor(error.to_string()))?;
        let mut rest = Self {
            schema,
            predecessor_rest_identity_sha256: body.identity().to_owned(),
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity();
        if rest.identity_sha256 != withdrawal.original_rest_identity_sha256 {
            return Err(GranularCultivationError::Wire(
                "recurrent granular restoration did not recover the exact successor".to_owned(),
            ));
        }
        if predecessor_identity.is_empty() {
            return Err(GranularCultivationError::Wire(
                "the recurrent granular predecessor lost its address".to_owned(),
            ));
        }
        Ok(rest)
    }
}

impl<Body> GranularAthenaRest<Body>
where
    Body: AthenaMembraneStanding + Serialize + DeserializeOwned,
{
    pub fn read(bytes: &[u8]) -> Result<Self, GranularCultivationError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| GranularCultivationError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, GranularCultivationError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| GranularCultivationError::Wire(error.to_string()))
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn body(&self) -> &Body {
        &self.body
    }

    pub fn granular_potential(&self) -> &NativeGranularPotential {
        &self.granular
    }

    pub fn validate(&self) -> Result<(), GranularCultivationError> {
        self.body
            .validate_membrane_standing()
            .map_err(GranularCultivationError::Predecessor)?;
        self.granular
            .validate()
            .map_err(|error| GranularCultivationError::Granular(error.to_string()))?;
        validate_factor_base(&self.body, &self.granular)?;
        if self.schema != GRANULAR_ATHENA_REST_SCHEMA
            || self.predecessor_rest_identity_sha256 != self.body.membrane_identity()
            || !is_digest(&self.cultivation_lineage_sha256)
            || self.identity_sha256 != self.rederived_identity()
        {
            return Err(GranularCultivationError::Wire(
                "the fine-incidence successor does not reconstruct over its moved predecessor"
                    .to_owned(),
            ));
        }
        Ok(())
    }

    pub fn withdraw(
        self,
    ) -> Result<(Body, GranularCultivationWithdrawal), GranularCultivationError> {
        self.validate()?;
        let Self {
            schema: _,
            predecessor_rest_identity_sha256,
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256,
        } = self;
        Ok((
            body,
            GranularCultivationWithdrawal {
                schema: GRANULAR_CULTIVATION_WITHDRAWAL_SCHEMA.to_owned(),
                original_rest_identity_sha256: identity_sha256,
                predecessor_rest_identity_sha256,
                cultivation_lineage_sha256,
                granular,
            },
        ))
    }

    pub fn restore(
        body: Body,
        withdrawal: GranularCultivationWithdrawal,
    ) -> Result<Self, GranularCultivationError> {
        withdrawal.validate()?;
        if body.membrane_identity() != withdrawal.predecessor_rest_identity_sha256 {
            return Err(GranularCultivationError::Wire(
                "the fine-incidence organ was offered to another Athena body".to_owned(),
            ));
        }
        let GranularCultivationWithdrawal {
            schema: _,
            original_rest_identity_sha256,
            predecessor_rest_identity_sha256,
            cultivation_lineage_sha256,
            granular,
        } = withdrawal;
        let mut rest = Self {
            schema: GRANULAR_ATHENA_REST_SCHEMA.to_owned(),
            predecessor_rest_identity_sha256,
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity();
        if rest.identity_sha256 != original_rest_identity_sha256 {
            return Err(GranularCultivationError::Wire(
                "restoration did not recover the exact granular Athena identity".to_owned(),
            ));
        }
        rest.validate()?;
        Ok(rest)
    }

    /// Compose a previously cultivated source-neutral organ with a compatible Athena body.
    ///
    /// The withdrawal is the move-owned organ.  Its former predecessor and cultivation lineage
    /// remain reconstruction testimony, while the new rest receives a distinct composition
    /// lineage.  Compatibility is decided by the exact affine factor base, never by a source
    /// label, model name, modality kind, or exterior payload.
    pub fn compose_source_neutral_organ(
        body: Body,
        withdrawal: GranularCultivationWithdrawal,
    ) -> Result<(Self, GranularSourceNeutralCompositionReceipt), GranularCultivationError> {
        body.validate_membrane_standing()
            .map_err(GranularCultivationError::Predecessor)?;
        withdrawal.validate()?;
        let GranularCultivationWithdrawal {
            schema: _,
            original_rest_identity_sha256,
            predecessor_rest_identity_sha256: inherited_predecessor_identity_sha256,
            cultivation_lineage_sha256: inherited_cultivation_lineage_sha256,
            granular,
        } = withdrawal;
        validate_factor_base(&body, &granular)?;
        let inherited_organ_identity_sha256 = granular.identity().to_owned();
        let receiving_body_identity_sha256 = body.membrane_identity().to_owned();
        let composition_lineage_sha256 = digest_json(&(
            GRANULAR_SOURCE_NEUTRAL_COMPOSITION_SCHEMA,
            &original_rest_identity_sha256,
            &inherited_predecessor_identity_sha256,
            &inherited_cultivation_lineage_sha256,
            &inherited_organ_identity_sha256,
            &receiving_body_identity_sha256,
        ))?;
        let affine_factor_population = body.membrane_correspondences().len();
        let boundary_port_population = granular.boundary_port_population();
        let causal_grain_population = granular.causal_grain_population();
        let mut rest = Self {
            schema: GRANULAR_ATHENA_REST_SCHEMA.to_owned(),
            predecessor_rest_identity_sha256: receiving_body_identity_sha256.clone(),
            cultivation_lineage_sha256: composition_lineage_sha256.clone(),
            body,
            granular,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity();
        rest.validate()?;
        let receipt = GranularSourceNeutralCompositionReceipt {
            schema: GRANULAR_SOURCE_NEUTRAL_COMPOSITION_SCHEMA.to_owned(),
            inherited_rest_identity_sha256: original_rest_identity_sha256,
            inherited_predecessor_identity_sha256,
            inherited_cultivation_lineage_sha256,
            inherited_organ_identity_sha256,
            receiving_body_identity_sha256,
            composed_rest_identity_sha256: rest.identity_sha256.clone(),
            composition_lineage_sha256,
            affine_factor_population,
            boundary_port_population,
            causal_grain_population,
            source_occurrence_consulted: false,
            source_payload_retained: false,
        };
        Ok((rest, receipt))
    }

    fn rederived_identity(&self) -> String {
        hex_sha256(
            &serde_json::to_vec(&(
                GRANULAR_ATHENA_REST_SCHEMA,
                self.body.membrane_identity(),
                &self.cultivation_lineage_sha256,
                self.granular.identity(),
            ))
            .expect("the fixed granular identity tuple is serializable"),
        )
    }
}

impl<Body> MembraneDifferenceStanding for GranularAthenaRest<Body>
where
    Body: MembraneDifferenceStanding + Serialize + DeserializeOwned,
    Body::Successor: AthenaMembraneStanding + Serialize + DeserializeOwned,
{
    type Successor = GranularAthenaRest<Body::Successor>;

    fn deposit_membrane_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self::Successor, String> {
        self.validate().map_err(|error| error.to_string())?;
        let Self {
            schema,
            predecessor_rest_identity_sha256: _,
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256: _,
        } = self;
        let body = body.deposit_membrane_difference(difference)?;
        let mut rest = GranularAthenaRest {
            schema,
            predecessor_rest_identity_sha256: body.membrane_identity().to_owned(),
            cultivation_lineage_sha256,
            body,
            granular,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity();
        rest.validate().map_err(|error| error.to_string())?;
        Ok(rest)
    }
}

impl<Body> AthenaMembraneStanding for GranularAthenaRest<Body>
where
    Body: AthenaMembraneStanding + Serialize + DeserializeOwned,
{
    fn validate_membrane_standing(&self) -> Result<(), String> {
        self.body.validate_membrane_standing()?;
        self.granular
            .validate()
            .map_err(|error| error.to_string())?;
        validate_factor_base(&self.body, &self.granular).map_err(|error| error.to_string())?;
        if self.schema != GRANULAR_ATHENA_REST_SCHEMA
            || self.predecessor_rest_identity_sha256 != self.body.membrane_identity()
            || !is_digest(&self.cultivation_lineage_sha256)
            || self.identity_sha256 != self.rederived_identity()
        {
            return Err("the granular Athena membrane standing lost its lineage".to_owned());
        }
        Ok(())
    }

    fn membrane_identity(&self) -> &str {
        &self.identity_sha256
    }

    fn membrane_ecology(&self) -> &holonic_engine::native_spool::NativeSituatedSpoolBundle {
        self.body.membrane_ecology()
    }

    fn membrane_realization(&self) -> &ReceiverHistoryRealizationPassage {
        self.body.membrane_realization()
    }

    fn membrane_branches(&self) -> &[SituatedCultivationBranch] {
        self.body.membrane_branches()
    }

    fn membrane_correspondences(&self) -> &[LaboratoryFactorCycleCorrespondence] {
        self.body.membrane_correspondences()
    }

    fn membrane_affine_cells(&self) -> &[LaboratoryCellAffineSection] {
        self.body.membrane_affine_cells()
    }
}

impl<Body> GranularAthenaMembraneStanding for GranularAthenaRest<Body>
where
    Body: AthenaMembraneStanding + Serialize + DeserializeOwned,
{
    fn membrane_granular_potential(&self) -> &NativeGranularPotential {
        &self.granular
    }
}

fn cultivate_granular<Body>(
    body: Body,
    aperture: &ContinuationAperture,
    world: &VisibleMessageProjection,
    lineage: &GranularFactorLineageProjection,
) -> Result<(GranularAthenaRest<Body>, GranularCultivationReceipt), GranularCultivationError>
where
    Body: AthenaMembraneStanding + Serialize + DeserializeOwned,
{
    body.validate_membrane_standing()
        .map_err(GranularCultivationError::Predecessor)?;
    if aperture.source_occurrence_sha256 != world.source_occurrence_sha256
        || aperture.families.is_empty()
        || aperture.response_text_copied_into_atlas
        || aperture.provider_or_material_kind_routes_partition
    {
        return Err(GranularCultivationError::Exterior(
            "the aperture and exterior occurrence projection do not share one lineage".to_owned(),
        ));
    }
    lineage.validate()?;
    let factor_addresses = body
        .membrane_correspondences()
        .iter()
        .map(|factor| factor.factor_address.clone())
        .collect::<Vec<_>>();
    if lineage.factor_population() != factor_addresses.len() {
        return Err(GranularCultivationError::Exterior(
            "the L1 lineage projection and admitted affine factor base differ".to_owned(),
        ));
    }
    let source_factors = lineage.source_factors()?;
    let mut builder =
        NativeGranularPotentialBuilder::new(&factor_addresses, lineage.factor_action().clone())
            .map_err(|error| GranularCultivationError::Granular(error.to_string()))?;
    let mut delivered = 0u64;
    let mut caused_octets = 0u64;
    for (source_at, family) in ordered_families(aperture) {
        let messages = family_messages(world, family)?;
        let factor = *source_factors
            .get(&u64::try_from(source_at).map_err(|_| {
                GranularCultivationError::Exterior("source extent overflow".to_owned())
            })?)
            .ok_or_else(|| {
                GranularCultivationError::Exterior(format!(
                    "continuation family {} has no admitted predecessor-factor incidence",
                    family.occurrence
                ))
            })?;
        let passages = messages
            .iter()
            .map(|message| {
                digest_json(&(
                    "soma-life.granular-cultivation-passage.v4",
                    &family.occurrence,
                    &message.occurrence,
                    factor,
                ))
                .map(|passage_identity| (passage_identity, message.text.as_bytes()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        builder
            .receive_world_tube(
                factor,
                passages
                    .iter()
                    .map(|(identity, payload)| (identity.as_str(), *payload)),
            )
            .map_err(|error| GranularCultivationError::Granular(error.to_string()))?;
        for message in messages {
            delivered = delivered.checked_add(1).ok_or_else(|| {
                GranularCultivationError::Exterior("occurrence overflow".to_owned())
            })?;
            caused_octets = caused_octets
                .checked_add(u64::try_from(message.text.len()).map_err(|_| {
                    GranularCultivationError::Exterior("octet extent overflow".to_owned())
                })?)
                .ok_or_else(|| GranularCultivationError::Exterior("octet overflow".to_owned()))?;
        }
    }
    let granular = builder
        .finish()
        .map_err(|error| GranularCultivationError::Granular(error.to_string()))?;
    let predecessor_rest_identity_sha256 = body.membrane_identity().to_owned();
    let cultivation_lineage_sha256 = lineage.identity().to_owned();
    let mut rest = GranularAthenaRest {
        schema: GRANULAR_ATHENA_REST_SCHEMA.to_owned(),
        predecessor_rest_identity_sha256: predecessor_rest_identity_sha256.clone(),
        cultivation_lineage_sha256: cultivation_lineage_sha256.clone(),
        body,
        granular,
        identity_sha256: String::new(),
    };
    rest.identity_sha256 = rest.rederived_identity();
    rest.validate()?;
    let receipt = GranularCultivationReceipt {
        predecessor_rest_identity_sha256,
        cultivated_rest_identity_sha256: rest.identity_sha256.clone(),
        cultivation_lineage_sha256,
        affine_factor_population: factor_addresses.len(),
        delivered_occurrence_population: delivered,
        caused_octet_population: caused_octets,
        boundary_port_population: rest.granular.boundary_port_population(),
        causal_grain_population: rest.granular.causal_grain_population(),
        source_payload_retained: false,
        word_or_token_class_authored: false,
    };
    Ok((rest, receipt))
}

fn ordered_families(aperture: &ContinuationAperture) -> Vec<(usize, &ContinuationFamily)> {
    let mut families = aperture.families.iter().enumerate().collect::<Vec<_>>();
    families.sort_by_key(|(_, family)| {
        (
            family.prompt.container,
            family.prompt.record,
            family.prompt.visible_index,
        )
    });
    families
}

fn family_messages<'a>(
    world: &'a VisibleMessageProjection,
    family: &ContinuationFamily,
) -> Result<Vec<&'a VisibleMessageFace>, GranularCultivationError> {
    let mut addresses = Vec::with_capacity(
        1 + family.response.len() + usize::from(family.later_operator_return.is_some()),
    );
    addresses.push(&family.prompt);
    addresses.extend(&family.response);
    addresses.extend(family.later_operator_return.iter());
    addresses
        .into_iter()
        .map(|address| addressed_message(world, address))
        .collect()
}

fn addressed_message<'a>(
    world: &'a VisibleMessageProjection,
    address: &MessageAddress,
) -> Result<&'a VisibleMessageFace, GranularCultivationError> {
    let message = world
        .messages
        .get(usize::try_from(address.visible_index).map_err(|_| {
            GranularCultivationError::Exterior("visible-message extent overflow".to_owned())
        })?)
        .ok_or_else(|| {
            GranularCultivationError::Exterior(format!(
                "message {} escaped the exterior projection",
                address.occurrence
            ))
        })?;
    if message.occurrence != address.occurrence
        || message.text_sha256 != address.content_sha256
        || message.container != address.container
        || message.record != address.record
    {
        return Err(GranularCultivationError::Exterior(format!(
            "message {} changed across its addressed charts",
            address.occurrence
        )));
    }
    Ok(message)
}

fn validate_factor_base(
    body: &impl AthenaMembraneStanding,
    granular: &NativeGranularPotential,
) -> Result<(), GranularCultivationError> {
    if granular.factor_faces().len() != body.membrane_correspondences().len()
        || granular
            .factor_faces()
            .iter()
            .zip(body.membrane_correspondences())
            .any(|(face, correspondence)| {
                face.factor != correspondence.factor
                    || !super::granular_potential::factor_face_is_native(face)
            })
    {
        return Err(GranularCultivationError::Predecessor(
            "the fine morphology lost its exact affine factor base".to_owned(),
        ));
    }
    Ok(())
}

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn digest_json(value: &impl Serialize) -> Result<String, GranularCultivationError> {
    let bytes = serde_json::to_vec(value)
        .map_err(|error| GranularCultivationError::Wire(error.to_string()))?;
    Ok(hex_sha256(&bytes))
}

use holonic_engine::is_sha256_digest as is_digest;

fn sha256_file(path: &Path) -> Result<String, GranularCultivationError> {
    let mut reader = BufReader::new(
        File::open(path).map_err(|error| GranularCultivationError::Exterior(error.to_string()))?,
    );
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 1024 * 1024];
    loop {
        let read = reader
            .read(&mut buffer)
            .map_err(|error| GranularCultivationError::Exterior(error.to_string()))?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(hasher
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

#[cfg(test)]
mod tests {
    use std::{fs, path::PathBuf, time::Instant};

    use crate::exchange_world_tube::{remount_visible_message_projection, ContinuationAperture};

    use super::*;
    use crate::athena_native::AdmittedReturnedAffineLaboratoryRestWitness;

    #[test]
    #[ignore = "crosses the admitted 431 MB body and 2.4 GB exterior rest"]
    fn admitted_returned_body_cultivates_and_remounts_one_granular_successor() {
        let began = Instant::now();
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let body_path = root.join(concat!(
            "output/the_returned_membrane_action_cultivates_one_source_detached_athena_rest_mem4/",
            "athena-returned-membrane-cultivated.rest"
        ));
        let witness = AdmittedReturnedAffineLaboratoryRestWitness::found(
            "646401462284e6782aaa43139202c3bd5e45043e174b414e4fe851ec92f4e2ad",
            "63c9ff122e50fe94efe9bb00fea66e9eaac606c47707d07bc69301449bb9aded",
            "3ab826fb8512aae85096193ce103a384092111e8f26836415b0e1dc7eba02178",
        )
        .expect("the admitted returned-body witness is exact");
        let body = ReturnedAffineLaboratoryAthenaRest::read_admitted(
            &fs::read(body_path).expect("the admitted body is present"),
            &witness,
        )
        .expect("the admitted returned body remounts");
        eprintln!(
            "stage=body-remount elapsed_ms={}",
            began.elapsed().as_millis()
        );
        let exchange = root.join(concat!(
            "output/the_complete_laboratory_exchange_returns_for_athena_alpha/",
            "exchange-world-tube.ewtb"
        ));
        let aperture: ContinuationAperture = serde_json::from_slice(
            &fs::read(root.join(concat!(
                "output/the_complete_laboratory_exchange_returns_for_athena_alpha/",
                "04-continuation-aperture.json"
            )))
            .expect("the continuation aperture is present"),
        )
        .expect("the continuation aperture decodes");
        eprintln!(
            "stage=aperture-remount elapsed_ms={}",
            began.elapsed().as_millis()
        );
        let lineage = GranularFactorLineageProjection::read_product(&root.join(concat!(
            "output/the_exchange_receiver_histories_cross_actual_k3_pullbacks_l1/",
            "01-exchange-situated-product.rest"
        )))
        .expect("the admitted L1 factor-lineage projection mounts");
        eprintln!(
            "stage=lineage-remount elapsed_ms={}",
            began.elapsed().as_millis()
        );
        let world = remount_visible_message_projection(&exchange)
            .expect("the exterior occurrence projection streams");
        eprintln!(
            "stage=world-projection elapsed_ms={} visible_messages={} visible_octets={}",
            began.elapsed().as_millis(),
            world.messages.len(),
            world
                .messages
                .iter()
                .map(|message| message.text.len())
                .sum::<usize>()
        );
        let (rest, receipt) =
            GranularReturnedAffineAthenaRest::cultivate_returned(body, &aperture, &world, &lineage)
                .expect("the fine-incidence successor cultivates");
        eprintln!(
            "stage=cultivated elapsed_ms={}",
            began.elapsed().as_millis()
        );
        assert_eq!(receipt.affine_factor_population, 2_221);
        assert!(receipt.delivered_occurrence_population > 0);
        assert!(receipt.caused_octet_population > 0);
        assert!(receipt.boundary_port_population > 1);
        assert!(!receipt.source_payload_retained);
        assert!(!receipt.word_or_token_class_authored);
        let identity = rest.identity().to_owned();
        let (body, withdrawal) = rest.withdraw().expect("the organ withdraws");
        let granular_wire = withdrawal
            .canonical_bytes()
            .expect("the fine organ writes one exact exterior chart");
        let withdrawal = GranularCultivationWithdrawal::read(&granular_wire)
            .expect("the fine organ remounts source-detached");
        let restored = GranularReturnedAffineAthenaRest::restore(body, withdrawal)
            .expect("the exact successor restores");
        eprintln!("stage=restored elapsed_ms={}", began.elapsed().as_millis());
        assert_eq!(restored.identity(), identity);
        eprintln!(
            "{}",
            serde_json::to_string(&receipt).expect("the receipt serializes")
        );
    }
}
