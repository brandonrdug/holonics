//! Backend-independent storage for one source-neutral rested morphology.
//!
//! The package is an exterior chart over a singular `NativeEcologyRest`. Its manifest is derived
//! from that hot body; parented lineage, evaluation, apparatus, and export testimony remain
//! physically separate lanes and never route native conduct.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::{
    native_ecology::holonic_intelligence::{
        DimensionFace, ExteriorDegree, IncidenceNullity, IncidenceRank, RepresentationRank,
        TopologicalDegree,
    },
    native_spool::{
        NativeCollapsedFibre, NativeExactReconstructionFibre, NativeMixedConstitutiveFamily,
        NativeShortestSeparator, NativeSituatedThreadWithdrawal, NativeSpoolRefusal, NativeThread,
        NativeTransportScaffold, SituatedNativeTransportScaffold, NATIVE_SPOOL_SCHEMA,
        NATIVE_THREAD_SCHEMA, NATIVE_TRANSPORT_SCAFFOLD_SCHEMA,
        SITUATED_NATIVE_TRANSPORT_SCAFFOLD_SCHEMA,
    },
    receiver_exact_compression::{Observation, ReceiverId},
    EventId,
};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::types::NATIVE_ECOLOGY_REST_SCHEMA;
use super::{
    NativeEcologyError, NativeEcologyRest, ReceiverHistoryRealizationPassage,
    ReleasedScaffoldCultivation,
};

pub const NATIVE_MORPHOLOGY_PACKAGE_SCHEMA: &str = "soma-life.native-morphology-package.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MorphologyWireSchemas {
    pub package: String,
    pub rest: String,
    pub scaffold: String,
    pub situated_scaffold: String,
    pub spool: String,
    pub thread: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MorphologyLineage {
    pub generation: u64,
    pub parent_occurrences: BTreeSet<EventId>,
    pub returned_occurrences: BTreeSet<EventId>,
}

impl MorphologyLineage {
    pub fn origin() -> Self {
        Self {
            generation: 0,
            parent_occurrences: BTreeSet::new(),
            returned_occurrences: BTreeSet::new(),
        }
    }

    fn validate(&self, hot_occurrences: &BTreeSet<EventId>) -> Result<(), MorphologyPackageError> {
        let origin = self.generation == 0
            && self.parent_occurrences.is_empty()
            && self.returned_occurrences.is_empty();
        let cultivated = self.generation > 0
            && !self.parent_occurrences.is_empty()
            && !self.returned_occurrences.is_empty()
            && self.returned_occurrences.is_subset(hot_occurrences)
            && self
                .parent_occurrences
                .is_disjoint(&self.returned_occurrences);
        if !origin && !cultivated {
            return Err(MorphologyPackageError::Lineage);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MorphologyAnatomyManifest {
    pub spool_population: usize,
    pub thread_population: usize,
    pub occurrence_population: usize,
    pub native_population: usize,
    pub connected_component_population: usize,
    pub incidence_rank: usize,
    pub incidence_nullity: usize,
    pub cycle_rank: usize,
    pub topological_degrees: BTreeSet<usize>,
    pub exterior_degrees: BTreeSet<usize>,
    pub representation_ranks: BTreeSet<usize>,
    pub generator_population: usize,
    pub receiver_population: usize,
    pub collapsed_fibre_population: usize,
    pub collapsed_occurrence_population: usize,
    pub shortest_separator_population: usize,
    pub mutual_constitutive_population: usize,
    pub greatest_local_valence: usize,
    pub open_obligation_population: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InferenceConfigurationAddress {
    pub ingress_aperture: String,
    pub occurrence: EventId,
    pub receiver: ReceiverId,
    pub continuation_receiver: String,
    pub world_return_law: String,
    pub emission_codec: String,
    pub apparatus: String,
    pub stochastic_current: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConfigurationEvaluationReceipt {
    pub configuration: InferenceConfigurationAddress,
    pub observations: Vec<Observation>,
    pub qualitative_surface_is_probe: bool,
}

impl ConfigurationEvaluationReceipt {
    fn validate(&self) -> Result<(), MorphologyPackageError> {
        let configuration = &self.configuration;
        if configuration.ingress_aperture.is_empty()
            || configuration.continuation_receiver.is_empty()
            || configuration.world_return_law.is_empty()
            || configuration.emission_codec.is_empty()
            || configuration.apparatus.is_empty()
            || self.observations.is_empty()
            || !self.qualitative_surface_is_probe
        {
            return Err(MorphologyPackageError::Evaluation);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiverCapabilityManifest {
    pub native_receiver_family: BTreeSet<ReceiverId>,
    pub evaluated_configurations: Vec<InferenceConfigurationAddress>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExportCodecKind {
    Onnx,
    Safetensors,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ApparatusRealization {
    pub apparatus_family: String,
    pub realization_version: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExportRealization {
    pub codec: ExportCodecKind,
    pub schema_or_opset: String,
    pub receiver_family: BTreeSet<ReceiverId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RealizationManifest {
    pub apparatus: Vec<ApparatusRealization>,
    pub exports: Vec<ExportRealization>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MorphologyVariantManifest {
    pub wire_schemas: MorphologyWireSchemas,
    pub lineage: MorphologyLineage,
    pub receiver_capability: ReceiverCapabilityManifest,
    pub realization: RealizationManifest,
    pub anatomy: MorphologyAnatomyManifest,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MorphologyReconstructionLane {
    pub collapsed_fibres: Vec<NativeCollapsedFibre>,
    pub shortest_separators: Vec<NativeShortestSeparator>,
    pub mixed_constitutive_families: Vec<NativeMixedConstitutiveFamily>,
    pub exact_reconstruction_fibres: Vec<NativeExactReconstructionFibre>,
    pub departed_inherited_withdrawals: Vec<Vec<u8>>,
    pub open_obligations: Vec<String>,
}

/// The two admitted rested native owners. `Situated` carries cultivated exact fibres beside the
/// same singular native scaffold; neither variant can contain a foreign executor.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "rest_kind", rename_all = "kebab-case")]
pub enum RestedMorphology {
    Native(NativeEcologyRest),
    Situated {
        ecology: SituatedNativeTransportScaffold,
        realization: ReceiverHistoryRealizationPassage,
    },
}

impl From<NativeEcologyRest> for RestedMorphology {
    fn from(rest: NativeEcologyRest) -> Self {
        Self::Native(rest)
    }
}

impl RestedMorphology {
    pub fn situated(
        ecology: SituatedNativeTransportScaffold,
    ) -> Result<Self, MorphologyPackageError> {
        ecology.validate()?;
        let realization = ReceiverHistoryRealizationPassage::found(ecology.native())?;
        Ok(Self::Situated {
            ecology,
            realization,
        })
    }

    pub fn native(&self) -> &NativeTransportScaffold {
        match self {
            Self::Native(rest) => &rest.ecology,
            Self::Situated { ecology, .. } => ecology.native(),
        }
    }

    pub fn realization(&self) -> &ReceiverHistoryRealizationPassage {
        match self {
            Self::Native(rest) => &rest.realization,
            Self::Situated { realization, .. } => realization,
        }
    }

    pub fn validate(&self) -> Result<(), MorphologyPackageError> {
        match self {
            Self::Native(rest) => rest.validate()?,
            Self::Situated {
                ecology,
                realization,
            } => {
                ecology.validate()?;
                realization.validate(ecology.native())?;
            }
        }
        Ok(())
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, MorphologyPackageError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| MorphologyPackageError::Wire(error.to_string()))
    }
}

/// One exterior package. `hot` is the sole conduct owner; every other field is testimony.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMorphologyPackage {
    pub schema: String,
    pub manifest: MorphologyVariantManifest,
    hot: RestedMorphology,
    pub reconstruction: MorphologyReconstructionLane,
    pub evaluation: Vec<ConfigurationEvaluationReceipt>,
}

#[derive(Debug, Error)]
pub enum MorphologyPackageError {
    #[error("the hot native rest refused packaging: {0}")]
    Hot(String),
    #[error("the morphology lineage is malformed")]
    Lineage,
    #[error("one inference evaluation is empty or treats its surface as a gate")]
    Evaluation,
    #[error("one apparatus/export realization is malformed")]
    Realization,
    #[error("the package manifest is not the exact projection of its lanes")]
    Manifest,
    #[error("the package wire is malformed: {0}")]
    Wire(String),
}

impl From<NativeEcologyError> for MorphologyPackageError {
    fn from(error: NativeEcologyError) -> Self {
        Self::Hot(error.to_string())
    }
}

impl From<NativeSpoolRefusal> for MorphologyPackageError {
    fn from(error: NativeSpoolRefusal) -> Self {
        Self::Hot(error.to_string())
    }
}

impl NativeMorphologyPackage {
    pub fn found<Hot>(
        hot: Hot,
        lineage: MorphologyLineage,
        evaluation: Vec<ConfigurationEvaluationReceipt>,
        apparatus: Vec<ApparatusRealization>,
        exports: Vec<ExportRealization>,
    ) -> Result<Self, MorphologyPackageError>
    where
        Hot: Into<RestedMorphology>,
    {
        Self::found_parts(
            hot.into(),
            lineage,
            evaluation,
            apparatus,
            exports,
            Vec::new(),
        )
    }

    pub fn found_released(
        released: ReleasedScaffoldCultivation,
        lineage: MorphologyLineage,
        evaluation: Vec<ConfigurationEvaluationReceipt>,
        apparatus: Vec<ApparatusRealization>,
        exports: Vec<ExportRealization>,
    ) -> Result<Self, MorphologyPackageError> {
        let departed = released
            .departed_inherited
            .iter()
            .map(|withdrawal| {
                serde_json::to_vec(withdrawal)
                    .map_err(|error| MorphologyPackageError::Wire(error.to_string()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Self::found_parts(
            RestedMorphology::situated(released.hot)?,
            lineage,
            evaluation,
            apparatus,
            exports,
            departed,
        )
    }

    fn found_parts(
        hot: RestedMorphology,
        lineage: MorphologyLineage,
        evaluation: Vec<ConfigurationEvaluationReceipt>,
        apparatus: Vec<ApparatusRealization>,
        exports: Vec<ExportRealization>,
        departed_inherited_withdrawals: Vec<Vec<u8>>,
    ) -> Result<Self, MorphologyPackageError> {
        hot.validate()?;
        validate_evaluation(&evaluation)?;
        validate_realizations(&apparatus, &exports)?;
        let hot_occurrences = hot_occurrences(&hot);
        lineage.validate(&hot_occurrences)?;
        validate_departed(&departed_inherited_withdrawals)?;
        let reconstruction = reconstruction_projection(&hot, departed_inherited_withdrawals);
        let manifest = manifest_projection(&hot, lineage, &evaluation, apparatus, exports)?;
        let package = Self {
            schema: NATIVE_MORPHOLOGY_PACKAGE_SCHEMA.to_owned(),
            manifest,
            hot,
            reconstruction,
            evaluation,
        };
        package.validate()?;
        Ok(package)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, MorphologyPackageError> {
        let package: Self = serde_json::from_slice(bytes)
            .map_err(|error| MorphologyPackageError::Wire(error.to_string()))?;
        package.validate()?;
        Ok(package)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, MorphologyPackageError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| MorphologyPackageError::Wire(error.to_string()))
    }

    pub fn hot(&self) -> &RestedMorphology {
        &self.hot
    }

    pub fn into_hot(self) -> RestedMorphology {
        self.hot
    }

    pub fn replace_realizations(
        mut self,
        apparatus: Vec<ApparatusRealization>,
        exports: Vec<ExportRealization>,
    ) -> Result<Self, MorphologyPackageError> {
        validate_realizations(&apparatus, &exports)?;
        self.manifest.realization = RealizationManifest { apparatus, exports };
        self.validate()?;
        Ok(self)
    }

    pub fn validate(&self) -> Result<(), MorphologyPackageError> {
        if self.schema != NATIVE_MORPHOLOGY_PACKAGE_SCHEMA {
            return Err(MorphologyPackageError::Wire(
                "unknown morphology package schema".to_owned(),
            ));
        }
        self.hot.validate()?;
        validate_evaluation(&self.evaluation)?;
        validate_realizations(
            &self.manifest.realization.apparatus,
            &self.manifest.realization.exports,
        )?;
        validate_departed(&self.reconstruction.departed_inherited_withdrawals)?;
        self.manifest
            .lineage
            .validate(&hot_occurrences(&self.hot))?;
        let expected_manifest = manifest_projection(
            &self.hot,
            self.manifest.lineage.clone(),
            &self.evaluation,
            self.manifest.realization.apparatus.clone(),
            self.manifest.realization.exports.clone(),
        )?;
        if self.manifest != expected_manifest
            || self.reconstruction
                != reconstruction_projection(
                    &self.hot,
                    self.reconstruction.departed_inherited_withdrawals.clone(),
                )
        {
            return Err(MorphologyPackageError::Manifest);
        }
        Ok(())
    }
}

fn hot_occurrences(hot: &RestedMorphology) -> BTreeSet<EventId> {
    hot.native()
        .spools
        .iter()
        .flat_map(|spool| &spool.threads)
        .flat_map(|thread| &thread.occurrences)
        .map(|occurrence| occurrence.occurrence)
        .collect()
}

fn manifest_projection(
    hot: &RestedMorphology,
    lineage: MorphologyLineage,
    evaluation: &[ConfigurationEvaluationReceipt],
    apparatus: Vec<ApparatusRealization>,
    exports: Vec<ExportRealization>,
) -> Result<MorphologyVariantManifest, MorphologyPackageError> {
    Ok(MorphologyVariantManifest {
        wire_schemas: MorphologyWireSchemas {
            package: NATIVE_MORPHOLOGY_PACKAGE_SCHEMA.to_owned(),
            rest: NATIVE_ECOLOGY_REST_SCHEMA.to_owned(),
            scaffold: NATIVE_TRANSPORT_SCAFFOLD_SCHEMA.to_owned(),
            situated_scaffold: SITUATED_NATIVE_TRANSPORT_SCAFFOLD_SCHEMA.to_owned(),
            spool: NATIVE_SPOOL_SCHEMA.to_owned(),
            thread: NATIVE_THREAD_SCHEMA.to_owned(),
        },
        lineage,
        receiver_capability: ReceiverCapabilityManifest {
            native_receiver_family: hot
                .native()
                .spools
                .iter()
                .flat_map(|spool| spool.receiver_family.iter().copied())
                .collect(),
            evaluated_configurations: evaluation
                .iter()
                .map(|receipt| receipt.configuration.clone())
                .collect(),
        },
        realization: RealizationManifest { apparatus, exports },
        anatomy: anatomy_projection(hot)?,
    })
}

fn anatomy_projection(
    hot: &RestedMorphology,
) -> Result<MorphologyAnatomyManifest, MorphologyPackageError> {
    let profile = hot.native().intrinsic_holon_profile()?;
    let threads = hot
        .native()
        .spools
        .iter()
        .flat_map(|spool| &spool.threads)
        .collect::<Vec<_>>();
    let incidence_rank = profile
        .holons
        .iter()
        .map(|holon| exact_incidence_rank(&holon.dimensions.incidence_rank))
        .sum();
    let incidence_nullity = profile
        .holons
        .iter()
        .map(|holon| exact_incidence_nullity(&holon.dimensions.incidence_nullity))
        .sum();
    let cycle_rank = profile
        .holons
        .iter()
        .map(|holon| match holon.dimensions.cycle_rank {
            DimensionFace::Exact(rank) => rank.0,
            DimensionFace::Open(_) => 0,
        })
        .sum();
    let native_population = hot
        .native()
        .spools
        .iter()
        .flat_map(|spool| spool.native_population.iter().copied())
        .collect::<BTreeSet<_>>();
    Ok(MorphologyAnatomyManifest {
        spool_population: hot.native().spools.len(),
        thread_population: threads.len(),
        occurrence_population: threads.iter().map(|thread| thread.occurrences.len()).sum(),
        native_population: native_population.len(),
        connected_component_population: hot.realization().connected_components.len(),
        incidence_rank,
        incidence_nullity,
        cycle_rank,
        topological_degrees: profile
            .holons
            .iter()
            .map(|holon| exact_topological_degree(&holon.dimensions.topological_degree))
            .collect(),
        exterior_degrees: profile
            .holons
            .iter()
            .map(|holon| exact_exterior_degree(&holon.dimensions.exterior_degree))
            .collect(),
        representation_ranks: profile
            .holons
            .iter()
            .map(|holon| exact_representation_rank(&holon.dimensions.representation_rank))
            .collect(),
        generator_population: hot
            .native()
            .spools
            .iter()
            .map(|spool| spool.generator_family.len())
            .sum(),
        receiver_population: hot
            .native()
            .spools
            .iter()
            .flat_map(|spool| spool.receiver_family.iter().copied())
            .collect::<BTreeSet<_>>()
            .len(),
        collapsed_fibre_population: hot
            .native()
            .spools
            .iter()
            .map(|spool| spool.reconstruction_fibres.len())
            .sum(),
        collapsed_occurrence_population: hot
            .native()
            .spools
            .iter()
            .flat_map(|spool| &spool.reconstruction_fibres)
            .map(|fibre| fibre.occurrences.len())
            .sum(),
        shortest_separator_population: hot
            .native()
            .spools
            .iter()
            .map(|spool| spool.shortest_separators.len())
            .sum(),
        mutual_constitutive_population: hot
            .native()
            .spools
            .iter()
            .map(|spool| spool.mutual_constitutive_responses.len())
            .sum(),
        greatest_local_valence: greatest_local_valence(&threads),
        open_obligation_population: profile.open_obligations.len()
            + profile
                .holons
                .iter()
                .map(|holon| holon.open_obligations.len())
                .sum::<usize>(),
    })
}

fn greatest_local_valence(threads: &[&NativeThread]) -> usize {
    let mut valence = BTreeMap::new();
    for term in threads.iter().flat_map(|thread| &thread.incidence) {
        *valence.entry(term.from).or_insert(0usize) += 1;
        *valence.entry(term.to).or_insert(0usize) += 1;
    }
    valence.into_values().max().unwrap_or(0)
}

fn exact_topological_degree(face: &DimensionFace<TopologicalDegree>) -> usize {
    match face {
        DimensionFace::Exact(value) => value.0,
        DimensionFace::Open(_) => 0,
    }
}

fn exact_exterior_degree(face: &DimensionFace<ExteriorDegree>) -> usize {
    match face {
        DimensionFace::Exact(value) => value.0,
        DimensionFace::Open(_) => 0,
    }
}

fn exact_representation_rank(face: &DimensionFace<RepresentationRank>) -> usize {
    match face {
        DimensionFace::Exact(value) => value.0,
        DimensionFace::Open(_) => 0,
    }
}

fn exact_incidence_rank(face: &DimensionFace<IncidenceRank>) -> usize {
    match face {
        DimensionFace::Exact(value) => value.0,
        DimensionFace::Open(_) => 0,
    }
}

fn exact_incidence_nullity(face: &DimensionFace<IncidenceNullity>) -> usize {
    match face {
        DimensionFace::Exact(value) => value.0,
        DimensionFace::Open(_) => 0,
    }
}

fn reconstruction_projection(
    hot: &RestedMorphology,
    departed_inherited_withdrawals: Vec<Vec<u8>>,
) -> MorphologyReconstructionLane {
    let mut open_obligations = hot.realization().open_exterior.clone();
    open_obligations.sort();
    open_obligations.dedup();
    let (mixed_constitutive_families, exact_reconstruction_fibres) = match hot {
        RestedMorphology::Native(_) => (Vec::new(), Vec::new()),
        RestedMorphology::Situated { ecology, .. } => (
            ecology.mixed_constitutive_families().to_vec(),
            ecology.exact_reconstruction_fibres().to_vec(),
        ),
    };
    MorphologyReconstructionLane {
        collapsed_fibres: hot
            .native()
            .spools
            .iter()
            .flat_map(|spool| spool.reconstruction_fibres.iter().cloned())
            .collect(),
        shortest_separators: hot
            .native()
            .spools
            .iter()
            .flat_map(|spool| spool.shortest_separators.iter().cloned())
            .collect(),
        mixed_constitutive_families,
        exact_reconstruction_fibres,
        departed_inherited_withdrawals,
        open_obligations,
    }
}

fn validate_departed(departed: &[Vec<u8>]) -> Result<(), MorphologyPackageError> {
    for wire in departed {
        let withdrawal: NativeSituatedThreadWithdrawal = serde_json::from_slice(wire)
            .map_err(|error| MorphologyPackageError::Wire(error.to_string()))?;
        withdrawal.native.thread.validate()?;
        for (_, family) in &withdrawal.mixed_constitutive_families {
            family.validate()?;
        }
        for (_, fibre) in &withdrawal.exact_reconstruction_fibres {
            fibre.validate()?;
        }
    }
    Ok(())
}

fn validate_evaluation(
    evaluation: &[ConfigurationEvaluationReceipt],
) -> Result<(), MorphologyPackageError> {
    let mut configurations = BTreeSet::new();
    for receipt in evaluation {
        receipt.validate()?;
        let wire = serde_json::to_vec(&receipt.configuration)
            .map_err(|error| MorphologyPackageError::Wire(error.to_string()))?;
        if !configurations.insert(wire) {
            return Err(MorphologyPackageError::Evaluation);
        }
    }
    Ok(())
}

fn validate_realizations(
    apparatus: &[ApparatusRealization],
    exports: &[ExportRealization],
) -> Result<(), MorphologyPackageError> {
    if apparatus.iter().any(|realization| {
        realization.apparatus_family.is_empty() || realization.realization_version.is_empty()
    }) || exports.iter().any(|realization| {
        realization.schema_or_opset.is_empty() || realization.receiver_family.is_empty()
    }) {
        return Err(MorphologyPackageError::Realization);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use holonic_engine::{
        native_ecology::holonic_intelligence::{
            conduct_native_inference, Bf16ExcitationDismantling, ExteriorModality,
            ForeignBf16Excitation, InferenceCirculation, NativeInferenceAddress,
            NativeInferenceRequest,
        },
        receiver_exact_compression::ReceiverId,
        soulkiller::dismantle,
        BoundaryId, EventId, ExactComplexWaveCurrent,
    };
    use num_bigint::BigInt;
    use num_rational::BigRational as Rat;

    use super::*;
    use crate::native_intelligence::{
        consume_dismantling_return, ReturnedScaffoldInteraction, ScaffoldCultivatedRest,
    };

    fn rest(excitations: usize) -> NativeEcologyRest {
        let excitations = (0..excitations)
            .map(|at| ForeignBf16Excitation {
                event: EventId(at as u64 + 1),
                predecessor: None,
                entering_boundary: BoundaryId(at as u64 * 2 + 1),
                emitting_boundary: BoundaryId(at as u64 * 2 + 2),
                source_occurrence: format!("cold/{at}"),
                exterior_modality: ExteriorModality::Text,
                entering_codewords: vec![0x3f80 + at as u16],
                returned_codewords: vec![0x4000 + at as u16],
                interventions: BTreeSet::from([format!("intervention/{at}")]),
                receiver_consequences: BTreeSet::from([format!("consequence/{at}")]),
            })
            .collect();
        let returned = dismantle(Bf16ExcitationDismantling {
            receiver: ReceiverId(7),
            excitations,
        })
        .expect("dismantle");
        consume_dismantling_return(returned).expect("handoff").0
    }

    #[test]
    fn package_round_trip_recovers_hot_rest_and_open_reconstruction() {
        let package = NativeMorphologyPackage::found(
            rest(2),
            MorphologyLineage::origin(),
            Vec::new(),
            vec![ApparatusRealization {
                apparatus_family: "cuda".to_owned(),
                realization_version: "compute-89".to_owned(),
            }],
            Vec::new(),
        )
        .expect("package");
        let hot = package.hot().canonical_bytes().expect("hot bytes");
        let open = package.reconstruction.open_obligations.clone();
        let bytes = package.canonical_bytes().expect("package bytes");
        let text = String::from_utf8(bytes.clone())
            .expect("JSON")
            .to_ascii_lowercase();
        assert!(!text.contains("source_occurrence"));
        assert!(!text.contains("foreign executor"));
        let recovered = NativeMorphologyPackage::read(&bytes).expect("package read");
        assert_eq!(recovered.hot().canonical_bytes().expect("recovered"), hot);
        assert_eq!(recovered.reconstruction.open_obligations, open);
    }

    #[test]
    fn apparatus_and_export_replacement_preserve_hot_morphology_and_capability() {
        let package = NativeMorphologyPackage::found(
            rest(1),
            MorphologyLineage::origin(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
        .expect("package");
        let hot = package.hot().canonical_bytes().expect("hot bytes");
        let capability = package.manifest.receiver_capability.clone();
        let replaced = package
            .replace_realizations(
                vec![ApparatusRealization {
                    apparatus_family: "cpu".to_owned(),
                    realization_version: "reference".to_owned(),
                }],
                vec![ExportRealization {
                    codec: ExportCodecKind::Safetensors,
                    schema_or_opset: "holonics-v1".to_owned(),
                    receiver_family: BTreeSet::from([ReceiverId(7)]),
                }],
            )
            .expect("replace realization");
        assert_eq!(replaced.hot().canonical_bytes().expect("hot bytes"), hot);
        assert_eq!(replaced.manifest.receiver_capability, capability);
    }

    #[test]
    fn anatomically_distinct_bodies_receive_distinct_derived_manifests() {
        let one = NativeMorphologyPackage::found(
            rest(1),
            MorphologyLineage::origin(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
        .expect("one");
        let two = NativeMorphologyPackage::found(
            rest(2),
            MorphologyLineage::origin(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
        .expect("two");
        assert_ne!(one.manifest.anatomy, two.manifest.anatomy);
        assert_eq!(one.manifest.anatomy.thread_population, 1);
        assert_eq!(two.manifest.anatomy.thread_population, 2);
    }

    #[test]
    fn released_cultivation_packages_situated_hot_and_departed_reconstruction_separately() {
        let predecessor = rest(2);
        let source = NativeInferenceAddress {
            spool: predecessor.ecology.spools[0].address.clone(),
            thread: predecessor.ecology.spools[0].threads[0].address.clone(),
            occurrence: EventId(1),
        };
        let cut = conduct_native_inference(
            &predecessor.ecology,
            NativeInferenceRequest {
                address: source.clone(),
                receiver: ReceiverId(7),
            },
        )
        .expect("emission");
        let returned = ReturnedScaffoldInteraction::found(
            cut.emitted_occurrence().clone(),
            EventId(100),
            BoundaryId(101),
            ExactComplexWaveCurrent::new(
                Rat::from_integer(BigInt::from(1)),
                Rat::from_integer(BigInt::from(1)),
            ),
            Rat::from_integer(BigInt::from(1)),
            BTreeSet::new(),
        )
        .expect("return");
        drop(cut);
        let released = ScaffoldCultivatedRest::cultivate(predecessor, source, returned)
            .expect("cultivate")
            .release()
            .expect("release");
        let package = NativeMorphologyPackage::found_released(
            released,
            MorphologyLineage {
                generation: 1,
                parent_occurrences: BTreeSet::from([EventId(1), EventId(2)]),
                returned_occurrences: BTreeSet::from([EventId(100)]),
            },
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
        .expect("released package");
        assert!(matches!(package.hot(), RestedMorphology::Situated { .. }));
        assert_eq!(
            package.reconstruction.departed_inherited_withdrawals.len(),
            2
        );
        let bytes = package.canonical_bytes().expect("package bytes");
        let recovered = NativeMorphologyPackage::read(&bytes).expect("package read");
        assert_eq!(recovered.canonical_bytes().expect("recovered bytes"), bytes);
    }
}
