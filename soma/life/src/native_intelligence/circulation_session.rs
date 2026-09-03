//! Move-owned live circulation over one native morphology artifact.
//!
//! The session owns one package and returns owned boundary testimony. Conduct borrows the hot
//! morphology; continuation is admitted only through an actual addressed successor returned by
//! the preceding cut. Configuration strings remain exterior testimony and never resolve a law.

use std::collections::BTreeSet;

use holonic_engine::{
    native_ecology::holonic_intelligence::{
        conduct_native_inference, InferenceCirculation, NativeEmissionAddress, NativeFutureFace,
        NativeInferenceAddress, NativeInferenceLineage, NativeInferenceRequest,
        NativeVariableGrainEmission, OpenScope,
    },
    native_spool::{NativeCollapsedFibre, NativeShortestSeparator},
    receiver_exact_compression::{InputId, ReceiverId},
    receiver_history_compression::NativeStateId,
    BoundaryId, EventId, OccurrencePort,
};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::{
    InferenceConfigurationAddress, MorphologyArtifactError, NativeMorphologyCommit,
    NativeMorphologyArtifact,
};

pub const NATIVE_CIRCULATION_SESSION_SCHEMA: &str = "soma-life.native-circulation-session.v2";

/// Exterior configuration of one mounted circulation family.
///
/// `address.occurrence` is the first ingress occurrence. Every returned boundary replaces only
/// that coordinate with its actual cut occurrence. The remaining fields are receipt testimony;
/// none is used as a registry key or behavior selector.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeCirculationConfiguration {
    pub schema: String,
    pub address: InferenceConfigurationAddress,
}

impl NativeCirculationConfiguration {
    pub fn found(address: InferenceConfigurationAddress) -> Result<Self, NativeSessionError> {
        let configuration = Self {
            schema: NATIVE_CIRCULATION_SESSION_SCHEMA.to_owned(),
            address,
        };
        configuration.validate()?;
        Ok(configuration)
    }

    pub fn validate(&self) -> Result<(), NativeSessionError> {
        if self.schema != NATIVE_CIRCULATION_SESSION_SCHEMA
            || self.address.ingress_aperture.is_empty()
            || self.address.continuation_receiver.is_empty()
            || self.address.world_return_law.is_empty()
            || self.address.emission_codec.is_empty()
            || self.address.apparatus.is_empty()
        {
            return Err(NativeSessionError::Configuration);
        }
        Ok(())
    }

    pub(crate) fn at(&self, occurrence: EventId) -> InferenceConfigurationAddress {
        let mut address = self.address.clone();
        address.occurrence = occurrence;
        address
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeOwnedOpenScope {
    Thread,
    Spool,
    Scaffold,
}

impl From<OpenScope> for NativeOwnedOpenScope {
    fn from(scope: OpenScope) -> Self {
        match scope {
            OpenScope::Thread => Self::Thread,
            OpenScope::Spool => Self::Spool,
            OpenScope::Scaffold => Self::Scaffold,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeOwnedOpenObligation {
    pub scope: NativeOwnedOpenScope,
    pub testimony: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeOwnedInferenceAddress {
    pub spool: String,
    pub thread: String,
    pub occurrence: EventId,
}

impl From<&NativeInferenceAddress> for NativeOwnedInferenceAddress {
    fn from(address: &NativeInferenceAddress) -> Self {
        Self {
            spool: address.spool.clone(),
            thread: address.thread.clone(),
            occurrence: address.occurrence,
        }
    }
}

impl NativeOwnedInferenceAddress {
    pub(crate) fn native(&self) -> NativeInferenceAddress {
        NativeInferenceAddress {
            spool: self.spool.clone(),
            thread: self.thread.clone(),
            occurrence: self.occurrence,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeOwnedInferenceRequest {
    pub address: NativeOwnedInferenceAddress,
    pub receiver: ReceiverId,
}

impl From<&NativeInferenceRequest> for NativeOwnedInferenceRequest {
    fn from(request: &NativeInferenceRequest) -> Self {
        Self {
            address: (&request.address).into(),
            receiver: request.receiver,
        }
    }
}

impl NativeOwnedInferenceRequest {
    pub(crate) fn native(&self) -> NativeInferenceRequest {
        NativeInferenceRequest {
            address: self.address.native(),
            receiver: self.receiver,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeOwnedInferenceLineage {
    pub entering_occurrence: EventId,
    pub predecessor: Option<EventId>,
    pub entering_port: OccurrencePort,
    pub emitting_port: OccurrencePort,
    pub ordered_word: Vec<InputId>,
    pub native_start: Vec<NativeStateId>,
    pub native_end: Vec<NativeStateId>,
}

impl From<&NativeInferenceLineage> for NativeOwnedInferenceLineage {
    fn from(lineage: &NativeInferenceLineage) -> Self {
        Self {
            entering_occurrence: lineage.entering_occurrence,
            predecessor: lineage.predecessor,
            entering_port: lineage.entering_port,
            emitting_port: lineage.emitting_port,
            ordered_word: lineage.ordered_word.clone(),
            native_start: lineage.native_start.clone(),
            native_end: lineage.native_end.clone(),
        }
    }
}

/// The complete owned reconstruction population for one plural future.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeOwnedFutureReconstruction {
    pub future: NativeFutureFace,
    pub fibres: Vec<NativeCollapsedFibre>,
}

/// One owned conduct boundary. Surfaces may render this object but cannot alter it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeCirculationBoundary {
    pub schema: String,
    pub generation: u64,
    pub request: NativeOwnedInferenceRequest,
    pub configuration: InferenceConfigurationAddress,
    pub emitting_boundary: BoundaryId,
    pub emission: NativeVariableGrainEmission,
    pub lineage: NativeOwnedInferenceLineage,
    pub futures: Vec<NativeOwnedFutureReconstruction>,
    pub shortest_separators: Vec<NativeShortestSeparator>,
    pub actual_successors: Vec<NativeOwnedInferenceRequest>,
    pub open_obligations: Vec<NativeOwnedOpenObligation>,
}

impl NativeCirculationBoundary {
    pub fn emitted(&self) -> &NativeEmissionAddress {
        &self.emission.address
    }

    fn validate_shape(
        &self,
        session: &NativeCirculationSession,
    ) -> Result<(), NativeSessionError> {
        if self.schema != NATIVE_CIRCULATION_SESSION_SCHEMA
            || self.generation != session.generation()
            || self.configuration.receiver != self.request.receiver
            || self.configuration.occurrence != self.request.address.occurrence
            || self.emission.address.entering_occurrence != self.request.address.occurrence
            || self.emitting_boundary.0 == 0
            || self.futures.is_empty()
            || self.emission.grains.len() != self.futures.len()
            || self.emission.selected_grain >= self.emission.grains.len()
            || self.futures.iter().any(|future| future.fibres.is_empty())
        {
            return Err(NativeSessionError::Boundary);
        }
        Ok(())
    }

    pub(crate) fn validate_for(
        &self,
        session: &NativeCirculationSession,
    ) -> Result<(), NativeSessionError> {
        self.validate_shape(session)?;
        let expected = session.boundary_for(self.request.native())?;
        if self != &expected {
            return Err(NativeSessionError::Boundary);
        }
        Ok(())
    }
}

/// A session owns exactly one package. It is intentionally neither `Clone` nor serializable as a
/// runtime object; snapshots belong to the package/storage boundary.
#[derive(Debug)]
pub struct NativeCirculationSession {
    pub(super) package: NativeMorphologyArtifact,
    pub(super) configuration: NativeCirculationConfiguration,
    pub(super) commits: Vec<NativeMorphologyCommit>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeDeclineReceipt {
    pub schema: String,
    pub generation_before: u64,
    pub generation_after: u64,
    pub emission: NativeEmissionAddress,
    pub morphology_unchanged: bool,
}

#[derive(Debug, Error)]
pub enum NativeSessionError {
    #[error("the native morphology artifact refused the live session: {0}")]
    Package(String),
    #[error("the circulation configuration is malformed or outside the package receiver family")]
    Configuration,
    #[error("one native conduct cut refused: {0}")]
    Conduct(String),
    #[error("the owned circulation boundary is stale or malformed")]
    Boundary,
    #[error("the requested continuation is not an actual successor of this emission")]
    FalseSuccessor,
    #[error("the exterior return is not a genuinely later consequence of this emission")]
    Return,
    #[error("the exterior world-face family is incomplete, stale, duplicated, or outside its issued support")]
    WorldFace,
    #[error("the source-neutral material ingress refused: {0}")]
    Ingress(String),
    #[error("the morphology commit refused: {0}")]
    Commit(String),
    #[error("the circulation snapshot or commit journal is malformed: {0}")]
    Snapshot(String),
}

impl From<MorphologyArtifactError> for NativeSessionError {
    fn from(error: MorphologyArtifactError) -> Self {
        Self::Package(error.to_string())
    }
}

impl NativeCirculationSession {
    pub fn mount(
        package: NativeMorphologyArtifact,
        configuration: NativeCirculationConfiguration,
    ) -> Result<Self, NativeSessionError> {
        package.validate()?;
        configuration.validate()?;
        if !package
            .manifest
            .receiver_capability
            .native_receiver_family
            .contains(&configuration.address.receiver)
        {
            return Err(NativeSessionError::Configuration);
        }
        Ok(Self {
            package,
            configuration,
            commits: Vec::new(),
        })
    }

    pub fn generation(&self) -> u64 {
        self.package.manifest.lineage.generation
    }

    pub fn package(&self) -> &NativeMorphologyArtifact {
        &self.package
    }

    pub fn configuration(&self) -> &NativeCirculationConfiguration {
        &self.configuration
    }

    pub fn commits(&self) -> &[NativeMorphologyCommit] {
        &self.commits
    }

    pub fn conduct(
        &self,
        request: NativeInferenceRequest,
    ) -> Result<NativeCirculationBoundary, NativeSessionError> {
        self.boundary_for(request)
    }

    pub(crate) fn boundary_for(
        &self,
        request: NativeInferenceRequest,
    ) -> Result<NativeCirculationBoundary, NativeSessionError> {
        if request.receiver != self.configuration.address.receiver {
            return Err(NativeSessionError::Configuration);
        }
        let cut = conduct_native_inference(self.package.hot().native(), request.clone())
            .map_err(|error| NativeSessionError::Conduct(error.to_string()))?;
        let mut grains = Vec::with_capacity(cut.face().plural_futures.len());
        let mut futures = Vec::with_capacity(cut.face().plural_futures.len());
        for future in &cut.face().plural_futures {
            let fibres = cut
                .reconstruction()
                .fibres
                .iter()
                .filter(|fibre| fibre.native == future.to)
                .map(|fibre| (*fibre).clone())
                .collect::<Vec<_>>();
            if fibres.is_empty() {
                return Err(NativeSessionError::Boundary);
            }
            let occurrences = fibres
                .iter()
                .flat_map(|fibre| fibre.occurrences.iter().copied())
                .collect::<BTreeSet<_>>();
            if occurrences.is_empty() {
                return Err(NativeSessionError::Boundary);
            }
            grains.push(
                holonic_engine::native_ecology::holonic_intelligence::NativeEmissionGrain {
                    future: *future,
                    occurrences,
                },
            );
            futures.push(NativeOwnedFutureReconstruction {
                future: *future,
                fibres,
            });
        }
        let boundary = NativeCirculationBoundary {
            schema: NATIVE_CIRCULATION_SESSION_SCHEMA.to_owned(),
            generation: self.generation(),
            request: (&request).into(),
            configuration: self.configuration.at(request.address.occurrence),
            emitting_boundary: cut.active_section().thread().emitting_boundary,
            emission: NativeVariableGrainEmission {
                address: cut.emitted_occurrence().clone(),
                grains,
                selected_grain: cut.face().emitted_future,
            },
            lineage: cut.lineage().into(),
            futures,
            shortest_separators: cut.reconstruction().shortest_separators.to_vec(),
            actual_successors: cut.successor_requests().iter().map(Into::into).collect(),
            open_obligations: cut
                .open_obligations()
                .iter()
                .map(|obligation| NativeOwnedOpenObligation {
                    scope: obligation.scope.into(),
                    testimony: obligation.testimony.to_owned(),
                })
                .collect(),
        };
        boundary.validate_shape(self)?;
        Ok(boundary)
    }

    pub fn continue_from(
        &self,
        boundary: &NativeCirculationBoundary,
        successor: &NativeOwnedInferenceAddress,
    ) -> Result<NativeCirculationBoundary, NativeSessionError> {
        boundary.validate_for(self)?;
        let request = boundary
            .actual_successors
            .iter()
            .find(|request| &request.address == successor)
            .ok_or(NativeSessionError::FalseSuccessor)?
            .native();
        let next = self.conduct(request)?;
        if next.lineage.predecessor != Some(boundary.request.address.occurrence) {
            return Err(NativeSessionError::FalseSuccessor);
        }
        Ok(next)
    }

    /// Decline one boundary without changing or cloning the owned package.
    pub fn decline(
        self,
        boundary: &NativeCirculationBoundary,
    ) -> Result<(Self, NativeDeclineReceipt), NativeSessionError> {
        boundary.validate_for(&self)?;
        let generation = self.generation();
        Ok((
            self,
            NativeDeclineReceipt {
                schema: NATIVE_CIRCULATION_SESSION_SCHEMA.to_owned(),
                generation_before: generation,
                generation_after: generation,
                emission: boundary.emission.address.clone(),
                morphology_unchanged: true,
            },
        ))
    }

    pub fn into_package(self) -> NativeMorphologyArtifact {
        self.package
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonic_engine::{
        native_ecology::holonic_intelligence::{
            Bf16ExcitationDismantling, ExteriorModality, ForeignBf16Excitation,
            NativeInferenceAddress,
        },
        receiver_exact_compression::ReceiverId,
        soulkiller::dismantle,
        BoundaryId,
    };

    use crate::native_intelligence::{consume_dismantling_return, MorphologyLineage};

    fn excitation(event: u64, predecessor: Option<u64>) -> ForeignBf16Excitation {
        let (entering, returned) = match event {
            1 => (0x3f80, 0x4000),
            2 => (0x4000, 0x4040),
            3 => (0x4040, 0x4080),
            _ => unreachable!("the bounded chain has three events"),
        };
        ForeignBf16Excitation {
            event: EventId(event),
            predecessor: predecessor.map(EventId),
            entering_boundary: BoundaryId(event * 2),
            emitting_boundary: BoundaryId(event * 2 + 1),
            source_occurrence: format!("cold/{event}"),
            exterior_modality: ExteriorModality::Text,
            entering_codewords: vec![entering],
            returned_codewords: vec![returned],
            interventions: BTreeSet::from([format!("intervention/{event}")]),
            receiver_consequences: BTreeSet::from([format!("consequence/{event}")]),
        }
    }

    fn session() -> NativeCirculationSession {
        let returned = dismantle(Bf16ExcitationDismantling {
            receiver: ReceiverId(7),
            excitations: vec![
                excitation(1, None),
                excitation(2, Some(1)),
                excitation(3, Some(2)),
            ],
        })
        .expect("dismantle");
        let (hot, _) = consume_dismantling_return(returned).expect("hot");
        let package = NativeMorphologyArtifact::found(
            hot,
            MorphologyLineage::origin(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
        .expect("package");
        NativeCirculationSession::mount(
            package,
            NativeCirculationConfiguration::found(InferenceConfigurationAddress {
                ingress_aperture: "native-addressed-occurrence".to_owned(),
                occurrence: EventId(1),
                receiver: ReceiverId(7),
                continuation_receiver: "exterior-receiver-decision".to_owned(),
                world_return_law: "genuinely-later-return".to_owned(),
                emission_codec: "owned-structural-boundary".to_owned(),
                apparatus: "resident-native-word".to_owned(),
                stochastic_current: None,
            })
            .expect("configuration"),
        )
        .expect("session")
    }

    fn first_request(session: &NativeCirculationSession) -> NativeInferenceRequest {
        let native = session.package().hot().native();
        NativeInferenceRequest {
            address: NativeInferenceAddress {
                spool: native.spools[0].address.clone(),
                thread: native.spools[0].threads[0].address.clone(),
                occurrence: EventId(1),
            },
            receiver: ReceiverId(7),
        }
    }

    #[test]
    fn actual_successor_continues_and_false_successor_refuses() {
        let session = session();
        let first = session.conduct(first_request(&session)).expect("first");
        assert_eq!(first.actual_successors.len(), 1);
        assert_eq!(first.actual_successors[0].address.occurrence, EventId(2));
        let second = session
            .continue_from(&first, &first.actual_successors[0].address)
            .expect("second");
        assert_eq!(second.lineage.predecessor, Some(EventId(1)));
        assert_eq!(second.request.address.occurrence, EventId(2));

        let false_successor = NativeOwnedInferenceAddress {
            spool: first.request.address.spool.clone(),
            thread: first.request.address.thread.clone(),
            occurrence: EventId(3),
        };
        assert!(matches!(
            session.continue_from(&first, &false_successor),
            Err(NativeSessionError::FalseSuccessor)
        ));
    }

    #[test]
    fn stale_boundary_refuses_and_decline_preserves_the_package() {
        let session = session();
        let before = session
            .package()
            .canonical_bytes()
            .expect("predecessor package");
        let boundary = session.conduct(first_request(&session)).expect("boundary");
        let mut stale = boundary.clone();
        stale.generation += 1;
        assert!(matches!(
            session.continue_from(&stale, &boundary.actual_successors[0].address),
            Err(NativeSessionError::Boundary)
        ));

        let (session, receipt) = session.decline(&boundary).expect("decline");
        assert!(receipt.morphology_unchanged);
        assert_eq!(receipt.generation_before, receipt.generation_after);
        assert_eq!(
            session.package().canonical_bytes().expect("same package"),
            before
        );
    }

    #[test]
    fn every_plural_future_retains_its_complete_owned_fibres() {
        let session = session();
        let boundary = session.conduct(first_request(&session)).expect("boundary");
        assert_eq!(boundary.emission.grains.len(), boundary.futures.len());
        for (grain, future) in boundary.emission.grains.iter().zip(&boundary.futures) {
            assert_eq!(grain.future, future.future);
            let complete = future
                .fibres
                .iter()
                .flat_map(|fibre| fibre.occurrences.iter().copied())
                .collect::<BTreeSet<_>>();
            assert_eq!(grain.occurrences, complete);
        }
    }
}
