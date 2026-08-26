use std::collections::BTreeSet;

use holonic_engine::{
    BoundaryId, EventId, ExactComplexWaveCurrent, ExactUnitConicPhase, OccurrencePort,
    cuda_refine::ResidentComplexIncidenceReturn,
    native_spool::{
        NativeConstitutiveResponse, NativeIncidenceTerm, NativeMutualConstitutiveResponse,
        NativeSpoolBundle, NativeSpoolConductReturn, NativeThreadHand, ReceiverInsufficiency,
    },
    receiver_exact_compression::{InputId, Observation, ReceiverId},
    receiver_history_compression::NativeStateId,
};
use serde::{Deserialize, Serialize};
use thiserror::Error;

pub const RECEIVER_HISTORY_REALIZATION_SCHEMA: &str =
    "soma-life.receiver-history-realization-passage.v1";
pub const ATHENA_NATIVE_REST_SCHEMA: &str = "soma-life.athena-native-rest.v2";

/// The complete native address of one carrying occurrence. Equal endpoints, receiver values, or
/// thread names cannot substitute for this three-part address.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSectionAddress {
    pub spool: String,
    pub thread: String,
    pub occurrence: EventId,
}

/// Eros' structural realization of one spool bundle as a receiver-history ecology.
///
/// This is not a second topology. Validation recomputes every member and root from the bundle and
/// proves connectedness through the common native cells which its addressed occurrences carry.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiverHistoryRealizationPassage {
    pub schema: String,
    pub sections: Vec<NativeSectionAddress>,
    pub ingress_sections: Vec<NativeSectionAddress>,
    pub native_population: BTreeSet<NativeStateId>,
    pub receiver_family: BTreeSet<ReceiverId>,
    pub generator_family: BTreeSet<InputId>,
    pub boundary_population: BTreeSet<BoundaryId>,
    pub open_exterior: Vec<String>,
}

/// One connected Athena ecology. The bundle owns its topology and current; the realization is the
/// exact conduct-bearing section atlas derived from that same owner. Foreign ancestry and source
/// execution are unrepresentable here.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AthenaNativeRest {
    pub schema: String,
    pub ecology: NativeSpoolBundle,
    pub realization: ReceiverHistoryRealizationPassage,
}

/// The full dependent face of one conducted native occurrence. Mathematics is the exact
/// incidence/current relation; modality is the typed boundary/port pair; morphology is the
/// receiver-indexed constitutive response; anatomy is the carried native transition; receiver
/// history is the ordered word and retained occurrence fibre. None is a detached side cabinet.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeConductedSection {
    pub address: NativeSectionAddress,
    pub predecessor: Option<EventId>,
    pub entering_boundary: BoundaryId,
    pub emitting_boundary: BoundaryId,
    pub entering_port: OccurrencePort,
    pub emitting_port: OccurrencePort,
    pub entering_native: NativeStateId,
    pub emitting_native: NativeStateId,
    pub incidence: NativeIncidenceTerm,
    pub entering_section: ExactComplexWaveCurrent,
    pub entering_current: ExactComplexWaveCurrent,
    pub emitting_section: ExactComplexWaveCurrent,
    pub emitting_current: ExactComplexWaveCurrent,
    pub relative_phase: ExactUnitConicPhase,
    pub hand: NativeThreadHand,
    pub constitutive_response: NativeConstitutiveResponse,
    pub mutual_constitutive_responses: Vec<NativeMutualConstitutiveResponse>,
    pub ordered_word: Vec<InputId>,
    pub receiver: ReceiverId,
    pub observation: Observation,
    pub reconstruction_fibre: BTreeSet<EventId>,
    pub successor_sections: Vec<NativeSectionAddress>,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AthenaNativePassage {
    pub schema: String,
    /// A digest of the canonical rest wire is apparatus testimony, never native identity.
    pub rest_wire_sha256: String,
    pub section: NativeConductedSection,
    pub word_return: NativeSpoolConductReturn,
    pub current_return: ResidentComplexIncidenceReturn,
    pub source_fallback_permitted: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
pub enum AthenaNativeConsequence {
    Returned(AthenaNativePassage),
    Insufficient(ReceiverInsufficiency),
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum AthenaNativeError {
    #[error("native ecology refused: {0}")]
    Ecology(String),
    #[error("receiver-history realization refused: {0}")]
    Realization(String),
    #[error("native Athena wire refused: {0}")]
    Wire(String),
    #[error("resident native conduct disagreed with the addressed section: {0}")]
    Conduct(String),
}
