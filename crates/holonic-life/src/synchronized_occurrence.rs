//! Exact synchronized receiver occurrences over the production live-current mouth.
//!
//! This module does not flatten plural media into a frame or a common sample
//! matrix. Every receiver section retains its own local clock. Exact affine
//! clock transports expose only the elementary occurrence intervals on which
//! sections actually overlap.
//!
//! Cross-receiver association is not supplied by this chart. A lower-stage
//! testimony, a later returned section, and their common occurrence horizon
//! enter as a receiver-caused commutative triangle. The existing Soma Swing
//! decides whether recurrent transported paths RIDE or remain OPEN. A sparse,
//! rebuildable atlas indexes only those returned outcomes. Withheld-section
//! prediction is consequently a plural fiber of exact candidate sections,
//! ordered by inclusion of established and obstructed contact support rather
//! than by a scalar score.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use body::{
    incidence::{
        EventCell, EventCellId, EventComplex, EventPort, IncidenceHand, OrientedIncidence,
    },
    num::{Cog, COG_WORDS},
};
use num_bigint::BigInt;
use num_rational::BigRational;
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryRadiation, CpuLiveCurrentExecutor, CurrentBoundaryPort, LiveBoundaryTransition,
    LiveCurrentError, LiveCurrentExecutor, LiveCurrentMachine, LiveCurrentRestImage,
    ReceiverCausalPassage, ReceiverChartIdentity, ReceiverFiberIdentity, RegionalSupportSection,
};

use crate::current_world::{
    present_native_event_with_regional, NativeEventCurrent, NativeEventRelation, NativeRegionalArc,
    NativeRegionalRelation, NativeRelationOrgan,
};

pub type ExactOccurrenceTime = BigRational;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SynchronizedReceiverId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SynchronizedCellId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SynchronizedCandidateId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SynchronizedCellOrigin {
    Inherited,
    Candidate,
}

/// Exact affine transport from one receiver's local clock to the occurrence
/// chart. Neither clock becomes an absolute time coordinate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactClockTransport {
    pub local_origin: ExactOccurrenceTime,
    pub occurrence_origin: ExactOccurrenceTime,
    pub occurrence_per_local: ExactOccurrenceTime,
}

impl ExactClockTransport {
    pub fn new(
        local_origin: ExactOccurrenceTime,
        occurrence_origin: ExactOccurrenceTime,
        occurrence_per_local: ExactOccurrenceTime,
    ) -> Result<Self, SynchronizedOccurrenceError> {
        if occurrence_per_local <= rational_zero() {
            return Err(SynchronizedOccurrenceError::NonPositiveClockTransport);
        }
        Ok(Self {
            local_origin,
            occurrence_origin,
            occurrence_per_local,
        })
    }

    pub fn transport(&self, local: &ExactOccurrenceTime) -> ExactOccurrenceTime {
        &self.occurrence_origin + (&self.occurrence_per_local * (local - &self.local_origin))
    }
}

/// One caused cell in a receiver-local chart.
///
/// `chart` names the comparable local coordinate/facet. `material` is the
/// exact received face at that coordinate. `arrival_stage` is inherited
/// experimental chronology (for example, sensory testimony before a returned
/// inscription); it is not a modality label or a learned edge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TimedReceiverCell {
    pub id: SynchronizedCellId,
    pub chart: ReceiverChartIdentity,
    pub source_identity: u64,
    pub material: RelationAtom,
    pub local_begin: ExactOccurrenceTime,
    pub local_end: ExactOccurrenceTime,
    pub arrival_stage: u32,
    pub origin: SynchronizedCellOrigin,
}

impl TimedReceiverCell {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        id: SynchronizedCellId,
        chart: ReceiverChartIdentity,
        source_identity: u64,
        material: RelationAtom,
        local_begin: ExactOccurrenceTime,
        local_end: ExactOccurrenceTime,
        arrival_stage: u32,
        origin: SynchronizedCellOrigin,
    ) -> Result<Self, SynchronizedOccurrenceError> {
        if local_begin >= local_end {
            return Err(SynchronizedOccurrenceError::EmptyCellInterval(id));
        }
        Ok(Self {
            id,
            chart,
            source_identity,
            material,
            local_begin,
            local_end,
            arrival_stage,
            origin,
        })
    }
}

/// One receiver's exact local section. Cells may overlap: plural facets of
/// one local occurrence are co-present, not serialized into an artificial
/// sequence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SynchronizedReceiverSection {
    pub receiver: SynchronizedReceiverId,
    pub clock: ExactClockTransport,
    pub cells: Vec<TimedReceiverCell>,
}

impl SynchronizedReceiverSection {
    pub fn new(
        receiver: SynchronizedReceiverId,
        clock: ExactClockTransport,
        cells: Vec<TimedReceiverCell>,
    ) -> Result<Self, SynchronizedOccurrenceError> {
        if cells.is_empty() {
            return Err(SynchronizedOccurrenceError::EmptyReceiverSection(receiver));
        }
        let result = Self {
            receiver,
            clock,
            cells,
        };
        result.validate()?;
        Ok(result)
    }

    fn validate(&self) -> Result<(), SynchronizedOccurrenceError> {
        if self.clock.occurrence_per_local <= rational_zero() || self.cells.is_empty() {
            return Err(SynchronizedOccurrenceError::EmptyReceiverSection(
                self.receiver,
            ));
        }
        let mut ids = BTreeSet::new();
        for cell in &self.cells {
            if cell.local_begin >= cell.local_end {
                return Err(SynchronizedOccurrenceError::EmptyCellInterval(cell.id));
            }
            if !ids.insert(cell.id) {
                return Err(SynchronizedOccurrenceError::DuplicateCell(cell.id));
            }
            if self.clock.transport(&cell.local_begin) >= self.clock.transport(&cell.local_end) {
                return Err(SynchronizedOccurrenceError::NonPositiveClockTransport);
            }
        }
        Ok(())
    }
}

/// Declared permission for two receiver sections to meet in one occurrence.
///
/// This is interaction doctrine, not an asserted association between their
/// cell materials. The ordered pair is canonical only for addressing.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SynchronizedInteraction {
    pub left: SynchronizedReceiverId,
    pub right: SynchronizedReceiverId,
}

impl SynchronizedInteraction {
    pub fn new(
        first: SynchronizedReceiverId,
        second: SynchronizedReceiverId,
    ) -> Result<Self, SynchronizedOccurrenceError> {
        if first == second {
            return Err(SynchronizedOccurrenceError::ReflexiveInteraction(first));
        }
        let (left, right) = if first < second {
            (first, second)
        } else {
            (second, first)
        };
        Ok(Self { left, right })
    }
}

/// One complete co-present world occurrence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactSynchronizedOccurrence {
    pub occurrence: u64,
    pub horizon_chart: ReceiverChartIdentity,
    pub horizon_material: RelationAtom,
    pub horizon_stage: u32,
    pub sections: Vec<SynchronizedReceiverSection>,
    pub interactions: BTreeSet<SynchronizedInteraction>,
}

impl ExactSynchronizedOccurrence {
    pub fn new(
        occurrence: u64,
        horizon_chart: ReceiverChartIdentity,
        horizon_material: RelationAtom,
        horizon_stage: u32,
        sections: Vec<SynchronizedReceiverSection>,
        interactions: impl IntoIterator<Item = SynchronizedInteraction>,
    ) -> Result<Self, SynchronizedOccurrenceError> {
        let result = Self {
            occurrence,
            horizon_chart,
            horizon_material,
            horizon_stage,
            sections,
            interactions: interactions.into_iter().collect(),
        };
        result.validate()?;
        Ok(result)
    }

    fn validate(&self) -> Result<(), SynchronizedOccurrenceError> {
        if self.sections.len() < 2 || self.interactions.is_empty() {
            return Err(SynchronizedOccurrenceError::MalformedOccurrence);
        }
        let mut receivers = BTreeMap::new();
        let mut cells = BTreeSet::new();
        let mut maximum_stage = 0_u32;
        for (at, section) in self.sections.iter().enumerate() {
            section.validate()?;
            if receivers.insert(section.receiver, at).is_some() {
                return Err(SynchronizedOccurrenceError::DuplicateReceiver(
                    section.receiver,
                ));
            }
            for cell in &section.cells {
                if !cells.insert(cell.id) {
                    return Err(SynchronizedOccurrenceError::DuplicateCell(cell.id));
                }
                maximum_stage = maximum_stage.max(cell.arrival_stage);
            }
        }
        if self.horizon_stage <= maximum_stage {
            return Err(SynchronizedOccurrenceError::HorizonDoesNotFollowReturn);
        }
        for interaction in &self.interactions {
            if interaction.left >= interaction.right
                || !receivers.contains_key(&interaction.left)
                || !receivers.contains_key(&interaction.right)
            {
                return Err(SynchronizedOccurrenceError::UnknownInteraction(
                    *interaction,
                ));
            }
        }
        Ok(())
    }

    fn section_index(
        &self,
        receiver: SynchronizedReceiverId,
    ) -> Result<usize, SynchronizedOccurrenceError> {
        self.sections
            .iter()
            .position(|section| section.receiver == receiver)
            .ok_or(SynchronizedOccurrenceError::UnknownReceiver(receiver))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MaterialFace(pub [u32; COG_WORDS]);

impl From<RelationAtom> for MaterialFace {
    fn from(value: RelationAtom) -> Self {
        Self(value.words())
    }
}

/// One exact receiver-local facet present on an elementary occurrence interval. Cell identity and
/// clock coordinate remain immediate testimony; durable recurrence retains the chart, material,
/// and inherited arrival stage.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SynchronizedSectionFacet {
    pub chart: u64,
    pub material: MaterialFace,
    pub stage: u32,
}

/// A receiver section is a plural face. Multiplicity is retained, while deterministic sorting
/// removes storage order from the durable association address.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SynchronizedSectionFace(pub Vec<SynchronizedSectionFacet>);

/// Chronology-free durable address of one cross-receiver section candidate.
///
/// Occurrence time and cell ordinals remain in immediate testimony. Durable
/// recurrence is addressed by both complete receiver-local faces and their
/// common horizon chart. The relation is not expanded into pairwise scalar
/// associations.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SynchronizedAssociationSignature {
    pub left_receiver: SynchronizedReceiverId,
    pub left_face: SynchronizedSectionFace,
    pub right_receiver: SynchronizedReceiverId,
    pub right_face: SynchronizedSectionFace,
    pub horizon_chart: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SynchronizedContactOccurrence {
    pub occurrence: u64,
    pub interval_begin: ExactOccurrenceTime,
    pub interval_end: ExactOccurrenceTime,
    pub left_cells: Vec<SynchronizedCellId>,
    pub right_cells: Vec<SynchronizedCellId>,
    pub left_origins: Vec<SynchronizedCellOrigin>,
    pub right_origins: Vec<SynchronizedCellOrigin>,
    pub signature: SynchronizedAssociationSignature,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SynchronizedContactRadiation {
    pub contact: SynchronizedContactOccurrence,
    pub boundary_transitions: Vec<LiveBoundaryTransition>,
    pub formed_ride: bool,
    pub formed_found: bool,
    pub open: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SynchronizedOccurrenceRadiation {
    pub occurrence: u64,
    pub source: ContemporaryRadiation,
    pub contacts: Vec<SynchronizedContactRadiation>,
    pub elementary_intervals: u64,
    pub local_sequence_relations: u64,
}

/// One exact moved source fibre whose heterogeneous local-clock sections have been charted into
/// synchronized contacts. The encoded exterior body is retained for reconstruction; neither it
/// nor a modality name participates in contact or later membrane transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactSynchronizedOccurrenceFibre {
    pub occurrence_address: String,
    pub predecessor_occurrence: Option<String>,
    pub locator: String,
    pub encoded_source: Vec<u8>,
    pub source_identity_sha256: String,
    pub synchronized: ExactSynchronizedOccurrence,
    pub contacts: Vec<SynchronizedContactOccurrence>,
    pub incidence_identity_sha256: String,
    pub open_exterior: Vec<String>,
}

impl ExactSynchronizedOccurrenceFibre {
    pub fn found(
        occurrence_address: impl Into<String>,
        predecessor_occurrence: Option<String>,
        locator: impl Into<String>,
        encoded_source: Vec<u8>,
        synchronized: ExactSynchronizedOccurrence,
        open_exterior: Vec<String>,
    ) -> Result<Self, SynchronizedOccurrenceError> {
        synchronized.validate()?;
        let contacts = SynchronizedOccurrenceChart::new().contacts(&synchronized)?;
        let mut fibre = Self {
            occurrence_address: occurrence_address.into(),
            predecessor_occurrence,
            locator: locator.into(),
            source_identity_sha256: hex_sha256(&encoded_source),
            encoded_source,
            incidence_identity_sha256: synchronized_contacts_sha256(&contacts),
            synchronized,
            contacts,
            open_exterior,
        };
        fibre.validate()?;
        // Recompute after complete assembly so the constructor cannot accidentally admit stale
        // derived testimony.
        fibre.incidence_identity_sha256 = synchronized_contacts_sha256(&fibre.contacts);
        Ok(fibre)
    }

    pub fn validate(&self) -> Result<(), SynchronizedOccurrenceError> {
        self.synchronized.validate()?;
        let derived = SynchronizedOccurrenceChart::new().contacts(&self.synchronized)?;
        if self.occurrence_address.is_empty()
            || self.locator.is_empty()
            || self.encoded_source.is_empty()
            || self.contacts.is_empty()
            || self.source_identity_sha256 != hex_sha256(&self.encoded_source)
            || self.incidence_identity_sha256 != synchronized_contacts_sha256(&derived)
            || self.contacts != derived
            || self
                .predecessor_occurrence
                .as_ref()
                .is_some_and(String::is_empty)
            || self.open_exterior.iter().any(String::is_empty)
        {
            return Err(SynchronizedOccurrenceError::MalformedOccurrence);
        }
        Ok(())
    }
}

mod chart;
mod ecology;
#[cfg(test)]
mod tests;

pub use self::chart::SynchronizedOccurrenceChart;
pub use self::ecology::*;

#[derive(Debug)]
pub enum SynchronizedOccurrenceError {
    MalformedOccurrence,
    NonPositiveClockTransport,
    EmptyReceiverSection(SynchronizedReceiverId),
    EmptyCellInterval(SynchronizedCellId),
    DuplicateReceiver(SynchronizedReceiverId),
    DuplicateCell(SynchronizedCellId),
    ReflexiveInteraction(SynchronizedReceiverId),
    UnknownInteraction(SynchronizedInteraction),
    UnknownReceiver(SynchronizedReceiverId),
    HorizonDoesNotFollowReturn,
    NonIncreasingCausalStage,
    ChronologyOverflow,
    CarrierOverflow,
    RadiationPopulationMismatch,
    MalformedRadiation,
    EmptyPredictionFiber,
    DuplicateCandidate(SynchronizedCandidateId),
    TargetHasNoCrossContact(SynchronizedReceiverId),
    IncomparableCandidateCharts,
    UnknownReturnedCandidate(SynchronizedCandidateId),
    PredictionEcologyChanged { predicted: u64, contemporary: u64 },
    Machine(LiveCurrentError),
}

impl fmt::Display for SynchronizedOccurrenceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for SynchronizedOccurrenceError {}

impl From<LiveCurrentError> for SynchronizedOccurrenceError {
    fn from(value: LiveCurrentError) -> Self {
        Self::Machine(value)
    }
}

fn rational_zero() -> BigRational {
    BigRational::from_integer(BigInt::from(0))
}

fn synchronized_contacts_sha256(contacts: &[SynchronizedContactOccurrence]) -> String {
    let mut digest = Sha256::new();
    digest.update(b"soma-life.exact-synchronized-contact-population.v1");
    for contact in contacts {
        digest.update(contact.occurrence.to_le_bytes());
        update_rational(&mut digest, &contact.interval_begin);
        update_rational(&mut digest, &contact.interval_end);
        for cell in &contact.left_cells {
            digest.update(cell.0.to_le_bytes());
        }
        digest.update([0xff]);
        for cell in &contact.right_cells {
            digest.update(cell.0.to_le_bytes());
        }
        digest.update(contact.signature.left_receiver.0.to_le_bytes());
        digest.update(contact.signature.right_receiver.0.to_le_bytes());
        for facet in contact
            .signature
            .left_face
            .0
            .iter()
            .chain(&contact.signature.right_face.0)
        {
            digest.update(facet.chart.to_le_bytes());
            for word in facet.material.0 {
                digest.update(word.to_le_bytes());
            }
            digest.update(facet.stage.to_le_bytes());
        }
        digest.update(contact.signature.horizon_chart.to_le_bytes());
    }
    render_hex(&digest.finalize())
}

fn update_rational(digest: &mut Sha256, value: &BigRational) {
    let numerator = value.numer().to_signed_bytes_be();
    let denominator = value.denom().to_signed_bytes_be();
    digest.update((numerator.len() as u64).to_le_bytes());
    digest.update(numerator);
    digest.update((denominator.len() as u64).to_le_bytes());
    digest.update(denominator);
}

fn hex_sha256(bytes: &[u8]) -> String {
    render_hex(&Sha256::digest(bytes))
}

fn render_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

pub fn relation_atom(value: i64) -> Result<RelationAtom, SynchronizedOccurrenceError> {
    RelationAtom::new(Cog::lit(value)).ok_or(SynchronizedOccurrenceError::MalformedOccurrence)
}
