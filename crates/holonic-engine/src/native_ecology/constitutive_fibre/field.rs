//! Coupled constitutive circulation on a complete port field. This extends the existing local
//! rational relation and lossless two-port law; it does not define a text encoder or a second
//! learner. Each junction receives its own exterior excitation. The source section retains BOTH
//! outgoing and held branches, and an actual later receiving field joins the same resident relation.
//!
//! This field chart has fixed nodes and unit-phase incidences. Live fixed-node recharting
//! and physical incoming-incidence replacement retain their distinct frame/history semantics;
//! shared immutable source standing supports distinct later contacts. Root-carrier enlargement
//! and a useful learned text product remain outside this component's established scope.
//! The paired-junction constructor additionally makes a formed Hermitian contact moment and
//! retained internal current operative on the root port field, with a complete internal decoder.

use super::circulation::HeldCurrentFrame;
use super::*;
use crate::dimensional_wave::ExactComplexWaveCurrent;
use std::rc::Rc;

mod archive;
mod current_history_source;
mod contextual_lift;
mod context_section;
pub use contextual_lift::{
    NativeContextContrastInspection, NativeContextContrastStatus, NativeContextualLiftInspection,
};
mod internal_current;
mod internal_mode;
mod junction;
mod material_transport;
mod receiver;
mod rechart;
mod relation_current;
mod resident_input;
mod rest;
pub use archive::NativeFieldHistoryPlacement;
use archive::{ArchivedField, FieldArchive};
pub use current_history_source::{
    NativeCurrentHistorySource, NativeCurrentHistorySourceReading,
    NativeCurrentHistorySourceReceiver,
};
pub use internal_current::{
    NativeInternalCurrentReading, NativeInternalPointAvailability, NativeResidentInternalCurrent,
};
pub use internal_mode::{
    NativeSharedDriveMode, NativeSharedDriveModeReading, NativeSharedDriveModeRest,
    NativeSharedDriveModeReturn,
};
pub use junction::{NativeOperativeReturnStorage,
    NativeFieldCurrentBall, NativeFieldEnclosedJunctionReading, NativeFieldExactJunctionReading,
    NativeFieldInternalCurrent, NativeFieldInternalCurrentBall, NativeFieldJunctionReading,
    NativeFieldJunctionRepresentation, NativeFieldJunctionSolver,
    PairedContactCotangent, PairedJunctionCotangent, PairedJunctionLinearization, PairedJunctionTangent,
    JointMaterialContactResponse,joint_material_contact,
    NativeOperativeContactBirth, NativeOperativeContactReading, NativeOperativeContactStaging, NativeOperativeReflectionReading,
    NativeMaterialContactResponse, NativeMaterialContactResponseReading,
    NativeContactRealization,
    NativeContactDepositReading,
};
use junction::{PairedJunction, PendingJunction};
use material_transport::{MaterialTransport, PendingMaterialTransport};
pub use material_transport::{
    NativeMaterialReportPacking, NativeMaterialReportPackingRest,
    NativeCompleteMaterialTransportReading, NativeCompleteMaterialTransportState,
    NativeFieldExactMaterialTransport, NativeFieldMaterialTransportReading,
    NativeFieldMaterialTransportResidual, NativeFieldMaterialTransportState,
    NativeMaterialModeComponent, NativeMaterialModeDifferential, NativeMaterialModeReading,
    NativeMaterialModeReturn, NativeMaterialModeUnfolding, NativeMaterialTransportSource,
    NativeMaterialTarget,
    NativeMomentMaterialReading, NativeContextualMaterialReading, NativeOperativeContextReading, NativeVisibleSourceReading,
};
pub use receiver::{NativeFieldDifferentialReading, NativeNormalizedMaterialReading, NativeNormalizedMaterialReturn,
    NativeMaterialPacketReading, NativePacketQuadrature, NativeMaterialActuation,
    NativeMaterialPullbackMetric, NativeMaterialSourcePullback, NativeMaterialSourcePullbackReading};
pub use resident_input::NativeFieldIncoming;
pub use rest::NativeFieldRest;

/// One actual emitted source from this live body. It is linear; the caller cannot manufacture
/// it from an occurrence number or duplicate it for another receiving edge.
#[derive(Debug)]
pub struct NativeFieldEmission {
    owner: Rc<()>,
    occurrence: usize,
}

/// Shared immutable source standing, issued only from an actual available emission. Cloning
/// this address shares its historical section and frame, never a continuing ecology or current.
#[derive(Clone, Debug)]
pub struct NativeFieldSourceAnchor {
    owner: Rc<()>,
    occurrence: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeFieldSourceContact {
    Emission,
    RetainedAnchor,
    MaterialActuation { quadrature:NativePacketQuadrature, coordinate:usize },
}

#[derive(Debug)]
pub struct NativeFieldOccurrence {
    incoming: Vec<NativePhaseCurrent>,
    source: Option<NativeFieldEmission>,
    anchor: Option<NativeFieldSourceAnchor>,
    actuation:Option<NativeMaterialActuation>,
}

impl NativeFieldOccurrence {
    pub fn actuating(source:NativeFieldEmission,incoming:Vec<NativePhaseCurrent>,actuation:NativeMaterialActuation)->Self{
        Self{incoming,source:Some(source),anchor:None,actuation:Some(actuation)}
    }
    pub fn material_actuation(&self)->Option<&NativeMaterialActuation>{self.actuation.as_ref()}

    pub fn entering(incoming: Vec<NativePhaseCurrent>) -> Self {
        Self {
            incoming,
            actuation:None,
            source: None,
            anchor: None,
        }
    }
    pub fn through(source: NativeFieldEmission, incoming: Vec<NativePhaseCurrent>) -> Self {
        Self {
            incoming,
            actuation:None,
            source: Some(source),
            anchor: None,
        }
    }
    /// Join a new receiving occurrence to shared historical standing. Its new contact and
    /// internal current belong to this actual receiving occurrence, not to a duplicated source.
    pub fn through_anchor(
        anchor: &NativeFieldSourceAnchor,
        incoming: Vec<NativePhaseCurrent>,
    ) -> Self {
        Self {
            incoming,
            actuation:None,
            source: None,
            anchor: Some(anchor.clone()),
        }
    }
    pub fn take_source(&mut self) -> Option<NativeFieldEmission> {
        self.source.take()
    }
    pub fn source_ref(&self) -> Option<&NativeFieldEmission> {
        self.source.as_ref()
    }
    pub fn anchor_ref(&self) -> Option<&NativeFieldSourceAnchor> {
        self.anchor.as_ref()
    }
    pub fn incoming(&self) -> &[NativePhaseCurrent] {
        &self.incoming
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
pub struct NativeFieldLineage {
    pub occurrence: usize,
    /// Producing chart in this body's frame chronology, never a contextual identity.
    pub frame: u64,
    pub predecessor_state: Option<usize>,
    pub received_from: Option<usize>,
    pub source_contact: Option<NativeFieldSourceContact>,
    /// Complete exterior excitation field, not a semantic feature vector or a fitted source.
    pub incoming: NativeFieldIncoming,
}

impl NativeFieldLineage {
    /// An applied transport retains its source edge without adding an observed relation.
    pub fn observed_source(&self)->Option<usize>{
        if matches!(self.source_contact,Some(NativeFieldSourceContact::MaterialActuation{..})){None}else{self.received_from}
    }
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldReceivedDifference<Reading = ConstitutiveReading> {
    pub source_occurrence: usize,
    pub former_receiver: Reading,
    pub arrived: Vec<ExactComplexWaveCurrent>,
}

#[derive(Debug)]
pub struct NativeFieldStep<Reading = ConstitutiveReading> {
    pub source: NativeFieldEmission,
    pub lineage: NativeFieldLineage,
    /// The immutable local frame in which this occurrence produced its source branches.
    pub frame: Rc<NativeCurrentFrame>,
    pub outgoing: Vec<ExactComplexWaveCurrent>,
    pub held_successor: Vec<ExactComplexWaveCurrent>,
    pub receiver: Reading,
    pub received_difference: Option<NativeFieldReceivedDifference<Reading>>,
    pub formed_pivot: Option<usize>,
    pub successor_rank: usize,
    pub junction: Option<NativeFieldJunctionReading>,
}

/// Continuation with numerical reports retained on the device. No numerical receiver is read.
#[derive(Debug)]
pub struct NativeFieldContinuation {
    pub source: NativeFieldEmission,
    pub lineage: NativeFieldLineage,
    pub frame: Rc<NativeCurrentFrame>,
}

/// A cold observation of one committed occurrence. This issues no receiving capability.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldOccurrenceStatus {
    pub receiver: NativeFieldReceiverStatus,
    pub former_receiver: Option<NativeFieldReceiverStatus>,
    pub formed_pivot: Option<usize>,
    pub successor_rank: usize,
}

struct FieldObservation<Reading> {
    outgoing: Vec<ExactComplexWaveCurrent>,
    held_successor: Vec<ExactComplexWaveCurrent>,
    receiver: Reading,
    received_difference: Option<NativeFieldReceivedDifference<Reading>>,
    formed_pivot: Option<usize>,
    successor_rank: usize,
    junction: Option<NativeFieldJunctionReading>,
}

/// Explicit classification projection. It contains no selected response or alleged full fibre;
/// all source/relation carriers remain owned by the continuing body.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeFieldReceiverStatus {
    Unique,
    OutsideDomain,
    Plural,
}

struct ResidentFieldHistory<'chart> {
    section: ResidentSection<'chart>,
    incoming: Option<Rc<ResidentSection<'chart>>>,
    junction: Option<Rc<ResidentSection<'chart>>>,
    transport: Option<Rc<ResidentSection<'chart>>>,
    operative: Option<junction::operative::HeldOperative<'chart>>,
}

struct HeldField<'chart> {
    resident: Option<ResidentFieldHistory<'chart>>,
    archived: Option<ArchivedField>,
    lineage: NativeFieldLineage,
    frame: Rc<HeldCurrentFrame<'chart>>,
    returned: bool,
}

/// One move owner for phase standing, the same local relation accumulator, and its actual
/// emitted sources. The wider source chart is 4N real coordinates (two complex branches/node);
/// the receiving chart is the complete 2N real coordinates of the next exterior input field.
pub struct NativeConstitutiveField<'chart> {
    seed: ResidentSection<'chart>,
    memory: ResidentSection<'chart>,
    relation: ResidentConstitutiveFibre<'chart>,
    material: Vec<NativeJunctionSeed>,
    frame: Rc<HeldCurrentFrame<'chart>>,
    recharts: Vec<NativeRechartReceipt>,
    incidence_changes: Vec<NativeIncidenceChange>,
    owner: Rc<()>,
    history: Vec<HeldField<'chart>>,
    archive: Option<FieldArchive>,
    pending: Option<HeldField<'chart>>,
    junction: Option<PairedJunction<'chart>>,
    pending_junction: Option<PendingJunction<'chart>>,
    transport: Option<MaterialTransport<'chart>>,
    pending_transport: Option<PendingMaterialTransport<'chart>>,
}

impl<'chart> NativeConstitutiveField<'chart> {
    pub fn found(
        surface: &'chart ResidentSurface<'chart>,
        material: Vec<NativeJunctionSeed>,
    ) -> Result<Self, ConstitutiveFibreError> {
        let nodes = material.len();
        let source_width = nodes.checked_mul(4).ok_or(ConstitutiveFibreError::Shape)?;
        let target_width = nodes.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        let scratch = nodes
            .checked_mul(24)
            .and_then(|v| v.checked_mul(16))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let available = surface.declaration().max_sectiond_bytes;
        if nodes == 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        if scratch > available as usize {
            return Err(ConstitutiveFibreError::ScratchAperture {
                required: scratch,
                available,
            });
        }
        for node in &material {
            node.validate()?;
        }
        let relation = ResidentConstitutiveFibre::found(surface, source_width, target_width)?;
        let mut seed_words = Vec::new();
        let mut memory_words = Vec::new();
        for node in &material {
            let turn = node.incoming_transport.words();
            seed_words.extend([
                node.incoming_admittance,
                node.held_admittance,
                turn[0],
                turn[1],
                turn[2],
            ]);
            memory_words.extend(node.initial_held.words());
        }
        let mount = |width, words: Vec<i64>| -> Result<_, ConstitutiveFibreError> {
            let rest = ResidentSectionRest::found(
                nodes,
                width,
                ResidentGrain(0),
                64,
                words.into_iter().map(|v| (v, v)).collect(),
            )
            .map_err(|_| ConstitutiveFibreError::Shape)?;
            Ok(surface.mount_section_rest(&rest)?)
        };
        let frame_native = mount(3, (0..nodes).flat_map(|_| [1, 0, 1]).collect())?;
        let frame = Rc::new(HeldCurrentFrame {
            native: frame_native,
            view: Rc::new(NativeCurrentFrame {
                ordinal: 0,
                root_to_local: vec![NativePhaseCurrent::unit(); nodes],
            }),
        });
        Ok(Self {
            seed: mount(5, seed_words)?,
            memory: mount(3, memory_words)?,
            relation,
            material,
            frame,
            recharts: Vec::new(),
            incidence_changes: Vec::new(),
            owner: Rc::new(()),
            history: Vec::new(),
            archive: None,
            pending: None,
            junction: None,
            pending_junction: None,
            transport: None,
            pending_transport: None,
        })
    }

    pub fn nodes(&self) -> usize {
        self.material.len()
    }
    pub fn material(&self) -> &[NativeJunctionSeed] {
        &self.material
    }
    pub fn occurrence_count(&self) -> usize {
        self.history.len()
    }
    pub fn census(&self) -> TransferCensus {
        self.relation.census()
    }
    pub fn pending_lineage(&self) -> Option<&NativeFieldLineage> {
        self.pending.as_ref().map(|p| &p.lineage)
    }
    pub fn current_frame(&self) -> &NativeCurrentFrame {
        &self.frame.view
    }
    pub fn recharts(&self) -> &[NativeRechartReceipt] {
        &self.recharts
    }
    pub fn incidence_changes(&self) -> &[NativeIncidenceChange] {
        &self.incidence_changes
    }
    pub fn lineage(&self, occurrence: usize) -> Option<&NativeFieldLineage> {
        self.history.get(occurrence).map(|p| &p.lineage)
    }
    /// The immutable producing chart for an inspected historical section; no receiving handle
    /// is issued by observing it.
    pub fn source_frame(&self, occurrence: usize) -> Option<&NativeCurrentFrame> {
        self.history.get(occurrence).map(|p| p.frame.view.as_ref())
    }
    /// Retain the immutable standing behind an available linear emission. The original handle
    /// remains linear. Anchored returns create separately recorded contacts and never restore or
    /// clone the source-time ecology.
    pub fn retain_source(
        &self,
        source: &NativeFieldEmission,
    ) -> Result<NativeFieldSourceAnchor, ConstitutiveFibreError> {
        if !Rc::ptr_eq(&source.owner, &self.owner)
            || self
                .history
                .get(source.occurrence)
                .is_none_or(|event| event.returned)
        {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        Ok(NativeFieldSourceAnchor {
            owner: Rc::clone(&self.owner),
            occurrence: source.occurrence,
        })
    }
    pub fn inspect_relation(&self) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        self.relation.inspect_relation()
    }
    pub fn inspect_held(&self) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        Ok(self.relation.surface.detach_section(&self.memory, 64)?)
    }
    /// Explicit historical source inspection; it issues no new receiving capability.
    pub fn inspect_source(
        &self,
        occurrence: usize,
    ) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        let source = self
            .history
            .get(occurrence)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        Ok(source.source_rest(self.relation.surface)?)
    }

    pub fn advance(
        &mut self,
        occurrence: &mut NativeFieldOccurrence,
    ) -> Result<NativeFieldStep, ConstitutiveFibreError> {
        self.advance_reading(occurrence, |relation, words, at, exclude| {
            relation.decode_reading(words, at, exclude)
        })
    }

    /// Read only the native receiver classification. In particular, this does not copy the
    /// resident paired basis to the host when the fibre is plural. Formation and successor
    /// conduct are identical to `advance`; the projection is only an exterior observation.
    pub fn advance_status(
        &mut self,
        occurrence: &mut NativeFieldOccurrence,
    ) -> Result<NativeFieldStep<NativeFieldReceiverStatus>, ConstitutiveFibreError> {
        self.advance_reading(occurrence, |relation, words, at, _exclude| {
            let width = relation.source_width + relation.target_width;
            if words[at + width].0 <= 0 {
                return Err(ConstitutiveFibreError::Uncertain);
            }
            match words[at + width + 1].0 {
                0 => Ok(NativeFieldReceiverStatus::Unique),
                1 => Ok(NativeFieldReceiverStatus::OutsideDomain),
                2 => Ok(NativeFieldReceiverStatus::Plural),
                _ => Err(ConstitutiveFibreError::Uncertain),
            }
        })
    }

    /// Enact the same operation and validate its obstruction receipt, leaving numerical
    /// sections resident. Source consumption and commit use the same owner as observed advances.
    pub fn advance_resident(
        &mut self,
        occurrence: &mut NativeFieldOccurrence,
    ) -> Result<NativeFieldContinuation, ConstitutiveFibreError> {
        self.advance_with(occurrence, None, |_, _, _| Ok(()))
            .map(|(continuation, ())| continuation)
    }

    /// Read the immutable status of an already committed occurrence, without issuing a handle.
    pub fn inspect_occurrence_status(
        &self,
        occurrence: usize,
    ) -> Result<NativeFieldOccurrenceStatus, ConstitutiveFibreError> {
        let event = self
            .history
            .get(occurrence)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let words = event.source_rest(self.relation.surface)?.intervals;
        let source_width = self.relation.source_width;
        let width = source_width + self.relation.target_width;
        let current_at = source_width + 1;
        if words.iter().any(|(lo, hi)| lo != hi) || words[source_width].0 <= 0 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let receiver = |at: usize| -> Result<NativeFieldReceiverStatus, ConstitutiveFibreError> {
            if words[at + width].0 <= 0 {
                return Err(ConstitutiveFibreError::Uncertain);
            }
            match words[at + width + 1].0 {
                0 => Ok(NativeFieldReceiverStatus::Unique),
                1 => Ok(NativeFieldReceiverStatus::OutsideDomain),
                2 => Ok(NativeFieldReceiverStatus::Plural),
                _ => Err(ConstitutiveFibreError::Uncertain),
            }
        };
        let formed_pivot = match words[current_at + width + 2].0 {
            -1 => None,
            p if p >= 0 && (p as usize) < width => Some(p as usize),
            _ => return Err(ConstitutiveFibreError::Uncertain),
        };
        let successor_rank = usize::try_from(words[current_at + width + 3].0)
            .map_err(|_| ConstitutiveFibreError::Uncertain)?;
        if successor_rank > width {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        Ok(NativeFieldOccurrenceStatus {
            receiver: receiver(current_at)?,
            former_receiver: event
                .lineage
                .observed_source()
                .map(|_| receiver(current_at + width + 4))
                .transpose()?,
            formed_pivot,
            successor_rank,
        })
    }

    fn advance_reading<Reading>(
        &mut self,
        occurrence: &mut NativeFieldOccurrence,
        read: impl Fn(
            &ResidentConstitutiveFibre<'chart>,
            &[(i64, i64)],
            usize,
            Option<usize>,
        ) -> Result<Reading, ConstitutiveFibreError>,
    ) -> Result<NativeFieldStep<Reading>, ConstitutiveFibreError> {
        let (continuation, observed) =
            self.advance_with(occurrence, None, |body, source_at, occurrence| {
                let surface = body.relation.surface;
                let words = surface.read_out(
                    &body
                        .pending
                        .as_ref()
                        .expect("pending field")
                        .resident()?
                        .section,
                )?;
                let source_width = body.relation.source_width;
                let width = source_width + body.relation.target_width;
                let current_at = source_width + 1;
                let former_at = current_at + width + 4;
                if words.iter().any(|(l, h)| l != h) || words[source_width].0 <= 0 {
                    return Err(ConstitutiveFibreError::Uncertain);
                }
                let formed_pivot = match words[current_at + width + 2].0 {
                    -1 => None,
                    p if p >= 0 && (p as usize) < width => Some(p as usize),
                    _ => return Err(ConstitutiveFibreError::Uncertain),
                };
                let rank = usize::try_from(words[current_at + width + 3].0)
                    .map_err(|_| ConstitutiveFibreError::Uncertain)?;
                if rank > width {
                    return Err(ConstitutiveFibreError::Uncertain);
                }
                let receiver = read(&body.relation, &words, current_at, None)?;
                let received_difference = source_at
                    .map(|source_occurrence| -> Result<_, ConstitutiveFibreError> {
                        Ok(NativeFieldReceivedDifference {
                            source_occurrence,
                            former_receiver: read(&body.relation, &words, former_at, formed_pivot)?,
                            arrived: occurrence.incoming.iter().map(|p| p.current()).collect(),
                        })
                    })
                    .transpose()?;
                let denominator = words[source_width].0;
                let phase = |j: usize| {
                    ExactComplexWaveCurrent::new(
                        Rat::new(words[j].0.into(), denominator.into()),
                        Rat::new(words[j + 1].0.into(), denominator.into()),
                    )
                };
                let outgoing = (0..body.nodes()).map(|i| phase(4 * i)).collect();
                let held_successor = (0..body.nodes()).map(|i| phase(4 * i + 2)).collect();
                let junction = body.read_pending_junction()?;
                Ok(FieldObservation {
                    outgoing,
                    held_successor,
                    receiver,
                    received_difference,
                    formed_pivot,
                    successor_rank: rank,
                    junction,
                })
            })?;
        Ok(NativeFieldStep {
            source: continuation.source,
            lineage: continuation.lineage,
            frame: continuation.frame,
            outgoing: observed.outgoing,
            held_successor: observed.held_successor,
            receiver: observed.receiver,
            received_difference: observed.received_difference,
            formed_pivot: observed.formed_pivot,
            successor_rank: observed.successor_rank,
            junction: observed.junction,
        })
    }

    fn advance_with<Observed>(
        &mut self,
        occurrence: &mut NativeFieldOccurrence,
        resident_current: Option<ResidentConstitutiveCurrent<'_, 'chart>>,
        observe: impl FnOnce(
            &Self,
            Option<usize>,
            &NativeFieldOccurrence,
        ) -> Result<Observed, ConstitutiveFibreError>,
    ) -> Result<(NativeFieldContinuation, Observed), ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if resident_current.map_or(occurrence.incoming.len() != self.nodes(), |c| {
            !occurrence.incoming.is_empty() || c.width != 2 * self.nodes()
        }) {
            return Err(ConstitutiveFibreError::Shape);
        }
        if occurrence.source.is_some() && occurrence.anchor.is_some() {
            return Err(ConstitutiveFibreError::Shape);
        }
        let source_at = if let Some(source) = &occurrence.source {
            if !Rc::ptr_eq(&source.owner, &self.owner)
                || self
                    .history
                    .get(source.occurrence)
                    .is_none_or(|h| h.returned)
            {
                return Err(ConstitutiveFibreError::ForeignOccurrence);
            }
            Some(source.occurrence)
        } else if let Some(anchor) = &occurrence.anchor {
            if !Rc::ptr_eq(&anchor.owner, &self.owner) || anchor.occurrence >= self.history.len() {
                return Err(ConstitutiveFibreError::ForeignOccurrence);
            }
            Some(anchor.occurrence)
        } else {
            None
        };
        let actuation=if let Some(a)=&occurrence.actuation {
            let source=occurrence.source.as_ref().ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
            if resident_current.is_some() || !a.describes_source(source) || !Rc::ptr_eq(&self.owner,&a.owner)
                || Some(a.reading.target_chart)!=self.material_target(){return Err(ConstitutiveFibreError::ForeignOccurrence);}
            Some((a.reading.quadrature,a.reading.selected.ok_or(ConstitutiveFibreError::Uncertain)?))
        }else{None};
        let observed_source_at=if actuation.is_some(){None}else{source_at};
        if let Some(at) = source_at {
            self.mount_history_source(at)?;
        }
        let next = self
            .relation
            .occurrences
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        if observed_source_at.is_some() {if let Some(o)=self.junction.as_mut().and_then(|j|j.operative.as_mut()) {o.births.try_reserve(1).map_err(|_|ConstitutiveFibreError::Shape)?;}}
        self.history
            .try_reserve(1)
            .map_err(|_| ConstitutiveFibreError::Shape)?;
        let at = self.history.len();
        let lineage = NativeFieldLineage {
            occurrence: at,
            frame: self.frame.view.ordinal,
            predecessor_state: at.checked_sub(1),
            received_from: source_at,
            source_contact: if let Some((quadrature,coordinate))=actuation {Some(NativeFieldSourceContact::MaterialActuation{quadrature,coordinate})}else{occurrence
                .source
                .as_ref()
                .map(|_| NativeFieldSourceContact::Emission)
                .or_else(|| {
                    occurrence
                        .anchor
                        .as_ref()
                        .map(|_| NativeFieldSourceContact::RetainedAnchor)
                })},
            incoming: if resident_current.is_some() {
                NativeFieldIncoming::Resident {
                    resident_nodes: self.nodes(),
                }
            } else {
                NativeFieldIncoming::Exterior(occurrence.incoming.clone())
            },
        };
        let surface = self.relation.surface;
        let input = Rc::new(if resident_current.is_some() {
            surface.fresh_section(self.nodes(), 3, ResidentGrain(0))?
        } else {
            surface.mount_section_rest(
                &ResidentSectionRest::found(
                    self.nodes(),
                    3,
                    ResidentGrain(0),
                    64,
                    occurrence
                        .incoming
                        .iter()
                        .flat_map(|p| p.words())
                        .map(|v| (v, v))
                        .collect(),
                )
                .map_err(|_| ConstitutiveFibreError::Shape)?,
            )?
        });
        let output_width = self
            .nodes()
            .checked_mul(16)
            .and_then(|v| v.checked_add(9))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let output = surface.fresh_section(1, output_width, ResidentGrain(0))?;
        if self.transport.as_ref().is_some_and(|t|!t.source.is_operative()) && self.junction.as_ref().and_then(|j|j.operative.as_ref()).is_some_and(|o|!o.is_fixed()) {
            return Err(ConstitutiveFibreError::Rest("the fixed-contact material source cannot read changed operative contacts".into()));
        }
        let material_target=self.transport.as_ref().map_or((self.nodes(),0),|t|(t.target.dimension(self.nodes()).unwrap(),t.target.kernel()));
        let prepared = self.prepare_junction(observed_source_at.is_some())?;
        let prepared_transport = self.prepare_material_transport(observed_source_at)?;
        let actuation_target=actuation.map(|_|surface.fresh_section(1,4*material_target.0+2,ResidentGrain(0))).transpose()?;
        let lineage_lanes = if resident_current.is_some() {
            vec![vec![], vec![0]]
        } else {
            vec![vec![]]
        };
        let mut passage = surface.begin_passage(&lineage_lanes)?;
        if let Some(current) = resident_current {
            {
                let lane = passage.open(0, &[])?;
                surface.record_field_current_input(&lane, current, &input)?;
            }
            passage.close(0, &input, 64)?;
        }
        let (field_lane, predecessors) = if resident_current.is_some() {
            (1, vec![0])
        } else {
            (0, vec![])
        };
        {
            let lane = passage.open(field_lane, &predecessors)?;
            if let Some((quadrature,coordinate))=actuation {
                surface.record_material_actuation(&lane,&input,self.nodes(),material_target.0,material_target.1,self.transport_grain()?,quadrature,coordinate,actuation_target.as_ref().unwrap())?;
            }
            if let Some(refresh) = prepared_transport.as_ref().and_then(|p| p.refresh.as_ref()) {
                if let Some(weights) = &refresh.moment_weights {
                    surface.record_moment_source_current(
                        &lane,
                        self.history[observed_source_at.expect("refresh source")]
                            .resident()?
                            .transport
                            .as_ref()
                            .expect("source report"),
                        &refresh.tail,
                        refresh.count,
                        weights,
                        self.nodes(),
                        self.transport_grain()?,
                        &refresh.output,
                    )?;
                } else {
                    surface.record_complete_material_source_current(
                        &lane,
                        self.history[observed_source_at.expect("refresh source")]
                            .resident()?
                            .transport
                            .as_ref()
                            .expect("complete source report"),
                        &refresh.tail,
                        refresh.count,
                        self.nodes(),
                        &refresh.output,
                    )?;
                }
            }
            surface.record_constitutive_field(
                &lane,
                &self.seed,
                &mut self.memory,
                &mut self.relation.basis,
                &input,
                observed_source_at
                    .map(|i| self.history[i].resident().map(|h| &h.section))
                    .transpose()?,
                &self.frame.native,
                observed_source_at.map(|i| &self.history[i].frame.native),
                self.junction
                    .as_ref()
                    .zip(prepared.as_ref())
                    .map(|(old, (next, scratch))| {
                        (
                            &old.covariance,
                            old.current.as_ref(),
                            &next.covariance,
                            next.report.as_ref(),
                            scratch,
                            old.kernel(),
                        )
                    }),
                self.transport
                    .as_mut()
                    .zip(prepared_transport.as_ref())
                    .map(|(old, next)| {
                        (
                            &mut old.state,
                            observed_source_at.and_then(|i| {
                                self.history[i]
                                    .resident
                                    .as_ref()
                                    .and_then(|h| h.junction.as_deref())
                            }),
                            observed_source_at.and_then(|i| {
                                self.history[i]
                                    .resident
                                    .as_ref()
                                    .and_then(|h| h.transport.as_deref())
                            }),
                            &next.delta,
                            next.report.as_ref(),
                            old.source.kernel(),
                            next.refresh.as_ref().map(|r| &r.output),
                        )
                    }),
                at as u64,
                prepared_transport
                    .as_ref()
                    .and_then(|p| p.moment.as_ref())
                    .map(|p| (&p.table, p.count, &p.weights)),
                prepared_transport.as_ref().and_then(|p|p.contextual.as_ref()).map(|p|(&p.table,&p.weights,&p.evaluations,observed_source_at.unwrap_or(0) as u64)),
                prepared.as_ref().and_then(|(p,_)|p.operative.as_ref()).map(|p|&p.table),
                material_target,
                &output,
            )?;
        }
        passage.close(field_lane, &output, 64)?;
        let passage = passage.finish()?;
        self.pending = Some(HeldField {
            archived: None,
            resident: Some(ResidentFieldHistory {
                section: output,
                incoming: resident_current.is_some().then(|| Rc::clone(&input)),
                junction: prepared.as_ref().map(|(next, _)| Rc::clone(&next.report)),
                transport: prepared_transport
                    .as_ref()
                    .map(|next| Rc::clone(&next.report)),
                operative: prepared.as_ref().and_then(|(p,_)|p.operative.as_ref()).map(|p|p.history()),
            }),
            lineage: lineage.clone(),
            frame: Rc::clone(&self.frame),
            returned: false,
        });
        let (pending_junction, junction_scratch) = match prepared {
            Some((next, scratch)) => (Some(next), Some(scratch)),
            None => (None, None),
        };
        self.pending_junction = pending_junction;
        self.pending_transport = prepared_transport;
        self.relation.usable = false;
        let launched = passage.launch()?;
        drop(junction_scratch);
        if !launched.obstruction.is_empty() {
            self.pending = None;
            self.pending_junction = None;
            self.pending_transport = None;
            self.relation.usable = true;
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "{:?}",
                launched.obstruction
            )));
        }
        // Observer failure retains the existing pending/uncertain state; it is not rollback.
        // The resident callback is unit-valued and performs no section readout.
        let observed = observe(self, observed_source_at, occurrence)?;
        if occurrence.source.is_some() {
            self.history[source_at.expect("linear source")].returned = true;
        }
        occurrence.source = None;
        self.history
            .push(self.pending.take().expect("completed field"));
        if let Some(mut next) = self.pending_junction.take() {
            let representation = self
                .junction
                .as_ref()
                .expect("existing junction")
                .representation;
            let mut operative=self.junction.as_mut().unwrap().operative.take();
            if let Some(pending)=next.operative.take() {operative.as_mut().unwrap().receive(pending,observed_source_at,at);}
            self.junction = Some(PairedJunction {
                representation,
                solver: self.junction.as_ref().expect("existing junction").solver,
                covariance: next.covariance,
                current: next.report,
                operative,
            });
        }
        self.relation.occurrences = next;
        self.pending_transport = None;
        self.relation.usable = true;
        Ok((
            NativeFieldContinuation {
                source: NativeFieldEmission {
                    owner: Rc::clone(&self.owner),
                    occurrence: at,
                },
                lineage,
                frame: Rc::clone(&self.frame.view),
            },
            observed,
        ))
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod resident_tests;
