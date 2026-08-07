//! Exact carried neighborhoods between a receiver-local star and a terminal face.
//!
//! A tube is not a cached picture.  Its core is one caused receiver, its
//! transverse section is the receiver's exact local primitive population, its
//! horizon is the link of the receiver's simplicial star, and its attachment
//! to the presentation is an exact projective transport.  A terminal trace is
//! retained only while all of those carriers and the terminal aperture remain
//! exact.  Change invalidates the affected tube, never the unrelated atlas.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;
use num_traits::Zero;
use relational_geometry::{RatMat3, ReceiverId};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    CertifiedReceiverFace, ContinuousPresentation, EventId, PluralReceiverAssembly,
    PresentationAddress, PresentedPrimitive, PresentedPrimitiveKey, PrimitiveApertureTrace,
    RayFamily, ReceiverApertureTrace, ReceiverFace, ReceiverFaceFormationCause,
    ReceiverFaceFormationReceipt, ReceiverFaceSpec, ReceiverPrimitive, ReceiverSourceRebase,
    ReceiverSourceSection, ReceiverStandingRelation, TerminalMatrixSpec, VertexStarLink,
    materialize_receiver_support,
};

/// How an already-formed receiver face crossed into the contemporary cut.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverFaceCarry {
    Retained,
    Rebased(Box<ReceiverSourceRebase>),
}

/// Why one receiver tube does or does not owe a new terminal restriction.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverTubeChange {
    /// No earlier tube carried this receiver.
    Founded,
    /// The causal receiver was replaced rather than continuously transported.
    Refounded,
    /// Its local simplicial horizon or local face changed.
    Deformed,
    /// Its local body remained exact while its presentation chart changed.
    Transported,
    /// Only the finite terminal aperture changed.
    ApertureChanged,
    /// Source and receiver were co-transported by one proved exact affine
    /// re-base, so their already-formed local and terminal faces carry.
    Rebased,
    /// Every carrier remains exact; its already-restricted support is standing.
    Retained,
}

impl ReceiverTubeChange {
    pub fn owes_terminal_trace(self) -> bool {
        !matches!(self, Self::Rebased | Self::Retained)
    }
}

/// One exact presentation-chart crossing in the tube's lived word.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPresentationTransport {
    pub event: EventId,
    pub map: RatMat3,
}

/// One event edge between two structurally exact tube sections.
///
/// This edge remains present even when the terminal trace is retained. Thus a
/// physical occurrence cannot disappear merely because observation happened
/// to reuse the same finite restriction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverTubeTransition {
    pub receiver: ReceiverId,
    pub predecessor_event: Option<EventId>,
    pub event: EventId,
    pub change: ReceiverTubeChange,
    pub source_rebase: Option<ReceiverSourceRebase>,
    pub presentation_transport: Option<ReceiverPresentationTransport>,
    pub terminal_trace_carried: bool,
}

/// One exact regular-neighborhood carrier at the current grain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverTube {
    pub schema: String,
    pub receiver: ReceiverId,
    /// Founding occurrence of the causal receiver body.
    pub source_event: EventId,
    /// Physical occurrence embodied by this contemporary tube section.
    pub contemporary_event: EventId,
    /// Closed star and transverse link: the combinatorial tube horizon.
    pub topology: VertexStarLink,
    /// Exact construction material in the receiver's intrinsic causal star,
    /// before receiver motion or projection.
    pub source_section: ReceiverSourceSection,
    /// The receiver's contemporary ray family. This is a transported chart,
    /// not deformation of `source_section`.
    pub receiver_rays: RayFamily,
    /// The complete intrinsic section after receiver-relative projection and
    /// before transport into the terminal presentation chart.
    pub receiver_face: ReceiverFace,
    pub formation: ReceiverFaceFormationReceipt,
    /// The caused map from that local section into the common presentation.
    pub relation: ReceiverStandingRelation,
    /// The same section after the current exact projective transport.
    pub presented_primitives: Vec<ReceiverPrimitive>,
    /// Ordered local presentation crossings since this receiver was founded.
    /// A product matrix is reconstructed only for a query which needs it.
    pub presentation_word: Vec<ReceiverPresentationTransport>,
    /// Event edges through which this tube section was reached.
    pub transitions: Vec<ReceiverTubeTransition>,
    /// The finite boundary restriction of the continuous presented section.
    pub terminal_trace: ReceiverApertureTrace,
}

impl ReceiverTube {
    pub fn presentation_holonomy(&self) -> RatMat3 {
        self.presentation_word
            .iter()
            .fold(RatMat3::identity(), |product, step| {
                step.map.multiply(&product)
            })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReceiverTubeCandidate {
    receiver: ReceiverId,
    source_event: EventId,
    contemporary_event: EventId,
    topology: VertexStarLink,
    source_section: ReceiverSourceSection,
    receiver_rays: RayFamily,
    receiver_face: ReceiverFace,
    formation: ReceiverFaceFormationReceipt,
    relation: ReceiverStandingRelation,
    presented_primitives: Vec<ReceiverPrimitive>,
    presentation_word: Vec<ReceiverPresentationTransport>,
    transitions: Vec<ReceiverTubeTransition>,
    new_transition: Option<ReceiverTubeTransition>,
}

/// Read-only reconciliation proposal.  Planning never mutates standing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TerminalTubePlan {
    specification: TerminalMatrixSpec,
    boundary_name: String,
    candidates: BTreeMap<ReceiverId, ReceiverTubeCandidate>,
    changes: BTreeMap<ReceiverId, ReceiverTubeChange>,
    departed: BTreeSet<ReceiverId>,
    materialized_receivers: usize,
    materialized_primitives: usize,
    /// A changed tube may share an exact continuous presented section with
    /// another changed tube.  Both then restrict through one representative
    /// trace; this is exact exterior-face reuse, not image deduplication.
    trace_sources: BTreeMap<ReceiverId, ReceiverId>,
    trace_receivers: BTreeSet<ReceiverId>,
    /// Candidate primitive key to the representative exact trace it shares.
    trace_primitive_sources: BTreeMap<PresentedPrimitiveKey, PresentedPrimitiveKey>,
    trace_primitives: BTreeSet<PresentedPrimitiveKey>,
}

impl TerminalTubePlan {
    pub fn change(&self, receiver: ReceiverId) -> Option<ReceiverTubeChange> {
        self.changes.get(&receiver).copied()
    }

    pub fn changes(&self) -> &BTreeMap<ReceiverId, ReceiverTubeChange> {
        &self.changes
    }

    pub fn departed(&self) -> &BTreeSet<ReceiverId> {
        &self.departed
    }

    pub fn trace_receivers(&self) -> &BTreeSet<ReceiverId> {
        &self.trace_receivers
    }

    pub fn trace_source(&self, receiver: ReceiverId) -> Option<ReceiverId> {
        self.trace_sources.get(&receiver).copied()
    }

    pub fn trace_primitive_keys(&self) -> &BTreeSet<PresentedPrimitiveKey> {
        &self.trace_primitives
    }

    pub fn trace_primitive_source(
        &self,
        key: PresentedPrimitiveKey,
    ) -> Option<PresentedPrimitiveKey> {
        self.trace_primitive_sources.get(&key).copied()
    }

    /// Materialize the exact presentation population actually owed by this
    /// plan. Retained and aperture-only sections are absent; their already
    /// formed presentation carriers remain in the atlas.
    pub fn trace_presentation(&self) -> ContinuousPresentation {
        let primitives = self
            .trace_primitives
            .iter()
            .map(|key| {
                let primitive = self.candidates[&key.receiver]
                    .presented_primitives
                    .iter()
                    .find(|primitive| primitive.id() == key.primitive)
                    .expect("every trace key was selected from its candidate");
                PresentedPrimitive {
                    receiver: key.receiver,
                    primitive: primitive.clone(),
                }
            })
            .collect();
        ContinuousPresentation::selected_support(self.boundary_name.clone(), primitives)
    }

    pub fn materialized_receivers(&self) -> usize {
        self.materialized_receivers
    }

    pub fn materialized_primitives(&self) -> usize {
        self.materialized_primitives
    }
}

/// One changed finite support member.  Absence is exact zero support.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TerminalSupportDelta {
    pub receiver: ReceiverId,
    pub address: PresentationAddress,
    pub before: BigUint,
    pub after: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TerminalTubeReceipt {
    pub founded: BigUint,
    pub refounded: BigUint,
    pub deformed: BigUint,
    pub transported: BigUint,
    pub aperture_changed: BigUint,
    pub rebased: BigUint,
    pub retained: BigUint,
    pub departed: BigUint,
    pub traced_receivers: BigUint,
    pub reused_receivers: BigUint,
    pub shared_trace_receivers: BigUint,
    pub traced_primitives: BigUint,
    pub reused_primitives: BigUint,
    pub shared_trace_primitives: BigUint,
    pub reused_addresses: BigUint,
    pub avoided_support_queries: BigUint,
    pub changed_addresses: BigUint,
    /// Receiver relations which had to act on a local section in this plan.
    pub materialized_receivers: BigUint,
    /// Exact primitives expanded through those selected receiver relations.
    pub materialized_primitives: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TerminalTubeRadiation {
    pub receipt: TerminalTubeReceipt,
    pub support_deltas: Vec<TerminalSupportDelta>,
    pub transitions: Vec<ReceiverTubeTransition>,
}

/// Persistent exact terminal restriction of the live receiver-tube population.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TerminalTubeAtlas {
    pub schema: String,
    pub specification: Option<TerminalMatrixSpec>,
    pub tubes: BTreeMap<ReceiverId, ReceiverTube>,
}

impl TerminalTubeAtlas {
    pub fn new() -> Self {
        Self {
            schema: "holonic-engine.terminal-tube-atlas.v3".to_owned(),
            specification: None,
            tubes: BTreeMap::new(),
        }
    }

    pub fn traces(&self) -> BTreeMap<ReceiverId, ReceiverApertureTrace> {
        self.tubes
            .iter()
            .map(|(receiver, tube)| (*receiver, tube.terminal_trace.clone()))
            .collect()
    }

    pub fn trace(&self, receiver: ReceiverId) -> Option<&ReceiverApertureTrace> {
        self.tubes.get(&receiver).map(|tube| &tube.terminal_trace)
    }

    /// Borrow the atlas's already materialized receiver sections as one
    /// continuous support view. No receiver relation is recomputed.
    pub fn support_presentation(&self, boundary_name: impl Into<String>) -> ContinuousPresentation {
        ContinuousPresentation::selected_support(
            boundary_name,
            self.tubes
                .values()
                .flat_map(|tube| {
                    tube.presented_primitives
                        .iter()
                        .cloned()
                        .map(move |primitive| PresentedPrimitive {
                            receiver: tube.receiver,
                            primitive,
                        })
                })
                .collect(),
        )
    }

    /// Carry a previously formed receiver face when every exact carrier which
    /// could change that face is either unchanged or co-transported through
    /// one proved affine re-base.
    ///
    /// This check happens before source projection. It is therefore lawful
    /// computational reuse rather than post-hoc recognition of a picture
    /// which has already been rebuilt.
    pub fn carried_receiver_face(
        &self,
        specification: &ReceiverFaceSpec,
        source_event: EventId,
        topology: &VertexStarLink,
        source_section: &ReceiverSourceSection,
    ) -> Option<(ReceiverFace, ReceiverFaceCarry)> {
        let tube = self.tubes.get(&specification.receiver.id)?;
        if tube.source_event != source_event {
            return None;
        }
        if tube.topology != *topology
            || tube.receiver_face.receiver != specification.receiver.id
            || tube.receiver_face.extent != specification.extent
            || tube.formation.orientation != specification.receiver.orientation
            || !acceptance_carries_event(&tube.receiver_face.acceptance, &specification.acceptance)
        {
            return None;
        }
        let mut face = tube.receiver_face.clone();
        face.acceptance = specification.acceptance.clone();
        if tube.source_section == *source_section && tube.receiver_rays == specification.rays {
            return Some((face, ReceiverFaceCarry::Retained));
        }
        let rebase = tube.source_section.exact_rebase_to(
            source_section,
            &tube.receiver_rays,
            &specification.rays,
        )?;
        face.rays = specification.rays.clone();
        Some((face, ReceiverFaceCarry::Rebased(Box::new(rebase))))
    }

    pub fn carried_receiver_formation(
        &self,
        event: EventId,
        specification: &ReceiverFaceSpec,
        source_event: EventId,
        topology: &VertexStarLink,
        source_section: &ReceiverSourceSection,
    ) -> Option<CertifiedReceiverFace> {
        let predecessor = self.tubes.get(&specification.receiver.id)?;
        let (face, carry) =
            self.carried_receiver_face(specification, source_event, topology, source_section)?;
        let cause = match carry {
            ReceiverFaceCarry::Retained => ReceiverFaceFormationCause::Retained {
                predecessor_event: predecessor.contemporary_event,
            },
            ReceiverFaceCarry::Rebased(proof) => ReceiverFaceFormationCause::Rebased {
                predecessor_event: predecessor.contemporary_event,
                proof,
            },
        };
        Some(CertifiedReceiverFace {
            formation: ReceiverFaceFormationReceipt {
                event,
                receiver: specification.receiver.id,
                source_section: source_section.clone(),
                rays: specification.rays.clone(),
                orientation: specification.receiver.orientation.clone(),
                face: face.clone(),
                cause,
            },
            face,
        })
    }

    /// Compatibility read for callers which require literal retention.
    pub fn retained_receiver_face(
        &self,
        specification: &ReceiverFaceSpec,
        source_event: EventId,
        topology: &VertexStarLink,
        source_section: &ReceiverSourceSection,
    ) -> Option<&ReceiverFace> {
        let tube = self.tubes.get(&specification.receiver.id)?;
        (tube.source_event == source_event
            && tube.topology == *topology
            && tube.source_section == *source_section
            && tube.receiver_rays == specification.rays
            && tube.formation.orientation == specification.receiver.orientation
            && tube.receiver_face.receiver == specification.receiver.id
            && tube.receiver_face.extent == specification.extent)
            .then_some(&tube.receiver_face)
    }

    /// Compare a complete contemporary receiver population to retained
    /// standing.  This forms no terminal support and changes no atlas state.
    #[allow(clippy::too_many_arguments)]
    pub fn plan(
        &self,
        event: EventId,
        assembly: &PluralReceiverAssembly,
        specification: &TerminalMatrixSpec,
        topologies: &BTreeMap<ReceiverId, VertexStarLink>,
        source_sections: &BTreeMap<ReceiverId, ReceiverSourceSection>,
        formations: &BTreeMap<ReceiverId, ReceiverFaceFormationReceipt>,
    ) -> Result<TerminalTubePlan, TerminalTubeError> {
        specification.validate()?;
        let assembly_receivers = assembly.faces.keys().copied().collect::<BTreeSet<_>>();
        if topologies.keys().copied().collect::<BTreeSet<_>>() != assembly_receivers {
            return Err(TerminalTubeError::TopologyPopulationMismatch);
        }
        if source_sections.keys().copied().collect::<BTreeSet<_>>() != assembly_receivers {
            return Err(TerminalTubeError::SourceSectionPopulationMismatch);
        }
        if formations.keys().copied().collect::<BTreeSet<_>>() != assembly_receivers {
            return Err(TerminalTubeError::FormationPopulationMismatch);
        }

        let aperture_changed = self.specification.as_ref() != Some(specification);
        let mut candidates = BTreeMap::new();
        let mut changes = BTreeMap::new();
        let mut trace_receivers = BTreeSet::new();
        let mut materialized_receivers = 0_usize;
        let mut materialized_primitives = 0_usize;
        for receiver in assembly_receivers.iter().copied() {
            let face = assembly
                .faces
                .get(&receiver)
                .expect("receiver population was checked");
            let relation = assembly
                .relations
                .get(&receiver)
                .expect("assembly construction checks relation population");
            let topology = topologies
                .get(&receiver)
                .expect("topology population was checked");
            let source_section = source_sections
                .get(&receiver)
                .expect("source-section population was checked");
            let formation = formations
                .get(&receiver)
                .expect("formation population was checked");
            if formation.event != event
                || formation.receiver != receiver
                || formation.source_section != *source_section
                || formation.rays != face.rays
                || formation.face != *face
            {
                return Err(TerminalTubeError::FormationReceiptMismatch(receiver));
            }
            if relation.source_event > event {
                return Err(TerminalTubeError::EventPrecedesReceiverFounding {
                    event,
                    receiver,
                    founding: relation.source_event,
                });
            }
            let previous = self.tubes.get(&receiver);
            let source_rebase = match &formation.cause {
                ReceiverFaceFormationCause::Projected => None,
                ReceiverFaceFormationCause::Retained { predecessor_event } => {
                    let previous =
                        previous.ok_or(TerminalTubeError::FormationReceiptMismatch(receiver))?;
                    let mut expected_face = previous.receiver_face.clone();
                    expected_face.acceptance = face.acceptance.clone();
                    if *predecessor_event != previous.contemporary_event
                        || previous.source_event != relation.source_event
                        || previous.topology != *topology
                        || previous.source_section != *source_section
                        || previous.receiver_rays != face.rays
                        || previous.formation.orientation != formation.orientation
                        || expected_face != *face
                    {
                        return Err(TerminalTubeError::FormationReceiptMismatch(receiver));
                    }
                    None
                }
                ReceiverFaceFormationCause::Rebased {
                    predecessor_event,
                    proof,
                } => {
                    let previous =
                        previous.ok_or(TerminalTubeError::FormationReceiptMismatch(receiver))?;
                    let derived = previous.source_section.exact_rebase_to(
                        source_section,
                        &previous.receiver_rays,
                        &face.rays,
                    );
                    let mut expected_face = previous.receiver_face.clone();
                    expected_face.rays = face.rays.clone();
                    expected_face.acceptance = face.acceptance.clone();
                    if *predecessor_event != previous.contemporary_event
                        || previous.source_event != relation.source_event
                        || previous.topology != *topology
                        || previous.formation.orientation != formation.orientation
                        || derived.as_ref() != Some(proof.as_ref())
                        || expected_face != *face
                    {
                        return Err(TerminalTubeError::FormationReceiptMismatch(receiver));
                    }
                    Some((**proof).clone())
                }
            };
            let change = match previous {
                None => ReceiverTubeChange::Founded,
                Some(previous) if previous.source_event != relation.source_event => {
                    ReceiverTubeChange::Refounded
                }
                Some(previous) if previous.topology != *topology => ReceiverTubeChange::Deformed,
                Some(previous)
                    if previous.source_section != *source_section
                        && source_rebase.is_some()
                        && matches!(
                            &formation.cause,
                            ReceiverFaceFormationCause::Rebased { .. }
                        )
                        && previous.receiver_face.extent == face.extent
                        && previous.receiver_face.arrangement == face.arrangement
                        && previous.relation == *relation =>
                {
                    ReceiverTubeChange::Rebased
                }
                Some(previous) if previous.source_section != *source_section => {
                    ReceiverTubeChange::Deformed
                }
                Some(previous)
                    if previous.relation != *relation
                        || previous.receiver_rays != face.rays
                        || previous.formation.orientation != formation.orientation =>
                {
                    ReceiverTubeChange::Transported
                }
                Some(previous) if !receiver_face_carries_event(&previous.receiver_face, face) => {
                    return Err(TerminalTubeError::ReceiverFactorizationChanged(receiver));
                }
                Some(_) if aperture_changed => ReceiverTubeChange::ApertureChanged,
                Some(_) => ReceiverTubeChange::Retained,
            };
            let presented_primitives = match (previous, change) {
                (
                    Some(previous),
                    ReceiverTubeChange::Retained
                    | ReceiverTubeChange::Rebased
                    | ReceiverTubeChange::ApertureChanged,
                ) => previous.presented_primitives.clone(),
                _ => {
                    let materialized = materialize_receiver_support(face, relation)?;
                    materialized_receivers += 1;
                    materialized_primitives += materialized.len();
                    materialized
                        .into_iter()
                        .map(|presented| presented.primitive)
                        .collect()
                }
            };
            let primitive_ids = presented_primitives
                .iter()
                .map(ReceiverPrimitive::id)
                .collect::<BTreeSet<_>>();
            if primitive_ids.len() != presented_primitives.len() {
                return Err(TerminalTubeError::DuplicatePresentedPrimitive(receiver));
            }
            let presentation_transport = match previous {
                Some(previous)
                    if change != ReceiverTubeChange::Refounded
                        && previous.relation != *relation =>
                {
                    Some(ReceiverPresentationTransport {
                        event,
                        map: presentation_step(previous, relation)?,
                    })
                }
                _ => None,
            };
            let mut presentation_word = match previous {
                Some(previous) if change != ReceiverTubeChange::Refounded => {
                    previous.presentation_word.clone()
                }
                _ => Vec::new(),
            };
            if let Some(step) = &presentation_transport {
                presentation_word.push(step.clone());
            }
            let mut transitions = previous
                .map(|previous| previous.transitions.clone())
                .unwrap_or_default();
            let new_transition = match previous {
                None => Some(ReceiverTubeTransition {
                    receiver,
                    predecessor_event: None,
                    event,
                    change,
                    source_rebase: source_rebase.clone(),
                    presentation_transport: presentation_transport.clone(),
                    terminal_trace_carried: !change.owes_terminal_trace(),
                }),
                Some(previous)
                    if previous.contemporary_event != event
                        || change != ReceiverTubeChange::Retained =>
                {
                    Some(ReceiverTubeTransition {
                        receiver,
                        predecessor_event: Some(previous.contemporary_event),
                        event,
                        change,
                        source_rebase: source_rebase.clone(),
                        presentation_transport: presentation_transport.clone(),
                        terminal_trace_carried: !change.owes_terminal_trace(),
                    })
                }
                Some(_) => None,
            };
            if let Some(transition) = &new_transition {
                transitions.push(transition.clone());
            }
            changes.insert(receiver, change);
            candidates.insert(
                receiver,
                ReceiverTubeCandidate {
                    receiver,
                    source_event: relation.source_event,
                    contemporary_event: event,
                    topology: topology.clone(),
                    source_section: source_section.clone(),
                    receiver_rays: face.rays.clone(),
                    receiver_face: face.clone(),
                    formation: formation.clone(),
                    relation: relation.clone(),
                    presented_primitives,
                    presentation_word,
                    transitions,
                    new_transition,
                },
            );
        }
        let departed = self
            .tubes
            .keys()
            .filter(|receiver| !assembly_receivers.contains(receiver))
            .copied()
            .collect();
        let mut trace_sources = BTreeMap::new();
        let mut representatives = Vec::<ReceiverId>::new();
        for (receiver, candidate) in &candidates {
            if !changes[receiver].owes_terminal_trace() {
                continue;
            }
            let representative = representatives
                .iter()
                .copied()
                .find(|prior| {
                    candidates[prior].presented_primitives == candidate.presented_primitives
                })
                .unwrap_or(*receiver);
            if representative == *receiver {
                representatives.push(*receiver);
                trace_receivers.insert(*receiver);
            }
            trace_sources.insert(*receiver, representative);
        }
        let mut trace_primitive_sources = BTreeMap::new();
        let mut trace_primitives = BTreeSet::new();
        let mut primitive_representatives =
            Vec::<(PresentedPrimitiveKey, ReceiverPrimitive)>::new();
        for (receiver, candidate) in &candidates {
            let previous = self.tubes.get(receiver);
            for primitive in &candidate.presented_primitives {
                let key = PresentedPrimitiveKey {
                    receiver: *receiver,
                    primitive: primitive.id(),
                };
                let retained = !aperture_changed
                    && previous.is_some_and(|previous| {
                        previous
                            .presented_primitives
                            .iter()
                            .find(|prior| prior.id() == primitive.id())
                            == Some(primitive)
                            && previous
                                .terminal_trace
                                .primitive_sections
                                .contains_key(&primitive.id())
                    });
                if retained {
                    continue;
                }
                let representative = primitive_representatives
                    .iter()
                    .find_map(|(prior_key, prior)| (prior == primitive).then_some(*prior_key))
                    .unwrap_or(key);
                if representative == key {
                    primitive_representatives.push((key, primitive.clone()));
                    trace_primitives.insert(key);
                }
                trace_primitive_sources.insert(key, representative);
            }
        }
        Ok(TerminalTubePlan {
            specification: specification.clone(),
            boundary_name: assembly.boundary_name.clone(),
            candidates,
            changes,
            departed,
            materialized_receivers,
            materialized_primitives,
            trace_sources,
            trace_receivers,
            trace_primitive_sources,
            trace_primitives,
        })
    }

    /// Atomically install one planned successor after the boundary executor
    /// returns every newly owed representative primitive trace. A legacy
    /// caller may return additional well-addressed primitive sections; they do
    /// not replace retained standing.
    pub fn commit(
        &mut self,
        plan: TerminalTubePlan,
        returned: BTreeMap<ReceiverId, ReceiverApertureTrace>,
    ) -> Result<TerminalTubeRadiation, TerminalTubeError> {
        let mut returned_sections =
            BTreeMap::<PresentedPrimitiveKey, PrimitiveApertureTrace>::new();
        for (receiver, trace) in &returned {
            if trace.receiver != *receiver {
                return Err(TerminalTubeError::MisaddressedTrace {
                    expected: *receiver,
                    actual: trace.receiver,
                });
            }
            for (primitive, section) in &trace.primitive_sections {
                let expected = PresentedPrimitiveKey {
                    receiver: *receiver,
                    primitive: *primitive,
                };
                if section.key != expected {
                    return Err(TerminalTubeError::MisaddressedPrimitiveTrace {
                        expected,
                        actual: section.key,
                    });
                }
                if returned_sections
                    .insert(expected, section.clone())
                    .is_some()
                {
                    return Err(TerminalTubeError::DuplicateReturnedPrimitive(expected));
                }
            }
        }
        let returned_keys = returned_sections.keys().copied().collect::<BTreeSet<_>>();
        if !plan.trace_primitives.is_subset(&returned_keys) {
            return Err(TerminalTubeError::PrimitiveTracePopulationMismatch {
                required: plan.trace_primitives.clone(),
                returned: returned_keys,
            });
        }
        let before = &self.tubes;
        let transitions = plan
            .candidates
            .values()
            .filter_map(|candidate| candidate.new_transition.clone())
            .collect::<Vec<_>>();
        let mut next = BTreeMap::new();
        for (receiver, candidate) in plan.candidates {
            let mut primitive_sections = Vec::new();
            for primitive in &candidate.presented_primitives {
                let key = PresentedPrimitiveKey {
                    receiver,
                    primitive: primitive.id(),
                };
                let mut section = if let Some(source) = plan.trace_primitive_sources.get(&key) {
                    returned_sections
                        .get(source)
                        .expect("the required returned primitive population was checked")
                        .clone()
                } else {
                    before
                        .get(&receiver)
                        .and_then(|tube| {
                            tube.terminal_trace.primitive_sections.get(&primitive.id())
                        })
                        .cloned()
                        .ok_or(TerminalTubeError::MissingRetainedPrimitive(key))?
                };
                section.key = key;
                primitive_sections.push(section);
            }
            let trace =
                ReceiverApertureTrace::from_primitive_sections(receiver, primitive_sections)?;
            next.insert(
                receiver,
                ReceiverTube {
                    schema: "holonic-engine.receiver-tube.v3".to_owned(),
                    receiver: candidate.receiver,
                    source_event: candidate.source_event,
                    contemporary_event: candidate.contemporary_event,
                    topology: candidate.topology,
                    source_section: candidate.source_section,
                    receiver_rays: candidate.receiver_rays,
                    receiver_face: candidate.receiver_face,
                    formation: candidate.formation,
                    relation: candidate.relation,
                    presented_primitives: candidate.presented_primitives,
                    presentation_word: candidate.presentation_word,
                    transitions: candidate.transitions,
                    terminal_trace: trace,
                },
            );
        }

        let mut support_deltas = Vec::new();
        let receivers = before
            .keys()
            .chain(next.keys())
            .copied()
            .collect::<BTreeSet<_>>();
        for receiver in receivers {
            let old_support = before
                .get(&receiver)
                .map(|tube| &tube.terminal_trace.support_multiplicity);
            let new_support = next
                .get(&receiver)
                .map(|tube| &tube.terminal_trace.support_multiplicity);
            let addresses = old_support
                .into_iter()
                .flat_map(|support| support.keys())
                .chain(new_support.into_iter().flat_map(|support| support.keys()))
                .copied()
                .collect::<BTreeSet<_>>();
            for address in addresses {
                let before_count = old_support
                    .and_then(|support| support.get(&address))
                    .cloned()
                    .unwrap_or_else(BigUint::zero);
                let after_count = new_support
                    .and_then(|support| support.get(&address))
                    .cloned()
                    .unwrap_or_else(BigUint::zero);
                if before_count != after_count {
                    support_deltas.push(TerminalSupportDelta {
                        receiver,
                        address,
                        before: before_count,
                        after: after_count,
                    });
                }
            }
        }

        let count = |species| {
            BigUint::from(
                plan.changes
                    .values()
                    .filter(|change| **change == species)
                    .count(),
            )
        };
        let reused = plan
            .changes
            .iter()
            .filter_map(|(receiver, change)| {
                matches!(
                    *change,
                    ReceiverTubeChange::Rebased | ReceiverTubeChange::Retained
                )
                .then(|| before.get(receiver))
                .flatten()
            })
            .collect::<Vec<_>>();
        let total_primitives = next
            .values()
            .map(|tube| tube.presented_primitives.len())
            .sum::<usize>();
        let shared_trace_primitives = plan
            .trace_primitive_sources
            .iter()
            .filter(|(candidate, source)| candidate != source)
            .count();
        let mut reused_primitive_sections = Vec::new();
        for (receiver, tube) in &next {
            for primitive in &tube.presented_primitives {
                let key = PresentedPrimitiveKey {
                    receiver: *receiver,
                    primitive: primitive.id(),
                };
                let reused = match plan.trace_primitive_sources.get(&key) {
                    None => before.get(receiver).and_then(|prior| {
                        prior
                            .terminal_trace
                            .primitive_sections
                            .get(&primitive.id())
                            .cloned()
                    }),
                    Some(source) if source != &key => returned_sections.get(source).cloned(),
                    Some(_) => None,
                };
                if let Some(section) = reused {
                    reused_primitive_sections.push(section);
                }
            }
        }
        let traced_receivers = plan
            .trace_primitives
            .iter()
            .map(|key| key.receiver)
            .collect::<BTreeSet<_>>();
        let receipt = TerminalTubeReceipt {
            founded: count(ReceiverTubeChange::Founded),
            refounded: count(ReceiverTubeChange::Refounded),
            deformed: count(ReceiverTubeChange::Deformed),
            transported: count(ReceiverTubeChange::Transported),
            aperture_changed: count(ReceiverTubeChange::ApertureChanged),
            rebased: count(ReceiverTubeChange::Rebased),
            retained: count(ReceiverTubeChange::Retained),
            departed: BigUint::from(plan.departed.len()),
            traced_receivers: BigUint::from(traced_receivers.len()),
            reused_receivers: BigUint::from(
                reused.len() + plan.trace_sources.len() - plan.trace_receivers.len(),
            ),
            shared_trace_receivers: BigUint::from(
                plan.trace_sources.len() - plan.trace_receivers.len(),
            ),
            traced_primitives: BigUint::from(plan.trace_primitives.len()),
            reused_primitives: BigUint::from(
                total_primitives.saturating_sub(plan.trace_primitives.len()),
            ),
            shared_trace_primitives: BigUint::from(shared_trace_primitives),
            reused_addresses: reused_primitive_sections
                .iter()
                .fold(BigUint::zero(), |sum, section| {
                    sum + BigUint::from(section.addresses.len())
                }),
            avoided_support_queries: reused_primitive_sections
                .iter()
                .fold(BigUint::zero(), |sum, section| {
                    sum + &section.exact_support_queries
                }),
            changed_addresses: BigUint::from(support_deltas.len()),
            materialized_receivers: BigUint::from(plan.materialized_receivers),
            materialized_primitives: BigUint::from(plan.materialized_primitives),
        };
        self.specification = Some(plan.specification);
        self.tubes = next;
        Ok(TerminalTubeRadiation {
            receipt,
            support_deltas,
            transitions,
        })
    }
}

fn acceptance_carries_event(
    previous: &Option<crate::ReceiverAcceptanceCover>,
    next: &Option<crate::ReceiverAcceptanceCover>,
) -> bool {
    match (previous, next) {
        (None, None) => true,
        (Some(previous), Some(next)) => {
            let mut carried = previous.clone();
            carried.event = next.event;
            carried == *next
        }
        (None, Some(_)) | (Some(_), None) => false,
    }
}

fn receiver_face_carries_event(previous: &ReceiverFace, next: &ReceiverFace) -> bool {
    let mut carried = previous.clone();
    carried.acceptance = next.acceptance.clone();
    carried == *next
}

fn presentation_step(
    previous: &ReceiverTube,
    next: &ReceiverStandingRelation,
) -> Result<RatMat3, TerminalTubeError> {
    let inverse = previous.relation.into_presentation.inverse().ok_or(
        TerminalTubeError::SingularRetainedRelation(previous.receiver),
    )?;
    Ok(next.into_presentation.multiply(&inverse))
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum TerminalTubeError {
    #[error(transparent)]
    Presentation(#[from] crate::PresentationError),
    #[error("the continuous presentation contains a receiver absent from its assembly")]
    PresentationPopulationMismatch {
        assembly: BTreeSet<ReceiverId>,
        presentation: BTreeSet<ReceiverId>,
    },
    #[error("the supplied topology population differs from the receiver assembly")]
    TopologyPopulationMismatch,
    #[error("the supplied source-section population differs from the receiver assembly")]
    SourceSectionPopulationMismatch,
    #[error("the supplied face-formation population differs from the receiver assembly")]
    FormationPopulationMismatch,
    #[error("receiver {0:?}'s face does not match its engine-owned formation receipt")]
    FormationReceiptMismatch(ReceiverId),
    #[error(
        "tube event {event:?} precedes receiver {receiver:?}'s founding occurrence {founding:?}"
    )]
    EventPrecedesReceiverFounding {
        event: EventId,
        receiver: ReceiverId,
        founding: EventId,
    },
    #[error("receiver {0:?} changed after local-face/presentation factorization")]
    PresentationFactorizationChanged(ReceiverId),
    #[error("receiver {0:?} presents one primitive identity more than once")]
    DuplicatePresentedPrimitive(ReceiverId),
    #[error("receiver {0:?}'s local face changed without a changed exact carrier")]
    ReceiverFactorizationChanged(ReceiverId),
    #[error("retained receiver {0:?} has a singular standing relation")]
    SingularRetainedRelation(ReceiverId),
    #[error("terminal trace population differs from the planned affected tubes")]
    TracePopulationMismatch {
        required: BTreeSet<ReceiverId>,
        returned: BTreeSet<ReceiverId>,
    },
    #[error("terminal primitive trace population omits one or more planned structural members")]
    PrimitiveTracePopulationMismatch {
        required: BTreeSet<PresentedPrimitiveKey>,
        returned: BTreeSet<PresentedPrimitiveKey>,
    },
    #[error("terminal primitive trace for {expected:?} was addressed to {actual:?}")]
    MisaddressedPrimitiveTrace {
        expected: PresentedPrimitiveKey,
        actual: PresentedPrimitiveKey,
    },
    #[error("terminal executor returned primitive {0:?} more than once")]
    DuplicateReturnedPrimitive(PresentedPrimitiveKey),
    #[error("planned retained primitive {0:?} has no exact standing restriction")]
    MissingRetainedPrimitive(PresentedPrimitiveKey),
    #[error("terminal trace for {expected:?} was addressed to {actual:?}")]
    MisaddressedTrace {
        expected: ReceiverId,
        actual: ReceiverId,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ConicCellId, HomogeneousConic, ProjectedConic, ProjectiveDepthLaw, ProjectiveLine2,
        ReceiverArrangement, ReceiverFace, ReceiverFaceExtent, ReceiverPrimitiveId,
        ReceiverSourceSelection, VertexId, VertexLinkClass, assemble_support_presentation_with_cpu,
        trace_primitives_aperture_with_cpu, trace_receivers_aperture_with_cpu,
    };
    use num_traits::One;
    use relational_geometry::{
        Construction, Geometry, ProjectionLaw, Rat, RatVec3, Receiver, integer,
    };

    fn topology(pivot: u64) -> VertexStarLink {
        VertexStarLink {
            pivot: VertexId(pivot),
            star_vertices: BTreeSet::from([VertexId(pivot)]),
            star_hinges: BTreeSet::new(),
            star_faces: BTreeSet::new(),
            link_vertices: BTreeSet::new(),
            link_edges: BTreeSet::new(),
            link_class: VertexLinkClass::Empty,
        }
    }

    fn face(receiver: ReceiverId) -> ReceiverFace {
        let line = ProjectiveLine2 {
            a: Rat::zero(),
            b: Rat::zero(),
            c: Rat::one(),
        };
        let form = HomogeneousConic {
            xx: integer(1),
            xy: integer(0),
            yy: integer(1),
            xw: integer(0),
            yw: integer(0),
            ww: integer(-1),
        };
        ReceiverFace {
            schema: "test".to_owned(),
            receiver,
            extent: ReceiverFaceExtent {
                horizontal_span: integer(2),
                vertical_span: integer(2),
            },
            rays: crate::RayFamily::Parallel {
                face_center: RatVec3::zero(),
                horizontal: RatVec3::from_i64(1, 0, 0),
                vertical: RatVec3::from_i64(0, 1, 0),
                direction: RatVec3::from_i64(0, 0, 1),
            },
            acceptance: None,
            arrangement: ReceiverArrangement {
                primitives: vec![ReceiverPrimitive::Conic(ProjectedConic {
                    source: ReceiverPrimitiveId::NativeConic(ConicCellId(1)),
                    class_in_receiver_chart: form.classify(),
                    form,
                    receiver_depth: ProjectiveDepthLaw {
                        numerator: line.clone(),
                        denominator: line,
                    },
                })],
                coordinate_fields: Vec::new(),
                linear_pieces: Vec::new(),
                relations: Vec::new(),
                seams: Vec::new(),
            },
            implicit_tori: Vec::new(),
        }
    }

    fn face_with_two_conics(receiver: ReceiverId) -> ReceiverFace {
        let mut face = face(receiver);
        let ReceiverPrimitive::Conic(first) = &face.arrangement.primitives[0] else {
            unreachable!("the base test face carries one conic")
        };
        let mut second = first.clone();
        second.source = ReceiverPrimitiveId::NativeConic(ConicCellId(2));
        second.form.ww = integer(-2);
        face.arrangement
            .primitives
            .push(ReceiverPrimitive::Conic(second));
        face
    }

    fn specification() -> TerminalMatrixSpec {
        TerminalMatrixSpec {
            width: 24,
            height: 16,
            boundary: crate::PresentationBoundary {
                horizontal_span: integer(4),
                vertical_span: integer(3),
            },
        }
    }

    fn source_sections(
        receivers: impl IntoIterator<Item = ReceiverId>,
    ) -> BTreeMap<ReceiverId, ReceiverSourceSection> {
        receivers
            .into_iter()
            .map(|receiver| (receiver, ReceiverSourceSection::default()))
            .collect()
    }

    fn projected_formations(
        event: EventId,
        assembly: &PluralReceiverAssembly,
        source_sections: &BTreeMap<ReceiverId, ReceiverSourceSection>,
    ) -> BTreeMap<ReceiverId, ReceiverFaceFormationReceipt> {
        assembly
            .faces
            .iter()
            .map(|(receiver, face)| {
                (
                    *receiver,
                    ReceiverFaceFormationReceipt {
                        event,
                        receiver: *receiver,
                        source_section: source_sections[receiver].clone(),
                        rays: face.rays.clone(),
                        orientation: relational_geometry::ReceiverOrientation::identity(),
                        face: face.clone(),
                        cause: ReceiverFaceFormationCause::Projected,
                    },
                )
            })
            .collect()
    }

    #[test]
    fn exact_retained_tube_avoids_retrace_and_matches_full_authority() {
        let receiver = ReceiverId(3);
        let assembly = PluralReceiverAssembly::new(
            "tube",
            vec![face(receiver)],
            vec![ReceiverStandingRelation::identity(receiver, EventId(7))],
        )
        .unwrap();
        let (presentation, _) =
            assemble_support_presentation_with_cpu(&assembly, &crate::CpuExecutor::serial())
                .unwrap();
        let topologies = BTreeMap::from([(receiver, topology(11))]);
        let source_sections = source_sections([receiver]);
        let specification = specification();
        let (authority, _) = trace_receivers_aperture_with_cpu(
            &presentation,
            &specification,
            &BTreeSet::from([receiver]),
            &crate::CpuExecutor::serial(),
        )
        .unwrap();

        let mut atlas = TerminalTubeAtlas::new();
        let first = atlas
            .plan(
                EventId(7),
                &assembly,
                &specification,
                &topologies,
                &source_sections,
                &projected_formations(EventId(7), &assembly, &source_sections),
            )
            .unwrap();
        assert_eq!(first.trace_receivers(), &BTreeSet::from([receiver]));
        assert_eq!(first.materialized_receivers(), 1);
        assert_eq!(
            first.materialized_primitives(),
            presentation.primitives.len()
        );
        assert_eq!(
            first.trace_presentation().primitives,
            presentation.primitives
        );
        atlas.commit(first, authority.clone()).unwrap();

        let retained = atlas
            .plan(
                EventId(8),
                &assembly,
                &specification,
                &topologies,
                &source_sections,
                &projected_formations(EventId(8), &assembly, &source_sections),
            )
            .unwrap();
        assert_eq!(
            retained.change(receiver),
            Some(ReceiverTubeChange::Retained)
        );
        assert!(retained.trace_receivers().is_empty());
        assert_eq!(retained.materialized_receivers(), 0);
        assert_eq!(retained.materialized_primitives(), 0);
        let radiation = atlas.commit(retained, BTreeMap::new()).unwrap();
        assert_eq!(radiation.receipt.reused_receivers, BigUint::one());
        assert!(radiation.receipt.avoided_support_queries > BigUint::zero());
        assert!(radiation.support_deltas.is_empty());
        assert_eq!(atlas.traces(), authority);

        let mut resized = specification.clone();
        resized.width += 1;
        let aperture_plan = atlas
            .plan(
                EventId(8),
                &assembly,
                &resized,
                &topologies,
                &source_sections,
                &projected_formations(EventId(8), &assembly, &source_sections),
            )
            .unwrap();
        assert_eq!(
            aperture_plan.change(receiver),
            Some(ReceiverTubeChange::ApertureChanged)
        );
        assert_eq!(aperture_plan.materialized_receivers(), 0);
        assert_eq!(aperture_plan.materialized_primitives(), 0);
        assert!(!aperture_plan.trace_primitive_keys().is_empty());

        let mut rotated = projected_formations(EventId(9), &assembly, &source_sections);
        rotated
            .get_mut(&receiver)
            .expect("the receiver formation exists")
            .orientation
            .precess_cayley(
                relational_geometry::ReceiverRotationAxis::Y,
                &(integer(1) / integer(16)),
            );
        let rotation_plan = atlas
            .plan(
                EventId(9),
                &assembly,
                &specification,
                &topologies,
                &source_sections,
                &rotated,
            )
            .unwrap();
        assert_eq!(
            rotation_plan.change(receiver),
            Some(ReceiverTubeChange::Transported)
        );
        assert_eq!(rotation_plan.trace_receivers(), &BTreeSet::from([receiver]));
        assert_eq!(rotation_plan.materialized_receivers(), 1);
        assert_eq!(
            rotation_plan.materialized_primitives(),
            presentation.primitives.len()
        );
    }

    #[test]
    fn exact_affine_rebase_carries_the_formed_face_and_terminal_trace() {
        let receiver = ReceiverId(4);
        let (mut construction, frame) = Construction::new("rebase source");
        let entity = construction
            .add_entity(
                "caused triangle",
                frame,
                Geometry::Triangle {
                    vertices: [
                        RatVec3::from_i64(-1, -1, 2),
                        RatVec3::from_i64(1, -1, 2),
                        RatVec3::from_i64(0, 1, 2),
                    ],
                },
            )
            .unwrap();
        let source = ReceiverSourceSelection {
            entities: BTreeSet::from([entity]),
            conics: BTreeSet::new(),
        }
        .section(&construction, &crate::NativeConicPopulation::default())
        .unwrap();
        let shift = RatVec3::from_i64(3, -2, 5);
        let mut target = source.clone();
        let Geometry::Triangle { vertices } =
            &mut target.entities.get_mut(&entity).unwrap().geometry
        else {
            unreachable!("the source contains one triangle")
        };
        for vertex in &mut *vertices {
            *vertex = vertex.add(&shift);
        }

        let initial_face = face(receiver);
        let initial = PluralReceiverAssembly::new(
            "rebase",
            vec![initial_face.clone()],
            vec![ReceiverStandingRelation::identity(receiver, EventId(8))],
        )
        .unwrap();
        let (initial_presentation, _) =
            assemble_support_presentation_with_cpu(&initial, &crate::CpuExecutor::serial())
                .unwrap();
        let specification = specification();
        let topologies = BTreeMap::from([(receiver, topology(12))]);
        let initial_sections = BTreeMap::from([(receiver, source)]);
        let (initial_trace, _) = trace_receivers_aperture_with_cpu(
            &initial_presentation,
            &specification,
            &BTreeSet::from([receiver]),
            &crate::CpuExecutor::serial(),
        )
        .unwrap();
        let mut atlas = TerminalTubeAtlas::new();
        let plan = atlas
            .plan(
                EventId(8),
                &initial,
                &specification,
                &topologies,
                &initial_sections,
                &projected_formations(EventId(8), &initial, &initial_sections),
            )
            .unwrap();
        atlas.commit(plan, initial_trace.clone()).unwrap();

        let mut moved_face = initial_face.clone();
        moved_face.rays = RayFamily::Parallel {
            face_center: shift,
            horizontal: RatVec3::from_i64(1, 0, 0),
            vertical: RatVec3::from_i64(0, 1, 0),
            direction: RatVec3::from_i64(0, 0, 1),
        };
        let mut inconsistent = target.clone();
        let Geometry::Triangle { vertices } =
            &mut inconsistent.entities.get_mut(&entity).unwrap().geometry
        else {
            unreachable!("the source contains one triangle")
        };
        vertices[0] = vertices[0].add(&RatVec3::from_i64(1, 0, 0));
        assert!(
            initial_sections[&receiver]
                .exact_rebase_to(&inconsistent, &initial_face.rays, &moved_face.rays)
                .is_none(),
            "one constituent outside the common affine map must force a fresh factorization"
        );
        let moved_specification = ReceiverFaceSpec {
            receiver: Receiver::new(
                receiver,
                "rebased receiver",
                frame,
                ProjectionLaw::Orthographic,
            ),
            extent: moved_face.extent.clone(),
            rays: moved_face.rays.clone(),
            acceptance: moved_face.acceptance.clone(),
        };
        let carried = atlas
            .carried_receiver_formation(
                EventId(9),
                &moved_specification,
                EventId(8),
                &topologies[&receiver],
                &target,
            )
            .expect("the co-transported section carries its already-formed face");
        assert!(matches!(
            carried.formation.cause(),
            ReceiverFaceFormationCause::Rebased { .. }
        ));
        assert_eq!(carried.face.arrangement, moved_face.arrangement);
        assert_eq!(carried.face.rays, moved_face.rays);

        let moved = PluralReceiverAssembly::new(
            "rebased",
            vec![carried.face.clone()],
            vec![ReceiverStandingRelation::identity(receiver, EventId(8))],
        )
        .unwrap();
        let moved_sections = BTreeMap::from([(receiver, target)]);
        let plan = atlas
            .plan(
                EventId(9),
                &moved,
                &specification,
                &topologies,
                &moved_sections,
                &BTreeMap::from([(receiver, carried.formation)]),
            )
            .unwrap();
        assert_eq!(plan.change(receiver), Some(ReceiverTubeChange::Rebased));
        assert!(plan.trace_receivers().is_empty());
        let radiation = atlas.commit(plan, BTreeMap::new()).unwrap();
        assert_eq!(radiation.receipt.rebased, BigUint::one());
        assert_eq!(atlas.traces(), initial_trace);
    }

    #[test]
    fn transported_tube_composes_exact_holonomy_and_only_changes_its_support() {
        let receiver = ReceiverId(5);
        let initial = PluralReceiverAssembly::new(
            "tube",
            vec![face(receiver)],
            vec![ReceiverStandingRelation::identity(receiver, EventId(9))],
        )
        .unwrap();
        let specification = specification();
        let topologies = BTreeMap::from([(receiver, topology(13))]);
        let source_sections = source_sections([receiver]);
        let (initial_presentation, _) =
            assemble_support_presentation_with_cpu(&initial, &crate::CpuExecutor::serial())
                .unwrap();
        let (initial_trace, _) = trace_receivers_aperture_with_cpu(
            &initial_presentation,
            &specification,
            &BTreeSet::from([receiver]),
            &crate::CpuExecutor::serial(),
        )
        .unwrap();
        let mut atlas = TerminalTubeAtlas::new();
        let plan = atlas
            .plan(
                EventId(9),
                &initial,
                &specification,
                &topologies,
                &source_sections,
                &projected_formations(EventId(9), &initial, &source_sections),
            )
            .unwrap();
        atlas.commit(plan, initial_trace).unwrap();

        let transport = RatMat3::from_i64([[1, 0, 1], [0, 1, 0], [0, 0, 1]]);
        let moved = PluralReceiverAssembly::new(
            "tube",
            vec![face(receiver)],
            vec![ReceiverStandingRelation::new(receiver, EventId(9), transport.clone()).unwrap()],
        )
        .unwrap();
        let (moved_presentation, _) =
            assemble_support_presentation_with_cpu(&moved, &crate::CpuExecutor::serial()).unwrap();
        let moved_plan = atlas
            .plan(
                EventId(10),
                &moved,
                &specification,
                &topologies,
                &source_sections,
                &projected_formations(EventId(10), &moved, &source_sections),
            )
            .unwrap();
        assert_eq!(
            moved_plan.change(receiver),
            Some(ReceiverTubeChange::Transported)
        );
        let (moved_authority, _) = trace_receivers_aperture_with_cpu(
            &moved_presentation,
            &specification,
            moved_plan.trace_receivers(),
            &crate::CpuExecutor::serial(),
        )
        .unwrap();
        let radiation = atlas.commit(moved_plan, moved_authority.clone()).unwrap();
        assert!(!radiation.support_deltas.is_empty());
        assert_eq!(atlas.traces(), moved_authority);
        assert_eq!(atlas.tubes[&receiver].presentation_holonomy(), transport);
    }

    #[test]
    fn one_changed_primitive_reuses_the_other_terminal_section() {
        let receiver = ReceiverId(6);
        let initial = PluralReceiverAssembly::new(
            "primitive-grain tube",
            vec![face_with_two_conics(receiver)],
            vec![ReceiverStandingRelation::identity(receiver, EventId(20))],
        )
        .unwrap();
        let specification = specification();
        let source_sections = source_sections([receiver]);
        let initial_topologies = BTreeMap::from([(receiver, topology(40))]);
        let (initial_presentation, _) =
            assemble_support_presentation_with_cpu(&initial, &crate::CpuExecutor::serial())
                .unwrap();
        let (initial_trace, _) = trace_receivers_aperture_with_cpu(
            &initial_presentation,
            &specification,
            &BTreeSet::from([receiver]),
            &crate::CpuExecutor::serial(),
        )
        .unwrap();
        let mut atlas = TerminalTubeAtlas::new();
        let initial_plan = atlas
            .plan(
                EventId(20),
                &initial,
                &specification,
                &initial_topologies,
                &source_sections,
                &projected_formations(EventId(20), &initial, &source_sections),
            )
            .unwrap();
        atlas.commit(initial_plan, initial_trace).unwrap();

        let mut changed_face = face_with_two_conics(receiver);
        let ReceiverPrimitive::Conic(changed) = &mut changed_face.arrangement.primitives[1] else {
            unreachable!("the second primitive is a conic")
        };
        changed.form.ww = integer(-3);
        let changed = PluralReceiverAssembly::new(
            "primitive-grain tube",
            vec![changed_face],
            vec![ReceiverStandingRelation::identity(receiver, EventId(20))],
        )
        .unwrap();
        let (changed_presentation, _) =
            assemble_support_presentation_with_cpu(&changed, &crate::CpuExecutor::serial())
                .unwrap();
        let changed_topologies = BTreeMap::from([(receiver, topology(41))]);
        let plan = atlas
            .plan(
                EventId(21),
                &changed,
                &specification,
                &changed_topologies,
                &source_sections,
                &projected_formations(EventId(21), &changed, &source_sections),
            )
            .unwrap();
        assert_eq!(plan.change(receiver), Some(ReceiverTubeChange::Deformed));
        assert_eq!(plan.trace_primitive_keys().len(), 1);
        assert_eq!(
            plan.trace_primitive_keys()
                .first()
                .expect("one primitive changed")
                .primitive,
            ReceiverPrimitiveId::NativeConic(ConicCellId(2))
        );
        let (returned_sections, _) = trace_primitives_aperture_with_cpu(
            &changed_presentation,
            &specification,
            plan.trace_primitive_keys(),
            &crate::CpuExecutor::serial(),
        )
        .unwrap();
        let returned = BTreeMap::from([(
            receiver,
            ReceiverApertureTrace::from_primitive_sections(
                receiver,
                returned_sections.into_values(),
            )
            .unwrap(),
        )]);
        let radiation = atlas.commit(plan, returned).unwrap();
        assert_eq!(radiation.receipt.traced_primitives, BigUint::one());
        assert_eq!(radiation.receipt.reused_primitives, BigUint::one());
        assert!(radiation.receipt.avoided_support_queries > BigUint::zero());

        let (authority, _) = trace_receivers_aperture_with_cpu(
            &changed_presentation,
            &specification,
            &BTreeSet::from([receiver]),
            &crate::CpuExecutor::serial(),
        )
        .unwrap();
        assert_eq!(atlas.traces(), authority);
    }

    #[test]
    fn a_changed_ray_cannot_hide_an_unproved_face_deformation() {
        let receiver = ReceiverId(8);
        let initial = PluralReceiverAssembly::new(
            "receiver transport",
            vec![face(receiver)],
            vec![ReceiverStandingRelation::identity(receiver, EventId(10))],
        )
        .unwrap();
        let specification = specification();
        let topologies = BTreeMap::from([(receiver, topology(17))]);
        let source_sections = source_sections([receiver]);
        let (initial_presentation, _) =
            assemble_support_presentation_with_cpu(&initial, &crate::CpuExecutor::serial())
                .unwrap();
        let (initial_trace, _) = trace_receivers_aperture_with_cpu(
            &initial_presentation,
            &specification,
            &BTreeSet::from([receiver]),
            &crate::CpuExecutor::serial(),
        )
        .unwrap();
        let mut atlas = TerminalTubeAtlas::new();
        let initial_formations = projected_formations(EventId(10), &initial, &source_sections);
        let plan = atlas
            .plan(
                EventId(10),
                &initial,
                &specification,
                &topologies,
                &source_sections,
                &initial_formations,
            )
            .unwrap();
        atlas.commit(plan, initial_trace).unwrap();

        let mut moved_face = face(receiver);
        moved_face.rays = crate::RayFamily::Parallel {
            face_center: RatVec3::from_i64(1, 0, 0),
            horizontal: RatVec3::from_i64(1, 0, 0),
            vertical: RatVec3::from_i64(0, 1, 0),
            direction: RatVec3::from_i64(0, 0, 1),
        };
        let ReceiverPrimitive::Conic(conic) = &mut moved_face.arrangement.primitives[0] else {
            unreachable!("the bounded tube face contains one conic")
        };
        conic.form.ww = integer(-4);
        let moved = PluralReceiverAssembly::new(
            "receiver transport",
            vec![moved_face],
            vec![ReceiverStandingRelation::identity(receiver, EventId(10))],
        )
        .unwrap();
        let error = atlas
            .plan(
                EventId(11),
                &moved,
                &specification,
                &topologies,
                &source_sections,
                &initial_formations,
            )
            .unwrap_err();
        assert_eq!(error, TerminalTubeError::FormationReceiptMismatch(receiver));
    }

    #[test]
    fn identical_presented_sections_share_one_exact_terminal_restriction() {
        let left = ReceiverId(21);
        let right = ReceiverId(22);
        let assembly = PluralReceiverAssembly::new(
            "shared exterior face",
            vec![face(left), face(right)],
            vec![
                ReceiverStandingRelation::identity(left, EventId(12)),
                ReceiverStandingRelation::identity(right, EventId(12)),
            ],
        )
        .unwrap();
        let (presentation, _) =
            assemble_support_presentation_with_cpu(&assembly, &crate::CpuExecutor::serial())
                .unwrap();
        let topologies = BTreeMap::from([(left, topology(31)), (right, topology(32))]);
        let source_sections = source_sections([left, right]);
        let specification = specification();
        let mut atlas = TerminalTubeAtlas::new();
        let plan = atlas
            .plan(
                EventId(12),
                &assembly,
                &specification,
                &topologies,
                &source_sections,
                &projected_formations(EventId(12), &assembly, &source_sections),
            )
            .unwrap();
        assert_eq!(plan.trace_receivers().len(), 1);
        assert_eq!(plan.trace_source(left), plan.trace_source(right));
        let (representative, _) = trace_receivers_aperture_with_cpu(
            &presentation,
            &specification,
            plan.trace_receivers(),
            &crate::CpuExecutor::serial(),
        )
        .unwrap();
        let radiation = atlas.commit(plan, representative).unwrap();
        assert_eq!(radiation.receipt.traced_receivers, BigUint::one());
        assert_eq!(radiation.receipt.shared_trace_receivers, BigUint::one());

        let (authority, _) = trace_receivers_aperture_with_cpu(
            &presentation,
            &specification,
            &BTreeSet::from([left, right]),
            &crate::CpuExecutor::serial(),
        )
        .unwrap();
        assert_eq!(atlas.traces(), authority);
    }

    #[test]
    fn empty_receiver_section_remains_a_live_exact_tube() {
        let receiver = ReceiverId(34);
        let mut empty_face = face(receiver);
        empty_face.arrangement.primitives.clear();
        let assembly = PluralReceiverAssembly::new(
            "empty section",
            vec![empty_face],
            vec![ReceiverStandingRelation::identity(receiver, EventId(15))],
        )
        .unwrap();
        let (presentation, _) =
            assemble_support_presentation_with_cpu(&assembly, &crate::CpuExecutor::serial())
                .unwrap();
        assert!(presentation.primitives.is_empty());
        let topologies = BTreeMap::from([(receiver, topology(35))]);
        let source_sections = source_sections([receiver]);
        let specification = specification();
        let mut atlas = TerminalTubeAtlas::new();
        let plan = atlas
            .plan(
                EventId(15),
                &assembly,
                &specification,
                &topologies,
                &source_sections,
                &projected_formations(EventId(15), &assembly, &source_sections),
            )
            .unwrap();
        let (trace, _) = trace_receivers_aperture_with_cpu(
            &presentation,
            &specification,
            plan.trace_receivers(),
            &crate::CpuExecutor::serial(),
        )
        .unwrap();
        atlas.commit(plan, trace).unwrap();
        assert!(atlas.tubes.contains_key(&receiver));
        assert!(
            atlas.tubes[&receiver]
                .terminal_trace
                .primitive_traces
                .is_zero()
        );
    }
}
