//! Joint, receiver-decorated causal paths.
//!
//! A source path and a receiver diagram are not interchangeable.  This
//! module keeps the ordered source incidence as the lawful path carrier while
//! allowing a co-present receiver family to decorate that path with exact
//! projected intervals, apparent crossings, and local turn quotients.
//!
//! An apparent crossing never creates source adjacency.  Its two branch
//! parameters merely refine the common path grain.  A later evaluation law
//! may compose the retained decorations, but the carrier itself is not a
//! scalar weighted graph.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact::{Rat, RatVec2, RatVec3};
use crate::model::{Construction, EntityId, FrameId, Geometry};
use crate::projection::{ProjectionError, Receiver, ReceiverId, project_point, receiver_metric};
use crate::receiver_topology::{
    DiagramNodeKind, ReceiverTopology, ReceiverTopologyError, SourceSegment, SourceSegmentAddress,
    SourceVertexId, analyze_receiver_topology,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SourceDartId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DecoratedTransitionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SourceDartAddress {
    pub segment: SourceSegmentAddress,
    pub forward: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CrossingRole {
    Over,
    Under,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverCrossingMark {
    /// Parameter on this source branch, not on its projected screen chord.
    pub source_parameter: Rat,
    pub screen_point: RatVec2,
    pub other_branch: SourceSegmentAddress,
    pub role: CrossingRole,
    /// Orientation of the receiver's ordered over/under pair.
    pub crossing_orientation: i8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverIntervalFace {
    /// These parameters follow the dart.  A reverse dart therefore carries a
    /// descending interval without destroying the canonical source values.
    pub source_start: Rat,
    pub source_end: Rat,
    pub screen_start: RatVec2,
    pub screen_end: RatVec2,
    pub screen_chord_squared: Rat,
    pub gauge_chord_squared: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverDartFace {
    pub receiver: ReceiverId,
    pub receiver_name: String,
    pub screen_origin: RatVec2,
    pub screen_target: RatVec2,
    pub screen_chord_squared: Rat,
    pub gauge_chord_squared: Rat,
    /// Every receiver uses the union of cuts founded by the co-present family.
    pub intervals: Vec<ReceiverIntervalFace>,
    /// Only crossings actually visible to this receiver appear here.
    pub crossings: Vec<ReceiverCrossingMark>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JointCausalDart {
    pub id: SourceDartId,
    pub address: SourceDartAddress,
    pub origin: SourceVertexId,
    pub target: SourceVertexId,
    pub source_frame: FrameId,
    pub source_chord_squared: Rat,
    /// Ordered canonical source parameters, including zero and one.
    pub ordered_source_cuts: Vec<Rat>,
    pub receiver_faces: Vec<ReceiverDartFace>,
}

/// Exact quotient between two nonzero oriented receiver chords.
///
/// If chords are read as Gaussian-rational directions, this is
/// `outgoing / incoming`.  It retains both the dot and oriented-area faces of
/// the turn and therefore does not collapse the turn to an angle scalar.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactTurn {
    pub parallel: Rat,
    pub transverse: Rat,
}

impl ExactTurn {
    pub fn one() -> Self {
        Self {
            parallel: Rat::one(),
            transverse: Rat::zero(),
        }
    }

    pub fn between(incoming: &RatVec2, outgoing: &RatVec2) -> Option<Self> {
        let denominator = incoming.norm_squared();
        if denominator.is_zero() {
            return None;
        }
        Some(Self {
            parallel: incoming.dot(outgoing) / &denominator,
            transverse: incoming.cross(outgoing) / denominator,
        })
    }

    pub fn multiply(&self, other: &Self) -> Self {
        Self {
            parallel: &self.parallel * &other.parallel - &self.transverse * &other.transverse,
            transverse: &self.parallel * &other.transverse + &self.transverse * &other.parallel,
        }
    }
}

impl fmt::Display for ExactTurn {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "({},{})",
            crate::exact::format_rat(&self.parallel),
            crate::exact::format_rat(&self.transverse)
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverTransitionFace {
    pub receiver: ReceiverId,
    pub receiver_name: String,
    pub turn: ExactTurn,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecoratedTransition {
    pub id: DecoratedTransitionId,
    pub incoming: SourceDartId,
    pub outgoing: SourceDartId,
    /// This is always an actual source incidence.  Receiver crossings cannot
    /// populate this field.
    pub through: SourceVertexId,
    pub receiver_faces: Vec<ReceiverTransitionFace>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverClosedTrace {
    pub receiver: ReceiverId,
    pub receiver_name: String,
    pub projected_chord_word: Vec<Rat>,
    pub interval_chord_word: Vec<Vec<Rat>>,
    pub crossing_word: Vec<Vec<ReceiverCrossingMark>>,
    pub local_turn_word: Vec<ExactTurn>,
    /// Product of the local turn word in traversal order.
    pub closed_return: ExactTurn,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecoratedPrimitiveTrace {
    /// A cyclically canonical source word. Reverse orientation remains
    /// distinct because causal parity is not discarded.
    pub source_word: Vec<SourceDartAddress>,
    pub source_chord_word: Vec<Rat>,
    pub receiver_traces: Vec<ReceiverClosedTrace>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JointDecoratedPathOperator {
    pub schema: String,
    pub receivers: Vec<(ReceiverId, String)>,
    pub source_segments: Vec<SourceSegment>,
    pub darts: Vec<JointCausalDart>,
    pub transitions: Vec<DecoratedTransition>,
    pub primitive_traces: Vec<DecoratedPrimitiveTrace>,
}

impl JointDecoratedPathOperator {
    pub fn dart(&self, id: SourceDartId) -> &JointCausalDart {
        &self.darts[id.0 as usize - 1]
    }

    pub fn transition(
        &self,
        incoming: SourceDartId,
        outgoing: SourceDartId,
    ) -> Option<&DecoratedTransition> {
        self.transitions
            .iter()
            .find(|row| row.incoming == incoming && row.outgoing == outgoing)
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum DecoratedPathError {
    #[error(transparent)]
    Topology(#[from] ReceiverTopologyError),
    #[error(transparent)]
    Projection(#[from] ProjectionError),
    #[error("a joint decorated path requires at least one receiver")]
    NoReceivers,
    #[error("receiver {0:?} occurs more than once")]
    DuplicateReceiver(ReceiverId),
    #[error("receiver topology {0:?} does not preserve the common source incidence")]
    InconsistentSourceIncidence(ReceiverId),
    #[error("source entity {0} is absent")]
    MissingEntity(EntityId),
    #[error("source entity {0} is not a thread")]
    NotAThread(EntityId),
    #[error("source segment {0:?} is absent")]
    MissingSegment(SourceSegmentAddress),
    #[error("source frame {0} is absent")]
    MissingFrame(FrameId),
    #[error("receiver {receiver:?} does not expose an exact rational face")]
    NonRationalReceiverFace { receiver: ReceiverId },
    #[error("receiver {receiver:?} collapses source dart {segment:?}")]
    ZeroReceiverDart {
        receiver: ReceiverId,
        segment: SourceSegmentAddress,
    },
    #[error("a closed trace failed its exact receiver return for {receiver:?}")]
    OpenReceiverReturn { receiver: ReceiverId },
}

pub fn build_joint_decorated_path_operator(
    construction: &Construction,
    receivers: &[Receiver],
    primitive_horizon: usize,
) -> Result<JointDecoratedPathOperator, DecoratedPathError> {
    if receivers.is_empty() {
        return Err(DecoratedPathError::NoReceivers);
    }
    let mut receiver_ids = BTreeSet::new();
    for receiver in receivers {
        if !receiver_ids.insert(receiver.id) {
            return Err(DecoratedPathError::DuplicateReceiver(receiver.id));
        }
    }

    let topologies = receivers
        .iter()
        .map(|receiver| analyze_receiver_topology(construction, receiver, primitive_horizon))
        .collect::<Result<Vec<_>, _>>()?;
    let source_segments = topologies[0].source_segments.clone();
    for topology in topologies.iter().skip(1) {
        if topology.source_segments != source_segments {
            return Err(DecoratedPathError::InconsistentSourceIncidence(
                topology.receiver,
            ));
        }
    }

    let crossing_marks = collect_crossing_marks(&topologies);
    let mut joint_cuts = source_segments
        .iter()
        .map(|segment| (segment.address, BTreeSet::from([Rat::zero(), Rat::one()])))
        .collect::<BTreeMap<_, _>>();
    for ((segment, _receiver), marks) in &crossing_marks {
        let cuts = joint_cuts
            .get_mut(segment)
            .expect("a topology crossing belongs to a source segment");
        cuts.extend(marks.iter().map(|mark| mark.source_parameter.clone()));
    }

    let mut darts = Vec::with_capacity(2 * source_segments.len());
    for segment in &source_segments {
        let (frame, source_start, source_end) =
            source_segment_geometry(construction, segment.address)?;
        let source_delta = source_end.subtract(&source_start);
        let source_frame = construction
            .frames
            .get(&frame)
            .ok_or(DecoratedPathError::MissingFrame(frame))?;
        let source_chord_squared = source_frame
            .chart
            .gram()
            .bilinear(&source_delta, &source_delta);
        let canonical_cuts = joint_cuts[&segment.address]
            .iter()
            .cloned()
            .collect::<Vec<_>>();

        let forward_id = SourceDartId(darts.len() as u64 + 1);
        let forward_faces = receivers
            .iter()
            .map(|receiver| {
                build_receiver_dart_face(
                    construction,
                    receiver,
                    segment.address,
                    frame,
                    &source_start,
                    &source_end,
                    &canonical_cuts,
                    crossing_marks
                        .get(&(segment.address, receiver.id))
                        .map(Vec::as_slice)
                        .unwrap_or(&[]),
                    true,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        darts.push(JointCausalDart {
            id: forward_id,
            address: SourceDartAddress {
                segment: segment.address,
                forward: true,
            },
            origin: segment.from,
            target: segment.to,
            source_frame: frame,
            source_chord_squared: source_chord_squared.clone(),
            ordered_source_cuts: canonical_cuts.clone(),
            receiver_faces: forward_faces,
        });

        let reverse_id = SourceDartId(darts.len() as u64 + 1);
        let reverse_faces = receivers
            .iter()
            .map(|receiver| {
                build_receiver_dart_face(
                    construction,
                    receiver,
                    segment.address,
                    frame,
                    &source_start,
                    &source_end,
                    &canonical_cuts,
                    crossing_marks
                        .get(&(segment.address, receiver.id))
                        .map(Vec::as_slice)
                        .unwrap_or(&[]),
                    false,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        darts.push(JointCausalDart {
            id: reverse_id,
            address: SourceDartAddress {
                segment: segment.address,
                forward: false,
            },
            origin: segment.to,
            target: segment.from,
            source_frame: frame,
            source_chord_squared,
            ordered_source_cuts: canonical_cuts.into_iter().rev().collect(),
            receiver_faces: reverse_faces,
        });
    }

    let transitions = build_transitions(&darts)?;
    let primitive_words = enumerate_primitive_words(&darts, &transitions, primitive_horizon);
    let primitive_traces = primitive_words
        .iter()
        .map(|word| form_trace(word, &darts, &transitions))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(JointDecoratedPathOperator {
        schema: "relational-geometry.joint-decorated-path.v1".to_owned(),
        receivers: receivers
            .iter()
            .map(|receiver| (receiver.id, receiver.name.clone()))
            .collect(),
        source_segments,
        darts,
        transitions,
        primitive_traces,
    })
}

fn collect_crossing_marks(
    topologies: &[ReceiverTopology],
) -> BTreeMap<(SourceSegmentAddress, ReceiverId), Vec<ReceiverCrossingMark>> {
    let mut marks = BTreeMap::<_, Vec<_>>::new();
    for topology in topologies {
        for node in &topology.nodes {
            let DiagramNodeKind::ApparentCrossing {
                first,
                second,
                over,
                orientation,
                first_source_parameter,
                second_source_parameter,
            } = &node.kind
            else {
                continue;
            };
            marks
                .entry((*first, topology.receiver))
                .or_default()
                .push(ReceiverCrossingMark {
                    source_parameter: first_source_parameter.clone(),
                    screen_point: node.point.clone(),
                    other_branch: *second,
                    role: if over == first {
                        CrossingRole::Over
                    } else {
                        CrossingRole::Under
                    },
                    crossing_orientation: *orientation,
                });
            marks
                .entry((*second, topology.receiver))
                .or_default()
                .push(ReceiverCrossingMark {
                    source_parameter: second_source_parameter.clone(),
                    screen_point: node.point.clone(),
                    other_branch: *first,
                    role: if over == second {
                        CrossingRole::Over
                    } else {
                        CrossingRole::Under
                    },
                    crossing_orientation: *orientation,
                });
        }
    }
    for rows in marks.values_mut() {
        rows.sort_by(|left, right| {
            left.source_parameter
                .cmp(&right.source_parameter)
                .then_with(|| left.other_branch.cmp(&right.other_branch))
        });
    }
    marks
}

fn source_segment_geometry(
    construction: &Construction,
    address: SourceSegmentAddress,
) -> Result<(FrameId, RatVec3, RatVec3), DecoratedPathError> {
    let entity = construction
        .entities
        .get(&address.entity)
        .ok_or(DecoratedPathError::MissingEntity(address.entity))?;
    let Geometry::Thread { vertices, closed } = &entity.geometry else {
        return Err(DecoratedPathError::NotAThread(address.entity));
    };
    let segment_count = if *closed {
        vertices.len()
    } else {
        vertices.len().saturating_sub(1)
    };
    if address.segment >= segment_count {
        return Err(DecoratedPathError::MissingSegment(address));
    }
    let next = (address.segment + 1) % vertices.len();
    Ok((
        entity.frame,
        vertices[address.segment].clone(),
        vertices[next].clone(),
    ))
}

#[allow(clippy::too_many_arguments)]
fn build_receiver_dart_face(
    construction: &Construction,
    receiver: &Receiver,
    segment: SourceSegmentAddress,
    frame: FrameId,
    source_start: &RatVec3,
    source_end: &RatVec3,
    canonical_cuts: &[Rat],
    canonical_crossings: &[ReceiverCrossingMark],
    forward: bool,
) -> Result<ReceiverDartFace, DecoratedPathError> {
    let source_delta = source_end.subtract(source_start);
    let mut samples = BTreeMap::new();
    for parameter in canonical_cuts {
        let source_point = source_start.add(&source_delta.scale(parameter));
        let projected = project_point(construction, frame, &source_point, receiver)?;
        let screen = projected
            .rational
            .ok_or(DecoratedPathError::NonRationalReceiverFace {
                receiver: receiver.id,
            })?;
        samples.insert(parameter.clone(), screen);
    }
    let gauge_squared = receiver_metric(receiver)?.reference_squared;
    let ordered_cuts = if forward {
        canonical_cuts.to_vec()
    } else {
        canonical_cuts.iter().rev().cloned().collect()
    };
    let intervals = ordered_cuts
        .windows(2)
        .map(|pair| {
            let screen_start = samples[&pair[0]].clone();
            let screen_end = samples[&pair[1]].clone();
            let chord_squared = screen_end.subtract(&screen_start).norm_squared();
            ReceiverIntervalFace {
                source_start: pair[0].clone(),
                source_end: pair[1].clone(),
                screen_start,
                screen_end,
                gauge_chord_squared: &chord_squared / &gauge_squared,
                screen_chord_squared: chord_squared,
            }
        })
        .collect::<Vec<_>>();
    let screen_origin = samples[ordered_cuts.first().expect("zero and one are present")].clone();
    let screen_target = samples[ordered_cuts.last().expect("zero and one are present")].clone();
    let screen_chord_squared = screen_target.subtract(&screen_origin).norm_squared();
    if screen_chord_squared.is_zero() {
        return Err(DecoratedPathError::ZeroReceiverDart {
            receiver: receiver.id,
            segment,
        });
    }
    let mut crossings = canonical_crossings.to_vec();
    if !forward {
        crossings.reverse();
    }
    Ok(ReceiverDartFace {
        receiver: receiver.id,
        receiver_name: receiver.name.clone(),
        screen_origin,
        screen_target,
        gauge_chord_squared: &screen_chord_squared / gauge_squared,
        screen_chord_squared,
        intervals,
        crossings,
    })
}

fn reverse_dart(id: SourceDartId) -> SourceDartId {
    if id.0 % 2 == 1 {
        SourceDartId(id.0 + 1)
    } else {
        SourceDartId(id.0 - 1)
    }
}

fn build_transitions(
    darts: &[JointCausalDart],
) -> Result<Vec<DecoratedTransition>, DecoratedPathError> {
    let mut transitions = Vec::new();
    for incoming in darts {
        for outgoing in darts {
            if incoming.target != outgoing.origin || outgoing.id == reverse_dart(incoming.id) {
                continue;
            }
            let receiver_faces = incoming
                .receiver_faces
                .iter()
                .zip(&outgoing.receiver_faces)
                .map(|(incoming_face, outgoing_face)| {
                    debug_assert_eq!(incoming_face.receiver, outgoing_face.receiver);
                    let incoming_direction = incoming_face
                        .screen_target
                        .subtract(&incoming_face.screen_origin);
                    let outgoing_direction = outgoing_face
                        .screen_target
                        .subtract(&outgoing_face.screen_origin);
                    let turn = ExactTurn::between(&incoming_direction, &outgoing_direction).ok_or(
                        DecoratedPathError::ZeroReceiverDart {
                            receiver: incoming_face.receiver,
                            segment: incoming.address.segment,
                        },
                    )?;
                    Ok(ReceiverTransitionFace {
                        receiver: incoming_face.receiver,
                        receiver_name: incoming_face.receiver_name.clone(),
                        turn,
                    })
                })
                .collect::<Result<Vec<_>, DecoratedPathError>>()?;
            transitions.push(DecoratedTransition {
                id: DecoratedTransitionId(transitions.len() as u64 + 1),
                incoming: incoming.id,
                outgoing: outgoing.id,
                through: incoming.target,
                receiver_faces,
            });
        }
    }
    Ok(transitions)
}

fn enumerate_primitive_words(
    darts: &[JointCausalDart],
    transitions: &[DecoratedTransition],
    horizon: usize,
) -> Vec<Vec<SourceDartId>> {
    let mut continuations = BTreeMap::<SourceDartId, Vec<SourceDartId>>::new();
    let transition_pairs = transitions
        .iter()
        .map(|row| ((row.incoming, row.outgoing), row.id))
        .collect::<BTreeMap<_, _>>();
    for transition in transitions {
        continuations
            .entry(transition.incoming)
            .or_default()
            .push(transition.outgoing);
    }
    let mut words = BTreeSet::new();
    for length in 2..=horizon {
        for start in darts {
            let mut path = vec![start.id];
            extend_words(
                length,
                start.id,
                &mut path,
                &continuations,
                &transition_pairs,
                &mut words,
            );
        }
    }
    words.into_iter().collect()
}

fn extend_words(
    target_length: usize,
    start: SourceDartId,
    path: &mut Vec<SourceDartId>,
    continuations: &BTreeMap<SourceDartId, Vec<SourceDartId>>,
    transition_pairs: &BTreeMap<(SourceDartId, SourceDartId), DecoratedTransitionId>,
    words: &mut BTreeSet<Vec<SourceDartId>>,
) {
    if path.len() == target_length {
        let last = *path.last().expect("a path has its start");
        if transition_pairs.contains_key(&(last, start)) {
            let canonical = canonical_rotation(path);
            if primitive_cyclic_word(&canonical) {
                words.insert(canonical);
            }
        }
        return;
    }
    let last = *path.last().expect("a path has its start");
    if let Some(next_rows) = continuations.get(&last) {
        for next in next_rows {
            path.push(*next);
            extend_words(
                target_length,
                start,
                path,
                continuations,
                transition_pairs,
                words,
            );
            path.pop();
        }
    }
}

fn canonical_rotation(word: &[SourceDartId]) -> Vec<SourceDartId> {
    (0..word.len())
        .map(|offset| {
            word[offset..]
                .iter()
                .chain(&word[..offset])
                .copied()
                .collect::<Vec<_>>()
        })
        .min()
        .expect("a closed word is nonempty")
}

fn primitive_cyclic_word(word: &[SourceDartId]) -> bool {
    for period in 1..word.len() {
        if word.len() % period == 0
            && (0..word.len()).all(|index| word[index] == word[index % period])
        {
            return false;
        }
    }
    true
}

fn form_trace(
    word: &[SourceDartId],
    darts: &[JointCausalDart],
    transitions: &[DecoratedTransition],
) -> Result<DecoratedPrimitiveTrace, DecoratedPathError> {
    let transition_lookup = transitions
        .iter()
        .map(|row| ((row.incoming, row.outgoing), row))
        .collect::<BTreeMap<_, _>>();
    let path_darts = word
        .iter()
        .map(|id| &darts[id.0 as usize - 1])
        .collect::<Vec<_>>();
    let path_transitions = (0..word.len())
        .map(|index| {
            let next = (index + 1) % word.len();
            transition_lookup[&(word[index], word[next])]
        })
        .collect::<Vec<_>>();

    let receiver_count = path_darts[0].receiver_faces.len();
    let mut receiver_traces = Vec::with_capacity(receiver_count);
    for receiver_index in 0..receiver_count {
        let first_face = &path_darts[0].receiver_faces[receiver_index];
        let local_turn_word = path_transitions
            .iter()
            .map(|transition| transition.receiver_faces[receiver_index].turn.clone())
            .collect::<Vec<_>>();
        let closed_return = local_turn_word
            .iter()
            .fold(ExactTurn::one(), |product, turn| product.multiply(turn));
        if closed_return != ExactTurn::one() {
            return Err(DecoratedPathError::OpenReceiverReturn {
                receiver: first_face.receiver,
            });
        }
        receiver_traces.push(ReceiverClosedTrace {
            receiver: first_face.receiver,
            receiver_name: first_face.receiver_name.clone(),
            projected_chord_word: path_darts
                .iter()
                .map(|dart| {
                    dart.receiver_faces[receiver_index]
                        .gauge_chord_squared
                        .clone()
                })
                .collect(),
            interval_chord_word: path_darts
                .iter()
                .map(|dart| {
                    dart.receiver_faces[receiver_index]
                        .intervals
                        .iter()
                        .map(|interval| interval.gauge_chord_squared.clone())
                        .collect()
                })
                .collect(),
            crossing_word: path_darts
                .iter()
                .map(|dart| dart.receiver_faces[receiver_index].crossings.clone())
                .collect(),
            local_turn_word,
            closed_return,
        });
    }

    Ok(DecoratedPrimitiveTrace {
        source_word: path_darts.iter().map(|dart| dart.address).collect(),
        source_chord_word: path_darts
            .iter()
            .map(|dart| dart.source_chord_squared.clone())
            .collect(),
        receiver_traces,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact::{integer, rat};
    use crate::model::ConstraintKind;
    use crate::projection::{ProjectionLaw, ReceiverOrientation};
    use crate::receiver_topology::SourceEndpoint;

    const EDGE_VERTICES: [(usize, usize); 6] = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];

    fn tetrahedron(height: Rat) -> Construction {
        let points = [
            RatVec3::from_i64(0, 0, 0),
            RatVec3::from_i64(4, 0, 0),
            RatVec3::from_i64(0, 4, 0),
            RatVec3::new(integer(1), integer(1), height),
        ];
        let (mut construction, frame) = Construction::new("source");
        let entities = EDGE_VERTICES
            .iter()
            .map(|(left, right)| {
                construction
                    .add_entity(
                        "edge",
                        frame,
                        Geometry::Thread {
                            vertices: vec![points[*left].clone(), points[*right].clone()],
                            closed: false,
                        },
                    )
                    .unwrap()
            })
            .collect::<Vec<_>>();
        for vertex in 0..4 {
            let members = EDGE_VERTICES
                .iter()
                .enumerate()
                .filter_map(|(index, (left, right))| {
                    if *left == vertex {
                        Some(SourceEndpoint {
                            entity: entities[index],
                            vertex: 0,
                        })
                    } else if *right == vertex {
                        Some(SourceEndpoint {
                            entity: entities[index],
                            vertex: 1,
                        })
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            for pair in members.windows(2) {
                construction.add_constraint(
                    "shared source incidence",
                    ConstraintKind::SharedVertex {
                        left: pair[0].entity,
                        right: pair[1].entity,
                        left_vertex: pair[0].vertex,
                        right_vertex: pair[1].vertex,
                    },
                );
            }
        }
        construction
    }

    fn receivers() -> [Receiver; 2] {
        let mut precessed = Receiver::new(
            ReceiverId(2),
            "precessed",
            FrameId(1),
            ProjectionLaw::Orthographic,
        );
        precessed.orientation =
            ReceiverOrientation::from_cayley_xyz(rat(-1, 2), rat(-1, 2), Rat::zero());
        [
            Receiver::new(
                ReceiverId(1),
                "direct",
                FrameId(1),
                ProjectionLaw::Orthographic,
            ),
            precessed,
        ]
    }

    #[test]
    fn every_receiver_turn_word_returns_exactly() {
        let operator =
            build_joint_decorated_path_operator(&tetrahedron(integer(1)), &receivers(), 4).unwrap();
        assert!(!operator.primitive_traces.is_empty());
        assert!(operator.primitive_traces.iter().all(|trace| {
            trace
                .receiver_traces
                .iter()
                .all(|receiver| receiver.closed_return == ExactTurn::one())
        }));
    }

    #[test]
    fn a_receiver_crossing_refines_the_joint_grain_without_founding_source_adjacency() {
        let operator =
            build_joint_decorated_path_operator(&tetrahedron(integer(1)), &receivers(), 4).unwrap();
        let ac = SourceSegmentAddress {
            entity: EntityId(2),
            segment: 0,
        };
        let bd = SourceSegmentAddress {
            entity: EntityId(5),
            segment: 0,
        };
        for segment in [ac, bd] {
            let dart = operator
                .darts
                .iter()
                .find(|dart| dart.address.segment == segment && dart.address.forward)
                .unwrap();
            assert_eq!(dart.receiver_faces[0].crossings.len(), 0);
            assert_eq!(dart.receiver_faces[0].intervals.len(), 2);
            assert_eq!(dart.receiver_faces[1].crossings.len(), 1);
            assert_eq!(dart.receiver_faces[1].intervals.len(), 2);
        }
        assert!(operator.transitions.iter().all(|transition| {
            let incoming = operator.dart(transition.incoming).address.segment;
            let outgoing = operator.dart(transition.outgoing).address.segment;
            !((incoming == ac && outgoing == bd) || (incoming == bd && outgoing == ac))
        }));
    }

    #[test]
    fn source_words_persist_while_receiver_and_metric_decorations_change() {
        let before =
            build_joint_decorated_path_operator(&tetrahedron(integer(1)), &receivers(), 4).unwrap();
        let after =
            build_joint_decorated_path_operator(&tetrahedron(rat(1, 4)), &receivers(), 4).unwrap();
        let before_words = before
            .primitive_traces
            .iter()
            .map(|trace| trace.source_word.clone())
            .collect::<Vec<_>>();
        let after_words = after
            .primitive_traces
            .iter()
            .map(|trace| trace.source_word.clone())
            .collect::<Vec<_>>();
        assert_eq!(before_words, after_words);
        assert_ne!(before.primitive_traces, after.primitive_traces);
        assert!(
            before
                .darts
                .iter()
                .any(|dart| !dart.receiver_faces[1].crossings.is_empty())
        );
        assert!(
            after
                .darts
                .iter()
                .all(|dart| dart.receiver_faces[1].crossings.is_empty())
        );
    }
}
