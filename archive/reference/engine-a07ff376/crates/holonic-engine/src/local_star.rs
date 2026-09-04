//! Exact event-local physics on an oriented simplicial complex.
//!
//! The operative unit is not a scalar cell.  It is the contemporary local
//! star of a hinge: its two cofaces, neighboring hinges, stored trajectory,
//! oriented current, shared vertices, attached receiver bodies, and any
//! boundary deed which actually arrives during this event.  Each active star
//! is solved against the same immutable predecessor.  Disjoint solves may be
//! realized on different CPU cores; their canonically ordered merge is one
//! atomic successor.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::{
    ExactSpin, FrameId, ProjectionLaw, ProjectiveRatio, Rat, RatVec3, Receiver, ReceiverId,
    ReceiverOrientation, ReceiverRotationAxis, integer,
};
use serde::{Deserialize, Deserializer, Serialize};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use thiserror::Error;

use crate::{
    ActionBalanceReceipt, CpuExecutionError, CpuExecutionReceipt, CpuExecutor, Edge, EventId,
    EventSuccessor, ExactEventLaw, FaceId, HingeId, HingeRadiation, HingeTrajectory,
    HingeTransportId, HingeWorldError, HingeWorldLaw, HingeWorldStanding, QuadraticHingeAction,
    RayFamily, ReceiverAcceptanceCover, ReceiverAcceptanceOrgan, ReceiverAcceptanceSeam,
    ReceiverFaceExtent, ReceiverFaceSpec, ReceiverPortSection, SimplicialError,
    SimplicialFlipReceipt, VertexId, VertexLinkClass, VertexStarLink,
};

/// One exact, oriented current transfer across one local incidence.
///
/// A complete event may cross many causally ordered incidences. Every
/// co-present current at one causal layer is solved against the same
/// predecessor and may be physically realized in parallel. Coefficients are
/// source-world constitutive data. Their signed sum need not be one: the
/// remainder is deposited in the source star.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalCurrentTransport {
    pub id: u64,
    pub source: HingeId,
    pub target: HingeId,
    /// `1` admits current in the source's positive hand, `-1` admits its
    /// negative hand, and `0` admits both. Hand is a local orientation, not
    /// a good/bad sign.
    pub hand: i8,
    pub coefficient: Rat,
}

impl LocalCurrentTransport {
    pub fn new(source: HingeId, target: HingeId, coefficient: Rat) -> Self {
        Self::with_hand(source, target, 0, coefficient)
    }

    pub fn with_hand(source: HingeId, target: HingeId, hand: i8, coefficient: Rat) -> Self {
        Self {
            id: 0,
            source,
            target,
            hand,
            coefficient,
        }
    }
}

/// Canonical contemporary current incidence.
///
/// The ordered carrier is a physical realization of source incidence, not a causal lookup table.
/// Its private representation guarantees that every source star occupies one contiguous range,
/// so an arriving current traverses only the transports emanating from its hinge. Serde retains
/// the historical transparent array face and canonicalizes storage order on remount.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(transparent)]
pub struct LocalCurrentIncidence {
    ordered: Vec<LocalCurrentTransport>,
}

impl LocalCurrentIncidence {
    fn canonical(mut ordered: Vec<LocalCurrentTransport>) -> Self {
        ordered.sort_by_key(|transport| (transport.source, transport.target, transport.id));
        Self { ordered }
    }

    pub fn transports(&self) -> &[LocalCurrentTransport] {
        &self.ordered
    }

    fn outgoing(&self, source: HingeId) -> &[LocalCurrentTransport] {
        fn boundary(transports: &[LocalCurrentTransport], source: HingeId, upper: bool) -> usize {
            let mut left = 0usize;
            let mut right = transports.len();
            while left < right {
                let middle = left + (right - left) / 2;
                let candidate = transports[middle].source;
                let passes = if upper {
                    candidate <= source
                } else {
                    candidate < source
                };
                if passes {
                    left = middle + 1;
                } else {
                    right = middle;
                }
            }
            left
        }

        let start = boundary(&self.ordered, source, false);
        let end = boundary(&self.ordered, source, true);
        &self.ordered[start..end]
    }

    fn retain(&mut self, mut keep: impl FnMut(&LocalCurrentTransport) -> bool) {
        self.ordered.retain(|transport| keep(transport));
    }
}

impl<'de> Deserialize<'de> for LocalCurrentIncidence {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Vec::<LocalCurrentTransport>::deserialize(deserializer).map(Self::canonical)
    }
}

/// The world occurrence which opened one exact current constituent.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum LocalCurrentRoot {
    Source {
        event: EventId,
        hinge: HingeId,
    },
    Receiver {
        event: EventId,
        receiver: ReceiverId,
    },
}

/// One local incidence crossed by a physical current constituent.
///
/// This word is distinct from `HingeTransitionWord`: it records physical
/// current transport, not projective coordinate transport.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LocalCurrentStep {
    pub transport: u64,
    pub source: HingeId,
    pub target: HingeId,
}

/// One causally distinct current arrival.
///
/// Equal amounts at the same hinge remain plural when they have different
/// roots or words. The local solve may sum their amounts as a derived impulse;
/// it may not replace this population with that sum.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalCurrentConstituent {
    pub root: LocalCurrentRoot,
    pub hinge: HingeId,
    pub amount: Rat,
    pub word: Vec<LocalCurrentStep>,
}

impl LocalCurrentConstituent {
    fn crossed(&self, transport: &LocalCurrentTransport) -> Self {
        let mut word = self.word.clone();
        word.push(LocalCurrentStep {
            transport: transport.id,
            source: transport.source,
            target: transport.target,
        });
        Self {
            root: self.root,
            hinge: transport.target,
            amount: &transport.coefficient * &self.amount,
            word,
        }
    }
}

fn sort_current_constituents(currents: &mut [LocalCurrentConstituent]) {
    currents.sort_by(|left, right| {
        (left.hinge, left.root, left.word.as_slice(), &left.amount).cmp(&(
            right.hinge,
            right.root,
            right.word.as_slice(),
            &right.amount,
        ))
    });
}

fn current_frontier(currents: &[LocalCurrentConstituent]) -> BTreeMap<HingeId, Rat> {
    let mut frontier = BTreeMap::<HingeId, Rat>::new();
    for current in currents {
        *frontier.entry(current.hinge).or_insert_with(Rat::zero) += &current.amount;
    }
    frontier.retain(|_, current| !current.is_zero());
    frontier
}

/// Complete constituent-level testimony for one arrival at one causal layer.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalCurrentPathReceipt {
    pub entered: LocalCurrentConstituent,
    pub deposited: Rat,
    pub emitted: Vec<LocalCurrentConstituent>,
    pub departed: Rat,
    pub exact_residual: Rat,
}

/// Constitutive response of one hinge-local star.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalStarMaterial {
    pub action: QuadraticHingeAction,
    /// Previous coface stress contributes this exact proportion of impulse.
    pub stress_response: Rat,
    /// An exact response direction in the bounded local chart.  The lower
    /// endpoint moves against it and the upper endpoint with it.
    pub geometry_response: RatVec3,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VertexFieldState {
    /// A receiver-derived representative in one connected component's local
    /// chart. This value is never stored as physical standing.
    pub previous_position: RatVec3,
    pub position: RatVec3,
    pub capacity: Rat,
}

/// One oriented relative spatial carrier.
///
/// `Edge` is canonically oriented from `lower` to `upper`, so `vector` is
/// always `x_upper - x_lower`. No absolute point or external origin is
/// physical standing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalEdgeState {
    pub previous_vector: RatVec3,
    pub vector: RatVec3,
}

/// The exact failure of one carried chord to agree with the component's
/// deterministic spanning-tree realization.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalChordResidual {
    pub edge: Edge,
    pub carried_vector: RatVec3,
    pub realized_vector: RatVec3,
    pub residual: RatVec3,
}

/// Translation-free spatial standing.
///
/// Each connected component has its own canonical root and therefore no
/// invented relation to another component. Point coordinates are reconstructed
/// only when a receiver asks for a representative. Face and chord residuals
/// remain first-class obstructions rather than being erased by reconstruction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalSpatialStanding {
    pub schema: String,
    pub component_roots: BTreeSet<VertexId>,
    pub edges: BTreeMap<Edge, LocalEdgeState>,
    pub capacities: BTreeMap<VertexId, Rat>,
    pub face_residuals: BTreeMap<FaceId, RatVec3>,
    pub chord_residuals: Vec<LocalChordResidual>,
}

type RealizedSpatialForest = (
    BTreeMap<VertexId, RatVec3>,
    BTreeSet<Edge>,
    BTreeSet<VertexId>,
);

impl LocalSpatialStanding {
    pub fn from_positions(
        complex: &crate::SimplicialComplex,
        positions: &BTreeMap<VertexId, RatVec3>,
    ) -> Result<Self, LocalStarError> {
        for vertex in complex.vertices.keys() {
            if !positions.contains_key(vertex) {
                return Err(LocalStarError::MissingVertexPosition(*vertex));
            }
        }
        let edges = complex
            .faces
            .values()
            .flat_map(|face| face.boundary().into_iter().map(|(edge, _)| edge))
            .chain(complex.hinges.values().map(|hinge| hinge.edge))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .map(|edge| {
                let vector = positions[&edge.upper].subtract(&positions[&edge.lower]);
                (
                    edge,
                    LocalEdgeState {
                        previous_vector: vector.clone(),
                        vector,
                    },
                )
            })
            .collect();
        let capacities = complex
            .vertices
            .keys()
            .copied()
            .map(|vertex| (vertex, Rat::one()))
            .collect();
        let mut standing = Self {
            schema: "holonic-engine.local-spatial-standing.v1".to_owned(),
            component_roots: BTreeSet::new(),
            edges,
            capacities,
            face_residuals: BTreeMap::new(),
            chord_residuals: Vec::new(),
        };
        standing.reform_obstructions(complex)?;
        Ok(standing)
    }

    fn realize_current(
        &self,
        complex: &crate::SimplicialComplex,
    ) -> Result<RealizedSpatialForest, LocalStarError> {
        self.realize_vectors(complex, false)
    }

    fn realize_previous(
        &self,
        complex: &crate::SimplicialComplex,
    ) -> Result<BTreeMap<VertexId, RatVec3>, LocalStarError> {
        self.realize_vectors(complex, true)
            .map(|(positions, _, _)| positions)
    }

    fn realize_vectors(
        &self,
        complex: &crate::SimplicialComplex,
        previous: bool,
    ) -> Result<RealizedSpatialForest, LocalStarError> {
        let mut adjacency = complex
            .vertices
            .keys()
            .copied()
            .map(|vertex| (vertex, Vec::<(VertexId, Edge)>::new()))
            .collect::<BTreeMap<_, _>>();
        for edge in self.edges.keys().copied() {
            adjacency
                .get_mut(&edge.lower)
                .ok_or(LocalStarError::MissingVertexPosition(edge.lower))?
                .push((edge.upper, edge));
            adjacency
                .get_mut(&edge.upper)
                .ok_or(LocalStarError::MissingVertexPosition(edge.upper))?
                .push((edge.lower, edge));
        }
        for neighbours in adjacency.values_mut() {
            neighbours.sort_by_key(|(vertex, edge)| (*vertex, *edge));
        }

        let mut positions = BTreeMap::new();
        let mut tree_edges = BTreeSet::new();
        let mut roots = BTreeSet::new();
        for root in complex.vertices.keys().copied() {
            if positions.contains_key(&root) {
                continue;
            }
            roots.insert(root);
            positions.insert(root, RatVec3::zero());
            let mut frontier = VecDeque::from([root]);
            while let Some(vertex) = frontier.pop_front() {
                let origin = positions[&vertex].clone();
                for (neighbour, edge) in &adjacency[&vertex] {
                    if positions.contains_key(neighbour) {
                        continue;
                    }
                    let state = self
                        .edges
                        .get(edge)
                        .ok_or(LocalStarError::MissingSpatialEdge(*edge))?;
                    let carried = if previous {
                        state.previous_vector.clone()
                    } else {
                        state.vector.clone()
                    };
                    let directed = if vertex == edge.lower {
                        carried
                    } else {
                        carried.scale(&-Rat::one())
                    };
                    positions.insert(*neighbour, origin.add(&directed));
                    tree_edges.insert(*edge);
                    frontier.push_back(*neighbour);
                }
            }
        }
        Ok((positions, tree_edges, roots))
    }

    fn reform_obstructions(
        &mut self,
        complex: &crate::SimplicialComplex,
    ) -> Result<(), LocalStarError> {
        self.face_residuals = complex
            .faces
            .values()
            .map(|face| {
                let residual = face.boundary().into_iter().try_fold(
                    RatVec3::zero(),
                    |sum, (edge, hand)| {
                        let vector = self
                            .edges
                            .get(&edge)
                            .ok_or(LocalStarError::MissingSpatialEdge(edge))?
                            .vector
                            .clone();
                        Ok::<_, LocalStarError>(
                            sum.add(&vector.scale(&Rat::from_integer(i64::from(hand).into()))),
                        )
                    },
                )?;
                Ok((face.id, residual))
            })
            .collect::<Result<_, LocalStarError>>()?;

        let (positions, tree_edges, roots) = self.realize_current(complex)?;
        self.component_roots = roots;
        self.chord_residuals = self
            .edges
            .iter()
            .filter(|(edge, _)| !tree_edges.contains(edge))
            .map(|(edge, state)| {
                let realized_vector = positions[&edge.upper].subtract(&positions[&edge.lower]);
                LocalChordResidual {
                    edge: *edge,
                    carried_vector: state.vector.clone(),
                    realized_vector: realized_vector.clone(),
                    residual: state.vector.subtract(&realized_vector),
                }
            })
            .collect();
        Ok(())
    }

    pub fn realized_vertices(
        &self,
        complex: &crate::SimplicialComplex,
    ) -> Result<BTreeMap<VertexId, VertexFieldState>, LocalStarError> {
        let (current, _, _) = self.realize_current(complex)?;
        let previous = self.realize_previous(complex)?;
        complex
            .vertices
            .keys()
            .copied()
            .map(|vertex| {
                Ok((
                    vertex,
                    VertexFieldState {
                        previous_position: previous[&vertex].clone(),
                        position: current[&vertex].clone(),
                        capacity: self
                            .capacities
                            .get(&vertex)
                            .cloned()
                            .ok_or(LocalStarError::MissingVertexPosition(vertex))?,
                    },
                ))
            })
            .collect()
    }

    pub fn position(
        &self,
        complex: &crate::SimplicialComplex,
        vertex: VertexId,
    ) -> Result<RatVec3, LocalStarError> {
        self.realize_current(complex)?
            .0
            .remove(&vertex)
            .ok_or(LocalStarError::MissingVertexPosition(vertex))
    }

    pub fn relative_vector(
        &self,
        complex: &crate::SimplicialComplex,
        from: VertexId,
        to: VertexId,
    ) -> Result<Option<RatVec3>, LocalStarError> {
        let (positions, _, roots) = self.realize_current(complex)?;
        let component_root = |vertex: VertexId| -> Result<VertexId, LocalStarError> {
            let mut reached = BTreeSet::from([vertex]);
            let mut frontier = VecDeque::from([vertex]);
            while let Some(at) = frontier.pop_front() {
                for edge in self.edges.keys() {
                    let neighbour = if edge.lower == at {
                        Some(edge.upper)
                    } else if edge.upper == at {
                        Some(edge.lower)
                    } else {
                        None
                    };
                    if let Some(neighbour) = neighbour
                        && reached.insert(neighbour)
                    {
                        frontier.push_back(neighbour);
                    }
                }
            }
            roots
                .iter()
                .copied()
                .find(|root| reached.contains(root))
                .ok_or(LocalStarError::MissingVertexPosition(vertex))
        };
        if component_root(from)? != component_root(to)? {
            return Ok(None);
        }
        Ok(Some(positions[&to].subtract(&positions[&from])))
    }

    fn advance(
        &self,
        complex: &crate::SimplicialComplex,
        vertex_displacements: &BTreeMap<VertexId, RatVec3>,
    ) -> Result<Self, LocalStarError> {
        let mut standing = self.clone();
        for (edge, state) in &mut standing.edges {
            state.previous_vector = state.vector.clone();
            let lower = vertex_displacements
                .get(&edge.lower)
                .cloned()
                .unwrap_or_else(RatVec3::zero);
            let upper = vertex_displacements
                .get(&edge.upper)
                .cloned()
                .unwrap_or_else(RatVec3::zero);
            state.vector = state.vector.add(&upper.subtract(&lower));
        }
        standing.reform_obstructions(complex)?;
        Ok(standing)
    }

    fn rewrite_for_complex(
        &self,
        before: &crate::SimplicialComplex,
        after: &crate::SimplicialComplex,
    ) -> Result<Self, LocalStarError> {
        let current = self.realize_current(before)?.0;
        let previous = self.realize_previous(before)?;
        let edges = after
            .faces
            .values()
            .flat_map(|face| face.boundary().into_iter().map(|(edge, _)| edge))
            .chain(after.hinges.values().map(|hinge| hinge.edge))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .map(|edge| {
                (
                    edge,
                    LocalEdgeState {
                        previous_vector: previous[&edge.upper].subtract(&previous[&edge.lower]),
                        vector: current[&edge.upper].subtract(&current[&edge.lower]),
                    },
                )
            })
            .collect();
        let mut standing = Self {
            schema: self.schema.clone(),
            component_roots: BTreeSet::new(),
            edges,
            capacities: self.capacities.clone(),
            face_residuals: BTreeMap::new(),
            chord_residuals: Vec::new(),
        };
        standing.reform_obstructions(after)?;
        Ok(standing)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaceFieldState {
    pub previous_circulation: Rat,
    pub circulation: Rat,
    /// Oriented change of circulation.  Its sign is chart hand, not value.
    pub stress: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverBodyState {
    pub receiver: ReceiverId,
    pub source_event: EventId,
    pub anchor: VertexId,
    /// The source-world incidence through which this receiver can act.
    pub port: HingeId,
    /// Exact local constitutive relations carried by this receiver.  The
    /// population is part of the receiver holon rather than a fixed list in
    /// the world law.
    pub couplings: Vec<ReceiverLocalCoupling>,
    pub local_offset: RatVec3,
    pub previous_local_offset: RatVec3,
    /// Primitive projective rational spin carried by the receiver body.
    pub orientation: ReceiverOrientation,
    pub previous_orientation: ReceiverOrientation,
    /// Receiver-relative `(coordinate, momentum, net impulse)` carried from
    /// its declared hinge couplings. This, not pose or palette, phases the
    /// outer monitor transduction.
    pub physical_phase: RatVec3,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverRotationCoupling {
    pub axis: ReceiverRotationAxis,
    pub cayley_per_turn: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverLocalCoupling {
    pub hinge: HingeId,
    pub translation_per_turn: RatVec3,
    /// Ordered local rotations emitted by one signed hinge turn.
    pub rotations_per_turn: Vec<ReceiverRotationCoupling>,
}

/// Source material sufficient to found one receiver holon.  Its topology is
/// not supplied as a label: the receiving law derives the star and link from
/// the contemporary simplicial complex.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverFounding {
    pub receiver: ReceiverId,
    pub source_event: EventId,
    pub anchor: VertexId,
    pub port: HingeId,
    pub couplings: Vec<ReceiverLocalCoupling>,
    pub local_offset: RatVec3,
    pub orientation: ReceiverOrientation,
}

/// A caused change to the receiver population.  Founding, departure, and
/// topological re-anchoring are event consequences; none is inferred from a
/// container index or display slot. Re-anchoring preserves the receiver's
/// position while changing which vertex carries its local offset. It is not a
/// coordinate re-base.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverPopulationDeed {
    Found(Box<ReceiverFounding>),
    Depart {
        receiver: ReceiverId,
    },
    Reanchor {
        receiver: ReceiverId,
        anchor: VertexId,
    },
}

/// Exact caused chart captured when a traversal occurrence enters the world
/// membrane. A later event may carry it only by identity; a changed chart
/// requires a separately derived connection.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverTraversalChart {
    pub event: EventId,
    pub receiver: ReceiverId,
    pub position: RatVec3,
    pub orientation: ReceiverOrientation,
    pub acceptance: ReceiverAcceptanceCover,
}

impl ReceiverTraversalChart {
    fn carries_by_identity(&self, contemporary: &Self) -> bool {
        self.receiver == contemporary.receiver
            && self.position == contemporary.position
            && self.orientation == contemporary.orientation
            && self.acceptance.receiver == contemporary.acceptance.receiver
            && self.acceptance.anchor == contemporary.acceptance.anchor
            && self.acceptance.link_class == contemporary.acceptance.link_class
            && self.acceptance.organs == contemporary.acceptance.organs
            && self.acceptance.seams == contemporary.acceptance.seams
            && self.acceptance.port_section == contemporary.acceptance.port_section
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverTraversalStep {
    /// Coordinates in the captured port basis `(horizontal, vertical,
    /// forward)`, not source-world coordinates or terminal-cell offsets.
    Translate { coordinates: RatVec3 },
    Rotate {
        axis: ReceiverRotationAxis,
        ratio: ProjectiveRatio,
    },
    /// A run of one identical elementary generator. The path multiplicity is
    /// retained while the declared affine/projective action is realized by
    /// exact scaling or binary powering.
    Repeat {
        generator: Box<ReceiverTraversalStep>,
        repetitions: BigUint,
    },
}

fn apply_receiver_traversal_step(
    body: &mut ReceiverBodyState,
    port: &ReceiverPortSection,
    step: &ReceiverTraversalStep,
    world_translation: &mut RatVec3,
) -> Result<(), LocalStarError> {
    let (generator, repetitions) = match step {
        ReceiverTraversalStep::Repeat {
            generator,
            repetitions,
        } => {
            if repetitions.is_zero() {
                return Err(LocalStarError::EmptyReceiverTraversalRun);
            }
            if matches!(generator.as_ref(), ReceiverTraversalStep::Repeat { .. }) {
                return Err(LocalStarError::NestedReceiverTraversalRun);
            }
            (generator.as_ref(), repetitions.clone())
        }
        generator => (generator, BigUint::one()),
    };
    match generator {
        ReceiverTraversalStep::Translate { coordinates } => {
            let repetitions = Rat::from_integer(BigInt::from(repetitions));
            let coordinates = coordinates.scale(&repetitions);
            let translated = port
                .horizontal
                .scale(&coordinates.x)
                .add(&port.vertical.scale(&coordinates.y))
                .add(&port.forward.scale(&coordinates.z));
            body.local_offset = body.local_offset.add(&translated);
            *world_translation = world_translation.add(&translated);
        }
        ReceiverTraversalStep::Rotate { axis, ratio } => {
            let spin = ExactSpin::axis(*axis, ratio).pow(&repetitions);
            body.orientation = body.orientation.followed_by(&spin);
        }
        ReceiverTraversalStep::Repeat { .. } => unreachable!("nested runs were refused"),
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverTraversalOccurrence {
    pub source_chart: ReceiverTraversalChart,
    pub steps: Vec<ReceiverTraversalStep>,
}

/// One external deed expressed in a caused receiver chart. Physical port
/// current is declared separately from traversal; no coordinate amount
/// implicitly becomes current.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverBoundaryDeed {
    pub receiver: ReceiverId,
    pub traversal: ReceiverTraversalOccurrence,
    pub port_current: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalStarStanding {
    pub schema: String,
    /// Latest completed physical occurrence embodied by this standing.
    pub event: EventId,
    pub kinematic: HingeWorldStanding,
    pub trajectories: BTreeMap<HingeId, HingeTrajectory>,
    pub spatial: LocalSpatialStanding,
    /// Contemporary physical-current incidence. The law supplies the
    /// founding relations; a topology deed retains only relations still
    /// admitted by the successor complex.
    pub current_transports: LocalCurrentIncidence,
    /// Chart-local constitutive directions carried with the standing body.
    ///
    /// Keeping these in the law would make a later chart transition move the
    /// geometry while leaving its response directions in an obsolete frame.
    pub geometry_responses: BTreeMap<HingeId, RatVec3>,
    pub faces: BTreeMap<FaceId, FaceFieldState>,
    pub receivers: BTreeMap<ReceiverId, ReceiverBodyState>,
    /// Lawful rewrite mouths opened by prior completed local solves.
    pub rewrite_openings: Vec<LocalRewriteCandidate>,
    /// The exact open current constituents which survive a complete event.
    ///
    /// Intermediate incidence fronts never enter this standing: they advance
    /// inside the event law. This population is therefore neither a frame
    /// buffer nor a queue. It exists only when exact recurrence or repeated
    /// cyclic support leaves a boundary for a genuinely later world deed.
    pub open_currents: Vec<LocalCurrentConstituent>,
}

impl LocalStarStanding {
    pub fn open_frontier(&self) -> BTreeMap<HingeId, Rat> {
        current_frontier(&self.open_currents)
    }

    pub fn coordination_defects(
        &self,
    ) -> Result<BTreeMap<VertexId, LocalCoordinationDefect>, LocalStarError> {
        self.kinematic
            .complex
            .vertices
            .keys()
            .copied()
            .map(|vertex| {
                Ok((
                    vertex,
                    coordination_defect(&self.kinematic.complex, vertex)?,
                ))
            })
            .collect()
    }

    pub fn realized_vertices(
        &self,
    ) -> Result<BTreeMap<VertexId, VertexFieldState>, LocalStarError> {
        self.spatial.realized_vertices(&self.kinematic.complex)
    }

    pub fn receiver_topology(&self, receiver: ReceiverId) -> Option<VertexStarLink> {
        let body = self.receivers.get(&receiver)?;
        self.kinematic.complex.vertex_star_link(body.anchor).ok()
    }

    pub fn receiver_position(&self, receiver: ReceiverId) -> Option<RatVec3> {
        let body = self.receivers.get(&receiver)?;
        let anchor = self
            .spatial
            .position(&self.kinematic.complex, body.anchor)
            .ok()?;
        Some(anchor.add(&body.local_offset))
    }

    /// Derive the receiver's complete directional organ cover from its
    /// contemporary oriented link.
    ///
    /// Each incident face contributes one organ. Shared link vertices form
    /// the overlap seams, and the explicit receiver port selects a finite
    /// projective section without consulting face or edge container order.
    pub fn receiver_acceptance_cover(
        &self,
        receiver: ReceiverId,
    ) -> Result<ReceiverAcceptanceCover, LocalStarError> {
        let body = self
            .receivers
            .get(&receiver)
            .ok_or(LocalStarError::MissingReceiverBody(receiver))?;
        let complex = &self.kinematic.complex;
        let topology = complex.vertex_star_link(body.anchor)?;
        let direction = |vertex| -> Result<RatVec3, LocalStarError> {
            self.spatial
                .relative_vector(complex, body.anchor, vertex)?
                .map(|relative| relative.subtract(&body.local_offset))
                .ok_or(LocalStarError::ReceiverDirectionOutsideComponent { receiver, vertex })
        };
        let organs = complex
            .oriented_vertex_link_cells(body.anchor)?
            .into_iter()
            .map(|cell| {
                let from = direction(cell.from)?;
                let to = direction(cell.to)?;
                Ok(ReceiverAcceptanceOrgan {
                    face: cell.face,
                    link_edge: cell.edge,
                    from: cell.from,
                    to: cell.to,
                    hand: cell.hand,
                    boundary_directions: [from.clone(), to.clone()],
                    central_direction: from.add(&to),
                    oriented_area: from.cross(&to),
                })
            })
            .collect::<Result<Vec<_>, LocalStarError>>()?;
        let seams = topology
            .link_vertices
            .iter()
            .copied()
            .map(|vertex| {
                let mut incoming = organs
                    .iter()
                    .filter(|organ| organ.to == vertex)
                    .map(|organ| organ.face)
                    .collect::<Vec<_>>();
                let mut outgoing = organs
                    .iter()
                    .filter(|organ| organ.from == vertex)
                    .map(|organ| organ.face)
                    .collect::<Vec<_>>();
                incoming.sort();
                outgoing.sort();
                Ok(ReceiverAcceptanceSeam {
                    vertex,
                    direction: direction(vertex)?,
                    incoming,
                    outgoing,
                })
            })
            .collect::<Result<Vec<_>, LocalStarError>>()?;

        let port = complex
            .hinges
            .get(&body.port)
            .ok_or(LocalStarError::MissingHinge(body.port))?;
        let distal = if port.edge.lower == body.anchor {
            port.edge.upper
        } else if port.edge.upper == body.anchor {
            port.edge.lower
        } else {
            return Err(LocalStarError::ReceiverPortMissesAnchor {
                receiver,
                hinge: body.port,
                anchor: body.anchor,
            });
        };
        let port_hand = if body.anchor == port.edge.lower {
            1
        } else {
            -1
        };
        let negative = port
            .cofaces
            .iter()
            .find(|coface| coface.hand != port_hand)
            .expect("a validated interior hinge has one opposed coface");
        let positive = port
            .cofaces
            .iter()
            .find(|coface| coface.hand == port_hand)
            .expect("a validated interior hinge has one aligned coface");
        let opposite = |face: FaceId| {
            complex.faces[&face]
                .vertices
                .into_iter()
                .find(|vertex| *vertex != body.anchor && *vertex != distal)
                .expect("a port coface has one transverse vertex")
        };
        let negative_direction = direction(opposite(negative.face))?;
        let positive_direction = direction(opposite(positive.face))?;
        let forward = direction(distal)?;
        let horizontal = positive_direction.subtract(&negative_direction);
        let vertical = forward.cross(&horizontal);
        if forward == RatVec3::zero()
            || horizontal == RatVec3::zero()
            || vertical == RatVec3::zero()
        {
            return Err(LocalStarError::CollapsedReceiverPortSection {
                receiver,
                hinge: body.port,
            });
        }
        Ok(ReceiverAcceptanceCover {
            event: self.event,
            receiver,
            anchor: body.anchor,
            link_class: topology.link_class,
            organs,
            seams,
            port_section: ReceiverPortSection {
                port: body.port,
                distal,
                negative_face: negative.face,
                positive_face: positive.face,
                forward,
                horizontal,
                vertical,
            },
        })
    }

    pub fn receiver_traversal_chart(
        &self,
        receiver: ReceiverId,
    ) -> Result<ReceiverTraversalChart, LocalStarError> {
        let body = self
            .receivers
            .get(&receiver)
            .ok_or(LocalStarError::MissingReceiverBody(receiver))?;
        Ok(ReceiverTraversalChart {
            event: self.event,
            receiver,
            position: self
                .receiver_position(receiver)
                .ok_or(LocalStarError::MissingReceiverBody(receiver))?,
            orientation: body.orientation.clone(),
            acceptance: self.receiver_acceptance_cover(receiver)?,
        })
    }

    /// Form the exact finite port chart selected by the receiver's declared
    /// causal incidence. The complete organ cover remains attached to the
    /// specification and later face formation testimony.
    pub fn receiver_face_specification(
        &self,
        frame: FrameId,
        receiver: ReceiverId,
    ) -> Result<ReceiverFaceSpec, LocalStarError> {
        let body = self
            .receivers
            .get(&receiver)
            .ok_or(LocalStarError::MissingReceiverBody(receiver))?;
        let position = self
            .receiver_position(receiver)
            .ok_or(LocalStarError::MissingReceiverBody(receiver))?;
        let acceptance = self.receiver_acceptance_cover(receiver)?;
        let horizontal_square = acceptance
            .port_section
            .horizontal
            .dot(&acceptance.port_section.horizontal);
        let vertical_square = acceptance
            .port_section
            .vertical
            .dot(&acceptance.port_section.vertical);
        if horizontal_square.is_zero() || vertical_square.is_zero() {
            return Err(LocalStarError::CollapsedReceiverPortSection {
                receiver,
                hinge: body.port,
            });
        }
        let mut receiver_body = Receiver::new(
            receiver,
            format!("receiver {} local star", receiver.0),
            frame,
            ProjectionLaw::PerspectiveRay {
                focal_distance: integer(1),
            },
        );
        receiver_body.orientation = body.orientation.clone();
        Ok(ReceiverFaceSpec {
            receiver: receiver_body,
            extent: ReceiverFaceExtent {
                horizontal_span: integer(2),
                vertical_span: integer(2) * vertical_square / horizontal_square,
            },
            rays: RayFamily::Central {
                center: position,
                forward: acceptance.port_section.forward.clone(),
                horizontal: acceptance.port_section.horizontal.clone(),
                vertical: acceptance.port_section.vertical.clone(),
            },
            acceptance: Some(acceptance),
        })
    }

    /// Receiver population in the terminal receiver's actual overlap
    /// component. Two receiver stars are adjacent only when their intrinsic
    /// simplicial sections share a vertex, hinge, or face.
    pub fn receiver_overlap_component(&self, terminal: ReceiverId) -> Option<BTreeSet<ReceiverId>> {
        self.receivers.get(&terminal)?;
        let mut reached = BTreeSet::from([terminal]);
        let mut frontier = vec![terminal];
        while let Some(receiver) = frontier.pop() {
            let body = &self.receivers[&receiver];
            let topology = self.kinematic.complex.vertex_star_link(body.anchor).ok()?;
            for (candidate, other) in &self.receivers {
                if reached.contains(candidate) {
                    continue;
                }
                let other_topology = self.kinematic.complex.vertex_star_link(other.anchor).ok()?;
                let overlaps = topology
                    .star_vertices
                    .iter()
                    .any(|vertex| other_topology.star_vertices.contains(vertex))
                    || topology
                        .star_hinges
                        .iter()
                        .any(|hinge| other_topology.star_hinges.contains(hinge))
                    || topology
                        .star_faces
                        .iter()
                        .any(|face| other_topology.star_faces.contains(face));
                if overlaps {
                    reached.insert(*candidate);
                    frontier.push(*candidate);
                }
            }
        }
        Some(reached)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalStarEvent {
    pub event: EventId,
    /// Direct source currents not mediated by a receiver port.
    pub source_currents: BTreeMap<HingeId, Rat>,
    pub receiver_deeds: Vec<ReceiverBoundaryDeed>,
    pub receiver_population: Vec<ReceiverPopulationDeed>,
    pub topology_deeds: Vec<LocalTopologyDeed>,
}

impl LocalStarEvent {
    pub fn continuation(event: EventId) -> Self {
        Self {
            event,
            source_currents: BTreeMap::new(),
            receiver_deeds: Vec::new(),
            receiver_population: Vec::new(),
            topology_deeds: Vec::new(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalCurrentBalance {
    pub hinge: HingeId,
    pub entered: Rat,
    pub deposited: Rat,
    pub emitted: Vec<(HingeId, Rat)>,
    pub departed: Rat,
    pub exact_residual: Rat,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LocalRewriteReason {
    CoordinateCrossedDiscriminant,
}

/// A lawful 2-to-2 edge-flip opening.  This record does not silently mutate
/// the topology: an application may admit it as the next event or leave the
/// found seam open.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalRewriteCandidate {
    pub hinge: HingeId,
    pub held_boundary: [VertexId; 4],
    pub proposed_diagonal: Edge,
    pub reason: LocalRewriteReason,
}

/// A topology deed can only close a rewrite mouth already present in
/// contemporary standing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LocalTopologyDeed {
    AdmitFlip(LocalRewriteCandidate),
}

/// Coordination defect derived from the actual receiver link.
///
/// The cycle case has the declared hexagonal coordination charge. Boundary
/// paths and singular links remain typed structural facts until their own
/// physical doctrine is supplied.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LocalCoordinationDefect {
    InteriorCycle { coordination: usize, charge: i64 },
    BoundaryPath { coordination: usize },
    Singular { coordination: usize },
    Isolated,
}

fn coordination_defect(
    complex: &crate::SimplicialComplex,
    vertex: VertexId,
) -> Result<LocalCoordinationDefect, LocalStarError> {
    let link = complex.vertex_star_link(vertex)?;
    Ok(match link.link_class {
        VertexLinkClass::Cycle => LocalCoordinationDefect::InteriorCycle {
            coordination: link.link_vertices.len(),
            charge: 6_i64
                - i64::try_from(link.link_vertices.len())
                    .expect("a local finite link cardinality fits i64"),
        },
        VertexLinkClass::Path => LocalCoordinationDefect::BoundaryPath {
            coordination: link.link_vertices.len(),
        },
        VertexLinkClass::Singular => LocalCoordinationDefect::Singular {
            coordination: link.link_vertices.len(),
        },
        VertexLinkClass::Empty => LocalCoordinationDefect::Isolated,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalDefectChange {
    pub vertex: VertexId,
    pub before: LocalCoordinationDefect,
    pub after: LocalCoordinationDefect,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalTopologyChange {
    pub flip: SimplicialFlipReceipt,
    pub defect_changes: Vec<LocalDefectChange>,
    /// Present only when every changed link is an interior cycle.
    pub exact_charge_residual: Option<i64>,
    pub departed_current_transports: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverTraversalReceipt {
    pub source_chart_event: EventId,
    pub enacted_chart_event: EventId,
    pub identity_carried: bool,
    pub steps: Vec<ReceiverTraversalStep>,
    pub world_translation: RatVec3,
    pub port_current: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverWorldlineStep {
    pub receiver: ReceiverId,
    pub position_before: RatVec3,
    pub position_after: RatVec3,
    pub orientation_before: ReceiverOrientation,
    pub orientation_after: ReceiverOrientation,
    pub traversal: Option<ReceiverTraversalReceipt>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ReceiverSharedOccurrence {
    Vertex(VertexId),
    Hinge(HingeId),
    Face(FaceId),
}

/// One actual event-supported cell of the receiver nerve.  A set of three or
/// more receivers remains one higher incidence and is never reconstructed
/// from a pairwise clique.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverNerveCell {
    pub occurrence: ReceiverSharedOccurrence,
    pub receivers: Vec<ReceiverId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverEventNerve {
    pub event: EventId,
    pub cells: Vec<ReceiverNerveCell>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverPopulationChange {
    Founded {
        receiver: ReceiverId,
        source_event: EventId,
        anchor: VertexId,
        topology: VertexStarLink,
    },
    Departed {
        receiver: ReceiverId,
    },
    Reanchored {
        receiver: ReceiverId,
        from: VertexId,
        to: VertexId,
        topology: VertexStarLink,
    },
}

/// Why one complete event stopped advancing its local incidence front.
///
/// `CyclicSupportOpen` is not a numerical timeout. Once more causal layers
/// than live hinges remain active, some hinge support has necessarily
/// recurred. The continuing current is retained as an exact open boundary for
/// a genuinely later deed; the display clock is not allowed to invent one.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LocalPropagationBoundary {
    Rest {
        causal_layers: usize,
    },
    ExactReturn {
        causal_layers: usize,
        returned_to_layer: usize,
    },
    CyclicSupportOpen {
        causal_layers: usize,
    },
}

/// Physical and causal testimony for one locally parallel antichain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalCausalLayerReceipt {
    pub ordinal: usize,
    pub active_hinges: Vec<HingeId>,
    pub emitted_frontier: BTreeMap<HingeId, Rat>,
    pub emitted_currents: Vec<LocalCurrentConstituent>,
    pub cpu_execution: CpuExecutionReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalStarRadiation {
    pub event: EventId,
    pub causal_layers: Vec<LocalCausalLayerReceipt>,
    pub propagation_boundary: LocalPropagationBoundary,
    pub active_hinges: Vec<HingeId>,
    pub balances: Vec<ActionBalanceReceipt>,
    pub current_balances: Vec<LocalCurrentBalance>,
    pub current_paths: Vec<LocalCurrentPathReceipt>,
    pub face_fields: BTreeMap<FaceId, FaceFieldState>,
    pub receiver_worldlines: Vec<ReceiverWorldlineStep>,
    pub receiver_nerve: ReceiverEventNerve,
    pub receiver_population: Vec<ReceiverPopulationChange>,
    pub topology_changes: Vec<LocalTopologyChange>,
    pub rewrite_candidates: Vec<LocalRewriteCandidate>,
    pub open_frontier: BTreeMap<HingeId, Rat>,
    pub cpu_execution: CpuExecutionReceipt,
    pub kinematic: HingeRadiation,
}

#[derive(Clone, Debug)]
pub struct LocalStarLaw {
    pub kinematic: HingeWorldLaw,
    pub materials: BTreeMap<HingeId, LocalStarMaterial>,
    pub transports: LocalCurrentIncidence,
    pub executor: CpuExecutor,
}

#[derive(Clone)]
struct LocalSolve {
    hinge: HingeId,
    trajectory: HingeTrajectory,
    balance: ActionBalanceReceipt,
    current_balance: LocalCurrentBalance,
    current_paths: Vec<LocalCurrentPathReceipt>,
    emitted_currents: Vec<LocalCurrentConstituent>,
    coordinate_change: Rat,
}

impl LocalStarLaw {
    pub fn new(
        kinematic: HingeWorldLaw,
        materials: BTreeMap<HingeId, LocalStarMaterial>,
        mut transports: Vec<LocalCurrentTransport>,
        executor: CpuExecutor,
    ) -> Result<Self, LocalStarError> {
        for hinge in kinematic.complex.hinges.keys() {
            if !materials.contains_key(hinge) {
                return Err(LocalStarError::MissingMaterial(*hinge));
            }
        }
        for hinge in materials.keys() {
            if !kinematic.complex.hinges.contains_key(hinge) {
                return Err(LocalStarError::MissingHinge(*hinge));
            }
        }
        for (offset, transport) in transports.iter_mut().enumerate() {
            if !matches!(transport.hand, -1..=1) {
                return Err(LocalStarError::InvalidTransportHand(transport.hand));
            }
            if transport.source == transport.target
                || !kinematic
                    .complex
                    .hinges_share_face(transport.source, transport.target)?
            {
                return Err(LocalStarError::NonlocalCurrentTransport {
                    from_hinge: transport.source,
                    to_hinge: transport.target,
                });
            }
            transport.id = u64::try_from(offset + 1).expect("transport count fits u64");
        }
        let transports = LocalCurrentIncidence::canonical(transports);

        Ok(Self {
            kinematic,
            materials,
            transports,
            executor,
        })
    }

    pub fn initial_standing(
        &self,
        mut kinematic: HingeWorldStanding,
        trajectories: BTreeMap<HingeId, HingeTrajectory>,
        positions: BTreeMap<VertexId, RatVec3>,
        receiver_foundings: Vec<ReceiverFounding>,
    ) -> Result<LocalStarStanding, LocalStarError> {
        for (hinge, parameter) in &kinematic.parameters {
            let trajectory = trajectories
                .get(hinge)
                .ok_or(LocalStarError::MissingTrajectory(*hinge))?;
            if &trajectory.current != parameter {
                return Err(LocalStarError::TrajectoryStandingMismatch(*hinge));
            }
        }
        let spatial = LocalSpatialStanding::from_positions(&kinematic.complex, &positions)?;
        let standing_event = kinematic
            .complex
            .vertices
            .values()
            .map(|vertex| vertex.source_event)
            .chain(
                receiver_foundings
                    .iter()
                    .map(|founding| founding.source_event),
            )
            .chain(
                kinematic
                    .conics
                    .cells
                    .values()
                    .map(|conic| conic.last_event),
            )
            .max()
            .unwrap_or(EventId(0));
        let local_positions = spatial
            .realized_vertices(&kinematic.complex)?
            .into_iter()
            .map(|(vertex, state)| (vertex, state.position))
            .collect::<BTreeMap<_, _>>();
        for family in self.kinematic.conic_families.values() {
            let anchor = family
                .coefficients
                .iter()
                .flat_map(|coefficient| coefficient.terms.keys())
                .find_map(|hinge| kinematic.complex.hinges.get(hinge))
                .map(|hinge| hinge.edge.lower)
                .or_else(|| kinematic.complex.vertices.keys().next().copied())
                .ok_or(LocalStarError::EmptySpatialComplex)?;
            let translation = local_positions[&anchor].subtract(&positions[&anchor]);
            let conic =
                kinematic
                    .conics
                    .cells
                    .get_mut(&family.cell)
                    .ok_or(LocalStarError::Kinematic(HingeWorldError::MissingConic(
                        family.cell,
                    )))?;
            conic.chart.origin = conic.chart.origin.add(&translation);
        }
        let mut receivers = BTreeMap::new();
        for founding in receiver_foundings {
            let mut body = self.found_receiver(&founding, &kinematic.complex, &spatial)?;
            body.physical_phase = self.receiver_physical_phase(&body, &trajectories, &[])?;
            if receivers.insert(body.receiver, body).is_some() {
                return Err(LocalStarError::DuplicateReceiverBody);
            }
        }
        let faces = self.face_fields(&kinematic.complex, &kinematic.parameters, None)?;
        Ok(LocalStarStanding {
            schema: "holonic-engine.local-star-standing.v5".to_owned(),
            event: standing_event,
            kinematic,
            trajectories,
            spatial,
            current_transports: self.transports.clone(),
            geometry_responses: self
                .materials
                .iter()
                .map(|(hinge, material)| (*hinge, material.geometry_response.clone()))
                .collect(),
            faces,
            receivers,
            rewrite_openings: Vec::new(),
            open_currents: Vec::new(),
        })
    }

    fn found_receiver(
        &self,
        founding: &ReceiverFounding,
        complex: &crate::SimplicialComplex,
        spatial: &LocalSpatialStanding,
    ) -> Result<ReceiverBodyState, LocalStarError> {
        if !spatial.capacities.contains_key(&founding.anchor) {
            return Err(LocalStarError::MissingVertexPosition(founding.anchor));
        }
        if !complex.hinges.contains_key(&founding.port) {
            return Err(LocalStarError::MissingHinge(founding.port));
        }
        let topology = complex.vertex_star_link(founding.anchor)?;
        if !topology.star_hinges.contains(&founding.port) {
            return Err(LocalStarError::ReceiverPortOutsideStar {
                receiver: founding.receiver,
                hinge: founding.port,
                anchor: founding.anchor,
            });
        }
        let port_edge = complex.hinges[&founding.port].edge;
        if port_edge.lower != founding.anchor && port_edge.upper != founding.anchor {
            return Err(LocalStarError::ReceiverPortMissesAnchor {
                receiver: founding.receiver,
                hinge: founding.port,
                anchor: founding.anchor,
            });
        }
        let mut couplings = founding.couplings.clone();
        couplings.sort_by_key(|coupling| coupling.hinge);
        for coupling in &couplings {
            if !topology.star_hinges.contains(&coupling.hinge) {
                return Err(LocalStarError::ReceiverCouplingOutsideStar {
                    receiver: founding.receiver,
                    hinge: coupling.hinge,
                    anchor: founding.anchor,
                });
            }
        }
        Ok(ReceiverBodyState {
            receiver: founding.receiver,
            source_event: founding.source_event,
            anchor: founding.anchor,
            port: founding.port,
            couplings,
            local_offset: founding.local_offset.clone(),
            previous_local_offset: founding.local_offset.clone(),
            orientation: founding.orientation.clone(),
            previous_orientation: founding.orientation.clone(),
            physical_phase: RatVec3::zero(),
        })
    }

    fn receiver_physical_phase(
        &self,
        body: &ReceiverBodyState,
        trajectories: &BTreeMap<HingeId, HingeTrajectory>,
        balances: &[ActionBalanceReceipt],
    ) -> Result<RatVec3, LocalStarError> {
        let coupled = body
            .couplings
            .iter()
            .map(|coupling| coupling.hinge)
            .collect::<BTreeSet<_>>();
        let mut coordinate = Rat::zero();
        let mut momentum = Rat::zero();
        let mut impulse = Rat::zero();
        for hinge in coupled {
            let trajectory = trajectories
                .get(&hinge)
                .ok_or(LocalStarError::MissingTrajectory(hinge))?;
            let material = self
                .materials
                .get(&hinge)
                .ok_or(LocalStarError::MissingMaterial(hinge))?;
            coordinate += &trajectory.current;
            momentum += &material.action.inertia * (&trajectory.current - &trajectory.previous);
            if let Some(balance) = balances.iter().find(|balance| balance.hinge == hinge) {
                impulse += &balance.internal_impulse + &balance.external_impulse;
            }
        }
        Ok(RatVec3::new(coordinate, momentum, impulse))
    }

    fn face_fields(
        &self,
        complex: &crate::SimplicialComplex,
        parameters: &BTreeMap<HingeId, Rat>,
        preceding: Option<&BTreeMap<FaceId, FaceFieldState>>,
    ) -> Result<BTreeMap<FaceId, FaceFieldState>, LocalStarError> {
        let edge_hinges = complex
            .hinges
            .values()
            .map(|hinge| (hinge.edge, hinge.id))
            .collect::<BTreeMap<_, _>>();
        complex
            .faces
            .values()
            .map(|face| {
                let circulation =
                    face.boundary()
                        .into_iter()
                        .try_fold(Rat::zero(), |sum, (edge, hand)| {
                            let hinge = edge_hinges
                                .get(&edge)
                                .ok_or(LocalStarError::MissingBoundaryHinge(edge))?;
                            let parameter = parameters
                                .get(hinge)
                                .ok_or(LocalStarError::MissingTrajectory(*hinge))?;
                            Ok::<_, LocalStarError>(
                                sum + Rat::from_integer(i64::from(hand).into()) * parameter,
                            )
                        })?;
                let previous_circulation = preceding
                    .and_then(|fields| fields.get(&face.id))
                    .map_or_else(|| circulation.clone(), |field| field.circulation.clone());
                let stress = &circulation - &previous_circulation;
                Ok((
                    face.id,
                    FaceFieldState {
                        previous_circulation,
                        circulation,
                        stress,
                    },
                ))
            })
            .collect()
    }

    fn incident_stress(
        &self,
        standing: &LocalStarStanding,
        hinge: HingeId,
    ) -> Result<Rat, LocalStarError> {
        let hinge = standing
            .kinematic
            .complex
            .hinges
            .get(&hinge)
            .ok_or(LocalStarError::MissingHinge(hinge))?;
        hinge.cofaces.iter().try_fold(Rat::zero(), |sum, coface| {
            let stress = &standing
                .faces
                .get(&coface.face)
                .ok_or(LocalStarError::MissingFaceState(coface.face))?
                .stress;
            Ok(sum + Rat::from_integer(i64::from(coface.hand).into()) * stress)
        })
    }

    fn solve_member(
        &self,
        standing: &LocalStarStanding,
        hinge: HingeId,
        constituents: &[LocalCurrentConstituent],
    ) -> Result<LocalSolve, LocalStarError> {
        let material = self
            .materials
            .get(&hinge)
            .ok_or(LocalStarError::MissingMaterial(hinge))?;
        let trajectory = standing
            .trajectories
            .get(&hinge)
            .ok_or(LocalStarError::MissingTrajectory(hinge))?;
        let entered = constituents
            .iter()
            .fold(Rat::zero(), |sum, current| sum + &current.amount);
        let mut current_paths = constituents
            .iter()
            .cloned()
            .map(|current| {
                let outgoing = standing.current_transports.outgoing(hinge);
                let mut emitted = Vec::with_capacity(outgoing.len());
                for transport in outgoing {
                    if transport.hand == 0
                        || (transport.hand == 1 && current.amount.is_positive())
                        || (transport.hand == -1 && current.amount.is_negative())
                    {
                        emitted.push(current.crossed(transport));
                    }
                }
                sort_current_constituents(&mut emitted);
                let emitted_total = emitted
                    .iter()
                    .fold(Rat::zero(), |sum, child| sum + &child.amount);
                let deposited = &current.amount - &emitted_total;
                LocalCurrentPathReceipt {
                    entered: current,
                    deposited,
                    emitted,
                    departed: Rat::zero(),
                    exact_residual: Rat::zero(),
                }
            })
            .collect::<Vec<_>>();
        let deposited = current_paths
            .iter()
            .fold(Rat::zero(), |sum, path| sum + &path.deposited);

        let momentum_before =
            &material.action.inertia * (&trajectory.current - &trajectory.previous);
        let elastic_impulse = -&material.action.stiffness * &trajectory.current;
        let stress_impulse = &material.stress_response * self.incident_stress(standing, hinge)?;
        let internal_impulse = elastic_impulse + stress_impulse;
        let momentum_after = &momentum_before + &internal_impulse + &deposited;
        let coordinate_after = &trajectory.current + &momentum_after / &material.action.inertia;
        // If this exact local solve lands at rest, its unexpressed transit
        // constituent departs instead of circulating forever as an
        // asymptotically smaller false continuation.  The deposited portion
        // remains embodied in the solved local state; no tolerance or
        // floating-point cutoff participates.
        if coordinate_after == trajectory.current && momentum_after.is_zero() {
            for path in &mut current_paths {
                path.departed = path
                    .emitted
                    .iter()
                    .fold(Rat::zero(), |sum, current| sum + &current.amount);
                path.emitted.clear();
            }
        }
        for path in &mut current_paths {
            let emitted = path
                .emitted
                .iter()
                .fold(Rat::zero(), |sum, current| sum + &current.amount);
            path.exact_residual = &path.entered.amount - &path.deposited - emitted - &path.departed;
            debug_assert!(path.exact_residual.is_zero());
        }
        let mut emitted_currents = current_paths
            .iter()
            .flat_map(|path| path.emitted.iter().cloned())
            .collect::<Vec<_>>();
        sort_current_constituents(&mut emitted_currents);
        let emitted_frontier = current_frontier(&emitted_currents);
        let emitted = emitted_frontier.into_iter().collect::<Vec<_>>();
        let departed = current_paths
            .iter()
            .fold(Rat::zero(), |sum, path| sum + &path.departed);
        let emitted_after = emitted
            .iter()
            .fold(Rat::zero(), |sum, (_, current)| sum + current);
        let exact_current_residual = &entered - &deposited - &emitted_after - &departed;
        let exact_residual = &momentum_after - &momentum_before - &internal_impulse - &deposited;
        debug_assert!(exact_residual.is_zero());
        Ok(LocalSolve {
            hinge,
            trajectory: HingeTrajectory {
                previous: trajectory.current.clone(),
                current: coordinate_after.clone(),
            },
            balance: ActionBalanceReceipt {
                hinge,
                coordinate_before: trajectory.current.clone(),
                coordinate_after: coordinate_after.clone(),
                momentum_before,
                internal_impulse,
                external_impulse: deposited.clone(),
                momentum_after: momentum_after.clone(),
                exact_residual,
                free_momentum_invariant: None,
                stored_boundary_current: momentum_after,
                units: material.action.units.clone(),
            },
            current_balance: LocalCurrentBalance {
                hinge,
                entered,
                deposited,
                emitted,
                departed,
                exact_residual: exact_current_residual,
            },
            current_paths,
            emitted_currents,
            coordinate_change: &coordinate_after - &trajectory.current,
        })
    }

    fn rewrite_candidate(
        &self,
        standing: &LocalStarStanding,
        hinge: HingeId,
        before: &Rat,
        after: &Rat,
    ) -> Option<LocalRewriteCandidate> {
        let crossed = !before.is_zero()
            && (after.is_zero()
                || (before.is_positive() && after.is_negative())
                || (before.is_negative() && after.is_positive()));
        if !crossed {
            return None;
        }
        let complex = &standing.kinematic.complex;
        let hinge_body = complex.hinges.get(&hinge)?;
        let opposite = hinge_body.cofaces.map(|coface| {
            complex.faces[&coface.face]
                .vertices
                .into_iter()
                .find(|vertex| *vertex != hinge_body.edge.lower && *vertex != hinge_body.edge.upper)
                .expect("a valid coface has one opposite vertex")
        });
        if opposite[0] == opposite[1] {
            return None;
        }
        let proposed_diagonal = Edge::new(opposite[0], opposite[1]).ok()?;
        if complex
            .hinges
            .values()
            .any(|body| body.edge == proposed_diagonal)
        {
            return None;
        }
        Some(LocalRewriteCandidate {
            hinge,
            held_boundary: [
                hinge_body.edge.lower,
                opposite[0],
                hinge_body.edge.upper,
                opposite[1],
            ],
            proposed_diagonal,
            reason: LocalRewriteReason::CoordinateCrossedDiscriminant,
        })
    }

    fn receiver_event_nerve(
        &self,
        complex: &crate::SimplicialComplex,
        receivers: &BTreeMap<ReceiverId, ReceiverBodyState>,
        event: EventId,
        active_hinges: &[HingeId],
        changed_faces: &[FaceId],
    ) -> ReceiverEventNerve {
        let mut occurrences = BTreeSet::new();
        for hinge in active_hinges {
            occurrences.insert(ReceiverSharedOccurrence::Hinge(*hinge));
            let body = &complex.hinges[hinge];
            occurrences.insert(ReceiverSharedOccurrence::Vertex(body.edge.lower));
            occurrences.insert(ReceiverSharedOccurrence::Vertex(body.edge.upper));
            for coface in &body.cofaces {
                occurrences.insert(ReceiverSharedOccurrence::Face(coface.face));
            }
        }
        occurrences.extend(
            changed_faces
                .iter()
                .copied()
                .map(ReceiverSharedOccurrence::Face),
        );
        let cells = occurrences
            .into_iter()
            .filter_map(|occurrence| {
                let receivers = receivers
                    .values()
                    .filter(|body| {
                        let Ok(topology) = complex.vertex_star_link(body.anchor) else {
                            return false;
                        };
                        match occurrence {
                            ReceiverSharedOccurrence::Vertex(vertex) => {
                                topology.star_vertices.contains(&vertex)
                            }
                            ReceiverSharedOccurrence::Hinge(hinge) => {
                                topology.star_hinges.contains(&hinge)
                            }
                            ReceiverSharedOccurrence::Face(face) => {
                                topology.star_faces.contains(&face)
                            }
                        }
                    })
                    .map(|body| body.receiver)
                    .collect::<Vec<_>>();
                (!receivers.is_empty()).then_some(ReceiverNerveCell {
                    occurrence,
                    receivers,
                })
            })
            .collect();
        ReceiverEventNerve { event, cells }
    }

    fn enact_topology_deed(
        &self,
        standing_before: &LocalStarStanding,
        event: EventId,
        deed: &LocalTopologyDeed,
        kinematic: &mut HingeWorldStanding,
        spatial: &mut LocalSpatialStanding,
        current_transports: &mut LocalCurrentIncidence,
    ) -> Result<LocalTopologyChange, LocalStarError> {
        let LocalTopologyDeed::AdmitFlip(candidate) = deed;
        if !standing_before.rewrite_openings.contains(candidate) {
            return Err(LocalStarError::RewriteOpeningAbsent(candidate.hinge));
        }
        if self.kinematic.conic_families.values().any(|family| {
            family
                .coefficients
                .iter()
                .any(|coefficient| coefficient.terms.contains_key(&candidate.hinge))
        }) {
            return Err(LocalStarError::TopologyRewriteTouchesAnchoredConic(
                candidate.hinge,
            ));
        }

        let before_complex = kinematic.complex.clone();
        let before_defects = before_complex
            .vertices
            .keys()
            .copied()
            .map(|vertex| Ok((vertex, coordination_defect(&before_complex, vertex)?)))
            .collect::<Result<BTreeMap<_, _>, LocalStarError>>()?;
        let mut after_complex = before_complex.clone();
        let flip = after_complex.flip_hinge(event, candidate.hinge, candidate.proposed_diagonal)?;
        if flip.held_boundary != candidate.held_boundary {
            return Err(LocalStarError::StaleRewriteOpening(candidate.hinge));
        }
        for relation in self.kinematic.transports.relations.values() {
            if !after_complex.hinges_share_face(relation.source, relation.target)? {
                return Err(
                    LocalStarError::TopologyRewriteInvalidatesProjectiveTransport {
                        relation: relation.id,
                        from_hinge: relation.source,
                        to_hinge: relation.target,
                    },
                );
            }
        }
        for body in standing_before.receivers.values() {
            let topology = after_complex.vertex_star_link(body.anchor)?;
            if !topology.star_hinges.contains(&body.port) {
                return Err(LocalStarError::ReceiverPortOutsideStar {
                    receiver: body.receiver,
                    hinge: body.port,
                    anchor: body.anchor,
                });
            }
            let port_edge = after_complex.hinges[&body.port].edge;
            if port_edge.lower != body.anchor && port_edge.upper != body.anchor {
                return Err(LocalStarError::ReceiverPortMissesAnchor {
                    receiver: body.receiver,
                    hinge: body.port,
                    anchor: body.anchor,
                });
            }
            if let Some(coupling) = body
                .couplings
                .iter()
                .find(|coupling| !topology.star_hinges.contains(&coupling.hinge))
            {
                return Err(LocalStarError::ReceiverCouplingOutsideStar {
                    receiver: body.receiver,
                    hinge: coupling.hinge,
                    anchor: body.anchor,
                });
            }
        }

        let mut departed_current_transports = current_transports
            .transports()
            .iter()
            .filter_map(|transport| {
                (!after_complex
                    .hinges_share_face(transport.source, transport.target)
                    .unwrap_or(false))
                .then_some(transport.id)
            })
            .collect::<Vec<_>>();
        departed_current_transports.sort_unstable();
        current_transports.retain(|transport| {
            after_complex
                .hinges_share_face(transport.source, transport.target)
                .unwrap_or(false)
        });
        *spatial = spatial.rewrite_for_complex(&before_complex, &after_complex)?;
        kinematic.complex = after_complex;

        let mut defect_changes = Vec::new();
        let mut charge_residual = 0_i64;
        let mut all_interior = true;
        for vertex in kinematic.complex.vertices.keys().copied() {
            let before = before_defects[&vertex].clone();
            let after = coordination_defect(&kinematic.complex, vertex)?;
            if before == after {
                continue;
            }
            match (&before, &after) {
                (
                    LocalCoordinationDefect::InteriorCycle { charge: before, .. },
                    LocalCoordinationDefect::InteriorCycle { charge: after, .. },
                ) => {
                    charge_residual += after - before;
                }
                _ => all_interior = false,
            }
            defect_changes.push(LocalDefectChange {
                vertex,
                before,
                after,
            });
        }
        Ok(LocalTopologyChange {
            flip,
            defect_changes,
            exact_charge_residual: all_interior.then_some(charge_residual),
            departed_current_transports,
        })
    }
}

impl LocalStarLaw {
    /// Advance exactly one causal antichain. This is an internal factor of a
    /// complete event, not a display or world-clock boundary.
    fn enact_layer(
        &self,
        standing_before: &LocalStarStanding,
        event: &LocalStarEvent,
    ) -> Result<EventSuccessor<LocalStarStanding, LocalStarRadiation>, LocalStarError> {
        let mut incoming = standing_before.open_currents.clone();
        for (hinge, current) in &event.source_currents {
            if !standing_before.kinematic.complex.hinges.contains_key(hinge) {
                return Err(LocalStarError::MissingHinge(*hinge));
            }
            if !current.is_zero() {
                incoming.push(LocalCurrentConstituent {
                    root: LocalCurrentRoot::Source {
                        event: event.event,
                        hinge: *hinge,
                    },
                    hinge: *hinge,
                    amount: current.clone(),
                    word: Vec::new(),
                });
            }
        }
        let mut receiver_deed_sources = BTreeSet::new();
        let mut admitted_traversal_charts = BTreeMap::new();
        for deed in &event.receiver_deeds {
            if !receiver_deed_sources.insert(deed.receiver) {
                return Err(LocalStarError::DuplicateReceiverBoundaryDeed(deed.receiver));
            }
            let body = standing_before
                .receivers
                .get(&deed.receiver)
                .ok_or(LocalStarError::MissingReceiverBody(deed.receiver))?;
            if deed.traversal.source_chart.receiver != deed.receiver {
                return Err(LocalStarError::MisaddressedReceiverTraversal {
                    deed: deed.receiver,
                    chart: deed.traversal.source_chart.receiver,
                });
            }
            let contemporary = standing_before.receiver_traversal_chart(deed.receiver)?;
            let identity_carried = deed.traversal.source_chart.event != contemporary.event;
            if deed.traversal.source_chart != contemporary
                && !deed
                    .traversal
                    .source_chart
                    .carries_by_identity(&contemporary)
            {
                return Err(LocalStarError::StaleReceiverTraversalChart {
                    receiver: deed.receiver,
                    supplied: deed.traversal.source_chart.event,
                    contemporary: contemporary.event,
                });
            }
            admitted_traversal_charts.insert(deed.receiver, (contemporary, identity_carried));
            if !deed.port_current.is_zero() {
                incoming.push(LocalCurrentConstituent {
                    root: LocalCurrentRoot::Receiver {
                        event: event.event,
                        receiver: deed.receiver,
                    },
                    hinge: body.port,
                    amount: deed.port_current.clone(),
                    word: Vec::new(),
                });
            }
        }
        sort_current_constituents(&mut incoming);
        let mut incoming_by_hinge = BTreeMap::<HingeId, Vec<LocalCurrentConstituent>>::new();
        for current in incoming {
            incoming_by_hinge
                .entry(current.hinge)
                .or_default()
                .push(current);
        }
        let active = incoming_by_hinge.keys().copied().collect::<Vec<_>>();
        if event.topology_deeds.len() > 1 {
            return Err(LocalStarError::MultipleTopologyDeeds);
        }
        if !event.topology_deeds.is_empty()
            && (!active.is_empty() || !event.receiver_population.is_empty())
        {
            return Err(LocalStarError::TopologyDeedHasCopresentStructuralChange);
        }
        let (solves, cpu_execution) = self
            .executor
            .execute_indexed(&active, |_index, hinge| {
                self.solve_member(standing_before, *hinge, &incoming_by_hinge[hinge])
            })
            .map_err(|error| match error {
                CpuExecutionError::WorkerPanicked => LocalStarError::CpuWorkerPanicked,
                CpuExecutionError::Operation(error) => error,
            })?;

        let mut assignments = BTreeMap::new();
        let mut trajectories = standing_before.trajectories.clone();
        let mut emitted_currents = Vec::new();
        let mut balances = Vec::new();
        let mut current_balances = Vec::new();
        let mut current_paths = Vec::new();
        let mut coordinate_changes = BTreeMap::new();
        let mut rewrite_candidates = Vec::new();
        for solved in solves {
            assignments.insert(solved.hinge, solved.trajectory.current.clone());
            coordinate_changes.insert(solved.hinge, solved.coordinate_change.clone());
            trajectories.insert(solved.hinge, solved.trajectory);
            emitted_currents.extend(solved.emitted_currents);
            current_paths.extend(solved.current_paths);
            if let Some(candidate) = self.rewrite_candidate(
                standing_before,
                solved.hinge,
                &solved.balance.coordinate_before,
                &solved.balance.coordinate_after,
            ) {
                rewrite_candidates.push(candidate);
            }
            balances.push(solved.balance);
            current_balances.push(solved.current_balance);
        }
        sort_current_constituents(&mut emitted_currents);
        let emitted_frontier = current_frontier(&emitted_currents);

        let (mut kinematic, mut kinematic_radiation) = self
            .kinematic
            .realize_parameter_population(&standing_before.kinematic, event.event, &assignments)?;

        let mut vertex_displacements = BTreeMap::<VertexId, RatVec3>::new();
        let half = Rat::new(1.into(), 2.into());
        for (hinge, change) in &coordinate_changes {
            let body = &standing_before.kinematic.complex.hinges[hinge];
            let displacement = standing_before.geometry_responses[hinge].scale(&(change * &half));
            let lower = vertex_displacements
                .entry(body.edge.lower)
                .or_insert_with(RatVec3::zero);
            *lower = lower.subtract(&displacement);
            let upper = vertex_displacements
                .entry(body.edge.upper)
                .or_insert_with(RatVec3::zero);
            *upper = upper.add(&displacement);
        }
        let mut spatial = standing_before
            .spatial
            .advance(&kinematic.complex, &vertex_displacements)?;
        let mut current_transports = standing_before.current_transports.clone();
        let mut rewrite_openings = standing_before.rewrite_openings.clone();
        let mut topology_changes = Vec::new();
        if let Some(deed) = event.topology_deeds.first() {
            let change = self.enact_topology_deed(
                standing_before,
                event.event,
                deed,
                &mut kinematic,
                &mut spatial,
                &mut current_transports,
            )?;
            let LocalTopologyDeed::AdmitFlip(candidate) = deed;
            rewrite_openings.retain(|opening| opening != candidate);
            kinematic_radiation.changed_hinges.push(change.flip.hinge);
            kinematic_radiation.changed_faces.extend(change.flip.faces);
            topology_changes.push(change);
        }
        for candidate in &rewrite_candidates {
            if !rewrite_openings.contains(candidate) {
                rewrite_openings.push(candidate.clone());
            }
        }
        rewrite_openings.sort_by_key(|candidate| {
            (
                candidate.hinge,
                candidate.proposed_diagonal,
                candidate.held_boundary,
            )
        });
        let faces = self.face_fields(
            &kinematic.complex,
            &kinematic.parameters,
            Some(&standing_before.faces),
        )?;

        let position_before = |receiver: ReceiverId| {
            standing_before
                .receiver_position(receiver)
                .ok_or(LocalStarError::MissingReceiverBody(receiver))
        };
        let mut receivers = standing_before.receivers.clone();
        for body in receivers.values_mut() {
            body.previous_local_offset = body.local_offset.clone();
            body.previous_orientation = body.orientation.clone();
        }
        let mut traversal_receipts = BTreeMap::new();
        for deed in &event.receiver_deeds {
            let body = receivers
                .get_mut(&deed.receiver)
                .ok_or(LocalStarError::MissingReceiverBody(deed.receiver))?;
            let (chart, identity_carried) = admitted_traversal_charts
                .get(&deed.receiver)
                .expect("every receiver deed was chart-validated");
            let port = &chart.acceptance.port_section;
            let mut world_translation = RatVec3::zero();
            for step in &deed.traversal.steps {
                apply_receiver_traversal_step(body, port, step, &mut world_translation)?;
            }
            traversal_receipts.insert(
                deed.receiver,
                ReceiverTraversalReceipt {
                    source_chart_event: deed.traversal.source_chart.event,
                    enacted_chart_event: chart.event,
                    identity_carried: *identity_carried,
                    steps: deed.traversal.steps.clone(),
                    world_translation,
                    port_current: deed.port_current.clone(),
                },
            );
        }
        for body in receivers.values_mut() {
            for coupling in &body.couplings {
                let Some(change) = coordinate_changes.get(&coupling.hinge) else {
                    continue;
                };
                body.local_offset = body
                    .local_offset
                    .add(&coupling.translation_per_turn.scale(change));
                for rotation in &coupling.rotations_per_turn {
                    body.orientation.precess(
                        rotation.axis,
                        &ProjectiveRatio::from_rat(&(&rotation.cayley_per_turn * change)),
                    );
                }
            }
        }
        let mut receiver_worldlines = Vec::new();
        for (receiver, body) in &receivers {
            let anchor = spatial.position(&kinematic.complex, body.anchor)?;
            receiver_worldlines.push(ReceiverWorldlineStep {
                receiver: *receiver,
                position_before: position_before(*receiver)?,
                position_after: anchor.add(&body.local_offset),
                orientation_before: standing_before.receivers[receiver].orientation.clone(),
                orientation_after: body.orientation.clone(),
                traversal: traversal_receipts.remove(receiver),
            });
        }

        let mut population_receivers = BTreeSet::new();
        for deed in &event.receiver_population {
            let receiver = match deed {
                ReceiverPopulationDeed::Found(founding) => founding.receiver,
                ReceiverPopulationDeed::Depart { receiver }
                | ReceiverPopulationDeed::Reanchor { receiver, .. } => *receiver,
            };
            if !population_receivers.insert(receiver) {
                return Err(LocalStarError::DuplicateReceiverPopulationDeed(receiver));
            }
        }
        let mut receiver_population = Vec::new();
        for deed in &event.receiver_population {
            match deed {
                ReceiverPopulationDeed::Found(founding) => {
                    if receivers.contains_key(&founding.receiver) {
                        return Err(LocalStarError::DuplicateReceiverBody);
                    }
                    let body = self.found_receiver(founding, &kinematic.complex, &spatial)?;
                    let topology = kinematic.complex.vertex_star_link(body.anchor)?;
                    receiver_population.push(ReceiverPopulationChange::Founded {
                        receiver: body.receiver,
                        source_event: body.source_event,
                        anchor: body.anchor,
                        topology,
                    });
                    receivers.insert(body.receiver, body);
                }
                ReceiverPopulationDeed::Depart { receiver } => {
                    receivers
                        .remove(receiver)
                        .ok_or(LocalStarError::MissingReceiverBody(*receiver))?;
                    receiver_population.push(ReceiverPopulationChange::Departed {
                        receiver: *receiver,
                    });
                }
                ReceiverPopulationDeed::Reanchor { receiver, anchor } => {
                    if !spatial.capacities.contains_key(anchor) {
                        return Err(LocalStarError::MissingVertexPosition(*anchor));
                    }
                    let body = receivers
                        .get_mut(receiver)
                        .ok_or(LocalStarError::MissingReceiverBody(*receiver))?;
                    let previous_anchor = body.anchor;
                    let position = spatial
                        .position(&kinematic.complex, body.anchor)?
                        .add(&body.local_offset);
                    let topology = kinematic.complex.vertex_star_link(*anchor)?;
                    if !topology.star_hinges.contains(&body.port) {
                        return Err(LocalStarError::ReceiverPortOutsideStar {
                            receiver: *receiver,
                            hinge: body.port,
                            anchor: *anchor,
                        });
                    }
                    let port_edge = kinematic.complex.hinges[&body.port].edge;
                    if port_edge.lower != *anchor && port_edge.upper != *anchor {
                        return Err(LocalStarError::ReceiverPortMissesAnchor {
                            receiver: *receiver,
                            hinge: body.port,
                            anchor: *anchor,
                        });
                    }
                    if let Some(coupling) = body
                        .couplings
                        .iter()
                        .find(|coupling| !topology.star_hinges.contains(&coupling.hinge))
                    {
                        return Err(LocalStarError::ReceiverCouplingOutsideStar {
                            receiver: *receiver,
                            hinge: coupling.hinge,
                            anchor: *anchor,
                        });
                    }
                    let local_offset =
                        position.subtract(&spatial.position(&kinematic.complex, *anchor)?);
                    body.anchor = *anchor;
                    body.local_offset = local_offset.clone();
                    body.previous_local_offset = local_offset;
                    receiver_population.push(ReceiverPopulationChange::Reanchored {
                        receiver: *receiver,
                        from: previous_anchor,
                        to: *anchor,
                        topology,
                    });
                }
            }
        }

        for body in receivers.values_mut() {
            body.physical_phase = self.receiver_physical_phase(body, &trajectories, &balances)?;
        }
        let receiver_nerve = self.receiver_event_nerve(
            &kinematic.complex,
            &receivers,
            event.event,
            &active,
            &kinematic_radiation.changed_faces,
        );
        let standing_after = LocalStarStanding {
            schema: standing_before.schema.clone(),
            event: event.event,
            kinematic,
            trajectories,
            spatial,
            current_transports,
            geometry_responses: standing_before.geometry_responses.clone(),
            faces: faces.clone(),
            receivers,
            rewrite_openings,
            open_currents: emitted_currents.clone(),
        };
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![LocalStarRadiation {
                event: event.event,
                causal_layers: Vec::new(),
                propagation_boundary: LocalPropagationBoundary::CyclicSupportOpen {
                    causal_layers: 1,
                },
                active_hinges: active,
                balances,
                current_balances,
                current_paths,
                face_fields: faces,
                receiver_worldlines,
                receiver_nerve,
                receiver_population,
                topology_changes,
                rewrite_candidates,
                open_frontier: emitted_frontier,
                cpu_execution,
                kinematic: kinematic_radiation,
            }],
            logical_resources: None,
            physical_resources: None,
        })
    }
}

impl LocalStarLaw {
    /// Close the causal incidence front opened by one supplied event.
    ///
    /// An antichain is locally parallel; successive antichains remain ordered
    /// because each consumes the preceding successor. The front therefore
    /// propagates across the bounded complex without borrowing ticks from the
    /// presentation loop. Exact rest and exact return close it. If live
    /// support survives more layers than there are hinges, a repeated hinge
    /// support is forced combinatorially and the current returns as a named
    /// open cyclic boundary.
    fn enact_frontier(
        &self,
        standing_before: &LocalStarStanding,
        event: &LocalStarEvent,
    ) -> Result<EventSuccessor<LocalStarStanding, LocalStarRadiation>, LocalStarError> {
        let horizon = standing_before
            .kinematic
            .complex
            .hinges
            .len()
            .saturating_add(1)
            .max(1);
        let mut standing = standing_before.clone();
        let mut seen = vec![standing.clone()];
        let mut layers = Vec::new();
        let mut boundary = None;

        for ordinal in 0..horizon {
            let layer_event = if ordinal == 0 {
                event.clone()
            } else {
                LocalStarEvent::continuation(event.event)
            };
            let mut successor = self.enact_layer(&standing, &layer_event)?;
            let radiation = successor
                .radiation
                .pop()
                .expect("one causal antichain emits one local radiation");
            standing = successor.standing_after;
            layers.push(radiation);

            if standing.open_currents.is_empty() {
                boundary = Some(LocalPropagationBoundary::Rest {
                    causal_layers: layers.len(),
                });
                break;
            }
            if let Some(returned_to_layer) = seen.iter().position(|prior| prior == &standing) {
                boundary = Some(LocalPropagationBoundary::ExactReturn {
                    causal_layers: layers.len(),
                    returned_to_layer,
                });
                break;
            }
            seen.push(standing.clone());
        }

        let boundary = boundary.unwrap_or(LocalPropagationBoundary::CyclicSupportOpen {
            causal_layers: layers.len(),
        });
        let radiation = merge_causal_layers(event.event, layers, boundary);
        Ok(EventSuccessor {
            standing_after: standing,
            radiation: vec![radiation],
            logical_resources: None,
            physical_resources: None,
        })
    }
}

fn merge_causal_layers(
    event: EventId,
    mut layers: Vec<LocalStarRadiation>,
    propagation_boundary: LocalPropagationBoundary,
) -> LocalStarRadiation {
    let receipts = layers
        .iter()
        .enumerate()
        .map(|(ordinal, layer)| LocalCausalLayerReceipt {
            ordinal,
            active_hinges: layer.active_hinges.clone(),
            emitted_frontier: layer.open_frontier.clone(),
            emitted_currents: layer
                .current_paths
                .iter()
                .flat_map(|path| path.emitted.iter().cloned())
                .collect(),
            cpu_execution: layer.cpu_execution.clone(),
        })
        .collect::<Vec<_>>();
    let cpu_execution = CpuExecutionReceipt::ordered_antichains(
        &receipts
            .iter()
            .map(|receipt| receipt.cpu_execution.clone())
            .collect::<Vec<_>>(),
    );
    let mut merged = layers
        .drain(..1)
        .next()
        .expect("a complete event always evaluates at least one antichain");
    for layer in layers {
        merged.active_hinges.extend(layer.active_hinges);
        merged.balances.extend(layer.balances);
        merged.current_balances.extend(layer.current_balances);
        merged.current_paths.extend(layer.current_paths);
        merged.face_fields = layer.face_fields;
        merged.receiver_worldlines.extend(layer.receiver_worldlines);
        merged
            .receiver_nerve
            .cells
            .extend(layer.receiver_nerve.cells);
        merged.receiver_population.extend(layer.receiver_population);
        merged.topology_changes.extend(layer.topology_changes);
        merged.rewrite_candidates.extend(layer.rewrite_candidates);
        merged.open_frontier = layer.open_frontier;
        merged
            .kinematic
            .changed_hinges
            .extend(layer.kinematic.changed_hinges);
        merged
            .kinematic
            .changed_faces
            .extend(layer.kinematic.changed_faces);
        merged
            .kinematic
            .changed_conics
            .extend(layer.kinematic.changed_conics);
        merged
            .kinematic
            .transported_candidates
            .extend(layer.kinematic.transported_candidates);
        merged
            .kinematic
            .cycle_returns
            .extend(layer.kinematic.cycle_returns);
        merged
            .kinematic
            .open_seams
            .extend(layer.kinematic.open_seams);
        merged.kinematic.exact_transport_evaluations += layer.kinematic.exact_transport_evaluations;
    }
    merged.event = event;
    merged.causal_layers = receipts;
    merged.propagation_boundary = propagation_boundary;
    merged.cpu_execution = cpu_execution;
    merged
}

impl ExactEventLaw for LocalStarLaw {
    type Standing = LocalStarStanding;
    type Event = LocalStarEvent;
    type Radiation = LocalStarRadiation;
    type Error = LocalStarError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        self.enact_frontier(standing_before, event)
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum LocalStarError {
    #[error("hinge {0:?} is absent from the local-star world")]
    MissingHinge(HingeId),
    #[error("hinge {0:?} has no local constitutive material")]
    MissingMaterial(HingeId),
    #[error("hinge {0:?} has no carried trajectory")]
    MissingTrajectory(HingeId),
    #[error("hinge {0:?}'s trajectory disagrees with its kinematic standing")]
    TrajectoryStandingMismatch(HingeId),
    #[error("vertex {0:?} has no exact bounded-chart position")]
    MissingVertexPosition(VertexId),
    #[error("relative spatial standing has no carrier for edge {0:?}")]
    MissingSpatialEdge(Edge),
    #[error("relative spatial standing requires at least one caused vertex")]
    EmptySpatialComplex,
    #[error("face {0:?} has no carried field state")]
    MissingFaceState(FaceId),
    #[error("face boundary edge {0:?} has no declared hinge carrier")]
    MissingBoundaryHinge(Edge),
    #[error("current transport {from_hinge:?}->{to_hinge:?} is not one local incidence")]
    NonlocalCurrentTransport {
        from_hinge: HingeId,
        to_hinge: HingeId,
    },
    #[error("local current transport hand must be -1, 0, or 1, got {0}")]
    InvalidTransportHand(i8),
    #[error("receiver {0:?} has no embodied field state")]
    MissingReceiverBody(ReceiverId),
    #[error("receiver {0:?} supplied more than one boundary deed in one event")]
    DuplicateReceiverBoundaryDeed(ReceiverId),
    #[error("receiver deed {deed:?} carries a traversal chart addressed to {chart:?}")]
    MisaddressedReceiverTraversal { deed: ReceiverId, chart: ReceiverId },
    #[error(
        "receiver {receiver:?} traversal captured chart event {supplied:?}, but contemporary chart event {contemporary:?} has no declared exact connection"
    )]
    StaleReceiverTraversalChart {
        receiver: ReceiverId,
        supplied: EventId,
        contemporary: EventId,
    },
    #[error("a receiver traversal run must contain at least one occurrence")]
    EmptyReceiverTraversalRun,
    #[error("receiver traversal runs cannot recursively contain another run")]
    NestedReceiverTraversalRun,
    #[error("one receiver body was supplied more than once")]
    DuplicateReceiverBody,
    #[error("receiver {receiver:?}'s port {hinge:?} is outside the star at {anchor:?}")]
    ReceiverPortOutsideStar {
        receiver: ReceiverId,
        hinge: HingeId,
        anchor: VertexId,
    },
    #[error("receiver {receiver:?}'s port {hinge:?} does not meet its anchor {anchor:?}")]
    ReceiverPortMissesAnchor {
        receiver: ReceiverId,
        hinge: HingeId,
        anchor: VertexId,
    },
    #[error(
        "receiver {receiver:?}'s direction to link vertex {vertex:?} leaves its spatial component"
    )]
    ReceiverDirectionOutsideComponent {
        receiver: ReceiverId,
        vertex: VertexId,
    },
    #[error("receiver {receiver:?}'s port section at hinge {hinge:?} is spatially collapsed")]
    CollapsedReceiverPortSection {
        receiver: ReceiverId,
        hinge: HingeId,
    },
    #[error("receiver {receiver:?}'s coupling {hinge:?} is outside the star at {anchor:?}")]
    ReceiverCouplingOutsideStar {
        receiver: ReceiverId,
        hinge: HingeId,
        anchor: VertexId,
    },
    #[error("receiver {0:?} has more than one population deed in one event")]
    DuplicateReceiverPopulationDeed(ReceiverId),
    #[error("event supplied more than one topology deed; their causal order is undefined")]
    MultipleTopologyDeeds,
    #[error("a topology deed cannot be co-present with active current or a population deed")]
    TopologyDeedHasCopresentStructuralChange,
    #[error("hinge {0:?} has no open rewrite mouth in contemporary standing")]
    RewriteOpeningAbsent(HingeId),
    #[error("hinge {0:?}'s open rewrite mouth no longer matches contemporary incidence")]
    StaleRewriteOpening(HingeId),
    #[error("hinge {0:?} carries a native conic whose rewrite transport is undeclared")]
    TopologyRewriteTouchesAnchoredConic(HingeId),
    #[error(
        "topology rewrite makes projective relation {relation:?} ({from_hinge:?}->{to_hinge:?}) nonlocal"
    )]
    TopologyRewriteInvalidatesProjectiveTransport {
        relation: HingeTransportId,
        from_hinge: HingeId,
        to_hinge: HingeId,
    },
    #[error("one physical CPU worker failed before returning its local star")]
    CpuWorkerPanicked,
    #[error(transparent)]
    Simplicial(#[from] SimplicialError),
    #[error(transparent)]
    Kinematic(#[from] HingeWorldError),
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;
    use std::collections::BTreeSet;
    use std::num::NonZeroUsize;

    use relational_geometry::integer;

    use super::*;
    use crate::{CausalWorld, HingeTransportNetwork, HingeUnitSystem, SimplicialComplex};

    fn rotation_couplings(components: RatVec3) -> Vec<ReceiverRotationCoupling> {
        [
            (ReceiverRotationAxis::X, components.x),
            (ReceiverRotationAxis::Y, components.y),
            (ReceiverRotationAxis::Z, components.z),
        ]
        .into_iter()
        .filter(|(_, coefficient)| !coefficient.is_zero())
        .map(|(axis, cayley_per_turn)| ReceiverRotationCoupling {
            axis,
            cayley_per_turn,
        })
        .collect()
    }

    fn receiver_deed(
        standing: &LocalStarStanding,
        receiver: ReceiverId,
        port_current: Rat,
        steps: Vec<ReceiverTraversalStep>,
    ) -> ReceiverBoundaryDeed {
        ReceiverBoundaryDeed {
            receiver,
            traversal: ReceiverTraversalOccurrence {
                source_chart: standing.receiver_traversal_chart(receiver).unwrap(),
                steps,
            },
            port_current,
        }
    }

    fn octahedral_law(executor: CpuExecutor) -> (LocalStarLaw, LocalStarStanding, Vec<HingeId>) {
        let founding = EventId(1);
        let mut complex = SimplicialComplex::default();
        let a = complex.found_vertex("a", founding);
        let b = complex.found_vertex("b", founding);
        let c = complex.found_vertex("c", founding);
        let d = complex.found_vertex("d", founding);
        let e = complex.found_vertex("e", founding);
        let f = complex.found_vertex("f", founding);
        complex.found_face("eab", founding, [e, a, b]).unwrap();
        complex.found_face("ebc", founding, [e, b, c]).unwrap();
        complex.found_face("ecd", founding, [e, c, d]).unwrap();
        complex.found_face("eda", founding, [e, d, a]).unwrap();
        complex.found_face("fba", founding, [f, b, a]).unwrap();
        complex.found_face("fcb", founding, [f, c, b]).unwrap();
        complex.found_face("fdc", founding, [f, d, c]).unwrap();
        complex.found_face("fad", founding, [f, a, d]).unwrap();
        let positions = BTreeMap::from([
            (a, RatVec3::from_i64(-3, -2, 6)),
            (b, RatVec3::from_i64(3, -2, 6)),
            (c, RatVec3::from_i64(0, 3, 7)),
            (d, RatVec3::from_i64(0, -3, 7)),
            (e, RatVec3::from_i64(0, 0, 11)),
            (f, RatVec3::from_i64(0, 0, 3)),
        ]);
        let edges = complex
            .faces
            .values()
            .flat_map(|face| face.boundary().map(|(edge, _)| edge))
            .collect::<BTreeSet<_>>();
        let mut hinges = Vec::new();
        for edge in edges {
            hinges.push(
                complex
                    .found_hinge("tetrahedral hinge", founding, edge)
                    .unwrap(),
            );
        }
        let kinematic =
            HingeWorldLaw::new(complex, HingeTransportNetwork::default(), Vec::new()).unwrap();
        let parameters = hinges
            .iter()
            .map(|hinge| (*hinge, integer(0)))
            .collect::<BTreeMap<_, _>>();
        let kinematic_standing = kinematic.initial_standing(parameters).unwrap();
        let units = HingeUnitSystem {
            coordinate: "turn".to_owned(),
            event_step: "event".to_owned(),
            action: "action".to_owned(),
            momentum: "action/turn".to_owned(),
            impulse: "action/turn".to_owned(),
        };
        let materials = hinges
            .iter()
            .enumerate()
            .map(|(index, hinge)| {
                (
                    *hinge,
                    LocalStarMaterial {
                        action: QuadraticHingeAction::new(
                            integer(2 + i64::try_from(index % 2).unwrap()),
                            integer(1),
                            units.clone(),
                        )
                        .unwrap(),
                        stress_response: integer(1) / integer(4),
                        geometry_response: match index % 3 {
                            0 => RatVec3::from_i64(1, 0, 0),
                            1 => RatVec3::from_i64(0, 1, 0),
                            _ => RatVec3::from_i64(0, 0, 1),
                        },
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        let field_axis = RatVec3::from_i64(1, 2, 4);
        let hinge_potential = hinges
            .iter()
            .map(|hinge| {
                let edge = kinematic.complex.hinges[hinge].edge;
                (
                    *hinge,
                    positions[&edge.lower]
                        .add(&positions[&edge.upper])
                        .dot(&field_axis),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut transports = Vec::new();
        for source in &hinges {
            let adjacent = hinges
                .iter()
                .filter(|target| {
                    **target != *source
                        && kinematic
                            .complex
                            .hinges_share_face(*source, **target)
                            .unwrap()
                })
                .copied()
                .collect::<Vec<_>>();
            for hand in [-1, 1] {
                let targets = adjacent
                    .iter()
                    .copied()
                    .filter(|target| {
                        (hand == 1 && hinge_potential[target] < hinge_potential[source])
                            || (hand == -1 && hinge_potential[target] > hinge_potential[source])
                    })
                    .collect::<Vec<_>>();
                if targets.is_empty() {
                    continue;
                }
                let coefficient = Rat::new(3.into(), (4 * targets.len()).into());
                transports.extend(targets.into_iter().map(|target| {
                    LocalCurrentTransport::with_hand(*source, target, hand, coefficient.clone())
                }));
            }
        }
        let first_port = hinges
            .iter()
            .copied()
            .find(|hinge| {
                let edge = kinematic.complex.hinges[hinge].edge;
                edge.lower == e || edge.upper == e
            })
            .unwrap();
        let second_port = hinges
            .iter()
            .rev()
            .copied()
            .find(|hinge| {
                let edge = kinematic.complex.hinges[hinge].edge;
                edge.lower == f || edge.upper == f
            })
            .unwrap();
        let law = LocalStarLaw::new(kinematic, materials, transports, executor).unwrap();
        let trajectories = hinges
            .iter()
            .map(|hinge| {
                (
                    *hinge,
                    HingeTrajectory {
                        previous: integer(0),
                        current: integer(0),
                    },
                )
            })
            .collect();
        let founding = |receiver, anchor, port, coupling| ReceiverFounding {
            receiver,
            source_event: founding,
            anchor,
            port,
            couplings: vec![coupling],
            local_offset: RatVec3::zero(),
            orientation: ReceiverOrientation::identity(),
        };
        let standing = law
            .initial_standing(
                kinematic_standing,
                trajectories,
                positions,
                vec![
                    founding(
                        ReceiverId(1),
                        e,
                        first_port,
                        ReceiverLocalCoupling {
                            hinge: hinges[0],
                            translation_per_turn: RatVec3::from_i64(0, 0, 1),
                            rotations_per_turn: rotation_couplings(RatVec3::from_i64(1, 0, 0)),
                        },
                    ),
                    founding(
                        ReceiverId(2),
                        f,
                        second_port,
                        ReceiverLocalCoupling {
                            hinge: second_port,
                            translation_per_turn: RatVec3::from_i64(0, 1, 0),
                            rotations_per_turn: rotation_couplings(RatVec3::from_i64(0, 1, 0)),
                        },
                    ),
                ],
            )
            .unwrap();
        (law, standing, hinges)
    }

    #[test]
    fn current_incidence_exposes_only_the_source_star_and_remount_canonicalizes_storage() {
        let (law, _, hinges) = octahedral_law(CpuExecutor::serial());
        for hinge in hinges {
            let expected = law
                .transports
                .transports()
                .iter()
                .filter(|transport| transport.source == hinge)
                .cloned()
                .collect::<Vec<_>>();
            assert_eq!(law.transports.outgoing(hinge), expected);
        }

        let mut reversed = law.transports.transports().to_vec();
        reversed.reverse();
        let wire = ron::ser::to_string(&reversed).unwrap();
        let remounted: LocalCurrentIncidence = ron::from_str(&wire).unwrap();
        assert_eq!(remounted, law.transports);
    }

    #[test]
    fn one_event_advances_its_complete_local_front_and_changes_geometry() {
        let (law, standing, hinges) = octahedral_law(CpuExecutor::serial());
        let before = standing.spatial.clone();
        let mut world = CausalWorld::new(law, standing);
        let first = world
            .receive(&LocalStarEvent {
                event: EventId(2),
                source_currents: BTreeMap::from([(hinges[0], integer(1))]),
                receiver_deeds: Vec::new(),
                receiver_population: Vec::new(),
                topology_deeds: Vec::new(),
            })
            .unwrap()
            .radiation
            .remove(0);
        assert_eq!(first.causal_layers[0].active_hinges, vec![hinges[0]]);
        assert!(first.causal_layers.len() > 1);
        assert!(
            first
                .current_balances
                .iter()
                .all(|balance| balance.exact_residual.is_zero())
        );
        assert!(first.open_frontier.is_empty());
        assert_eq!(
            first.propagation_boundary,
            LocalPropagationBoundary::Rest {
                causal_layers: first.causal_layers.len(),
            }
        );
        assert!(first.cpu_execution.tasks > 1_u8.into());
        assert_ne!(world.standing().spatial, before);
    }

    #[test]
    fn repeated_local_support_returns_one_open_boundary_without_display_ticks() {
        let (seed_law, standing, hinges) = octahedral_law(CpuExecutor::serial());
        let source = hinges[0];
        let target = hinges
            .iter()
            .copied()
            .find(|candidate| {
                *candidate != source
                    && seed_law
                        .kinematic
                        .complex
                        .hinges_share_face(source, *candidate)
                        .unwrap()
            })
            .expect("the octahedral source hinge has an adjacent hinge");
        let half = integer(1) / integer(2);
        let law = LocalStarLaw::new(
            seed_law.kinematic,
            seed_law.materials,
            vec![
                LocalCurrentTransport::new(source, target, half.clone()),
                LocalCurrentTransport::new(target, source, half),
            ],
            CpuExecutor::serial(),
        )
        .unwrap();
        let mut standing = standing;
        standing.current_transports = law.transports.clone();
        let radiation = law
            .enact(
                &standing,
                &LocalStarEvent {
                    event: EventId(2),
                    source_currents: BTreeMap::from([(source, integer(1))]),
                    receiver_deeds: Vec::new(),
                    receiver_population: Vec::new(),
                    topology_deeds: Vec::new(),
                },
            )
            .unwrap()
            .radiation
            .remove(0);

        assert_eq!(
            radiation.causal_layers.len(),
            law.kinematic.complex.hinges.len() + 1
        );
        assert_eq!(
            radiation.propagation_boundary,
            LocalPropagationBoundary::CyclicSupportOpen {
                causal_layers: radiation.causal_layers.len(),
            }
        );
        assert!(!radiation.open_frontier.is_empty());
        assert!(
            radiation
                .current_balances
                .iter()
                .all(|balance| balance.exact_residual.is_zero())
        );
    }

    #[test]
    fn serial_and_multicore_local_star_merges_are_exactly_identical() {
        let (serial_law, standing, hinges) = octahedral_law(CpuExecutor::serial());
        let (parallel_law, parallel_standing, parallel_hinges) =
            octahedral_law(CpuExecutor::multicore(NonZeroUsize::new(4).unwrap()));
        assert_eq!(hinges, parallel_hinges);
        assert_eq!(standing, parallel_standing);
        let event = LocalStarEvent {
            event: EventId(2),
            source_currents: BTreeMap::from([(hinges[0], integer(1)), (hinges[5], integer(-1))]),
            receiver_deeds: Vec::new(),
            receiver_population: Vec::new(),
            topology_deeds: Vec::new(),
        };
        let serial = serial_law.enact(&standing, &event).unwrap();
        let parallel = parallel_law.enact(&parallel_standing, &event).unwrap();
        assert_eq!(serial.standing_after, parallel.standing_after);
        let mut serial_radiation = serial.radiation[0].clone();
        let parallel_radiation = &parallel.radiation[0];
        assert_eq!(
            serial_radiation.active_hinges,
            parallel_radiation.active_hinges
        );
        assert_eq!(serial_radiation.balances, parallel_radiation.balances);
        assert_eq!(
            serial_radiation.current_balances,
            parallel_radiation.current_balances
        );
        assert_eq!(
            serial_radiation.receiver_worldlines,
            parallel_radiation.receiver_worldlines
        );
        assert_eq!(
            serial_radiation.open_frontier,
            parallel_radiation.open_frontier
        );
        for (serial_layer, parallel_layer) in serial_radiation
            .causal_layers
            .iter_mut()
            .zip(&parallel_radiation.causal_layers)
        {
            serial_layer.cpu_execution = parallel_layer.cpu_execution.clone();
        }
        serial_radiation.cpu_execution = parallel_radiation.cpu_execution.clone();
        assert_eq!(serial_radiation, *parallel_radiation);
        assert!(parallel_radiation.cpu_execution.workers_used > 1_u8.into());
    }

    #[test]
    fn receiver_deeds_enter_through_ports_without_recentring_physical_standing() {
        let (law, standing, _) = octahedral_law(CpuExecutor::serial());
        let before_first = standing.receiver_position(ReceiverId(1)).unwrap();
        let before_second = standing.receiver_position(ReceiverId(2)).unwrap();
        let successor = law
            .enact(
                &standing,
                &LocalStarEvent {
                    event: EventId(2),
                    source_currents: BTreeMap::new(),
                    receiver_deeds: vec![receiver_deed(
                        &standing,
                        ReceiverId(1),
                        integer(1),
                        vec![
                            ReceiverTraversalStep::Translate {
                                coordinates: RatVec3::from_i64(1, 0, 0),
                            },
                            ReceiverTraversalStep::Rotate {
                                axis: ReceiverRotationAxis::Z,
                                ratio: ProjectiveRatio::from_rat(&integer(1)),
                            },
                        ],
                    )],
                    receiver_population: Vec::new(),
                    topology_deeds: Vec::new(),
                },
            )
            .unwrap();
        let after = successor.standing_after;
        assert_ne!(
            after.receiver_position(ReceiverId(1)).unwrap(),
            before_first
        );
        assert_eq!(
            successor.radiation[0].receiver_worldlines[0].position_before,
            before_first
        );
        // Receiver two has no copied control deed. It moves only if its own
        // anchor/coupled local field moves.
        assert_eq!(
            successor.radiation[0].receiver_worldlines[1].position_before,
            before_second
        );
    }

    #[test]
    fn receiver_traversal_preserves_noncommutative_step_order_in_radiation() {
        let (law, standing, _) = octahedral_law(CpuExecutor::serial());
        let steps = vec![
            ReceiverTraversalStep::Rotate {
                axis: ReceiverRotationAxis::X,
                ratio: ProjectiveRatio::from_rat(&(integer(1) / integer(3))),
            },
            ReceiverTraversalStep::Rotate {
                axis: ReceiverRotationAxis::Y,
                ratio: ProjectiveRatio::from_rat(&(integer(1) / integer(5))),
            },
            ReceiverTraversalStep::Rotate {
                axis: ReceiverRotationAxis::X,
                ratio: ProjectiveRatio::from_rat(&(integer(1) / integer(7))),
            },
        ];
        let successor = law
            .enact(
                &standing,
                &LocalStarEvent {
                    event: EventId(2),
                    source_currents: BTreeMap::new(),
                    receiver_deeds: vec![receiver_deed(
                        &standing,
                        ReceiverId(1),
                        Rat::zero(),
                        steps.clone(),
                    )],
                    receiver_population: Vec::new(),
                    topology_deeds: Vec::new(),
                },
            )
            .unwrap();
        let worldline = successor.radiation[0]
            .receiver_worldlines
            .iter()
            .find(|step| step.receiver == ReceiverId(1))
            .unwrap();
        assert_eq!(worldline.traversal.as_ref().unwrap().steps, steps);
        assert_ne!(
            worldline.orientation_after,
            standing.receivers[&ReceiverId(1)].orientation
        );
    }

    #[test]
    fn repeated_traversal_generator_matches_the_complete_elementary_word() {
        let (law, standing, _) = octahedral_law(CpuExecutor::serial());
        let generator = ReceiverTraversalStep::Rotate {
            axis: ReceiverRotationAxis::Z,
            ratio: ProjectiveRatio::from_rat(&(integer(1) / integer(16))),
        };
        let explicit = law
            .enact(
                &standing,
                &LocalStarEvent {
                    event: EventId(2),
                    source_currents: BTreeMap::new(),
                    receiver_deeds: vec![receiver_deed(
                        &standing,
                        ReceiverId(1),
                        Rat::zero(),
                        vec![generator.clone(); 37],
                    )],
                    receiver_population: Vec::new(),
                    topology_deeds: Vec::new(),
                },
            )
            .unwrap();
        let compressed = law
            .enact(
                &standing,
                &LocalStarEvent {
                    event: EventId(2),
                    source_currents: BTreeMap::new(),
                    receiver_deeds: vec![receiver_deed(
                        &standing,
                        ReceiverId(1),
                        Rat::zero(),
                        vec![ReceiverTraversalStep::Repeat {
                            generator: Box::new(generator),
                            repetitions: BigUint::from(37_u8),
                        }],
                    )],
                    receiver_population: Vec::new(),
                    topology_deeds: Vec::new(),
                },
            )
            .unwrap();
        assert_eq!(compressed.standing_after, explicit.standing_after);
        assert_eq!(
            compressed.radiation[0].receiver_worldlines[0].orientation_after,
            explicit.radiation[0].receiver_worldlines[0].orientation_after
        );
    }

    #[test]
    fn an_unchanged_chart_carries_across_rest_but_a_changed_chart_refuses_stale_input() {
        let (law, standing, _) = octahedral_law(CpuExecutor::serial());
        let captured = receiver_deed(
            &standing,
            ReceiverId(1),
            Rat::zero(),
            vec![ReceiverTraversalStep::Rotate {
                axis: ReceiverRotationAxis::Y,
                ratio: ProjectiveRatio::from_rat(&(integer(1) / integer(11))),
            }],
        );
        let rest = law
            .enact(&standing, &LocalStarEvent::continuation(EventId(2)))
            .unwrap()
            .standing_after;
        let carried = law
            .enact(
                &rest,
                &LocalStarEvent {
                    event: EventId(3),
                    source_currents: BTreeMap::new(),
                    receiver_deeds: vec![captured.clone()],
                    receiver_population: Vec::new(),
                    topology_deeds: Vec::new(),
                },
            )
            .unwrap();
        let receipt = carried.radiation[0]
            .receiver_worldlines
            .iter()
            .find(|step| step.receiver == ReceiverId(1))
            .unwrap()
            .traversal
            .as_ref()
            .unwrap();
        assert!(receipt.identity_carried);
        assert_eq!(receipt.source_chart_event, standing.event);
        assert_eq!(receipt.enacted_chart_event, rest.event);

        let changed = carried.standing_after;
        assert!(matches!(
            law.enact(
                &changed,
                &LocalStarEvent {
                    event: EventId(4),
                    source_currents: BTreeMap::new(),
                    receiver_deeds: vec![captured],
                    receiver_population: Vec::new(),
                    topology_deeds: Vec::new(),
                },
            ),
            Err(LocalStarError::StaleReceiverTraversalChart {
                receiver: ReceiverId(1),
                ..
            })
        ));
    }

    #[test]
    fn receiver_population_is_caused_and_its_event_nerve_retains_higher_incidence() {
        let (law, standing, _) = octahedral_law(CpuExecutor::serial());
        let anchors = standing
            .kinematic
            .complex
            .vertices
            .keys()
            .copied()
            .filter(|vertex| {
                !standing
                    .receivers
                    .values()
                    .any(|body| body.anchor == *vertex)
            })
            .take(2)
            .collect::<Vec<_>>();
        let first_topology = standing
            .kinematic
            .complex
            .vertex_star_link(anchors[0])
            .unwrap();
        let second_topology = standing
            .kinematic
            .complex
            .vertex_star_link(anchors[1])
            .unwrap();
        let shared_port = first_topology
            .star_hinges
            .intersection(&second_topology.star_hinges)
            .next()
            .copied()
            .expect("neighboring stars share an actual incidence");
        assert_eq!(first_topology.link_class, crate::VertexLinkClass::Cycle);

        let mut world = CausalWorld::new(law, standing);
        let founding = ReceiverFounding {
            receiver: ReceiverId(3),
            source_event: EventId(2),
            anchor: anchors[0],
            port: shared_port,
            couplings: vec![ReceiverLocalCoupling {
                hinge: shared_port,
                translation_per_turn: RatVec3::from_i64(1, 1, 0),
                rotations_per_turn: rotation_couplings(RatVec3::from_i64(0, 1, 1)),
            }],
            local_offset: RatVec3::from_i64(1, 2, 3),
            orientation: ReceiverOrientation::identity(),
        };
        let founded = world
            .receive(&LocalStarEvent {
                event: EventId(2),
                source_currents: BTreeMap::new(),
                receiver_deeds: Vec::new(),
                receiver_population: vec![ReceiverPopulationDeed::Found(Box::new(founding))],
                topology_deeds: Vec::new(),
            })
            .unwrap()
            .radiation
            .remove(0);
        assert_eq!(world.standing().receivers.len(), 3);
        assert!(matches!(
            founded.receiver_population.as_slice(),
            [ReceiverPopulationChange::Founded {
                receiver: ReceiverId(3),
                ..
            }]
        ));

        let contact = world
            .receive(&LocalStarEvent {
                event: EventId(3),
                source_currents: BTreeMap::from([(shared_port, integer(1))]),
                receiver_deeds: Vec::new(),
                receiver_population: Vec::new(),
                topology_deeds: Vec::new(),
            })
            .unwrap()
            .radiation
            .remove(0);
        assert!(
            contact.receiver_nerve.cells.iter().any(|cell| {
                cell.receivers.len() >= 2 && cell.receivers.contains(&ReceiverId(3))
            })
        );

        for event in 4..=24 {
            if world.standing().open_currents.is_empty() {
                break;
            }
            world
                .receive(&LocalStarEvent::continuation(EventId(event)))
                .unwrap();
        }
        assert!(world.standing().open_currents.is_empty());
        let before_rebase = world.standing().receiver_position(ReceiverId(3)).unwrap();
        let rebased = world
            .receive(&LocalStarEvent {
                event: EventId(25),
                source_currents: BTreeMap::new(),
                receiver_deeds: Vec::new(),
                receiver_population: vec![ReceiverPopulationDeed::Reanchor {
                    receiver: ReceiverId(3),
                    anchor: anchors[1],
                }],
                topology_deeds: Vec::new(),
            })
            .unwrap()
            .radiation
            .remove(0);
        assert_eq!(
            world.standing().receiver_position(ReceiverId(3)).unwrap(),
            before_rebase
        );
        assert!(matches!(
            rebased.receiver_population.as_slice(),
            [ReceiverPopulationChange::Reanchored {
                receiver: ReceiverId(3),
                ..
            }]
        ));

        world
            .receive(&LocalStarEvent {
                event: EventId(26),
                source_currents: BTreeMap::new(),
                receiver_deeds: Vec::new(),
                receiver_population: vec![ReceiverPopulationDeed::Depart {
                    receiver: ReceiverId(3),
                }],
                topology_deeds: Vec::new(),
            })
            .unwrap();
        assert!(!world.standing().receivers.contains_key(&ReceiverId(3)));
    }

    #[test]
    fn bounded_ecology_exposes_nonuniform_stress_and_a_local_rewrite_opening() {
        let (law, standing, hinges) =
            octahedral_law(CpuExecutor::multicore(NonZeroUsize::new(4).unwrap()));
        let mut world = CausalWorld::new(law, standing);
        let mut event = LocalStarEvent {
            event: EventId(2),
            source_currents: BTreeMap::from([(hinges[0], integer(3))]),
            receiver_deeds: Vec::new(),
            receiver_population: Vec::new(),
            topology_deeds: Vec::new(),
        };
        let mut witnessed_rewrite = false;
        let mut witnessed_stress = false;
        let mut witnessed_nonuniform = false;
        for ordinal in 2..=48 {
            event.event = EventId(ordinal);
            if ordinal == 3 {
                // A genuinely opposed boundary deed drives the already
                // founded local coordinate through its discriminant.
                event.source_currents.insert(hinges[0], integer(-100));
            }
            let radiation = world.receive(&event).unwrap().radiation.remove(0);
            witnessed_rewrite |= !radiation.rewrite_candidates.is_empty();
            witnessed_stress |= radiation
                .face_fields
                .values()
                .any(|field| !field.stress.is_zero());
            let coordinates = world
                .standing()
                .trajectories
                .values()
                .map(|trajectory| trajectory.current.clone())
                .collect::<BTreeSet<_>>();
            witnessed_nonuniform |= coordinates.len() > 2;
            assert!(
                radiation
                    .current_balances
                    .iter()
                    .all(|balance| balance.exact_residual.is_zero())
            );
            event = LocalStarEvent::continuation(EventId(ordinal + 1));
            if witnessed_rewrite && witnessed_stress && witnessed_nonuniform {
                break;
            }
        }
        assert!(witnessed_stress);
        assert!(witnessed_nonuniform);
        assert!(witnessed_rewrite);
    }

    #[test]
    fn oriented_refractory_front_rests_without_a_numeric_tolerance() {
        let (law, standing, hinges) = octahedral_law(CpuExecutor::serial());
        let mut world = CausalWorld::new(law, standing);
        world
            .receive(&LocalStarEvent {
                event: EventId(2),
                source_currents: BTreeMap::from([(hinges[0], integer(1))]),
                receiver_deeds: Vec::new(),
                receiver_population: Vec::new(),
                topology_deeds: Vec::new(),
            })
            .unwrap();
        for event in 3..=u64::try_from(hinges.len() + 3).unwrap() {
            if world.standing().open_currents.is_empty() {
                break;
            }
            world
                .receive(&LocalStarEvent::continuation(EventId(event)))
                .unwrap();
        }
        assert!(world.standing().open_currents.is_empty());
    }

    #[test]
    fn common_translation_is_absent_from_relative_spatial_standing() {
        let founding = EventId(1);
        let mut complex = SimplicialComplex::default();
        let a = complex.found_vertex("a", founding);
        let b = complex.found_vertex("b", founding);
        let c = complex.found_vertex("c", founding);
        let face = complex.found_face("abc", founding, [a, b, c]).unwrap();
        let positions = BTreeMap::from([
            (a, RatVec3::from_i64(2, -3, 5)),
            (b, RatVec3::from_i64(7, 1, 4)),
            (c, RatVec3::from_i64(-1, 6, 9)),
        ]);
        let translation = RatVec3::from_i64(101, -43, 29);
        let translated = positions
            .iter()
            .map(|(vertex, position)| (*vertex, position.add(&translation)))
            .collect();
        let first = LocalSpatialStanding::from_positions(&complex, &positions).unwrap();
        let second = LocalSpatialStanding::from_positions(&complex, &translated).unwrap();
        assert_eq!(first, second);
        assert_eq!(first.face_residuals[&face], RatVec3::zero());
        assert!(
            first
                .chord_residuals
                .iter()
                .all(|residual| residual.residual == RatVec3::zero())
        );
    }

    #[test]
    fn receiver_deed_permutation_cannot_select_a_physical_origin() {
        let (law, standing, _) = octahedral_law(CpuExecutor::serial());
        let deeds = vec![
            receiver_deed(
                &standing,
                ReceiverId(1),
                Rat::zero(),
                vec![
                    ReceiverTraversalStep::Translate {
                        coordinates: RatVec3::from_i64(1, 2, 3),
                    },
                    ReceiverTraversalStep::Rotate {
                        axis: ReceiverRotationAxis::X,
                        ratio: ProjectiveRatio::from_rat(&integer(1)),
                    },
                ],
            ),
            receiver_deed(
                &standing,
                ReceiverId(2),
                Rat::zero(),
                vec![
                    ReceiverTraversalStep::Translate {
                        coordinates: RatVec3::from_i64(-2, 1, 4),
                    },
                    ReceiverTraversalStep::Rotate {
                        axis: ReceiverRotationAxis::Y,
                        ratio: ProjectiveRatio::from_rat(&integer(1)),
                    },
                ],
            ),
        ];
        let forward = law
            .enact(
                &standing,
                &LocalStarEvent {
                    event: EventId(2),
                    source_currents: BTreeMap::new(),
                    receiver_deeds: deeds.clone(),
                    receiver_population: Vec::new(),
                    topology_deeds: Vec::new(),
                },
            )
            .unwrap();
        let reverse = law
            .enact(
                &standing,
                &LocalStarEvent {
                    event: EventId(2),
                    source_currents: BTreeMap::new(),
                    receiver_deeds: deeds.into_iter().rev().collect(),
                    receiver_population: Vec::new(),
                    topology_deeds: Vec::new(),
                },
            )
            .unwrap();
        assert_eq!(forward.standing_after, reverse.standing_after);
        assert_eq!(forward.radiation, reverse.radiation);
    }

    #[test]
    fn equal_total_current_keeps_source_and_receiver_lineages_distinct() {
        let (law, standing, _) = octahedral_law(CpuExecutor::serial());
        let port = standing.receivers[&ReceiverId(1)].port;
        let radiation = law
            .enact(
                &standing,
                &LocalStarEvent {
                    event: EventId(2),
                    source_currents: BTreeMap::from([(port, integer(1))]),
                    receiver_deeds: vec![receiver_deed(
                        &standing,
                        ReceiverId(1),
                        integer(1),
                        Vec::new(),
                    )],
                    receiver_population: Vec::new(),
                    topology_deeds: Vec::new(),
                },
            )
            .unwrap()
            .radiation
            .remove(0);
        let roots = radiation
            .current_paths
            .iter()
            .filter(|path| path.entered.hinge == port && path.entered.word.is_empty())
            .map(|path| path.entered.root)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            roots,
            BTreeSet::from([
                LocalCurrentRoot::Source {
                    event: EventId(2),
                    hinge: port,
                },
                LocalCurrentRoot::Receiver {
                    event: EventId(2),
                    receiver: ReceiverId(1),
                },
            ])
        );
        assert!(
            radiation
                .current_paths
                .iter()
                .all(|path| path.exact_residual.is_zero())
        );
    }

    #[test]
    fn receiver_cover_is_the_complete_oriented_link_and_port_caused() {
        let (_law, standing, _hinges) = octahedral_law(CpuExecutor::serial());
        let receiver = ReceiverId(1);
        let body = &standing.receivers[&receiver];
        let cover = standing.receiver_acceptance_cover(receiver).unwrap();
        let topology = standing.receiver_topology(receiver).unwrap();
        assert_eq!(cover.link_class, VertexLinkClass::Cycle);
        assert_eq!(cover.organs.len(), 4);
        assert_eq!(cover.seams.len(), 4);
        assert_eq!(
            cover
                .organs
                .iter()
                .map(|organ| organ.face)
                .collect::<BTreeSet<_>>(),
            topology.star_faces
        );
        assert!(
            cover
                .seams
                .iter()
                .all(|seam| seam.incoming.len() == 1 && seam.outgoing.len() == 1)
        );
        for organ in &cover.organs {
            let seam = cover
                .seams
                .iter()
                .find(|seam| seam.vertex == organ.to)
                .unwrap();
            assert!(seam.incoming.contains(&organ.face));
            assert_eq!(
                organ.oriented_area,
                organ.boundary_directions[0].cross(&organ.boundary_directions[1])
            );
        }
        let port_faces = standing.kinematic.complex.hinges[&body.port]
            .cofaces
            .iter()
            .map(|coface| coface.face)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            BTreeSet::from([
                cover.port_section.negative_face,
                cover.port_section.positive_face,
            ]),
            port_faces
        );
        let specification = standing
            .receiver_face_specification(FrameId(1), receiver)
            .unwrap();
        assert_eq!(specification.acceptance.as_ref(), Some(&cover));
        match specification.rays {
            RayFamily::Central {
                forward,
                horizontal,
                vertical,
                ..
            } => {
                assert_eq!(forward, cover.port_section.forward);
                assert_eq!(horizontal, cover.port_section.horizontal);
                assert_eq!(vertical, cover.port_section.vertical);
            }
            RayFamily::Parallel { .. } => panic!("a local-star port is central"),
        }
    }

    #[test]
    fn bounded_outcome_basin_is_enacted_by_the_production_local_star_law() {
        let (law, standing, hinges) = octahedral_law(CpuExecutor::serial());
        let hinge = hinges[0];
        let prepared = [integer(-1), integer(0), integer(1)]
            .into_iter()
            .enumerate()
            .map(|(index, current)| crate::ExactConfigurationCell {
                id: crate::ConfigurationCellId(u64::try_from(index + 1).unwrap()),
                standing: standing.clone(),
                deed: LocalStarEvent {
                    event: EventId(2),
                    source_currents: (!current.is_zero())
                        .then_some((hinge, current))
                        .into_iter()
                        .collect(),
                    receiver_deeds: Vec::new(),
                    receiver_population: Vec::new(),
                    topology_deeds: Vec::new(),
                },
                measure: integer(1),
            })
            .collect::<Vec<_>>();
        let preparation = crate::ExactConfigurationComplex::new(
            prepared,
            [
                crate::ExactConfigurationAdjacency {
                    left: crate::ConfigurationCellId(1),
                    right: crate::ConfigurationCellId(2),
                    action: integer(1),
                },
                crate::ExactConfigurationAdjacency {
                    left: crate::ConfigurationCellId(2),
                    right: crate::ConfigurationCellId(3),
                    action: integer(1),
                },
            ],
        )
        .unwrap();
        let basin = preparation
            .enact_outcome_basin(
                &law,
                ReceiverId(1),
                |_receiver, _cell, successor| {
                    successor.standing_after.trajectories[&hinge]
                        .current
                        .cmp(&Rat::zero())
                },
                |outcome| *outcome == Ordering::Greater,
            )
            .unwrap();
        assert_eq!(
            basin.accepted.members,
            BTreeSet::from([crate::ConfigurationCellId(3)])
        );
        assert_eq!(basin.probability, integer(1) / integer(3));
        assert_eq!(basin.loss.measure, integer(2));
        assert_eq!(basin.loss.region.components.len(), 1);
        assert_eq!(basin.loss.boundary.len(), 1);
        assert_eq!(
            basin.loss.minimum_corrections[&crate::ConfigurationCellId(1)]
                .as_ref()
                .unwrap()
                .action,
            integer(2)
        );
        assert_eq!(
            basin.loss.minimum_corrections[&crate::ConfigurationCellId(2)]
                .as_ref()
                .unwrap()
                .path,
            vec![crate::ConfigurationCellId(2), crate::ConfigurationCellId(3)]
        );
        assert!(
            basin
                .outcomes
                .values()
                .all(|cell| cell.successor.standing_after.event == EventId(2))
        );
    }

    #[test]
    fn admitted_flip_changes_live_links_and_conserves_coordination_defect() {
        let (law, standing, hinges) = octahedral_law(CpuExecutor::serial());
        let initial_total = standing
            .coordination_defects()
            .unwrap()
            .values()
            .map(|defect| match defect {
                LocalCoordinationDefect::InteriorCycle { charge, .. } => *charge,
                other => panic!("closed octahedron has an interior-cycle link, got {other:?}"),
            })
            .sum::<i64>();
        assert_eq!(initial_total, 12);

        let mut world = CausalWorld::new(law, standing);
        let mut next_event = 2_u64;
        for current in [integer(3), integer(-100)] {
            world
                .receive(&LocalStarEvent {
                    event: EventId(next_event),
                    source_currents: BTreeMap::from([(hinges[0], current)]),
                    receiver_deeds: Vec::new(),
                    receiver_population: Vec::new(),
                    topology_deeds: Vec::new(),
                })
                .unwrap();
            next_event += 1;
        }
        while world.standing().rewrite_openings.is_empty() && next_event < 32 {
            world
                .receive(&LocalStarEvent {
                    event: EventId(next_event),
                    source_currents: BTreeMap::from([(hinges[0], integer(-100))]),
                    receiver_deeds: Vec::new(),
                    receiver_population: Vec::new(),
                    topology_deeds: Vec::new(),
                })
                .unwrap();
            next_event += 1;
        }
        assert!(!world.standing().rewrite_openings.is_empty());
        while !world.standing().open_currents.is_empty() && next_event < 64 {
            world
                .receive(&LocalStarEvent::continuation(EventId(next_event)))
                .unwrap();
            next_event += 1;
        }
        assert!(world.standing().open_currents.is_empty());

        let candidate = world.standing().rewrite_openings[0].clone();
        let old_diagonal = world.standing().kinematic.complex.hinges[&candidate.hinge].edge;
        let radiation = world
            .receive(&LocalStarEvent {
                event: EventId(next_event),
                source_currents: BTreeMap::new(),
                receiver_deeds: Vec::new(),
                receiver_population: Vec::new(),
                topology_deeds: vec![LocalTopologyDeed::AdmitFlip(candidate.clone())],
            })
            .unwrap()
            .radiation
            .remove(0);
        assert_eq!(radiation.topology_changes.len(), 1);
        let change = &radiation.topology_changes[0];
        assert_eq!(change.flip.old_diagonal, old_diagonal);
        assert_eq!(change.flip.new_diagonal, candidate.proposed_diagonal);
        assert_eq!(change.exact_charge_residual, Some(0));
        assert_eq!(change.defect_changes.len(), 4);
        assert_eq!(
            world.standing().kinematic.complex.hinges[&candidate.hinge].edge,
            candidate.proposed_diagonal
        );
        let final_total = world
            .standing()
            .coordination_defects()
            .unwrap()
            .values()
            .map(|defect| match defect {
                LocalCoordinationDefect::InteriorCycle { charge, .. } => *charge,
                other => panic!("flipped closed sphere remains interior, got {other:?}"),
            })
            .sum::<i64>();
        assert_eq!(final_total, initial_total);
        assert!(
            world
                .standing()
                .spatial
                .face_residuals
                .values()
                .all(|residual| residual == &RatVec3::zero())
        );
        assert!(
            world
                .standing()
                .spatial
                .chord_residuals
                .iter()
                .all(|residual| residual.residual == RatVec3::zero())
        );
    }
}
