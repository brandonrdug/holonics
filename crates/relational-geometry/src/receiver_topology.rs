//! Exact topology presented by one receiver.
//!
//! Source incidence and projected incidence are deliberately distinct. A
//! declared source vertex remains one source vertex in every receiver. A
//! regular projected crossing is split only in the receiver diagram and
//! retains the two source branches and their over/under order. Faces and
//! their dual graph are therefore receiver testimony, not a reconstruction of
//! the source.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact::{Rat, RatVec2, RatVec3, sign};
use crate::model::{ConstraintKind, Construction, EntityId, FrameId, Geometry};
use crate::projection::{ProjectionError, ProjectionLaw, Receiver, ReceiverId, project_point};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SourceVertexId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DiagramNodeId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DiagramEdgeId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DiagramFaceId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SourceEndpoint {
    pub entity: EntityId,
    pub vertex: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SourceSegmentAddress {
    pub entity: EntityId,
    pub segment: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceVertex {
    pub id: SourceVertexId,
    pub members: Vec<SourceEndpoint>,
    pub receiver_point: RatVec2,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceSegment {
    pub address: SourceSegmentAddress,
    pub from: SourceVertexId,
    pub to: SourceVertexId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DiagramNodeKind {
    SourceIncidence {
        source: SourceVertexId,
    },
    ApparentCrossing {
        first: SourceSegmentAddress,
        second: SourceSegmentAddress,
        over: SourceSegmentAddress,
        orientation: i8,
        /// Parameter on the first source segment whose projection reaches the
        /// crossing. This is distinct from interpolation in the screen plane
        /// for perspective and stereographic receivers.
        first_source_parameter: Rat,
        /// Parameter on the second source segment whose projection reaches
        /// the crossing.
        second_source_parameter: Rat,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiagramNode {
    pub id: DiagramNodeId,
    pub point: RatVec2,
    pub kind: DiagramNodeKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiagramEdge {
    pub id: DiagramEdgeId,
    pub source: SourceSegmentAddress,
    pub from: DiagramNodeId,
    pub to: DiagramNodeId,
    /// Interpolation parameter on the projected screen chord. This is diagram
    /// testimony and must not be read as chronology on the source segment.
    pub screen_parameter_start: Rat,
    pub screen_parameter_end: Rat,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiagramDart {
    pub edge: DiagramEdgeId,
    pub forward: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiagramFace {
    pub id: DiagramFaceId,
    pub boundary: Vec<DiagramDart>,
    pub signed_double_area: Rat,
    pub bounded: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GraphEdge {
    pub left: usize,
    pub right: usize,
    pub source: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactMultiGraph {
    pub vertex_count: usize,
    pub edges: Vec<GraphEdge>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactPolynomial {
    /// Coefficient of `u^k` at index `k`.
    pub coefficients: Vec<BigInt>,
}

impl ExactPolynomial {
    pub fn zero() -> Self {
        Self {
            coefficients: vec![BigInt::zero()],
        }
    }

    pub fn one() -> Self {
        Self {
            coefficients: vec![BigInt::one()],
        }
    }

    pub fn from_coefficients(coefficients: Vec<BigInt>) -> Self {
        let mut polynomial = Self { coefficients };
        polynomial.normalize();
        polynomial
    }

    pub fn add(&self, other: &Self) -> Self {
        let length = self.coefficients.len().max(other.coefficients.len());
        let mut coefficients = vec![BigInt::zero(); length];
        for (index, value) in self.coefficients.iter().enumerate() {
            coefficients[index] += value;
        }
        for (index, value) in other.coefficients.iter().enumerate() {
            coefficients[index] += value;
        }
        Self::from_coefficients(coefficients)
    }

    pub fn subtract(&self, other: &Self) -> Self {
        self.add(&other.negate())
    }

    pub fn negate(&self) -> Self {
        Self::from_coefficients(
            self.coefficients
                .iter()
                .map(|coefficient| -coefficient)
                .collect(),
        )
    }

    pub fn multiply(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut coefficients =
            vec![BigInt::zero(); self.coefficients.len() + other.coefficients.len() - 1];
        for (left_index, left) in self.coefficients.iter().enumerate() {
            for (right_index, right) in other.coefficients.iter().enumerate() {
                coefficients[left_index + right_index] += left * right;
            }
        }
        Self::from_coefficients(coefficients)
    }

    pub fn pow(&self, mut exponent: usize) -> Self {
        let mut result = Self::one();
        let mut factor = self.clone();
        while exponent > 0 {
            if exponent % 2 == 1 {
                result = result.multiply(&factor);
            }
            exponent /= 2;
            if exponent > 0 {
                factor = factor.multiply(&factor);
            }
        }
        result
    }

    pub fn is_zero(&self) -> bool {
        self.coefficients.iter().all(Zero::is_zero)
    }

    fn normalize(&mut self) {
        while self.coefficients.len() > 1 && self.coefficients.last().is_some_and(Zero::is_zero) {
            self.coefficients.pop();
        }
        if self.coefficients.is_empty() {
            self.coefficients.push(BigInt::zero());
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IharaSignature {
    /// `det(I-uB)`, equivalently the reciprocal Ihara zeta polynomial.
    pub reciprocal: ExactPolynomial,
    /// Oriented primitive cycles, modulo cyclic choice of starting dart.
    /// Index zero is length one.
    pub primitive_oriented_cycles: Vec<BigInt>,
}

/// The two-route reading of one `IharaSignature`.
///
/// Ihara's theorem states
/// `det(I - uB) = prod over primitive closed geodesics [P] of (1 - u^len(P))`.
/// `IharaSignature` carries the determinant on one side and the primitive
/// cycle counts on the other; this carries the comparison of the two, and it
/// carries both windows rather than a verdict.
///
/// The caller-declared horizon truncates the product. `prod_{l > horizon}
/// (1 - u^l)^{N_l}` is `1 + O(u^{horizon + 1})`, so the truncated product is
/// congruent to the determinant modulo `u^{horizon + 1}` and says nothing at
/// all above that degree. Coefficients `0..=horizon` are therefore compared
/// and coefficients above the horizon are withheld. A window wider than the
/// determinant's own degree is still lawful and is a stronger reading: the
/// product's coefficients there must vanish.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IharaCrossCheck {
    /// The horizon the signature was taken at, read off the length of
    /// `primitive_oriented_cycles` rather than authored here.
    pub horizon: usize,
    /// Coefficients `0..=horizon` of `prod_{l=1}^{horizon} (1 - u^l)^{N_l}`.
    pub euler_product_window: Vec<BigInt>,
    /// Coefficients `0..=horizon` of `det(I - uB)`, zero-extended.
    pub reciprocal_window: Vec<BigInt>,
    /// Degree of `det(I - uB)`.
    pub reciprocal_degree: usize,
    /// `horizon + 1`.
    pub compared_coefficients: usize,
    /// Coefficients of `det(I - uB)` strictly above the horizon, which the
    /// truncated product does not determine.
    pub withheld_coefficients: usize,
    /// Lowest degree at which the two windows disagree.
    pub first_disagreement: Option<usize>,
}

impl IharaCrossCheck {
    pub fn agrees(&self) -> bool {
        self.first_disagreement.is_none()
    }
}

/// One frame's reading of the Ihara identity, carrying the graph shape the
/// identity was taken over so two frames can be compared without re-deriving
/// it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IharaFrameReading {
    pub frame: String,
    pub vertex_count: usize,
    pub edge_count: usize,
    /// `edges - vertices + 1`. `ihara_signature` has already refused a
    /// disconnected graph, so this is the first Betti number.
    pub cycle_rank: usize,
    pub reciprocal_degree: usize,
    pub reciprocal: ExactPolynomial,
    pub primitive_oriented_cycles: Vec<BigInt>,
    pub cross_check: IharaCrossCheck,
}

/// The source graph and the face-dual graph read as two frames on one
/// construction.
///
/// The face dual is dual to the **diagram** graph, not to the source graph:
/// an apparent crossing splits source segments into further diagram edges. The
/// diagram counts are carried here so that difference is visible rather than
/// assumed away, and the dual pairing is asserted against the diagram.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TwoFrameIharaReading {
    pub source: IharaFrameReading,
    pub face_dual: IharaFrameReading,
    pub apparent_crossings: usize,
    pub diagram_vertex_count: usize,
    pub diagram_edge_count: usize,
    pub diagram_cycle_rank: usize,
    /// True exactly when no apparent crossing split a source segment, which is
    /// when the source graph *is* the diagram graph.
    pub source_graph_is_diagram_graph: bool,
    /// `cycle_rank(diagram) + cycle_rank(face dual)`.
    pub dual_cycle_rank_sum: usize,
    /// Euler's formula makes the sum above equal the shared edge count.
    pub dual_cycle_rank_sum_is_edge_count: bool,
    pub reciprocal_degrees_agree: bool,
    /// Lowest degree at which the two frames' reciprocals differ.
    pub first_reciprocal_difference: Option<usize>,
    /// Lowest length at which the two frames' primitive cycle counts differ.
    pub first_cycle_count_difference: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TopologyDiscriminant {
    UnsupportedRadicalProjection,
    DeclaredIncidenceDoesNotMeet {
        source: SourceVertexId,
    },
    DistinctSourceVerticesCollapse {
        first: SourceVertexId,
        second: SourceVertexId,
        point: RatVec2,
    },
    CollinearBranchOverlap {
        first: SourceSegmentAddress,
        second: SourceSegmentAddress,
    },
    UnrelatedEndpointCoincidence {
        first: SourceSegmentAddress,
        second: SourceSegmentAddress,
        point: RatVec2,
    },
    EqualDepthCrossing {
        first: SourceSegmentAddress,
        second: SourceSegmentAddress,
        point: RatVec2,
    },
    MultipleCrossingAtOnePoint {
        point: RatVec2,
    },
    ZeroDiagramEdge {
        source: SourceSegmentAddress,
    },
    NonCellularEmbedding {
        vertices: usize,
        edges: usize,
        boundary_cycles: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverTopology {
    pub receiver: ReceiverId,
    pub receiver_name: String,
    pub source_vertices: Vec<SourceVertex>,
    pub source_segments: Vec<SourceSegment>,
    pub nodes: Vec<DiagramNode>,
    pub edges: Vec<DiagramEdge>,
    pub faces: Vec<DiagramFace>,
    pub source_graph: ExactMultiGraph,
    pub face_dual_graph: ExactMultiGraph,
    pub source_ihara: IharaSignature,
    pub face_dual_ihara: IharaSignature,
}

impl ReceiverTopology {
    pub fn apparent_crossing_count(&self) -> usize {
        self.nodes
            .iter()
            .filter(|node| matches!(node.kind, DiagramNodeKind::ApparentCrossing { .. }))
            .count()
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ReceiverTopologyError {
    #[error(transparent)]
    Projection(#[from] ProjectionError),
    #[error("the construction contains no thread segments")]
    NoThreads,
    #[error("thread endpoint {0:?} is not present")]
    MissingEndpoint(SourceEndpoint),
    #[error("receiver topology reaches a projection discriminant: {0:?}")]
    Discriminant(TopologyDiscriminant),
    #[error("the graph contains a loop and is outside this exact Ihara cut")]
    GraphLoop,
    #[error("the graph is disconnected")]
    DisconnectedGraph,
    #[error("the graph has no recurrent core")]
    AcyclicGraph,
    #[error("the determinant cut admits at most 20 vertices, received {0}")]
    DeterminantCutExceeded(usize),
    #[error("primitive-cycle division was not exact at length {0}")]
    NonIntegralPrimitiveCount(usize),
}

#[derive(Clone)]
struct RawSegment {
    address: SourceSegmentAddress,
    endpoints: [SourceEndpoint; 2],
    frame: FrameId,
    source_points: [RatVec3; 2],
}

#[derive(Clone)]
struct ProjectedSegment {
    source: SourceSegment,
    receiver_points: [RatVec3; 2],
    screen_points: [RatVec2; 2],
}

#[derive(Clone)]
struct SplitPoint {
    parameter: Rat,
    node: DiagramNodeId,
}

pub fn analyze_receiver_topology(
    construction: &Construction,
    receiver: &Receiver,
    primitive_cycle_horizon: usize,
) -> Result<ReceiverTopology, ReceiverTopologyError> {
    if matches!(receiver.projection, ProjectionLaw::Isometric) {
        return Err(ReceiverTopologyError::Discriminant(
            TopologyDiscriminant::UnsupportedRadicalProjection,
        ));
    }

    let raw_segments = collect_thread_segments(construction)?;
    let (source_vertices, source_segments, endpoint_vertices) =
        source_incidence(construction, receiver, &raw_segments)?;
    let source_graph = ExactMultiGraph {
        vertex_count: source_vertices.len(),
        edges: source_segments
            .iter()
            .map(|segment| GraphEdge {
                left: segment.from.0 as usize - 1,
                right: segment.to.0 as usize - 1,
                source: format!("e{}:{}", segment.address.entity.0, segment.address.segment),
            })
            .collect(),
    };

    let source_points = source_vertices
        .iter()
        .map(|vertex| (vertex.id, vertex.receiver_point.clone()))
        .collect::<BTreeMap<_, _>>();
    let projected_segments = raw_segments
        .iter()
        .zip(source_segments.iter())
        .map(|(raw, source)| {
            let first = project_point(construction, raw.frame, &raw.source_points[0], receiver)?;
            let second = project_point(construction, raw.frame, &raw.source_points[1], receiver)?;
            let (Some(screen_first), Some(screen_second)) =
                (first.rational.clone(), second.rational.clone())
            else {
                return Err(ReceiverTopologyError::Discriminant(
                    TopologyDiscriminant::UnsupportedRadicalProjection,
                ));
            };
            Ok(ProjectedSegment {
                source: source.clone(),
                receiver_points: [first.receiver_point, second.receiver_point],
                screen_points: [screen_first, screen_second],
            })
        })
        .collect::<Result<Vec<_>, ReceiverTopologyError>>()?;

    let mut nodes = source_vertices
        .iter()
        .map(|vertex| DiagramNode {
            id: DiagramNodeId(vertex.id.0),
            point: vertex.receiver_point.clone(),
            kind: DiagramNodeKind::SourceIncidence { source: vertex.id },
        })
        .collect::<Vec<_>>();
    let mut occupied_points = BTreeMap::new();
    for vertex in &source_vertices {
        let key = point_key(&vertex.receiver_point);
        if let Some(first) = occupied_points.insert(key, vertex.id) {
            return Err(ReceiverTopologyError::Discriminant(
                TopologyDiscriminant::DistinctSourceVerticesCollapse {
                    first,
                    second: vertex.id,
                    point: vertex.receiver_point.clone(),
                },
            ));
        }
    }

    let mut splits = projected_segments
        .iter()
        .map(|segment| {
            vec![
                SplitPoint {
                    parameter: Rat::zero(),
                    node: DiagramNodeId(segment.source.from.0),
                },
                SplitPoint {
                    parameter: Rat::one(),
                    node: DiagramNodeId(segment.source.to.0),
                },
            ]
        })
        .collect::<Vec<_>>();
    let mut crossing_points = BTreeSet::new();

    for first_index in 0..projected_segments.len() {
        for second_index in (first_index + 1)..projected_segments.len() {
            let first = &projected_segments[first_index];
            let second = &projected_segments[second_index];
            if share_source_vertex(&first.source, &second.source) {
                continue;
            }
            let first_direction = first.screen_points[1].subtract(&first.screen_points[0]);
            let second_direction = second.screen_points[1].subtract(&second.screen_points[0]);
            let denominator = first_direction.cross(&second_direction);
            let offset = second.screen_points[0].subtract(&first.screen_points[0]);
            if denominator.is_zero() {
                if offset.cross(&first_direction).is_zero()
                    && collinear_intervals_overlap(first, second)
                {
                    return Err(ReceiverTopologyError::Discriminant(
                        TopologyDiscriminant::CollinearBranchOverlap {
                            first: first.source.address,
                            second: second.source.address,
                        },
                    ));
                }
                continue;
            }

            let first_parameter = offset.cross(&second_direction) / &denominator;
            let second_parameter = offset.cross(&first_direction) / &denominator;
            if outside_unit_interval(&first_parameter) || outside_unit_interval(&second_parameter) {
                continue;
            }
            let point = first.screen_points[0].add(&first_direction.scale(&first_parameter));
            if is_endpoint(&first_parameter) || is_endpoint(&second_parameter) {
                return Err(ReceiverTopologyError::Discriminant(
                    TopologyDiscriminant::UnrelatedEndpointCoincidence {
                        first: first.source.address,
                        second: second.source.address,
                        point,
                    },
                ));
            }
            let key = point_key(&point);
            if occupied_points.contains_key(&key) || !crossing_points.insert(key) {
                return Err(ReceiverTopologyError::Discriminant(
                    TopologyDiscriminant::MultipleCrossingAtOnePoint { point },
                ));
            }

            let first_source_parameter = source_parameter(first, &point, &receiver.projection);
            let second_source_parameter = source_parameter(second, &point, &receiver.projection);
            let first_receiver_point = interpolate(
                &first.receiver_points[0],
                &first.receiver_points[1],
                &first_source_parameter,
            );
            let second_receiver_point = interpolate(
                &second.receiver_points[0],
                &second.receiver_points[1],
                &second_source_parameter,
            );
            let first_depth = receiver_depth(&first_receiver_point, &receiver.projection);
            let second_depth = receiver_depth(&second_receiver_point, &receiver.projection);
            if first_depth == second_depth {
                return Err(ReceiverTopologyError::Discriminant(
                    TopologyDiscriminant::EqualDepthCrossing {
                        first: first.source.address,
                        second: second.source.address,
                        point,
                    },
                ));
            }
            let first_is_over = first_depth < second_depth;
            let orientation = if first_is_over {
                sign(&first_direction.cross(&second_direction))
            } else {
                sign(&second_direction.cross(&first_direction))
            };
            let node = DiagramNodeId(nodes.len() as u64 + 1);
            nodes.push(DiagramNode {
                id: node,
                point: point.clone(),
                kind: DiagramNodeKind::ApparentCrossing {
                    first: first.source.address,
                    second: second.source.address,
                    over: if first_is_over {
                        first.source.address
                    } else {
                        second.source.address
                    },
                    orientation,
                    first_source_parameter,
                    second_source_parameter,
                },
            });
            splits[first_index].push(SplitPoint {
                parameter: first_parameter,
                node,
            });
            splits[second_index].push(SplitPoint {
                parameter: second_parameter,
                node,
            });
        }
    }

    let mut edges = Vec::new();
    for (segment, segment_splits) in projected_segments.iter().zip(splits.iter_mut()) {
        segment_splits.sort_by(|left, right| left.parameter.cmp(&right.parameter));
        for pair in segment_splits.windows(2) {
            if pair[0].parameter == pair[1].parameter || pair[0].node == pair[1].node {
                return Err(ReceiverTopologyError::Discriminant(
                    TopologyDiscriminant::ZeroDiagramEdge {
                        source: segment.source.address,
                    },
                ));
            }
            edges.push(DiagramEdge {
                id: DiagramEdgeId(edges.len() as u64 + 1),
                source: segment.source.address,
                from: pair[0].node,
                to: pair[1].node,
                screen_parameter_start: pair[0].parameter.clone(),
                screen_parameter_end: pair[1].parameter.clone(),
            });
        }
    }

    let (faces, dart_faces) = recover_faces(&nodes, &edges)?;
    let expected_faces = edges.len() + 2 - nodes.len();
    if faces.len() != expected_faces {
        return Err(ReceiverTopologyError::Discriminant(
            TopologyDiscriminant::NonCellularEmbedding {
                vertices: nodes.len(),
                edges: edges.len(),
                boundary_cycles: faces.len(),
            },
        ));
    }
    let face_dual_graph = ExactMultiGraph {
        vertex_count: faces.len(),
        edges: edges
            .iter()
            .enumerate()
            .map(|(edge_index, edge)| GraphEdge {
                left: dart_faces[2 * edge_index],
                right: dart_faces[2 * edge_index + 1],
                source: format!(
                    "e{}:{}@{}",
                    edge.source.entity.0, edge.source.segment, edge.id.0
                ),
            })
            .collect(),
    };
    let source_ihara = ihara_signature(&source_graph, primitive_cycle_horizon)?;
    let face_dual_ihara = ihara_signature(&face_dual_graph, primitive_cycle_horizon)?;

    // Keep the lookup live through construction so a malformed constraint can
    // never silently disappear during a later refactor.
    debug_assert_eq!(
        endpoint_vertices.len(),
        raw_segments
            .iter()
            .flat_map(|segment| segment.endpoints)
            .collect::<BTreeSet<_>>()
            .len()
    );
    debug_assert_eq!(source_points.len(), source_vertices.len());

    Ok(ReceiverTopology {
        receiver: receiver.id,
        receiver_name: receiver.name.clone(),
        source_vertices,
        source_segments,
        nodes,
        edges,
        faces,
        source_graph,
        face_dual_graph,
        source_ihara,
        face_dual_ihara,
    })
}

fn collect_thread_segments(
    construction: &Construction,
) -> Result<Vec<RawSegment>, ReceiverTopologyError> {
    let mut segments = Vec::new();
    for (entity_id, entity) in &construction.entities {
        let Geometry::Thread { vertices, closed } = &entity.geometry else {
            continue;
        };
        if vertices.len() < 2 {
            continue;
        }
        let segment_count = if *closed {
            vertices.len()
        } else {
            vertices.len() - 1
        };
        for segment in 0..segment_count {
            let next = (segment + 1) % vertices.len();
            segments.push(RawSegment {
                address: SourceSegmentAddress {
                    entity: *entity_id,
                    segment,
                },
                endpoints: [
                    SourceEndpoint {
                        entity: *entity_id,
                        vertex: segment,
                    },
                    SourceEndpoint {
                        entity: *entity_id,
                        vertex: next,
                    },
                ],
                frame: entity.frame,
                source_points: [vertices[segment].clone(), vertices[next].clone()],
            });
        }
    }
    if segments.is_empty() {
        Err(ReceiverTopologyError::NoThreads)
    } else {
        Ok(segments)
    }
}

fn source_incidence(
    construction: &Construction,
    receiver: &Receiver,
    raw_segments: &[RawSegment],
) -> Result<
    (
        Vec<SourceVertex>,
        Vec<SourceSegment>,
        BTreeMap<SourceEndpoint, SourceVertexId>,
    ),
    ReceiverTopologyError,
> {
    let endpoints = raw_segments
        .iter()
        .flat_map(|segment| segment.endpoints)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let endpoint_indices = endpoints
        .iter()
        .enumerate()
        .map(|(index, endpoint)| (*endpoint, index))
        .collect::<BTreeMap<_, _>>();
    let mut union = UnionFind::new(endpoints.len());
    for constraint in construction.constraints.values() {
        let ConstraintKind::SharedVertex {
            left,
            right,
            left_vertex,
            right_vertex,
        } = constraint.kind
        else {
            continue;
        };
        let left = SourceEndpoint {
            entity: left,
            vertex: left_vertex,
        };
        let right = SourceEndpoint {
            entity: right,
            vertex: right_vertex,
        };
        match (endpoint_indices.get(&left), endpoint_indices.get(&right)) {
            (Some(left), Some(right)) => union.join(*left, *right),
            (None, None) => {}
            (None, Some(_)) => return Err(ReceiverTopologyError::MissingEndpoint(left)),
            (Some(_), None) => return Err(ReceiverTopologyError::MissingEndpoint(right)),
        }
    }

    let mut roots = BTreeMap::<usize, Vec<SourceEndpoint>>::new();
    for (index, endpoint) in endpoints.iter().enumerate() {
        roots.entry(union.root(index)).or_default().push(*endpoint);
    }
    let mut endpoint_vertices = BTreeMap::new();
    let mut source_vertices = Vec::new();
    for members in roots.values() {
        let id = SourceVertexId(source_vertices.len() as u64 + 1);
        let mut point = None;
        for endpoint in members {
            endpoint_vertices.insert(*endpoint, id);
            let (frame, source_point) = endpoint_point(construction, *endpoint)?;
            let projected = project_point(construction, frame, source_point, receiver)?;
            let Some(projected) = projected.rational else {
                return Err(ReceiverTopologyError::Discriminant(
                    TopologyDiscriminant::UnsupportedRadicalProjection,
                ));
            };
            if point
                .as_ref()
                .is_some_and(|existing| existing != &projected)
            {
                return Err(ReceiverTopologyError::Discriminant(
                    TopologyDiscriminant::DeclaredIncidenceDoesNotMeet { source: id },
                ));
            }
            point = Some(projected);
        }
        source_vertices.push(SourceVertex {
            id,
            members: members.clone(),
            receiver_point: point.expect("a source incidence has at least one endpoint"),
        });
    }

    let source_segments = raw_segments
        .iter()
        .map(|segment| SourceSegment {
            address: segment.address,
            from: endpoint_vertices[&segment.endpoints[0]],
            to: endpoint_vertices[&segment.endpoints[1]],
        })
        .collect();
    Ok((source_vertices, source_segments, endpoint_vertices))
}

fn endpoint_point(
    construction: &Construction,
    endpoint: SourceEndpoint,
) -> Result<(FrameId, &RatVec3), ReceiverTopologyError> {
    let Some(entity) = construction.entities.get(&endpoint.entity) else {
        return Err(ReceiverTopologyError::MissingEndpoint(endpoint));
    };
    let Geometry::Thread { vertices, .. } = &entity.geometry else {
        return Err(ReceiverTopologyError::MissingEndpoint(endpoint));
    };
    let Some(point) = vertices.get(endpoint.vertex) else {
        return Err(ReceiverTopologyError::MissingEndpoint(endpoint));
    };
    Ok((entity.frame, point))
}

fn share_source_vertex(first: &SourceSegment, second: &SourceSegment) -> bool {
    first.from == second.from
        || first.from == second.to
        || first.to == second.from
        || first.to == second.to
}

fn point_key(point: &RatVec2) -> (Rat, Rat) {
    (point.x.clone(), point.y.clone())
}

fn outside_unit_interval(value: &Rat) -> bool {
    value.is_negative() || value > &Rat::one()
}

fn is_endpoint(value: &Rat) -> bool {
    value.is_zero() || value.is_one()
}

fn collinear_intervals_overlap(first: &ProjectedSegment, second: &ProjectedSegment) -> bool {
    let use_x = first.screen_points[0].x != first.screen_points[1].x;
    let coordinate = |point: &RatVec2| {
        if use_x {
            point.x.clone()
        } else {
            point.y.clone()
        }
    };
    let first_a = coordinate(&first.screen_points[0]);
    let first_b = coordinate(&first.screen_points[1]);
    let second_a = coordinate(&second.screen_points[0]);
    let second_b = coordinate(&second.screen_points[1]);
    let first_min = first_a.clone().min(first_b.clone());
    let first_max = first_a.max(first_b);
    let second_min = second_a.clone().min(second_b.clone());
    let second_max = second_a.max(second_b);
    first_min.max(second_min) <= first_max.min(second_max)
}

fn source_parameter(
    segment: &ProjectedSegment,
    screen_point: &RatVec2,
    projection: &ProjectionLaw,
) -> Rat {
    let origin = &segment.receiver_points[0];
    let delta = segment.receiver_points[1].subtract(origin);
    match projection {
        ProjectionLaw::Orthographic => solve_parameter(
            &origin.x,
            &delta.x,
            &screen_point.x,
            &origin.y,
            &delta.y,
            &screen_point.y,
        ),
        ProjectionLaw::PerspectiveRay { focal_distance } => {
            let x_denominator = focal_distance * &delta.x - &screen_point.x * &delta.z;
            if !x_denominator.is_zero() {
                (&screen_point.x * (focal_distance + &origin.z) - focal_distance * &origin.x)
                    / x_denominator
            } else {
                let y_denominator = focal_distance * &delta.y - &screen_point.y * &delta.z;
                (&screen_point.y * (focal_distance + &origin.z) - focal_distance * &origin.y)
                    / y_denominator
            }
        }
        ProjectionLaw::StereographicNorth => {
            let x_denominator = &delta.x + &screen_point.x * &delta.z;
            if !x_denominator.is_zero() {
                (&screen_point.x * (Rat::one() - &origin.z) - &origin.x) / x_denominator
            } else {
                let y_denominator = &delta.y + &screen_point.y * &delta.z;
                (&screen_point.y * (Rat::one() - &origin.z) - &origin.y) / y_denominator
            }
        }
        ProjectionLaw::Isometric => unreachable!("the radical chart was rejected"),
    }
}

fn solve_parameter(
    first_origin: &Rat,
    first_delta: &Rat,
    first_target: &Rat,
    second_origin: &Rat,
    second_delta: &Rat,
    second_target: &Rat,
) -> Rat {
    if !first_delta.is_zero() {
        (first_target - first_origin) / first_delta
    } else {
        debug_assert!(!second_delta.is_zero());
        (second_target - second_origin) / second_delta
    }
}

fn interpolate(first: &RatVec3, second: &RatVec3, parameter: &Rat) -> RatVec3 {
    first.add(&second.subtract(first).scale(parameter))
}

fn receiver_depth(point: &RatVec3, projection: &ProjectionLaw) -> Rat {
    match projection {
        ProjectionLaw::Orthographic | ProjectionLaw::Isometric => point.z.clone(),
        ProjectionLaw::PerspectiveRay { focal_distance } => focal_distance + &point.z,
        ProjectionLaw::StereographicNorth => Rat::one() - &point.z,
    }
}

fn recover_faces(
    nodes: &[DiagramNode],
    edges: &[DiagramEdge],
) -> Result<(Vec<DiagramFace>, Vec<usize>), ReceiverTopologyError> {
    let points = nodes
        .iter()
        .map(|node| (node.id, &node.point))
        .collect::<BTreeMap<_, _>>();
    let mut outgoing = vec![Vec::new(); nodes.len()];
    for (edge_index, edge) in edges.iter().enumerate() {
        outgoing[edge.from.0 as usize - 1].push(2 * edge_index);
        outgoing[edge.to.0 as usize - 1].push(2 * edge_index + 1);
    }
    if !diagram_connected(nodes.len(), edges) {
        return Err(ReceiverTopologyError::DisconnectedGraph);
    }
    for (node_index, darts) in outgoing.iter_mut().enumerate() {
        let node = DiagramNodeId(node_index as u64 + 1);
        darts.sort_by(|left, right| {
            compare_rays(
                &dart_direction(*left, edges, &points, node),
                &dart_direction(*right, edges, &points, node),
            )
            .then_with(|| left.cmp(right))
        });
    }

    let mut dart_faces = vec![usize::MAX; 2 * edges.len()];
    let mut faces = Vec::new();
    for start in 0..dart_faces.len() {
        if dart_faces[start] != usize::MAX {
            continue;
        }
        let face_index = faces.len();
        let mut current = start;
        let mut boundary = Vec::new();
        loop {
            if dart_faces[current] != usize::MAX {
                debug_assert_eq!(current, start);
                break;
            }
            dart_faces[current] = face_index;
            let edge_index = current / 2;
            let forward = current % 2 == 0;
            boundary.push(DiagramDart {
                edge: edges[edge_index].id,
                forward,
            });
            let target = dart_target(current, edges);
            let reverse = current ^ 1;
            let target_outgoing = &outgoing[target.0 as usize - 1];
            let reverse_position = target_outgoing
                .iter()
                .position(|candidate| *candidate == reverse)
                .expect("the reverse dart leaves the target");
            current = target_outgoing
                [(reverse_position + target_outgoing.len() - 1) % target_outgoing.len()];
        }

        let signed_double_area = boundary.iter().fold(Rat::zero(), |area, dart| {
            let edge = &edges[dart.edge.0 as usize - 1];
            let (from, to) = if dart.forward {
                (edge.from, edge.to)
            } else {
                (edge.to, edge.from)
            };
            area + points[&from].cross(points[&to])
        });
        faces.push(DiagramFace {
            id: DiagramFaceId(face_index as u64 + 1),
            bounded: signed_double_area.is_positive(),
            signed_double_area,
            boundary,
        });
    }
    Ok((faces, dart_faces))
}

fn dart_origin(dart: usize, edges: &[DiagramEdge]) -> DiagramNodeId {
    let edge = &edges[dart / 2];
    if dart % 2 == 0 { edge.from } else { edge.to }
}

fn dart_target(dart: usize, edges: &[DiagramEdge]) -> DiagramNodeId {
    let edge = &edges[dart / 2];
    if dart % 2 == 0 { edge.to } else { edge.from }
}

fn dart_direction(
    dart: usize,
    edges: &[DiagramEdge],
    points: &BTreeMap<DiagramNodeId, &RatVec2>,
    expected_origin: DiagramNodeId,
) -> RatVec2 {
    let origin = dart_origin(dart, edges);
    debug_assert_eq!(origin, expected_origin);
    points[&dart_target(dart, edges)].subtract(points[&origin])
}

fn compare_rays(first: &RatVec2, second: &RatVec2) -> Ordering {
    let first_upper = first.y.is_positive() || (first.y.is_zero() && !first.x.is_negative());
    let second_upper = second.y.is_positive() || (second.y.is_zero() && !second.x.is_negative());
    match (first_upper, second_upper) {
        (true, false) => Ordering::Less,
        (false, true) => Ordering::Greater,
        _ => match sign(&first.cross(second)) {
            1 => Ordering::Less,
            -1 => Ordering::Greater,
            _ => first.norm_squared().cmp(&second.norm_squared()),
        },
    }
}

fn diagram_connected(vertex_count: usize, edges: &[DiagramEdge]) -> bool {
    if vertex_count == 0 {
        return false;
    }
    let mut adjacency = vec![Vec::new(); vertex_count];
    for edge in edges {
        let left = edge.from.0 as usize - 1;
        let right = edge.to.0 as usize - 1;
        adjacency[left].push(right);
        adjacency[right].push(left);
    }
    connected_adjacency(&adjacency)
}

fn connected_adjacency(adjacency: &[Vec<usize>]) -> bool {
    let mut visited = vec![false; adjacency.len()];
    let mut queue = VecDeque::from([0]);
    visited[0] = true;
    while let Some(vertex) = queue.pop_front() {
        for next in &adjacency[vertex] {
            if !visited[*next] {
                visited[*next] = true;
                queue.push_back(*next);
            }
        }
    }
    visited.into_iter().all(|value| value)
}

pub fn ihara_signature(
    graph: &ExactMultiGraph,
    primitive_cycle_horizon: usize,
) -> Result<IharaSignature, ReceiverTopologyError> {
    if graph.vertex_count > 20 {
        return Err(ReceiverTopologyError::DeterminantCutExceeded(
            graph.vertex_count,
        ));
    }
    let mut adjacency_counts = vec![vec![0usize; graph.vertex_count]; graph.vertex_count];
    let mut adjacency = vec![Vec::new(); graph.vertex_count];
    let mut degrees = vec![0usize; graph.vertex_count];
    for edge in &graph.edges {
        if edge.left == edge.right {
            return Err(ReceiverTopologyError::GraphLoop);
        }
        adjacency_counts[edge.left][edge.right] += 1;
        adjacency_counts[edge.right][edge.left] += 1;
        adjacency[edge.left].push(edge.right);
        adjacency[edge.right].push(edge.left);
        degrees[edge.left] += 1;
        degrees[edge.right] += 1;
    }
    if !connected_adjacency(&adjacency) {
        return Err(ReceiverTopologyError::DisconnectedGraph);
    }
    if graph.edges.len() < graph.vertex_count {
        return Err(ReceiverTopologyError::AcyclicGraph);
    }

    let matrix = (0..graph.vertex_count)
        .map(|row| {
            (0..graph.vertex_count)
                .map(|column| {
                    let mut coefficients = vec![
                        if row == column {
                            BigInt::one()
                        } else {
                            BigInt::zero()
                        },
                        -BigInt::from(adjacency_counts[row][column]),
                    ];
                    if row == column {
                        coefficients.push(BigInt::from(degrees[row] - 1));
                    }
                    ExactPolynomial::from_coefficients(coefficients)
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let determinant = determinant(&matrix)?;
    let trivial_factor =
        ExactPolynomial::from_coefficients(vec![BigInt::one(), BigInt::zero(), -BigInt::one()])
            .pow(graph.edges.len() - graph.vertex_count);
    let reciprocal = trivial_factor.multiply(&determinant);
    let primitive_oriented_cycles = primitive_cycle_counts(graph, primitive_cycle_horizon)?;
    Ok(IharaSignature {
        reciprocal,
        primitive_oriented_cycles,
    })
}

/// `(1 - u^length)^exponent`, as coefficients `0..=bound`.
///
/// The generalized binomial series is used rather than repeated multiplication
/// so that a **negative** exponent is carried by the same owner as a positive
/// one. A negative exponent is what a perturbation control needs, and routing
/// it through a second code path would let the control and the check disagree
/// for a reason that is not the material.
fn one_minus_power_raised(length: usize, exponent: &BigInt, bound: usize) -> Vec<BigInt> {
    let mut window = vec![BigInt::zero(); bound + 1];
    if length == 0 {
        // `(1 - u^0)^e` is not a factor of any Euler product: a closed geodesic
        // has positive length. Return the zero window so a caller that reaches
        // here cannot silently read it as the identity factor.
        return window;
    }
    let mut binomial = BigInt::one();
    let mut step = 0usize;
    loop {
        let Some(degree) = step.checked_mul(length) else {
            break;
        };
        if degree > bound {
            break;
        }
        window[degree] = if step % 2 == 0 {
            binomial.clone()
        } else {
            -binomial.clone()
        };
        // C(e, k+1) = C(e, k) * (e - k) / (k + 1), exact over the integers.
        let numerator = &binomial * (exponent - BigInt::from(step));
        let divisor = BigInt::from(step + 1);
        debug_assert!((&numerator % &divisor).is_zero());
        binomial = numerator / divisor;
        if binomial.is_zero() {
            break;
        }
        step += 1;
    }
    window
}

fn truncated_window_multiply(left: &[BigInt], right: &[BigInt], bound: usize) -> Vec<BigInt> {
    let mut product = vec![BigInt::zero(); bound + 1];
    for (left_degree, left_value) in left.iter().enumerate() {
        if left_value.is_zero() || left_degree > bound {
            continue;
        }
        for (right_degree, right_value) in right.iter().enumerate() {
            let degree = left_degree + right_degree;
            if degree > bound {
                break;
            }
            if right_value.is_zero() {
                continue;
            }
            product[degree] += left_value * right_value;
        }
    }
    product
}

/// `prod_{l=1}^{horizon} (1 - u^l)^{N_l}` as coefficients `0..=horizon`, where
/// `N_l` is `primitive_oriented_cycles[l - 1]`.
///
/// The horizon is the length of the slice, which is the horizon the caller
/// declared to `ihara_signature`. Nothing here authors one.
pub fn ihara_euler_product_window(primitive_oriented_cycles: &[BigInt]) -> Vec<BigInt> {
    let horizon = primitive_oriented_cycles.len();
    let mut window = vec![BigInt::zero(); horizon + 1];
    window[0] = BigInt::one();
    for (index, count) in primitive_oriented_cycles.iter().enumerate() {
        if count.is_zero() {
            continue;
        }
        let factor = one_minus_power_raised(index + 1, count, horizon);
        window = truncated_window_multiply(&window, &factor, horizon);
    }
    window
}

/// Assert Ihara's theorem against one signature: expand the Euler product over
/// the primitive closed geodesics and compare it coefficient by coefficient
/// with `det(I - uB)`.
pub fn cross_check_ihara(signature: &IharaSignature) -> IharaCrossCheck {
    cross_check_ihara_perturbed(signature, &[])
}

/// The same comparison with the primitive-cycle counts perturbed first.
///
/// `perturbations` are `(length, delta)` pairs. A length outside
/// `1..=horizon` lies outside the compared window and is not applied. An
/// empty slice is the identity, and the check is evidence only because a
/// non-empty perturbation breaks it: multiplying the product by
/// `(1 - u^l)^{delta}` moves the coefficient at degree `l` by exactly
/// `-delta`, since the product's constant coefficient is one.
pub fn cross_check_ihara_perturbed(
    signature: &IharaSignature,
    perturbations: &[(usize, i64)],
) -> IharaCrossCheck {
    let horizon = signature.primitive_oriented_cycles.len();
    let mut counts = signature.primitive_oriented_cycles.clone();
    for (length, delta) in perturbations {
        if (1..=horizon).contains(length) {
            counts[length - 1] += BigInt::from(*delta);
        }
    }
    let euler_product_window = ihara_euler_product_window(&counts);
    let reciprocal_degree = signature.reciprocal.coefficients.len().saturating_sub(1);
    let reciprocal_window = (0..=horizon)
        .map(|degree| {
            signature
                .reciprocal
                .coefficients
                .get(degree)
                .cloned()
                .unwrap_or_else(BigInt::zero)
        })
        .collect::<Vec<_>>();
    let first_disagreement =
        (0..=horizon).find(|degree| euler_product_window[*degree] != reciprocal_window[*degree]);
    IharaCrossCheck {
        horizon,
        euler_product_window,
        reciprocal_window,
        reciprocal_degree,
        compared_coefficients: horizon + 1,
        withheld_coefficients: reciprocal_degree.saturating_sub(horizon),
        first_disagreement,
    }
}

pub fn ihara_frame_reading(
    frame: impl Into<String>,
    graph: &ExactMultiGraph,
    signature: &IharaSignature,
) -> IharaFrameReading {
    IharaFrameReading {
        frame: frame.into(),
        vertex_count: graph.vertex_count,
        edge_count: graph.edges.len(),
        cycle_rank: graph.edges.len() + 1 - graph.vertex_count,
        reciprocal_degree: signature.reciprocal.coefficients.len().saturating_sub(1),
        reciprocal: signature.reciprocal.clone(),
        primitive_oriented_cycles: signature.primitive_oriented_cycles.clone(),
        cross_check: cross_check_ihara(signature),
    }
}

/// The graph the receiver diagram presents, after apparent crossings have split
/// source segments. The face-dual graph is dual to this, not to the source
/// graph.
pub fn diagram_graph(topology: &ReceiverTopology) -> ExactMultiGraph {
    ExactMultiGraph {
        vertex_count: topology.nodes.len(),
        edges: topology
            .edges
            .iter()
            .map(|edge| GraphEdge {
                left: edge.from.0 as usize - 1,
                right: edge.to.0 as usize - 1,
                source: format!(
                    "e{}:{}@{}",
                    edge.source.entity.0, edge.source.segment, edge.id.0
                ),
            })
            .collect(),
    }
}

fn first_coefficient_difference(left: &ExactPolynomial, right: &ExactPolynomial) -> Option<usize> {
    let length = left.coefficients.len().max(right.coefficients.len());
    (0..length).find(|degree| {
        let left_value = left.coefficients.get(*degree);
        let right_value = right.coefficients.get(*degree);
        match (left_value, right_value) {
            (Some(left_value), Some(right_value)) => left_value != right_value,
            (Some(value), None) | (None, Some(value)) => !value.is_zero(),
            (None, None) => false,
        }
    })
}

impl ReceiverTopology {
    /// Read the source graph and the face-dual graph as two frames on one
    /// construction, asserting Ihara's theorem separately in each.
    pub fn two_frame_ihara_reading(&self) -> TwoFrameIharaReading {
        let diagram = diagram_graph(self);
        let source = ihara_frame_reading("source graph", &self.source_graph, &self.source_ihara);
        let face_dual = ihara_frame_reading(
            "face-dual graph",
            &self.face_dual_graph,
            &self.face_dual_ihara,
        );
        let diagram_cycle_rank = diagram.edges.len() + 1 - diagram.vertex_count;
        let dual_cycle_rank_sum = diagram_cycle_rank + face_dual.cycle_rank;
        TwoFrameIharaReading {
            apparent_crossings: self.apparent_crossing_count(),
            diagram_vertex_count: diagram.vertex_count,
            diagram_edge_count: diagram.edges.len(),
            diagram_cycle_rank,
            source_graph_is_diagram_graph: diagram.vertex_count == self.source_graph.vertex_count
                && diagram.edges.len() == self.source_graph.edges.len(),
            dual_cycle_rank_sum,
            dual_cycle_rank_sum_is_edge_count: dual_cycle_rank_sum == diagram.edges.len()
                && diagram.edges.len() == face_dual.edge_count,
            reciprocal_degrees_agree: source.reciprocal_degree == face_dual.reciprocal_degree,
            first_reciprocal_difference: first_coefficient_difference(
                &source.reciprocal,
                &face_dual.reciprocal,
            ),
            first_cycle_count_difference: (0..source
                .primitive_oriented_cycles
                .len()
                .min(face_dual.primitive_oriented_cycles.len()))
                .find(|index| {
                    source.primitive_oriented_cycles[*index]
                        != face_dual.primitive_oriented_cycles[*index]
                })
                .map(|index| index + 1),
            source,
            face_dual,
        }
    }
}

fn determinant(matrix: &[Vec<ExactPolynomial>]) -> Result<ExactPolynomial, ReceiverTopologyError> {
    let size = matrix.len();
    if size > 20 {
        return Err(ReceiverTopologyError::DeterminantCutExceeded(size));
    }
    let states = 1usize << size;
    let mut partials = vec![ExactPolynomial::zero(); states];
    partials[0] = ExactPolynomial::one();
    for mask in 0..states {
        let row = mask.count_ones() as usize;
        if row == size || partials[mask].is_zero() {
            continue;
        }
        for column in 0..size {
            if mask & (1usize << column) != 0 {
                continue;
            }
            let prior_after = (column + 1..size)
                .filter(|prior| mask & (1usize << prior) != 0)
                .count();
            let term = partials[mask].multiply(&matrix[row][column]);
            let next = mask | (1usize << column);
            partials[next] = if prior_after % 2 == 0 {
                partials[next].add(&term)
            } else {
                partials[next].subtract(&term)
            };
        }
    }
    Ok(partials[states - 1].clone())
}

fn primitive_cycle_counts(
    graph: &ExactMultiGraph,
    horizon: usize,
) -> Result<Vec<BigInt>, ReceiverTopologyError> {
    let dart_count = 2 * graph.edges.len();
    let mut origin = vec![0usize; dart_count];
    let mut target = vec![0usize; dart_count];
    for (edge_index, edge) in graph.edges.iter().enumerate() {
        origin[2 * edge_index] = edge.left;
        target[2 * edge_index] = edge.right;
        origin[2 * edge_index + 1] = edge.right;
        target[2 * edge_index + 1] = edge.left;
    }
    let mut transition = vec![vec![BigInt::zero(); dart_count]; dart_count];
    for first in 0..dart_count {
        for second in 0..dart_count {
            if target[first] == origin[second] && second != (first ^ 1) {
                transition[first][second] = BigInt::one();
            }
        }
    }
    let mut power = identity_integer_matrix(dart_count);
    let mut closed_walks = vec![BigInt::zero(); horizon + 1];
    for length in 1..=horizon {
        power = multiply_integer_matrices(&power, &transition);
        closed_walks[length] = (0..dart_count)
            .map(|index| power[index][index].clone())
            .sum();
    }

    let mut primitive = vec![BigInt::zero(); horizon + 1];
    for length in 1..=horizon {
        let mut numerator = closed_walks[length].clone();
        for divisor in 1..length {
            if length % divisor == 0 {
                numerator -= BigInt::from(divisor) * &primitive[divisor];
            }
        }
        let denominator = BigInt::from(length);
        if &numerator % &denominator != BigInt::zero() {
            return Err(ReceiverTopologyError::NonIntegralPrimitiveCount(length));
        }
        primitive[length] = numerator / denominator;
    }
    Ok(primitive.into_iter().skip(1).collect())
}

fn identity_integer_matrix(size: usize) -> Vec<Vec<BigInt>> {
    (0..size)
        .map(|row| {
            (0..size)
                .map(|column| {
                    if row == column {
                        BigInt::one()
                    } else {
                        BigInt::zero()
                    }
                })
                .collect()
        })
        .collect()
}

fn multiply_integer_matrices(left: &[Vec<BigInt>], right: &[Vec<BigInt>]) -> Vec<Vec<BigInt>> {
    let size = left.len();
    let mut product = vec![vec![BigInt::zero(); size]; size];
    for row in 0..size {
        for pivot in 0..size {
            if left[row][pivot].is_zero() {
                continue;
            }
            for column in 0..size {
                if !right[pivot][column].is_zero() {
                    product[row][column] += &left[row][pivot] * &right[pivot][column];
                }
            }
        }
    }
    product
}

struct UnionFind {
    parents: Vec<usize>,
}

impl UnionFind {
    fn new(size: usize) -> Self {
        Self {
            parents: (0..size).collect(),
        }
    }

    fn root(&mut self, value: usize) -> usize {
        if self.parents[value] != value {
            self.parents[value] = self.root(self.parents[value]);
        }
        self.parents[value]
    }

    fn join(&mut self, left: usize, right: usize) {
        let left = self.root(left);
        let right = self.root(right);
        if left != right {
            self.parents[right] = left;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact::RatVec3;
    use crate::model::Construction;
    use crate::projection::ProjectionLaw;

    #[test]
    fn a_closed_square_recovers_its_inside_and_outside_faces() {
        let (mut construction, frame) = Construction::new("square");
        construction
            .add_entity(
                "closed square",
                frame,
                Geometry::Thread {
                    vertices: vec![
                        RatVec3::from_i64(-1, -1, 0),
                        RatVec3::from_i64(1, -1, 0),
                        RatVec3::from_i64(1, 1, 0),
                        RatVec3::from_i64(-1, 1, 0),
                    ],
                    closed: true,
                },
            )
            .unwrap();
        let receiver = Receiver::new(
            ReceiverId(1),
            "square receiver",
            frame,
            ProjectionLaw::Orthographic,
        );
        let topology = analyze_receiver_topology(&construction, &receiver, 8).unwrap();
        assert_eq!(topology.nodes.len(), 4);
        assert_eq!(topology.edges.len(), 4);
        assert_eq!(topology.faces.len(), 2);
        assert_eq!(topology.faces.iter().filter(|face| face.bounded).count(), 1);
    }

    #[test]
    fn k4_has_eight_oriented_primitive_triangles() {
        let graph = ExactMultiGraph {
            vertex_count: 4,
            edges: vec![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
                .into_iter()
                .map(|(left, right)| GraphEdge {
                    left,
                    right,
                    source: format!("{left}-{right}"),
                })
                .collect(),
        };
        let signature = ihara_signature(&graph, 6).unwrap();
        assert_eq!(signature.primitive_oriented_cycles[2], BigInt::from(8));
        assert_eq!(signature.reciprocal.coefficients[0], BigInt::one());
    }

    fn complete_graph(vertex_count: usize) -> ExactMultiGraph {
        let mut edges = Vec::new();
        for left in 0..vertex_count {
            for right in (left + 1)..vertex_count {
                edges.push(GraphEdge {
                    left,
                    right,
                    source: format!("{left}-{right}"),
                });
            }
        }
        ExactMultiGraph {
            vertex_count,
            edges,
        }
    }

    fn cycle_graph(vertex_count: usize) -> ExactMultiGraph {
        ExactMultiGraph {
            vertex_count,
            edges: (0..vertex_count)
                .map(|left| GraphEdge {
                    left,
                    right: (left + 1) % vertex_count,
                    source: format!("c{left}"),
                })
                .collect(),
        }
    }

    fn bowtie_construction() -> (Construction, Receiver) {
        let (mut construction, frame) = Construction::new("apparent crossing");
        construction
            .add_entity(
                "self-crossing closed thread",
                frame,
                Geometry::Thread {
                    vertices: vec![
                        RatVec3::from_i64(0, 0, 0),
                        RatVec3::from_i64(2, 2, 0),
                        RatVec3::from_i64(2, 0, 1),
                        RatVec3::from_i64(0, 2, 1),
                    ],
                    closed: true,
                },
            )
            .unwrap();
        let receiver = Receiver::new(
            ReceiverId(1),
            "crossing receiver",
            frame,
            ProjectionLaw::Orthographic,
        );
        (construction, receiver)
    }

    #[test]
    fn the_euler_product_over_primitive_geodesics_reproduces_the_ihara_determinant() {
        // 2|E| = 12 for K4, so a horizon of 12 compares every coefficient the
        // determinant carries and withholds none.
        let signature = ihara_signature(&complete_graph(4), 12).unwrap();
        let check = cross_check_ihara(&signature);
        assert_eq!(check.horizon, 12);
        assert_eq!(check.reciprocal_degree, 12);
        assert_eq!(check.compared_coefficients, 13);
        assert_eq!(check.withheld_coefficients, 0);
        assert_eq!(check.first_disagreement, None);
        assert!(check.agrees());
        assert_eq!(check.euler_product_window, check.reciprocal_window);
    }

    #[test]
    fn the_k4_determinant_matches_the_published_closed_form() {
        // A third route, outside this body. Terras gives the Ihara zeta of K4
        // in factored form as
        //     Z(u)^-1 = (1 - u^2)^2 (1 - u)(1 - 2u)(1 + u + 2u^2)^3.
        // Two routes agreeing with each other is weaker evidence than either
        // agreeing with a source neither of them produced, so the factors are
        // multiplied out here and compared with the determinant.
        let factored =
            ExactPolynomial::from_coefficients(vec![BigInt::one(), BigInt::zero(), -BigInt::one()])
                .pow(2)
                .multiply(&ExactPolynomial::from_coefficients(vec![
                    BigInt::one(),
                    -BigInt::one(),
                ]))
                .multiply(&ExactPolynomial::from_coefficients(vec![
                    BigInt::one(),
                    BigInt::from(-2),
                ]))
                .multiply(
                    &ExactPolynomial::from_coefficients(vec![
                        BigInt::one(),
                        BigInt::one(),
                        BigInt::from(2),
                    ])
                    .pow(3),
                );
        let signature = ihara_signature(&complete_graph(4), 12).unwrap();
        assert_eq!(signature.reciprocal, factored);
        assert_eq!(
            factored.coefficients,
            vec![1, 0, 0, -8, -6, 0, 16, 24, -3, -16, -24, 0, 16]
                .into_iter()
                .map(BigInt::from)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn a_horizon_below_the_determinant_degree_withholds_the_coefficients_it_cannot_determine() {
        let signature = ihara_signature(&complete_graph(4), 5).unwrap();
        let check = cross_check_ihara(&signature);
        assert_eq!(check.compared_coefficients, 6);
        assert_eq!(check.withheld_coefficients, 7);
        assert!(check.agrees());
        // The truncated product is wrong above the horizon, which is exactly
        // why those coefficients are withheld rather than compared.
        let full = ihara_euler_product_window(
            &ihara_signature(&complete_graph(4), 12)
                .unwrap()
                .primitive_oriented_cycles,
        );
        let truncated = ihara_euler_product_window(&signature.primitive_oriented_cycles);
        assert_eq!(truncated[..=5], full[..=5]);
    }

    #[test]
    fn a_perturbed_primitive_cycle_count_breaks_the_ihara_comparison_at_that_length() {
        let signature = ihara_signature(&complete_graph(4), 12).unwrap();
        assert!(cross_check_ihara(&signature).agrees());
        for length in 1..=12usize {
            for delta in [1i64, -1] {
                let broken = cross_check_ihara_perturbed(&signature, &[(length, delta)]);
                assert_eq!(
                    broken.first_disagreement,
                    Some(length),
                    "perturbing length {length} by {delta} must first disagree at degree {length}"
                );
                let moved = &broken.euler_product_window[length]
                    - &cross_check_ihara(&signature).euler_product_window[length];
                assert_eq!(moved, BigInt::from(-delta));
            }
        }
    }

    #[test]
    fn a_pendant_vertex_lies_on_no_closed_geodesic_and_drops_the_determinant_degree() {
        // A triangle with one pendant edge. `2|E|` is 8, but the leading
        // coefficient of `det(I - Au + (D - I)u^2)` is `prod (deg - 1)`, which
        // the degree-one vertex sends to zero. The degree is `2|E|` of the
        // two-core, and both routes see only the triangle.
        let graph = ExactMultiGraph {
            vertex_count: 4,
            edges: [(0, 1), (1, 2), (2, 0), (0, 3)]
                .into_iter()
                .map(|(left, right)| GraphEdge {
                    left,
                    right,
                    source: format!("{left}-{right}"),
                })
                .collect(),
        };
        let signature = ihara_signature(&graph, 8).unwrap();
        let check = cross_check_ihara(&signature);
        assert_eq!(check.reciprocal_degree, 6);
        assert!(check.reciprocal_degree < 2 * graph.edges.len());
        assert_eq!(signature.primitive_oriented_cycles[2], BigInt::from(2));
        assert!(check.agrees());
        // Identical to the two-core's reciprocal: the pendant edge is invisible
        // on both routes rather than absorbed differently by each.
        let triangle = cycle_graph(3);
        assert_eq!(
            signature.reciprocal,
            ihara_signature(&triangle, 8).unwrap().reciprocal
        );
    }

    #[test]
    fn a_perturbation_above_the_horizon_is_outside_the_compared_window() {
        let signature = ihara_signature(&complete_graph(4), 5).unwrap();
        let untouched = cross_check_ihara_perturbed(&signature, &[(9, 1)]);
        assert!(untouched.agrees());
        assert_eq!(untouched.withheld_coefficients, 7);
    }

    #[test]
    fn the_four_cycle_reciprocal_is_the_square_of_one_minus_u_to_the_fourth() {
        let signature = ihara_signature(&cycle_graph(4), 8).unwrap();
        assert_eq!(
            signature.reciprocal.coefficients,
            vec![
                BigInt::one(),
                BigInt::zero(),
                BigInt::zero(),
                BigInt::zero(),
                BigInt::from(-2),
                BigInt::zero(),
                BigInt::zero(),
                BigInt::zero(),
                BigInt::one(),
            ]
        );
        assert_eq!(signature.primitive_oriented_cycles[3], BigInt::from(2));
        let check = cross_check_ihara(&signature);
        assert!(check.agrees());
        assert_eq!(check.withheld_coefficients, 0);
    }

    #[test]
    fn the_square_and_its_face_dual_are_two_frames_carrying_one_identity() {
        let (mut construction, frame) = Construction::new("square");
        construction
            .add_entity(
                "closed square",
                frame,
                Geometry::Thread {
                    vertices: vec![
                        RatVec3::from_i64(-1, -1, 0),
                        RatVec3::from_i64(1, -1, 0),
                        RatVec3::from_i64(1, 1, 0),
                        RatVec3::from_i64(-1, 1, 0),
                    ],
                    closed: true,
                },
            )
            .unwrap();
        let receiver = Receiver::new(
            ReceiverId(1),
            "square receiver",
            frame,
            ProjectionLaw::Orthographic,
        );
        let topology = analyze_receiver_topology(&construction, &receiver, 8).unwrap();
        let reading = topology.two_frame_ihara_reading();

        // The identity is what does not move.
        assert!(reading.source.cross_check.agrees());
        assert!(reading.face_dual.cross_check.agrees());

        // With no apparent crossing the source graph is the diagram graph, so
        // the two frames are a genuine planar dual pair.
        assert_eq!(reading.apparent_crossings, 0);
        assert!(reading.source_graph_is_diagram_graph);
        assert_eq!(reading.source.edge_count, reading.face_dual.edge_count);
        assert!(reading.reciprocal_degrees_agree);
        assert_eq!(reading.source.reciprocal_degree, 8);

        // The cycle ranks are complementary and sum to the shared edge count.
        assert_eq!(reading.source.cycle_rank, 1);
        assert_eq!(reading.face_dual.cycle_rank, 3);
        assert!(reading.dual_cycle_rank_sum_is_edge_count);

        // And the orbit is not trivial: the two frames' returns differ.
        assert_eq!(reading.first_reciprocal_difference, Some(2));
        assert_eq!(reading.first_cycle_count_difference, Some(2));
    }

    #[test]
    fn an_apparent_crossing_separates_the_source_graph_from_the_frame_the_face_dual_is_dual_to() {
        let (construction, receiver) = bowtie_construction();
        let topology = analyze_receiver_topology(&construction, &receiver, 12).unwrap();
        let reading = topology.two_frame_ihara_reading();

        assert_eq!(reading.apparent_crossings, 1);
        assert!(!reading.source_graph_is_diagram_graph);
        assert_eq!(reading.source.edge_count, 4);
        assert_eq!(reading.diagram_edge_count, 6);
        assert_eq!(reading.face_dual.edge_count, 6);

        // The identity still holds in both frames.
        assert!(reading.source.cross_check.agrees());
        assert!(reading.face_dual.cross_check.agrees());

        // `2|E|` is the invariant, and it is shared by the diagram graph and
        // its dual rather than by the source graph and the dual.
        assert_eq!(reading.source.reciprocal_degree, 8);
        assert_eq!(reading.face_dual.reciprocal_degree, 12);
        assert!(!reading.reciprocal_degrees_agree);
        let diagram = diagram_graph(&topology);
        let diagram_signature = ihara_signature(&diagram, 12).unwrap();
        assert_eq!(
            diagram_signature.reciprocal.coefficients.len() - 1,
            2 * reading.diagram_edge_count
        );
        assert!(cross_check_ihara(&diagram_signature).agrees());
        assert!(reading.dual_cycle_rank_sum_is_edge_count);
    }
}
