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
}
