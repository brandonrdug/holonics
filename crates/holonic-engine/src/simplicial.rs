//! Oriented simplicial incidence and exact projective hinge propagation.
//!
//! A hinge has no independent scalar behavior.  It is an oriented shared
//! boundary whose contemporary turn exists only inside its incident faces
//! and declared transport relations.  One event solves the reachable local
//! relation against one immutable predecessor and emits one atomic successor.

use std::collections::{BTreeMap, BTreeSet, VecDeque, btree_map::Entry};

use num_bigint::BigUint;
use num_traits::{One, Zero};
use relational_geometry::{FrameId, Rat};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    ConicCellId, ConicChart, EventId, EventSuccessor, ExactEventLaw, HomogeneousConic,
    NativeConicPopulation,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct VertexId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct FaceId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct HingeId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct HingeTransportId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ConicFamilyId(pub u64);

/// Topological species of the link of one vertex in the contemporary
/// two-dimensional simplicial complex.
///
/// A cycle is the combinatorial `S^1` horizon of an interior two-manifold
/// point; a path is the `B^1` horizon of a boundary point.  Everything else
/// remains explicitly singular instead of being forced into either regular
/// species.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum VertexLinkClass {
    Empty,
    Path,
    Cycle,
    Singular,
}

/// The exact closed star and link of one caused vertex.
///
/// This is the bounded topological body available to a receiver founded at
/// `pivot`.  The star is the local interior; the link is its hyperspherical
/// horizon at the current two-dimensional grain.  No coordinate radius or
/// display resolution participates in this object.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VertexStarLink {
    pub pivot: VertexId,
    pub star_vertices: BTreeSet<VertexId>,
    pub star_hinges: BTreeSet<HingeId>,
    pub star_faces: BTreeSet<FaceId>,
    pub link_vertices: BTreeSet<VertexId>,
    pub link_edges: BTreeSet<Edge>,
    pub link_class: VertexLinkClass,
}

/// One oriented one-simplex in the link of a caused vertex.
///
/// The orientation is induced by the orientation of the incident
/// two-simplex: deleting vertex `i` contributes the usual `(-1)^i` hand.
/// Consequently the cells of a regular interior link join head-to-tail into
/// the receiver's oriented directional cycle. Container order is not part of
/// this carrier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OrientedLinkCell {
    pub face: FaceId,
    pub edge: Edge,
    pub from: VertexId,
    pub to: VertexId,
    /// Orientation of `from -> to` relative to the canonical `Edge` hand.
    pub hand: i8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Edge {
    pub lower: VertexId,
    pub upper: VertexId,
}

impl Edge {
    pub fn new(left: VertexId, right: VertexId) -> Result<Self, SimplicialError> {
        if left == right {
            return Err(SimplicialError::CollapsedEdge(left));
        }
        Ok(if left < right {
            Self {
                lower: left,
                upper: right,
            }
        } else {
            Self {
                lower: right,
                upper: left,
            }
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausedVertex {
    pub id: VertexId,
    pub name: String,
    pub source_event: EventId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrientedFace {
    pub id: FaceId,
    pub name: String,
    pub source_event: EventId,
    pub vertices: [VertexId; 3],
}

impl OrientedFace {
    pub fn boundary(&self) -> [(Edge, i8); 3] {
        [
            oriented_edge(self.vertices[0], self.vertices[1]),
            oriented_edge(self.vertices[1], self.vertices[2]),
            oriented_edge(self.vertices[2], self.vertices[0]),
        ]
    }
}

fn oriented_edge(source: VertexId, target: VertexId) -> (Edge, i8) {
    let edge = Edge::new(source, target).expect("a validated face has distinct vertices");
    let hand = if source == edge.lower { 1 } else { -1 };
    (edge, hand)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrientedCoface {
    pub face: FaceId,
    pub hand: i8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Hinge {
    pub id: HingeId,
    pub name: String,
    pub source_event: EventId,
    pub edge: Edge,
    pub cofaces: [OrientedCoface; 2],
}

/// Exact incidence testimony for one identity-preserving 2-to-2 flip.
///
/// The hinge and its two coface identities survive. Only their contemporary
/// incidences change, so material and causal identities do not get silently
/// replaced by container allocation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SimplicialFlipReceipt {
    pub event: EventId,
    pub hinge: HingeId,
    pub faces: [FaceId; 2],
    pub old_diagonal: Edge,
    pub new_diagonal: Edge,
    pub held_boundary: [VertexId; 4],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SimplicialComplex {
    pub schema: String,
    pub vertices: BTreeMap<VertexId, CausedVertex>,
    pub faces: BTreeMap<FaceId, OrientedFace>,
    pub hinges: BTreeMap<HingeId, Hinge>,
    next_vertex: u64,
    next_face: u64,
    next_hinge: u64,
}

impl Default for SimplicialComplex {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.oriented-simplicial-complex.v1".to_owned(),
            vertices: BTreeMap::new(),
            faces: BTreeMap::new(),
            hinges: BTreeMap::new(),
            next_vertex: 1,
            next_face: 1,
            next_hinge: 1,
        }
    }
}

impl SimplicialComplex {
    pub fn found_vertex(&mut self, name: impl Into<String>, source_event: EventId) -> VertexId {
        let id = VertexId(self.next_vertex);
        self.next_vertex += 1;
        self.vertices.insert(
            id,
            CausedVertex {
                id,
                name: name.into(),
                source_event,
            },
        );
        id
    }

    pub fn found_face(
        &mut self,
        name: impl Into<String>,
        source_event: EventId,
        vertices: [VertexId; 3],
    ) -> Result<FaceId, SimplicialError> {
        if vertices[0] == vertices[1] || vertices[1] == vertices[2] || vertices[2] == vertices[0] {
            return Err(SimplicialError::CollapsedFace(vertices));
        }
        for vertex in vertices {
            if !self.vertices.contains_key(&vertex) {
                return Err(SimplicialError::MissingVertex(vertex));
            }
        }
        let id = FaceId(self.next_face);
        self.next_face += 1;
        self.faces.insert(
            id,
            OrientedFace {
                id,
                name: name.into(),
                source_event,
                vertices,
            },
        );
        Ok(id)
    }

    pub fn edge_cofaces(&self, edge: Edge) -> Vec<OrientedCoface> {
        self.faces
            .values()
            .flat_map(|face| {
                face.boundary()
                    .into_iter()
                    .filter_map(move |(candidate, hand)| {
                        (candidate == edge).then_some(OrientedCoface {
                            face: face.id,
                            hand,
                        })
                    })
            })
            .collect()
    }

    pub fn found_hinge(
        &mut self,
        name: impl Into<String>,
        source_event: EventId,
        edge: Edge,
    ) -> Result<HingeId, SimplicialError> {
        if self.hinges.values().any(|existing| existing.edge == edge) {
            return Err(SimplicialError::DuplicateHinge(edge));
        }
        let cofaces = self.edge_cofaces(edge);
        if cofaces.len() != 2 {
            return Err(SimplicialError::HingeCofaceCount {
                edge,
                count: cofaces.len(),
            });
        }
        if cofaces[0].hand == cofaces[1].hand {
            return Err(SimplicialError::FaceOrientationConflict {
                edge,
                left: cofaces[0].face,
                right: cofaces[1].face,
            });
        }
        let id = HingeId(self.next_hinge);
        self.next_hinge += 1;
        self.hinges.insert(
            id,
            Hinge {
                id,
                name: name.into(),
                source_event,
                edge,
                cofaces: [cofaces[0], cofaces[1]],
            },
        );
        Ok(id)
    }

    /// Atomically replace one interior diagonal by the other diagonal of its
    /// held quadrilateral while preserving the oriented exterior boundary.
    pub fn flip_hinge(
        &mut self,
        event: EventId,
        hinge: HingeId,
        proposed_diagonal: Edge,
    ) -> Result<SimplicialFlipReceipt, SimplicialError> {
        let body = self
            .hinges
            .get(&hinge)
            .cloned()
            .ok_or(SimplicialError::MissingHinge(hinge))?;
        let faces = [body.cofaces[0].face, body.cofaces[1].face];
        let opposites = faces.map(|face| {
            self.faces[&face]
                .vertices
                .into_iter()
                .find(|vertex| vertex != &body.edge.lower && vertex != &body.edge.upper)
                .expect("a valid hinge coface has one opposite vertex")
        });
        if opposites[0] == opposites[1]
            || proposed_diagonal != Edge::new(opposites[0], opposites[1])?
        {
            return Err(SimplicialError::InvalidFlipDiagonal {
                hinge,
                proposed: proposed_diagonal,
            });
        }
        if self.faces.values().any(|face| {
            face.boundary()
                .into_iter()
                .any(|(edge, _)| edge == proposed_diagonal)
        }) {
            return Err(SimplicialError::FlipDiagonalAlreadyPresent(
                proposed_diagonal,
            ));
        }

        let boundary_sum = |triangles: [[VertexId; 3]; 2]| {
            let mut sum = BTreeMap::<Edge, i16>::new();
            for vertices in triangles {
                let face = OrientedFace {
                    id: FaceId(0),
                    name: String::new(),
                    source_event: event,
                    vertices,
                };
                for (edge, hand) in face.boundary() {
                    *sum.entry(edge).or_default() += i16::from(hand);
                }
            }
            sum.retain(|_, hand| *hand != 0);
            sum
        };
        let old_boundary = boundary_sum([
            self.faces[&faces[0]].vertices,
            self.faces[&faces[1]].vertices,
        ]);
        let permutations = |vertices: [VertexId; 3]| {
            let [a, b, c] = vertices;
            [
                [a, b, c],
                [a, c, b],
                [b, a, c],
                [b, c, a],
                [c, a, b],
                [c, b, a],
            ]
        };
        let endpoint_assignments = [
            [body.edge.lower, body.edge.upper],
            [body.edge.upper, body.edge.lower],
        ];
        let mut admitted = Vec::<[[VertexId; 3]; 2]>::new();
        for endpoints in endpoint_assignments {
            for left in permutations([opposites[0], opposites[1], endpoints[0]]) {
                for right in permutations([opposites[0], opposites[1], endpoints[1]]) {
                    let candidate = [left, right];
                    if boundary_sum(candidate) == old_boundary {
                        admitted.push(candidate);
                    }
                }
            }
        }
        admitted.sort();
        admitted.dedup();
        let replacement = admitted
            .into_iter()
            .next()
            .ok_or(SimplicialError::UnorientableFlip(hinge))?;

        let mut successor = self.clone();
        successor.faces.get_mut(&faces[0]).unwrap().vertices = replacement[0];
        successor.faces.get_mut(&faces[1]).unwrap().vertices = replacement[1];
        successor.hinges.get_mut(&hinge).unwrap().edge = proposed_diagonal;
        let hinge_edges = successor
            .hinges
            .iter()
            .map(|(id, hinge)| (*id, hinge.edge))
            .collect::<Vec<_>>();
        for (id, edge) in hinge_edges {
            let cofaces = successor.edge_cofaces(edge);
            if cofaces.len() != 2 {
                return Err(SimplicialError::HingeCofaceCount {
                    edge,
                    count: cofaces.len(),
                });
            }
            if cofaces[0].hand == cofaces[1].hand {
                return Err(SimplicialError::FaceOrientationConflict {
                    edge,
                    left: cofaces[0].face,
                    right: cofaces[1].face,
                });
            }
            successor.hinges.get_mut(&id).unwrap().cofaces = [cofaces[0], cofaces[1]];
        }
        *self = successor;
        Ok(SimplicialFlipReceipt {
            event,
            hinge,
            faces,
            old_diagonal: body.edge,
            new_diagonal: proposed_diagonal,
            held_boundary: [body.edge.lower, opposites[0], body.edge.upper, opposites[1]],
        })
    }

    pub fn hinges_share_face(
        &self,
        left: HingeId,
        right: HingeId,
    ) -> Result<bool, SimplicialError> {
        let left = self
            .hinges
            .get(&left)
            .ok_or(SimplicialError::MissingHinge(left))?;
        let right = self
            .hinges
            .get(&right)
            .ok_or(SimplicialError::MissingHinge(right))?;
        Ok(left.cofaces.iter().any(|left_face| {
            right
                .cofaces
                .iter()
                .any(|right_face| left_face.face == right_face.face)
        }))
    }

    pub fn faces_incident_to(
        &self,
        hinges: impl IntoIterator<Item = HingeId>,
    ) -> Result<BTreeSet<FaceId>, SimplicialError> {
        let mut faces = BTreeSet::new();
        for hinge in hinges {
            let hinge = self
                .hinges
                .get(&hinge)
                .ok_or(SimplicialError::MissingHinge(hinge))?;
            faces.extend(hinge.cofaces.iter().map(|coface| coface.face));
        }
        Ok(faces)
    }

    /// Derive the complete closed star and link of `pivot` from actual
    /// simplicial incidence.
    pub fn vertex_star_link(&self, pivot: VertexId) -> Result<VertexStarLink, SimplicialError> {
        if !self.vertices.contains_key(&pivot) {
            return Err(SimplicialError::MissingVertex(pivot));
        }
        let star_faces = self
            .faces
            .values()
            .filter(|face| face.vertices.contains(&pivot))
            .map(|face| face.id)
            .collect::<BTreeSet<_>>();
        let mut star_vertices = star_faces
            .iter()
            .flat_map(|face| self.faces[face].vertices)
            .collect::<BTreeSet<_>>();
        // The closed star contains its pivot even when the pivot is currently
        // isolated and therefore has no incident two-simplex.
        star_vertices.insert(pivot);
        let star_edges = star_faces
            .iter()
            .flat_map(|face| {
                self.faces[face]
                    .boundary()
                    .into_iter()
                    .map(|(edge, _)| edge)
            })
            .collect::<BTreeSet<_>>();
        let star_hinges = self
            .hinges
            .values()
            .filter(|hinge| star_edges.contains(&hinge.edge))
            .map(|hinge| hinge.id)
            .collect::<BTreeSet<_>>();
        let link_vertices = star_vertices
            .iter()
            .copied()
            .filter(|vertex| *vertex != pivot)
            .collect::<BTreeSet<_>>();
        let link_edges = star_faces
            .iter()
            .map(|face| {
                let opposite = self.faces[face]
                    .vertices
                    .into_iter()
                    .filter(|vertex| *vertex != pivot)
                    .collect::<Vec<_>>();
                debug_assert_eq!(opposite.len(), 2);
                Edge::new(opposite[0], opposite[1])
                    .expect("a valid face has two distinct vertices opposite its pivot")
            })
            .collect::<BTreeSet<_>>();

        let mut degrees = link_vertices
            .iter()
            .copied()
            .map(|vertex| (vertex, 0_usize))
            .collect::<BTreeMap<_, _>>();
        let mut adjacency = link_vertices
            .iter()
            .copied()
            .map(|vertex| (vertex, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        for edge in &link_edges {
            *degrees
                .get_mut(&edge.lower)
                .expect("a link edge endpoint belongs to the link") += 1;
            *degrees
                .get_mut(&edge.upper)
                .expect("a link edge endpoint belongs to the link") += 1;
            adjacency
                .get_mut(&edge.lower)
                .expect("a link edge endpoint belongs to the link")
                .insert(edge.upper);
            adjacency
                .get_mut(&edge.upper)
                .expect("a link edge endpoint belongs to the link")
                .insert(edge.lower);
        }
        let connected = if let Some(first) = link_vertices.first().copied() {
            let mut reached = BTreeSet::from([first]);
            let mut frontier = VecDeque::from([first]);
            while let Some(vertex) = frontier.pop_front() {
                for neighbour in &adjacency[&vertex] {
                    if reached.insert(*neighbour) {
                        frontier.push_back(*neighbour);
                    }
                }
            }
            reached.len() == link_vertices.len()
        } else {
            true
        };
        let degree_one = degrees.values().filter(|degree| **degree == 1).count();
        let link_class = if link_vertices.is_empty() {
            VertexLinkClass::Empty
        } else if connected && degrees.values().all(|degree| *degree == 2) {
            VertexLinkClass::Cycle
        } else if connected
            && degree_one == 2
            && degrees.values().all(|degree| matches!(*degree, 1 | 2))
        {
            VertexLinkClass::Path
        } else {
            VertexLinkClass::Singular
        };
        Ok(VertexStarLink {
            pivot,
            star_vertices,
            star_hinges,
            star_faces,
            link_vertices,
            link_edges,
            link_class,
        })
    }

    /// Derive the complete oriented cell population of `pivot`'s link.
    ///
    /// This is deliberately distinct from `VertexStarLink::link_edges`,
    /// whose set representation records incidence but cannot carry cyclic
    /// hand. Every incident face contributes exactly one directional cell.
    pub fn oriented_vertex_link_cells(
        &self,
        pivot: VertexId,
    ) -> Result<Vec<OrientedLinkCell>, SimplicialError> {
        if !self.vertices.contains_key(&pivot) {
            return Err(SimplicialError::MissingVertex(pivot));
        }
        self.faces
            .values()
            .filter(|face| face.vertices.contains(&pivot))
            .map(|face| {
                let [from, to] = match face
                    .vertices
                    .iter()
                    .position(|vertex| *vertex == pivot)
                    .expect("the face was selected by pivot incidence")
                {
                    0 => [face.vertices[1], face.vertices[2]],
                    1 => [face.vertices[2], face.vertices[0]],
                    2 => [face.vertices[0], face.vertices[1]],
                    _ => unreachable!("a two-simplex has exactly three vertices"),
                };
                let edge = Edge::new(from, to)?;
                Ok(OrientedLinkCell {
                    face: face.id,
                    edge,
                    from,
                    to,
                    hand: if from == edge.lower { 1 } else { -1 },
                })
            })
            .collect()
    }
}

/// Exact projective re-base of one hinge turn:
///
/// `target = (a*source + b) / (c*source + d)`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectiveTurn {
    pub a: Rat,
    pub b: Rat,
    pub c: Rat,
    pub d: Rat,
}

impl ProjectiveTurn {
    pub fn new(a: Rat, b: Rat, c: Rat, d: Rat) -> Result<Self, SimplicialError> {
        if (&a * &d - &b * &c).is_zero() {
            return Err(SimplicialError::SingularTurn);
        }
        Ok(Self { a, b, c, d })
    }

    pub fn identity() -> Self {
        Self {
            a: Rat::one(),
            b: Rat::zero(),
            c: Rat::zero(),
            d: Rat::one(),
        }
    }

    pub fn apply(&self, source: &Rat) -> Option<Rat> {
        let denominator = &self.c * source + &self.d;
        (!denominator.is_zero()).then(|| (&self.a * source + &self.b) / denominator)
    }

    /// Compose two exact local turns in causal order.
    ///
    /// `first.followed_by(second)` means `second(first(q))`. Projective
    /// matrices are deliberately not normalized: a common nonzero scale is
    /// gauge and no quotient needs to choose a preferred scalar.
    pub fn followed_by(&self, second: &Self) -> Self {
        Self {
            a: &second.a * &self.a + &second.b * &self.c,
            b: &second.a * &self.b + &second.b * &self.d,
            c: &second.c * &self.a + &second.d * &self.c,
            d: &second.c * &self.b + &second.d * &self.d,
        }
    }

    /// Exact inverse projective turn.  The common determinant divisor is
    /// omitted because projective matrices are defined only up to nonzero
    /// scale.
    pub fn inverse(&self) -> Self {
        Self {
            a: self.d.clone(),
            b: -self.b.clone(),
            c: -self.c.clone(),
            d: self.a.clone(),
        }
    }

    /// Whether this matrix represents the identity projective map. Every
    /// nonzero scalar multiple of the identity is the same projective turn.
    pub fn is_projective_identity(&self) -> bool {
        self.b.is_zero() && self.c.is_zero() && self.a == self.d
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HingeTransport {
    pub id: HingeTransportId,
    pub name: String,
    pub source: HingeId,
    pub target: HingeId,
    pub turn: ProjectiveTurn,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HingeTransportNetwork {
    pub schema: String,
    pub relations: BTreeMap<HingeTransportId, HingeTransport>,
    next_relation: u64,
}

impl Default for HingeTransportNetwork {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.hinge-transport-network.v2".to_owned(),
            relations: BTreeMap::new(),
            next_relation: 1,
        }
    }
}

impl HingeTransportNetwork {
    pub fn add(
        &mut self,
        complex: &SimplicialComplex,
        name: impl Into<String>,
        source: HingeId,
        target: HingeId,
        turn: ProjectiveTurn,
    ) -> Result<HingeTransportId, SimplicialError> {
        if source == target {
            return Err(SimplicialError::ReflexiveTransport(source));
        }
        if !complex.hinges_share_face(source, target)? {
            return Err(SimplicialError::NonlocalTransport {
                from_hinge: source,
                to_hinge: target,
            });
        }
        let id = HingeTransportId(self.next_relation);
        self.next_relation += 1;
        self.relations.insert(
            id,
            HingeTransport {
                id,
                name: name.into(),
                source,
                target,
                turn,
            },
        );
        Ok(id)
    }

    fn outgoing(&self, source: HingeId) -> impl Iterator<Item = &HingeTransport> {
        self.relations
            .values()
            .filter(move |relation| relation.source == source)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AffineHingeForm {
    pub constant: Rat,
    pub terms: BTreeMap<HingeId, Rat>,
}

impl AffineHingeForm {
    pub fn constant(value: Rat) -> Self {
        Self {
            constant: value,
            terms: BTreeMap::new(),
        }
    }

    pub fn plus_hinge(mut self, hinge: HingeId, coefficient: Rat) -> Self {
        self.terms.insert(hinge, coefficient);
        self
    }

    pub fn evaluate(&self, parameters: &BTreeMap<HingeId, Rat>) -> Result<Rat, HingeWorldError> {
        let mut value = self.constant.clone();
        for (hinge, coefficient) in &self.terms {
            value += coefficient
                * parameters
                    .get(hinge)
                    .ok_or(HingeWorldError::MissingParameter(*hinge))?;
        }
        Ok(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConicFamilyLaw {
    pub id: ConicFamilyId,
    pub cell: ConicCellId,
    pub name: String,
    pub source_event: EventId,
    pub frame: FrameId,
    pub chart: ConicChart,
    pub coefficients: [AffineHingeForm; 6],
}

impl ConicFamilyLaw {
    pub fn new(
        name: impl Into<String>,
        source_event: EventId,
        frame: FrameId,
        chart: ConicChart,
        coefficients: [AffineHingeForm; 6],
    ) -> Self {
        Self {
            id: ConicFamilyId(0),
            cell: ConicCellId(0),
            name: name.into(),
            source_event,
            frame,
            chart,
            coefficients,
        }
    }

    fn form(
        &self,
        parameters: &BTreeMap<HingeId, Rat>,
    ) -> Result<HomogeneousConic, HingeWorldError> {
        Ok(HomogeneousConic::new([
            self.coefficients[0].evaluate(parameters)?,
            self.coefficients[1].evaluate(parameters)?,
            self.coefficients[2].evaluate(parameters)?,
            self.coefficients[3].evaluate(parameters)?,
            self.coefficients[4].evaluate(parameters)?,
            self.coefficients[5].evaluate(parameters)?,
        ])?)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HingeWorldStanding {
    pub schema: String,
    /// Contemporary oriented incidence. The law supplies the founding
    /// complex, but later topology deeds replace this standing value
    /// atomically; receivers must never consult a cached founding snapshot.
    pub complex: SimplicialComplex,
    pub parameters: BTreeMap<HingeId, Rat>,
    pub conics: NativeConicPopulation,
    /// First-return constituents emitted by the latest complete event. They
    /// are active topology, not executor testimony.
    pub cycle_returns: Vec<HingeCycleReturn>,
    pub open_seams: Vec<HingeOpenSeam>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HingeEvent {
    pub event: EventId,
    pub pivot: HingeId,
    pub parameter: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HingeOpenSeam {
    ConflictingCandidates {
        hinge: HingeId,
        candidates: Vec<HingeTransportCandidate>,
    },
    UndefinedTransport {
        relation: HingeTransportId,
        source: HingeId,
        target: HingeId,
        parameter: Rat,
    },
}

/// One causally distinct arrival at a hinge. Equal parameters reached through
/// different words remain plural testimony even when they glue.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HingeTransportCandidate {
    pub hinge: HingeId,
    pub parameter: Rat,
    pub relations: Vec<HingeTransportId>,
}

/// Orientation of one exact relation inside a lived transition word.
///
/// `Along` crosses the relation from its declared source to target.
/// `Against` crosses the same local overlap in the inverse direction.  The
/// direction belongs to this occurrence in the word; it is not a second
/// stored relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HingeTransitionDirection {
    Along,
    Against,
}

/// One local crossing in an ordered projective transition word.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HingeTransitionStep {
    pub relation: HingeTransportId,
    pub direction: HingeTransitionDirection,
}

/// The caused interior of a projective transport.
///
/// The word is retained instead of eagerly multiplying its factors into one
/// absolute matrix.  A product matrix is a lawful contemporary face, but it
/// is not the lived path and its coefficients can grow even when every local
/// crossing remains small.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HingeTransitionWord {
    pub steps: Vec<HingeTransitionStep>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HingeCycleClass {
    /// The complete return word is a scalar multiple of the identity.
    ProjectiveGauge,
    /// The word is nonidentity but the contemporary parameter is its fixed
    /// point. The coordinate closes while the carried frame does not.
    FixedPointHolonomy,
    /// The returned parameter differs from the entered parameter.
    DisplacedHolonomy,
}

/// One generator of the local return topology relative to the event-rooted
/// transport tree.  It stores two tree words and one chord instead of
/// enumerating every simple path around every cycle.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HingeCycleReturn {
    pub base: HingeId,
    pub source: HingeId,
    pub target: HingeId,
    pub tree_to_source: Vec<HingeTransportId>,
    pub chord: HingeTransportId,
    pub tree_to_target: Vec<HingeTransportId>,
    pub entered_parameter: Rat,
    pub returned_parameter: Rat,
    pub transition_word: HingeTransitionWord,
    pub class: HingeCycleClass,
    /// Difference between the chord arrival and the target's tree arrival.
    /// This is the exact gluing residual exposed by this generator.
    pub target_residual: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HingeRadiation {
    pub event: EventId,
    pub changed_hinges: Vec<HingeId>,
    pub changed_faces: Vec<FaceId>,
    pub changed_conics: Vec<ConicCellId>,
    pub transported_candidates: Vec<HingeTransportCandidate>,
    pub cycle_returns: Vec<HingeCycleReturn>,
    pub open_seams: Vec<HingeOpenSeam>,
    pub exact_transport_evaluations: BigUint,
}

#[derive(Clone, Debug)]
pub struct HingeWorldLaw {
    pub complex: SimplicialComplex,
    pub transports: HingeTransportNetwork,
    pub conic_families: BTreeMap<ConicFamilyId, ConicFamilyLaw>,
}

impl HingeWorldLaw {
    fn transition_turn(
        &self,
        step: HingeTransitionStep,
    ) -> Result<ProjectiveTurn, HingeWorldError> {
        let relation = self
            .transports
            .relations
            .get(&step.relation)
            .ok_or(HingeWorldError::MissingTransport(step.relation))?;
        Ok(match step.direction {
            HingeTransitionDirection::Along => relation.turn.clone(),
            HingeTransitionDirection::Against => relation.turn.inverse(),
        })
    }

    /// Apply a transition word to a homogeneous projective coordinate.
    ///
    /// Each local crossing is canonicalized before the next crossing.  Thus
    /// the carrier remains a local projective representative rather than the
    /// coefficient expansion of the complete path.  `(1,0)` carries the
    /// point at infinity without inventing an affine exception.
    fn apply_transition_word_homogeneous(
        &self,
        word: &HingeTransitionWord,
        mut numerator: Rat,
        mut denominator: Rat,
    ) -> Result<(Rat, Rat), HingeWorldError> {
        for step in &word.steps {
            let turn = self.transition_turn(*step)?;
            let next_numerator = &turn.a * &numerator + &turn.b * &denominator;
            let next_denominator = &turn.c * &numerator + &turn.d * &denominator;
            if next_denominator.is_zero() {
                numerator = Rat::one();
                denominator = Rat::zero();
            } else {
                numerator = next_numerator / &next_denominator;
                denominator = Rat::one();
            }
        }
        Ok((numerator, denominator))
    }

    fn apply_transition_word(
        &self,
        word: &HingeTransitionWord,
        source: &Rat,
    ) -> Result<Option<Rat>, HingeWorldError> {
        let (numerator, denominator) =
            self.apply_transition_word_homogeneous(word, source.clone(), Rat::one())?;
        Ok((!denominator.is_zero()).then(|| numerator / denominator))
    }

    /// A projective map is determined by three distinct projective points.
    /// Testing `0`, `1`, and infinity avoids materializing the word's product
    /// matrix while recognizing every scalar multiple of the identity.
    fn transition_word_is_identity(
        &self,
        word: &HingeTransitionWord,
    ) -> Result<bool, HingeWorldError> {
        for (source_numerator, source_denominator) in [
            (Rat::zero(), Rat::one()),
            (Rat::one(), Rat::one()),
            (Rat::one(), Rat::zero()),
        ] {
            let (target_numerator, target_denominator) = self.apply_transition_word_homogeneous(
                word,
                source_numerator.clone(),
                source_denominator.clone(),
            )?;
            if target_numerator * source_denominator != source_numerator * target_denominator {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn new(
        complex: SimplicialComplex,
        transports: HingeTransportNetwork,
        families: Vec<ConicFamilyLaw>,
    ) -> Result<Self, HingeWorldError> {
        let mut conic_families = BTreeMap::new();
        for (offset, mut family) in families.into_iter().enumerate() {
            for hinge in family
                .coefficients
                .iter()
                .flat_map(|coefficient| coefficient.terms.keys())
            {
                if !complex.hinges.contains_key(hinge) {
                    return Err(HingeWorldError::MissingHinge(*hinge));
                }
            }
            let ordinal = u64::try_from(offset + 1).expect("family count fits u64");
            family.id = ConicFamilyId(ordinal);
            family.cell = ConicCellId(ordinal);
            conic_families.insert(family.id, family);
        }
        Ok(Self {
            complex,
            transports,
            conic_families,
        })
    }

    /// Native conic cells whose constitutive forms actually depend on at
    /// least one hinge in the supplied local star.
    ///
    /// A constant family has no caused incidence with any particular star
    /// and therefore is not silently copied into every receiver section.
    pub fn conic_cells_incident_to(&self, hinges: &BTreeSet<HingeId>) -> BTreeSet<ConicCellId> {
        self.conic_families
            .values()
            .filter(|family| {
                family
                    .coefficients
                    .iter()
                    .flat_map(|coefficient| coefficient.terms.keys())
                    .any(|hinge| hinges.contains(hinge))
            })
            .map(|family| family.cell)
            .collect()
    }

    pub fn initial_standing(
        &self,
        parameters: BTreeMap<HingeId, Rat>,
    ) -> Result<HingeWorldStanding, HingeWorldError> {
        for hinge in self.complex.hinges.keys() {
            if !parameters.contains_key(hinge) {
                return Err(HingeWorldError::MissingParameter(*hinge));
            }
        }
        for hinge in parameters.keys() {
            if !self.complex.hinges.contains_key(hinge) {
                return Err(HingeWorldError::MissingHinge(*hinge));
            }
        }
        let mut conics = NativeConicPopulation::default();
        for family in self.conic_families.values() {
            let cell = conics.found(
                family.name.clone(),
                family.source_event,
                family.frame,
                family.chart.clone(),
                family.form(&parameters)?,
            );
            debug_assert_eq!(cell, family.cell);
        }
        Ok(HingeWorldStanding {
            schema: "holonic-engine.hinge-world-standing.v2".to_owned(),
            complex: self.complex.clone(),
            parameters,
            conics,
            cycle_returns: Vec::new(),
            open_seams: Vec::new(),
        })
    }

    /// Realize one already-solved, same-predecessor population of local
    /// hinge parameters.
    ///
    /// This is the kinematic mouth used by a higher-dimensional local-star
    /// law.  It deliberately performs no transport of its own: the caller
    /// has already solved the co-present local incidences and this method
    /// only emits their one conic/face successor.  Re-enacting every member
    /// as a serial `HingeEvent` would invent an order which was absent from
    /// the event.
    pub fn realize_parameter_population(
        &self,
        standing_before: &HingeWorldStanding,
        event: EventId,
        assignments: &BTreeMap<HingeId, Rat>,
    ) -> Result<(HingeWorldStanding, HingeRadiation), HingeWorldError> {
        let mut standing_after = standing_before.clone();
        let mut changed_hinges = Vec::new();
        for (hinge, parameter) in assignments {
            if !standing_before.complex.hinges.contains_key(hinge) {
                return Err(HingeWorldError::MissingHinge(*hinge));
            }
            let previous = standing_after
                .parameters
                .get_mut(hinge)
                .ok_or(HingeWorldError::MissingParameter(*hinge))?;
            if previous != parameter {
                *previous = parameter.clone();
                changed_hinges.push(*hinge);
            }
        }
        standing_after.cycle_returns.clear();
        standing_after.open_seams.clear();
        let changed_faces = standing_before
            .complex
            .faces_incident_to(changed_hinges.iter().copied())?
            .into_iter()
            .collect::<Vec<_>>();
        let mut changed_conics = Vec::new();
        for family in self.conic_families.values() {
            let form = family.form(&standing_after.parameters)?;
            let previous = standing_after
                .conics
                .cells
                .get(&family.cell)
                .ok_or(HingeWorldError::MissingConic(family.cell))?;
            if previous.form != form {
                standing_after
                    .conics
                    .replace_form(family.cell, event, form)?;
                changed_conics.push(family.cell);
            }
        }
        Ok((
            standing_after,
            HingeRadiation {
                event,
                changed_hinges,
                changed_faces,
                changed_conics,
                transported_candidates: Vec::new(),
                cycle_returns: Vec::new(),
                open_seams: Vec::new(),
                exact_transport_evaluations: BigUint::zero(),
            },
        ))
    }

    fn propagate(
        &self,
        standing_before: &HingeWorldStanding,
        event: &HingeEvent,
    ) -> Result<(HingeWorldStanding, HingeRadiation), HingeWorldError> {
        if !standing_before.complex.hinges.contains_key(&event.pivot) {
            return Err(HingeWorldError::MissingHinge(event.pivot));
        }
        let initial = HingeTransportCandidate {
            hinge: event.pivot,
            parameter: event.parameter.clone(),
            relations: Vec::new(),
        };
        let mut candidates = BTreeMap::<HingeId, Vec<HingeTransportCandidate>>::from([(
            event.pivot,
            vec![initial.clone()],
        )]);
        let mut transported_candidates = vec![initial];
        let mut tree_parameters =
            BTreeMap::<HingeId, Rat>::from([(event.pivot, event.parameter.clone())]);
        let mut tree_words =
            BTreeMap::<HingeId, Vec<HingeTransportId>>::from([(event.pivot, Vec::new())]);
        let mut tree_relations = BTreeSet::<HingeTransportId>::new();
        let mut frontier = VecDeque::from([event.pivot]);
        let mut cycle_returns = Vec::new();
        let mut open_seams = Vec::new();
        let mut conflicting_targets = BTreeSet::new();
        let mut transport_evaluations = 0_u64;

        while let Some(hinge) = frontier.pop_front() {
            let parameter = tree_parameters
                .get(&hinge)
                .expect("every frontier hinge belongs to the rooted tree")
                .clone();
            let source_word = tree_words[&hinge].clone();
            for relation in self.transports.outgoing(hinge) {
                transport_evaluations += 1;
                if let Some(target_parameter) = relation.turn.apply(&parameter) {
                    let mut relation_word = source_word.clone();
                    relation_word.push(relation.id);
                    let candidate = HingeTransportCandidate {
                        hinge: relation.target,
                        parameter: target_parameter.clone(),
                        relations: relation_word.clone(),
                    };
                    transported_candidates.push(candidate);
                    match tree_parameters.entry(relation.target) {
                        Entry::Vacant(entry) => {
                            candidates.entry(relation.target).or_default().push(
                                HingeTransportCandidate {
                                    hinge: relation.target,
                                    parameter: target_parameter.clone(),
                                    relations: relation_word.clone(),
                                },
                            );
                            tree_relations.insert(relation.id);
                            entry.insert(target_parameter);
                            tree_words.insert(relation.target, relation_word);
                            frontier.push_back(relation.target);
                        }
                        Entry::Occupied(entry) if !tree_relations.contains(&relation.id) => {
                            let existing_target_parameter = entry.get().clone();
                            let target_word = tree_words[&relation.target].clone();
                            let transition_word = HingeTransitionWord {
                                steps: source_word
                                    .iter()
                                    .copied()
                                    .map(|relation| HingeTransitionStep {
                                        relation,
                                        direction: HingeTransitionDirection::Along,
                                    })
                                    .chain(std::iter::once(HingeTransitionStep {
                                        relation: relation.id,
                                        direction: HingeTransitionDirection::Along,
                                    }))
                                    .chain(target_word.iter().rev().copied().map(|relation| {
                                        HingeTransitionStep {
                                            relation,
                                            direction: HingeTransitionDirection::Against,
                                        }
                                    }))
                                    .collect(),
                            };
                            let returned_parameter = self
                                .apply_transition_word(&transition_word, &event.parameter)?
                                .expect(
                                    "a rooted return generator has an admitted event parameter",
                                );
                            let class = if self.transition_word_is_identity(&transition_word)? {
                                HingeCycleClass::ProjectiveGauge
                            } else if returned_parameter == event.parameter {
                                HingeCycleClass::FixedPointHolonomy
                            } else {
                                HingeCycleClass::DisplacedHolonomy
                            };
                            cycle_returns.push(HingeCycleReturn {
                                base: event.pivot,
                                source: relation.source,
                                target: relation.target,
                                tree_to_source: source_word.clone(),
                                chord: relation.id,
                                tree_to_target: target_word.clone(),
                                entered_parameter: event.parameter.clone(),
                                returned_parameter,
                                transition_word,
                                class,
                                target_residual: &target_parameter - &existing_target_parameter,
                            });
                            if relation.target != event.pivot
                                && target_parameter != existing_target_parameter
                            {
                                conflicting_targets.insert(relation.target);
                                open_seams.push(HingeOpenSeam::ConflictingCandidates {
                                    hinge: relation.target,
                                    candidates: vec![
                                        HingeTransportCandidate {
                                            hinge: relation.target,
                                            parameter: existing_target_parameter,
                                            relations: target_word,
                                        },
                                        HingeTransportCandidate {
                                            hinge: relation.target,
                                            parameter: target_parameter,
                                            relations: relation_word,
                                        },
                                    ],
                                });
                            }
                        }
                        Entry::Occupied(_) => {}
                    }
                } else {
                    open_seams.push(HingeOpenSeam::UndefinedTransport {
                        relation: relation.id,
                        source: relation.source,
                        target: relation.target,
                        parameter: parameter.clone(),
                    });
                }
            }
        }

        transported_candidates.sort_by(|left, right| {
            left.hinge
                .cmp(&right.hinge)
                .then_with(|| left.parameter.cmp(&right.parameter))
                .then_with(|| left.relations.cmp(&right.relations))
        });
        cycle_returns.sort_by(|left, right| {
            left.base
                .cmp(&right.base)
                .then_with(|| left.chord.cmp(&right.chord))
        });
        let mut assignments = BTreeMap::<HingeId, Rat>::new();
        for (hinge, mut arrivals) in candidates {
            if conflicting_targets.contains(&hinge) {
                continue;
            }
            arrivals.sort_by(|left, right| {
                left.parameter
                    .cmp(&right.parameter)
                    .then_with(|| left.relations.cmp(&right.relations))
            });
            let distinct = arrivals
                .iter()
                .map(|candidate| candidate.parameter.clone())
                .collect::<BTreeSet<_>>();
            if distinct.len() == 1 {
                assignments.insert(
                    hinge,
                    distinct
                        .into_iter()
                        .next()
                        .expect("one distinct candidate exists"),
                );
            } else {
                open_seams.push(HingeOpenSeam::ConflictingCandidates {
                    hinge,
                    candidates: arrivals,
                });
            }
        }

        let mut standing_after = standing_before.clone();
        let mut changed_hinges = Vec::new();
        for (hinge, parameter) in assignments {
            let previous = standing_after
                .parameters
                .get_mut(&hinge)
                .ok_or(HingeWorldError::MissingParameter(hinge))?;
            if *previous != parameter {
                *previous = parameter;
                changed_hinges.push(hinge);
            }
        }
        standing_after.cycle_returns = cycle_returns.clone();
        standing_after.open_seams = open_seams.clone();
        let changed_faces = standing_before
            .complex
            .faces_incident_to(changed_hinges.iter().copied())?
            .into_iter()
            .collect::<Vec<_>>();
        let mut changed_conics = Vec::new();
        for family in self.conic_families.values() {
            let form = family.form(&standing_after.parameters)?;
            let previous = standing_after
                .conics
                .cells
                .get(&family.cell)
                .ok_or(HingeWorldError::MissingConic(family.cell))?;
            if previous.form != form {
                standing_after
                    .conics
                    .replace_form(family.cell, event.event, form)?;
                changed_conics.push(family.cell);
            }
        }

        Ok((
            standing_after,
            HingeRadiation {
                event: event.event,
                changed_hinges,
                changed_faces,
                changed_conics,
                transported_candidates,
                cycle_returns,
                open_seams,
                exact_transport_evaluations: BigUint::from(transport_evaluations),
            },
        ))
    }
}

impl ExactEventLaw for HingeWorldLaw {
    type Standing = HingeWorldStanding;
    type Event = HingeEvent;
    type Radiation = HingeRadiation;
    type Error = HingeWorldError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        let (standing_after, radiation) = self.propagate(standing_before, event)?;
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![radiation],
            logical_resources: None,
            physical_resources: None,
        })
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum SimplicialError {
    #[error("vertex {0:?} is absent")]
    MissingVertex(VertexId),
    #[error("hinge {0:?} is absent")]
    MissingHinge(HingeId),
    #[error("edge at vertex {0:?} is collapsed")]
    CollapsedEdge(VertexId),
    #[error("face {0:?} contains a repeated vertex")]
    CollapsedFace([VertexId; 3]),
    #[error("edge {0:?} already carries a hinge")]
    DuplicateHinge(Edge),
    #[error("hinge {hinge:?} cannot be flipped onto proposed diagonal {proposed:?}")]
    InvalidFlipDiagonal { hinge: HingeId, proposed: Edge },
    #[error("proposed flip diagonal {0:?} is already present in the complex")]
    FlipDiagonalAlreadyPresent(Edge),
    #[error("hinge {0:?}'s two cofaces admit no orientation-preserving 2-to-2 flip")]
    UnorientableFlip(HingeId),
    #[error("edge {edge:?} has {count} cofaces rather than exactly two")]
    HingeCofaceCount { edge: Edge, count: usize },
    #[error("faces {left:?} and {right:?} carry the same hand at shared edge {edge:?}")]
    FaceOrientationConflict {
        edge: Edge,
        left: FaceId,
        right: FaceId,
    },
    #[error("a projective turn must have nonzero determinant")]
    SingularTurn,
    #[error("a hinge cannot transport to itself: {0:?}")]
    ReflexiveTransport(HingeId),
    #[error("hinges {from_hinge:?} and {to_hinge:?} share no incident face")]
    NonlocalTransport {
        from_hinge: HingeId,
        to_hinge: HingeId,
    },
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum HingeWorldError {
    #[error("hinge {0:?} is absent")]
    MissingHinge(HingeId),
    #[error("hinge transport {0:?} is absent")]
    MissingTransport(HingeTransportId),
    #[error("standing has no exact parameter for hinge {0:?}")]
    MissingParameter(HingeId),
    #[error("standing has no realized conic cell {0:?}")]
    MissingConic(ConicCellId),
    #[error(transparent)]
    Simplicial(#[from] SimplicialError),
    #[error(transparent)]
    Conic(#[from] crate::ConicError),
}

#[cfg(test)]
mod tests {
    use relational_geometry::{Construction, RatVec3, integer};

    use super::*;
    use crate::{CausalWorld, ConicClass};

    struct Strip {
        complex: SimplicialComplex,
        first: HingeId,
        second: HingeId,
        unrelated: HingeId,
        source_event: EventId,
    }

    fn strip() -> Strip {
        let source_event = EventId(1);
        let mut complex = SimplicialComplex::default();
        let vertices = (0..10)
            .map(|index| complex.found_vertex(format!("v{index}"), source_event))
            .collect::<Vec<_>>();
        complex
            .found_face(
                "first",
                source_event,
                [vertices[0], vertices[1], vertices[2]],
            )
            .unwrap();
        complex
            .found_face(
                "middle",
                source_event,
                [vertices[2], vertices[1], vertices[3]],
            )
            .unwrap();
        complex
            .found_face(
                "last",
                source_event,
                [vertices[2], vertices[3], vertices[4]],
            )
            .unwrap();
        complex
            .found_face(
                "unrelated-left",
                source_event,
                [vertices[5], vertices[6], vertices[7]],
            )
            .unwrap();
        complex
            .found_face(
                "unrelated-right",
                source_event,
                [vertices[7], vertices[6], vertices[8]],
            )
            .unwrap();
        let first = complex
            .found_hinge(
                "first hinge",
                source_event,
                Edge::new(vertices[1], vertices[2]).unwrap(),
            )
            .unwrap();
        let second = complex
            .found_hinge(
                "second hinge",
                source_event,
                Edge::new(vertices[2], vertices[3]).unwrap(),
            )
            .unwrap();
        let unrelated = complex
            .found_hinge(
                "unrelated hinge",
                source_event,
                Edge::new(vertices[6], vertices[7]).unwrap(),
            )
            .unwrap();
        Strip {
            complex,
            first,
            second,
            unrelated,
            source_event,
        }
    }

    fn circle_family(hinge: HingeId, source_event: EventId, frame: FrameId) -> ConicFamilyLaw {
        ConicFamilyLaw::new(
            "hinge-caused circle",
            source_event,
            frame,
            ConicChart::new(
                RatVec3::zero(),
                RatVec3::from_i64(1, 0, 0),
                RatVec3::from_i64(0, 1, 0),
            )
            .unwrap(),
            [
                AffineHingeForm::constant(integer(1)),
                AffineHingeForm::constant(integer(0)),
                AffineHingeForm::constant(integer(1)),
                AffineHingeForm::constant(integer(0)),
                AffineHingeForm::constant(integer(0)),
                AffineHingeForm::constant(integer(-1)).plus_hinge(hinge, integer(-1)),
            ],
        )
    }

    #[test]
    fn one_event_changes_only_its_reachable_local_star_and_caused_conic() {
        let strip = strip();
        let mut network = HingeTransportNetwork::default();
        network
            .add(
                &strip.complex,
                "turn crosses the middle face",
                strip.first,
                strip.second,
                ProjectiveTurn::identity(),
            )
            .unwrap();
        let (construction, frame) = Construction::new("receiver frame");
        let law = HingeWorldLaw::new(
            strip.complex.clone(),
            network,
            vec![circle_family(strip.second, strip.source_event, frame)],
        )
        .unwrap();
        let standing = law
            .initial_standing(BTreeMap::from([
                (strip.first, integer(0)),
                (strip.second, integer(0)),
                (strip.unrelated, integer(0)),
            ]))
            .unwrap();
        let before = standing.conics.cells[&ConicCellId(1)].form.clone();
        assert_eq!(before.classify(), ConicClass::CircleInThisChart);
        let mut world = CausalWorld::new(law, standing);
        let receipt = world
            .receive(&HingeEvent {
                event: EventId(2),
                pivot: strip.first,
                parameter: integer(3),
            })
            .unwrap();
        let radiation = &receipt.radiation[0];
        assert_eq!(radiation.changed_hinges, vec![strip.first, strip.second]);
        assert!(!radiation.changed_faces.is_empty());
        assert_eq!(radiation.changed_conics, vec![ConicCellId(1)]);
        assert_eq!(world.standing().parameters[&strip.unrelated], integer(0));
        assert_eq!(
            world.standing().conics.cells[&ConicCellId(1)].form.ww,
            integer(-4)
        );
        drop(construction);
    }

    #[test]
    fn incompatible_paths_leave_an_explicit_seam_without_fabricating_a_target() {
        let strip = strip();
        let mut network = HingeTransportNetwork::default();
        network
            .add(
                &strip.complex,
                "identity candidate",
                strip.first,
                strip.second,
                ProjectiveTurn::identity(),
            )
            .unwrap();
        network
            .add(
                &strip.complex,
                "translated candidate",
                strip.first,
                strip.second,
                ProjectiveTurn::new(integer(1), integer(1), integer(0), integer(1)).unwrap(),
            )
            .unwrap();
        let (_, frame) = Construction::new("receiver frame");
        let law = HingeWorldLaw::new(
            strip.complex,
            network,
            vec![circle_family(strip.second, strip.source_event, frame)],
        )
        .unwrap();
        let standing = law
            .initial_standing(BTreeMap::from([
                (strip.first, integer(0)),
                (strip.second, integer(0)),
                (strip.unrelated, integer(0)),
            ]))
            .unwrap();
        let mut world = CausalWorld::new(law, standing);
        let receipt = world
            .receive(&HingeEvent {
                event: EventId(2),
                pivot: strip.first,
                parameter: integer(2),
            })
            .unwrap();
        assert_eq!(world.standing().parameters[&strip.first], integer(2));
        assert_eq!(world.standing().parameters[&strip.second], integer(0));
        assert!(matches!(
            receipt.radiation[0].open_seams.as_slice(),
            [HingeOpenSeam::ConflictingCandidates { hinge, candidates }]
                if *hinge == strip.second
                    && candidates.iter().map(|candidate| candidate.parameter.clone()).collect::<Vec<_>>()
                        == vec![integer(2), integer(3)]
        ));
    }

    #[test]
    fn first_return_carries_one_compressed_generator_and_exact_holonomy() {
        let source_event = EventId(1);
        let mut complex = SimplicialComplex::default();
        let vertices = (0..4)
            .map(|index| complex.found_vertex(format!("v{index}"), source_event))
            .collect::<Vec<_>>();
        for (name, face) in [
            ("front", [vertices[0], vertices[2], vertices[1]]),
            ("right", [vertices[0], vertices[1], vertices[3]]),
            ("left", [vertices[0], vertices[3], vertices[2]]),
            ("base", [vertices[1], vertices[2], vertices[3]]),
        ] {
            complex.found_face(name, source_event, face).unwrap();
        }
        let first = complex
            .found_hinge(
                "first",
                source_event,
                Edge::new(vertices[0], vertices[1]).unwrap(),
            )
            .unwrap();
        let second = complex
            .found_hinge(
                "second",
                source_event,
                Edge::new(vertices[0], vertices[2]).unwrap(),
            )
            .unwrap();
        let third = complex
            .found_hinge(
                "third",
                source_event,
                Edge::new(vertices[0], vertices[3]).unwrap(),
            )
            .unwrap();
        let translate =
            ProjectiveTurn::new(integer(1), integer(1), integer(0), integer(1)).unwrap();
        let mut network = HingeTransportNetwork::default();
        let first_relation = network
            .add(
                &complex,
                "first to second",
                first,
                second,
                translate.clone(),
            )
            .unwrap();
        let second_relation = network
            .add(
                &complex,
                "second to third",
                second,
                third,
                translate.clone(),
            )
            .unwrap();
        let third_relation = network
            .add(&complex, "third to first", third, first, translate)
            .unwrap();
        let law = HingeWorldLaw::new(complex, network, Vec::new()).unwrap();
        let standing = law
            .initial_standing(BTreeMap::from([
                (first, integer(0)),
                (second, integer(0)),
                (third, integer(0)),
            ]))
            .unwrap();
        let successor = law
            .enact(
                &standing,
                &HingeEvent {
                    event: EventId(2),
                    pivot: first,
                    parameter: integer(2),
                },
            )
            .unwrap();
        let radiation = &successor.radiation[0];

        assert_eq!(successor.standing_after.parameters[&first], integer(2));
        assert_eq!(successor.standing_after.parameters[&second], integer(3));
        assert_eq!(successor.standing_after.parameters[&third], integer(4));
        assert_eq!(radiation.cycle_returns.len(), 1);
        let returned = &radiation.cycle_returns[0];
        assert_eq!(
            successor.standing_after.cycle_returns,
            vec![returned.clone()]
        );
        assert_eq!(returned.base, first);
        assert_eq!(returned.source, third);
        assert_eq!(returned.target, first);
        assert_eq!(
            returned.tree_to_source,
            vec![first_relation, second_relation]
        );
        assert_eq!(returned.chord, third_relation);
        assert!(returned.tree_to_target.is_empty());
        assert_eq!(returned.entered_parameter, integer(2));
        assert_eq!(returned.returned_parameter, integer(5));
        assert_eq!(returned.class, HingeCycleClass::DisplacedHolonomy);
        assert_eq!(returned.target_residual, integer(3));
    }
}
