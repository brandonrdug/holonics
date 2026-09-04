//! Relational construction state.
//!
//! A frame is not a global coordinate system.  It is one local chart joined
//! to other charts by declared exact maps.  Geometry can be compared only
//! when a unique route is available or a caller supplies an explicit route.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::exact::{
    AffineMap3, Rat, RatMat3, RatVec3, cayley_rotation_x, cayley_rotation_y, cayley_rotation_z,
    format_rat, integer, rat, rational_circle, sign,
};

macro_rules! id_type {
    ($name:ident) => {
        #[derive(
            Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
        )]
        pub struct $name(pub u64);

        impl std::fmt::Display for $name {
            fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(formatter, "{}", self.0)
            }
        }
    };
}

id_type!(FrameId);
id_type!(RelationId);
id_type!(EntityId);
id_type!(ConstraintId);

/// One exact ordered chart carried by a local frame.
///
/// The chart is not an ambient coordinate system. Its origin and ordered
/// basis vectors state how local components are embodied inside this frame.
/// A receiver can compare it with another chart only through declared frame
/// relations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalChart {
    pub origin: RatVec3,
    pub basis: [RatVec3; 3],
    pub labels: [String; 3],
}

impl Default for LocalChart {
    fn default() -> Self {
        Self {
            origin: RatVec3::zero(),
            basis: [
                RatVec3::from_i64(1, 0, 0),
                RatVec3::from_i64(0, 1, 0),
                RatVec3::from_i64(0, 0, 1),
            ],
            labels: ["e1".to_owned(), "e2".to_owned(), "e3".to_owned()],
        }
    }
}

impl LocalChart {
    pub fn point(&self, components: &RatVec3) -> RatVec3 {
        self.origin
            .add(&self.basis[0].scale(&components.x))
            .add(&self.basis[1].scale(&components.y))
            .add(&self.basis[2].scale(&components.z))
    }

    pub fn basis_matrix(&self) -> RatMat3 {
        RatMat3::new([
            [
                self.basis[0].x.clone(),
                self.basis[1].x.clone(),
                self.basis[2].x.clone(),
            ],
            [
                self.basis[0].y.clone(),
                self.basis[1].y.clone(),
                self.basis[2].y.clone(),
            ],
            [
                self.basis[0].z.clone(),
                self.basis[1].z.clone(),
                self.basis[2].z.clone(),
            ],
        ])
    }

    pub fn gram(&self) -> RatMat3 {
        let basis = self.basis_matrix();
        basis.transpose().multiply(&basis)
    }

    pub fn orientation(&self) -> i8 {
        sign(&self.basis_matrix().determinant())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalFrame {
    pub id: FrameId,
    pub name: String,
    pub rank: usize,
    #[serde(default)]
    pub chart: LocalChart,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HingeAxis {
    X,
    Y,
    Z,
}

impl HingeAxis {
    pub fn rotation(self, parameter: &Rat) -> RatMat3 {
        match self {
            Self::X => cayley_rotation_x(parameter),
            Self::Y => cayley_rotation_y(parameter),
            Self::Z => cayley_rotation_z(parameter),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FrameRelationKind {
    Declared {
        law: String,
    },
    Hinge {
        pivot_in_target: RatVec3,
        axis: HingeAxis,
        parameter: Rat,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrameRelation {
    pub id: RelationId,
    pub name: String,
    /// The exact affine map carries coordinates from `source` to `target`.
    pub source: FrameId,
    pub target: FrameId,
    pub forward: AffineMap3,
    pub kind: FrameRelationKind,
}

impl FrameRelation {
    pub fn inverse_map(&self) -> Option<AffineMap3> {
        self.forward.inverse()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConicSpecies {
    Circle,
    Ellipse,
    Hyperbola,
    LinePair,
}

impl ConicSpecies {
    pub fn label(self) -> &'static str {
        match self {
            Self::Circle => "circle",
            Self::Ellipse => "ellipse",
            Self::Hyperbola => "hyperbola",
            Self::LinePair => "line pair",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectiveConic {
    pub center: RatVec3,
    /// First intrinsic conic axis in the entity's local frame.
    pub axis_u: RatVec3,
    /// Second intrinsic conic axis in the entity's local frame.
    pub axis_v: RatVec3,
    pub species: ConicSpecies,
}

impl ProjectiveConic {
    pub fn intrinsic_form(&self) -> RatMat3 {
        let second_sign = match self.species {
            ConicSpecies::Circle | ConicSpecies::Ellipse => Rat::one(),
            ConicSpecies::Hyperbola => -Rat::one(),
            ConicSpecies::LinePair => Rat::zero(),
        };
        RatMat3::new([
            [Rat::one(), Rat::zero(), Rat::zero()],
            [Rat::zero(), second_sign, Rat::zero()],
            [Rat::zero(), Rat::zero(), -Rat::one()],
        ])
    }

    pub fn determinant(&self) -> Rat {
        self.intrinsic_form().determinant()
    }

    pub fn equation(&self) -> &'static str {
        match self.species {
            ConicSpecies::Circle | ConicSpecies::Ellipse => "alpha^2 + beta^2 - omega^2 = 0",
            ConicSpecies::Hyperbola => "alpha^2 - beta^2 - omega^2 = 0",
            ConicSpecies::LinePair => "alpha^2 - omega^2 = 0",
        }
    }

    pub fn rational_parameterization(&self) -> &'static str {
        match self.species {
            ConicSpecies::Circle | ConicSpecies::Ellipse => "C(u)=(1-u^2)/(1+u^2), S(u)=2u/(1+u^2)",
            ConicSpecies::Hyperbola => "C_h(u)=(1+u^2)/(1-u^2), S_h(u)=2u/(1-u^2)",
            ConicSpecies::LinePair => "alpha=+omega or alpha=-omega; beta is free",
        }
    }

    /// Exact points used by a receiver membrane.  They remain rational until
    /// the final raster conversion.
    pub fn exact_samples(&self, subdivisions: i64) -> Vec<Vec<RatVec3>> {
        assert!(subdivisions >= 2);
        match self.species {
            ConicSpecies::Circle | ConicSpecies::Ellipse => {
                let mut right = Vec::new();
                for step in -subdivisions..=subdivisions {
                    let parameter = rat(step, subdivisions);
                    let (cosine, sine) = rational_circle(&parameter);
                    right.push(
                        self.center
                            .add(&self.axis_u.scale(&cosine))
                            .add(&self.axis_v.scale(&sine)),
                    );
                }
                let mut left = right
                    .iter()
                    .rev()
                    .map(|point| {
                        let displacement = point.subtract(&self.center);
                        self.center.subtract(&displacement)
                    })
                    .collect::<Vec<_>>();
                right.append(&mut left);
                vec![right]
            }
            ConicSpecies::Hyperbola => {
                let mut positive = Vec::new();
                for step in (-subdivisions + 1)..subdivisions {
                    let parameter = rat(step, subdivisions);
                    let square = &parameter * &parameter;
                    let denominator = Rat::one() - &square;
                    let cosine = (Rat::one() + square) / &denominator;
                    let sine = (integer(2) * &parameter) / denominator;
                    positive.push(
                        self.center
                            .add(&self.axis_u.scale(&cosine))
                            .add(&self.axis_v.scale(&sine)),
                    );
                }
                let negative = positive
                    .iter()
                    .map(|point| {
                        let displacement = point.subtract(&self.center);
                        self.center.subtract(&displacement)
                    })
                    .collect();
                vec![positive, negative]
            }
            ConicSpecies::LinePair => {
                let extent = integer(3);
                let first_center = self.center.add(&self.axis_u);
                let second_center = self.center.subtract(&self.axis_u);
                vec![
                    vec![
                        first_center.subtract(&self.axis_v.scale(&extent)),
                        first_center.add(&self.axis_v.scale(&extent)),
                    ],
                    vec![
                        second_center.subtract(&self.axis_v.scale(&extent)),
                        second_center.add(&self.axis_v.scale(&extent)),
                    ],
                ]
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Geometry {
    Triangle {
        vertices: [RatVec3; 3],
    },
    Conic(ProjectiveConic),
    Thread {
        vertices: Vec<RatVec3>,
        closed: bool,
    },
}

impl Geometry {
    pub fn kind_label(&self) -> &'static str {
        match self {
            Self::Triangle { .. } => "triangle",
            Self::Conic(conic) => conic.species.label(),
            Self::Thread { closed: true, .. } => "closed thread",
            Self::Thread { closed: false, .. } => "thread",
        }
    }

    pub fn control_points(&self) -> Vec<RatVec3> {
        match self {
            Self::Triangle { vertices } => vertices.to_vec(),
            Self::Conic(conic) => vec![
                conic.center.clone(),
                conic.center.add(&conic.axis_u),
                conic.center.add(&conic.axis_v),
            ],
            Self::Thread { vertices, .. } => vertices.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeometryEntity {
    pub id: EntityId,
    pub name: String,
    pub frame: FrameId,
    pub geometry: Geometry,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConstraintKind {
    SharedVertex {
        left: EntityId,
        right: EntityId,
        left_vertex: usize,
        right_vertex: usize,
    },
    PointOnConic {
        point_entity: EntityId,
        point_index: usize,
        conic: EntityId,
    },
    Declared {
        expression: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Constraint {
    pub id: ConstraintId,
    pub name: String,
    pub kind: ConstraintKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Construction {
    pub schema: String,
    pub frames: BTreeMap<FrameId, LocalFrame>,
    pub relations: BTreeMap<RelationId, FrameRelation>,
    pub entities: BTreeMap<EntityId, GeometryEntity>,
    pub constraints: BTreeMap<ConstraintId, Constraint>,
    next_frame: u64,
    next_relation: u64,
    next_entity: u64,
    next_constraint: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PathStep {
    relation: RelationId,
    next_frame: FrameId,
    map: AffineMap3,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum TransportError {
    #[error("frame {0} is not present")]
    MissingFrame(FrameId),
    #[error("no declared relation joins frame {from} to frame {target}")]
    Disconnected { from: FrameId, target: FrameId },
    #[error(
        "more than one relation path joins frame {from} to frame {target}; an explicit route is required"
    )]
    Ambiguous { from: FrameId, target: FrameId },
    #[error("relation {0} is not present")]
    MissingRelation(RelationId),
    #[error("relation {relation} does not continue from frame {frame}")]
    BrokenRoute {
        relation: RelationId,
        frame: FrameId,
    },
    #[error("route terminates at frame {actual}, expected frame {expected}")]
    WrongRouteEnd { actual: FrameId, expected: FrameId },
    #[error("relation {0} is not invertible")]
    SingularRelation(RelationId),
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ConstructionError {
    #[error("entity {0} is not present")]
    MissingEntity(EntityId),
    #[error("frame {0} is not present")]
    MissingFrame(FrameId),
    #[error("relation {0} is not present")]
    MissingRelation(RelationId),
    #[error("entity {entity} is not carried by relation {relation}'s source frame")]
    HingeFrameMismatch {
        entity: EntityId,
        relation: RelationId,
    },
    #[error("relation {0} is not a hinge")]
    NotAHinge(RelationId),
}

impl Construction {
    pub fn new(first_frame_name: impl Into<String>) -> (Self, FrameId) {
        let first = FrameId(1);
        let mut frames = BTreeMap::new();
        frames.insert(
            first,
            LocalFrame {
                id: first,
                name: first_frame_name.into(),
                rank: 3,
                chart: LocalChart::default(),
            },
        );
        (
            Self {
                schema: "relational-geometry.construction.v1".to_owned(),
                frames,
                relations: BTreeMap::new(),
                entities: BTreeMap::new(),
                constraints: BTreeMap::new(),
                next_frame: 2,
                next_relation: 1,
                next_entity: 1,
                next_constraint: 1,
            },
            first,
        )
    }

    pub fn add_frame(&mut self, name: impl Into<String>, rank: usize) -> FrameId {
        let id = FrameId(self.next_frame);
        self.next_frame += 1;
        self.frames.insert(
            id,
            LocalFrame {
                id,
                name: name.into(),
                rank,
                chart: LocalChart::default(),
            },
        );
        id
    }

    pub fn add_relation(
        &mut self,
        name: impl Into<String>,
        source: FrameId,
        target: FrameId,
        forward: AffineMap3,
        kind: FrameRelationKind,
    ) -> Result<RelationId, ConstructionError> {
        if !self.frames.contains_key(&source) {
            return Err(ConstructionError::MissingFrame(source));
        }
        if !self.frames.contains_key(&target) {
            return Err(ConstructionError::MissingFrame(target));
        }
        let id = RelationId(self.next_relation);
        self.next_relation += 1;
        self.relations.insert(
            id,
            FrameRelation {
                id,
                name: name.into(),
                source,
                target,
                forward,
                kind,
            },
        );
        Ok(id)
    }

    pub fn add_entity(
        &mut self,
        name: impl Into<String>,
        frame: FrameId,
        geometry: Geometry,
    ) -> Result<EntityId, ConstructionError> {
        if !self.frames.contains_key(&frame) {
            return Err(ConstructionError::MissingFrame(frame));
        }
        let id = EntityId(self.next_entity);
        self.next_entity += 1;
        self.entities.insert(
            id,
            GeometryEntity {
                id,
                name: name.into(),
                frame,
                geometry,
            },
        );
        Ok(id)
    }

    pub fn add_constraint(
        &mut self,
        name: impl Into<String>,
        kind: ConstraintKind,
    ) -> ConstraintId {
        let id = ConstraintId(self.next_constraint);
        self.next_constraint += 1;
        self.constraints.insert(
            id,
            Constraint {
                id,
                name: name.into(),
                kind,
            },
        );
        id
    }

    /// Place one entity in a new child frame and join that frame to the
    /// supplied parent by an exact hinge.  The pivot is expressed in both
    /// frames at the moment the hinge is founded.
    pub fn found_hinge(
        &mut self,
        entity: EntityId,
        parent: FrameId,
        pivot: RatVec3,
        axis: HingeAxis,
        parameter: Rat,
    ) -> Result<RelationId, ConstructionError> {
        let entity_name = self
            .entities
            .get(&entity)
            .ok_or(ConstructionError::MissingEntity(entity))?
            .name
            .clone();
        if !self.frames.contains_key(&parent) {
            return Err(ConstructionError::MissingFrame(parent));
        }
        let child = self.add_frame(format!("{entity_name} hinge frame"), 3);
        self.entities
            .get_mut(&entity)
            .expect("entity was checked")
            .frame = child;
        let map = AffineMap3::rotation_about(&pivot, axis.rotation(&parameter));
        self.add_relation(
            format!("{entity_name} hinge"),
            child,
            parent,
            map,
            FrameRelationKind::Hinge {
                pivot_in_target: pivot,
                axis,
                parameter,
            },
        )
    }

    pub fn set_hinge_parameter(
        &mut self,
        relation: RelationId,
        parameter: Rat,
    ) -> Result<(), ConstructionError> {
        let relation = self
            .relations
            .get_mut(&relation)
            .ok_or(ConstructionError::MissingRelation(relation))?;
        let FrameRelationKind::Hinge {
            pivot_in_target,
            axis,
            parameter: current,
        } = &mut relation.kind
        else {
            return Err(ConstructionError::NotAHinge(relation.id));
        };
        *current = parameter;
        relation.forward = AffineMap3::rotation_about(pivot_in_target, axis.rotation(current));
        Ok(())
    }

    pub fn hinge_for_entity(&self, entity: EntityId) -> Option<RelationId> {
        let frame = self.entities.get(&entity)?.frame;
        self.relations.values().find_map(|relation| {
            (relation.source == frame && matches!(relation.kind, FrameRelationKind::Hinge { .. }))
                .then_some(relation.id)
        })
    }

    pub fn transport(
        &self,
        source: FrameId,
        target: FrameId,
    ) -> Result<AffineMap3, TransportError> {
        if !self.frames.contains_key(&source) {
            return Err(TransportError::MissingFrame(source));
        }
        if !self.frames.contains_key(&target) {
            return Err(TransportError::MissingFrame(target));
        }
        if source == target {
            return Ok(AffineMap3::identity());
        }

        let mut paths = Vec::new();
        let mut visited = BTreeSet::from([source]);
        self.collect_paths(source, target, &mut visited, &mut Vec::new(), &mut paths)?;
        match paths.len() {
            0 => Err(TransportError::Disconnected {
                from: source,
                target,
            }),
            1 => Ok(Self::compose_steps(&paths[0])),
            _ => Err(TransportError::Ambiguous {
                from: source,
                target,
            }),
        }
    }

    pub fn transport_via(
        &self,
        source: FrameId,
        target: FrameId,
        route: &[RelationId],
    ) -> Result<AffineMap3, TransportError> {
        if !self.frames.contains_key(&source) {
            return Err(TransportError::MissingFrame(source));
        }
        if !self.frames.contains_key(&target) {
            return Err(TransportError::MissingFrame(target));
        }
        let mut current = source;
        let mut map = AffineMap3::identity();
        for id in route {
            let relation = self
                .relations
                .get(id)
                .ok_or(TransportError::MissingRelation(*id))?;
            let step = if relation.source == current {
                PathStep {
                    relation: *id,
                    next_frame: relation.target,
                    map: relation.forward.clone(),
                }
            } else if relation.target == current {
                PathStep {
                    relation: *id,
                    next_frame: relation.source,
                    map: relation
                        .inverse_map()
                        .ok_or(TransportError::SingularRelation(*id))?,
                }
            } else {
                return Err(TransportError::BrokenRoute {
                    relation: *id,
                    frame: current,
                });
            };
            map = map.followed_by(&step.map);
            current = step.next_frame;
        }
        if current != target {
            return Err(TransportError::WrongRouteEnd {
                actual: current,
                expected: target,
            });
        }
        Ok(map)
    }

    fn collect_paths(
        &self,
        current: FrameId,
        target: FrameId,
        visited: &mut BTreeSet<FrameId>,
        path: &mut Vec<PathStep>,
        results: &mut Vec<Vec<PathStep>>,
    ) -> Result<(), TransportError> {
        if results.len() > 1 {
            return Ok(());
        }
        for relation in self.relations.values() {
            let step = if relation.source == current {
                Some(PathStep {
                    relation: relation.id,
                    next_frame: relation.target,
                    map: relation.forward.clone(),
                })
            } else if relation.target == current {
                Some(PathStep {
                    relation: relation.id,
                    next_frame: relation.source,
                    map: relation
                        .inverse_map()
                        .ok_or(TransportError::SingularRelation(relation.id))?,
                })
            } else {
                None
            };
            let Some(step) = step else {
                continue;
            };
            if visited.contains(&step.next_frame) {
                continue;
            }
            path.push(step.clone());
            if step.next_frame == target {
                results.push(path.clone());
            } else {
                visited.insert(step.next_frame);
                self.collect_paths(step.next_frame, target, visited, path, results)?;
                visited.remove(&step.next_frame);
            }
            path.pop();
        }
        Ok(())
    }

    fn compose_steps(steps: &[PathStep]) -> AffineMap3 {
        let mut map = AffineMap3::identity();
        for step in steps {
            map = map.followed_by(&step.map);
        }
        map
    }

    /// Compact integrity witness for the selected RON archive encoding.
    ///
    /// This is not construction identity: causal or structural sameness must
    /// be established in the construction type and its declared relations.
    pub fn archive_digest(&self) -> String {
        let encoded = ron::to_string(self).expect("construction state is serializable");
        let mut digest = Sha256::new();
        digest.update(encoded.as_bytes());
        let bytes = digest.finalize();
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    pub fn exact_summary(&self) -> Vec<String> {
        vec![
            format!("{} local frames", self.frames.len()),
            format!("{} declared frame relations", self.relations.len()),
            format!("{} geometric entities", self.entities.len()),
            format!("{} exact constraints", self.constraints.len()),
        ]
    }
}

pub fn starter_conic(species: ConicSpecies) -> ProjectiveConic {
    let (axis_u, axis_v) = match species {
        ConicSpecies::Circle => (RatVec3::from_i64(2, 0, 0), RatVec3::from_i64(0, 2, 0)),
        ConicSpecies::Ellipse => (RatVec3::from_i64(3, 0, 0), RatVec3::from_i64(0, 2, 0)),
        ConicSpecies::Hyperbola => (RatVec3::from_i64(2, 0, 0), RatVec3::from_i64(0, 1, 0)),
        ConicSpecies::LinePair => (RatVec3::from_i64(1, 0, 0), RatVec3::from_i64(0, 1, 0)),
    };
    ProjectiveConic {
        center: RatVec3::zero(),
        axis_u,
        axis_v,
        species,
    }
}

pub fn describe_point(point: &RatVec3) -> String {
    format!(
        "({}, {}, {})",
        format_rat(&point.x),
        format_rat(&point.y),
        format_rat(&point.z)
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disconnected_frames_refuse_an_inferred_common_chart() {
        let (mut construction, first) = Construction::new("first");
        let second = construction.add_frame("second", 3);
        assert_eq!(
            construction.transport(first, second),
            Err(TransportError::Disconnected {
                from: first,
                target: second
            })
        );
    }

    #[test]
    fn multiple_routes_refuse_an_implicit_transport() {
        let (mut construction, first) = Construction::new("first");
        let second = construction.add_frame("second", 3);
        let third = construction.add_frame("third", 3);
        construction
            .add_relation(
                "direct",
                first,
                third,
                AffineMap3::identity(),
                FrameRelationKind::Declared {
                    law: "direct".to_owned(),
                },
            )
            .unwrap();
        construction
            .add_relation(
                "first-second",
                first,
                second,
                AffineMap3::identity(),
                FrameRelationKind::Declared {
                    law: "leg one".to_owned(),
                },
            )
            .unwrap();
        construction
            .add_relation(
                "second-third",
                second,
                third,
                AffineMap3::identity(),
                FrameRelationKind::Declared {
                    law: "leg two".to_owned(),
                },
            )
            .unwrap();
        assert_eq!(
            construction.transport(first, third),
            Err(TransportError::Ambiguous {
                from: first,
                target: third
            })
        );
    }

    #[test]
    fn a_hinged_entity_retains_exact_local_vertices() {
        let (mut construction, frame) = Construction::new("receiver");
        let vertices = [
            RatVec3::from_i64(0, 0, 0),
            RatVec3::from_i64(2, 0, 0),
            RatVec3::from_i64(0, 1, 0),
        ];
        let triangle = construction
            .add_entity(
                "triangle",
                frame,
                Geometry::Triangle {
                    vertices: vertices.clone(),
                },
            )
            .unwrap();
        let relation = construction
            .found_hinge(
                triangle,
                frame,
                vertices[0].clone(),
                HingeAxis::Z,
                rat(1, 2),
            )
            .unwrap();
        assert_eq!(
            construction.entities[&triangle].geometry,
            Geometry::Triangle { vertices }
        );
        let child = construction.entities[&triangle].frame;
        let transported = construction
            .transport(child, frame)
            .unwrap()
            .apply(&RatVec3::from_i64(1, 0, 0));
        assert_eq!(transported, RatVec3::new(rat(3, 5), rat(4, 5), Rat::zero()));
        assert_eq!(construction.hinge_for_entity(triangle), Some(relation));
    }

    #[test]
    fn conic_discriminant_is_exact() {
        for species in [
            ConicSpecies::Circle,
            ConicSpecies::Ellipse,
            ConicSpecies::Hyperbola,
        ] {
            assert!(!starter_conic(species).determinant().is_zero());
        }
        assert!(
            starter_conic(ConicSpecies::LinePair)
                .determinant()
                .is_zero()
        );
    }
}
