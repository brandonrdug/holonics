//! Exact scene, receiver family, and discrete construction history.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact::{AffineMap3, RatVec3, rat};
use crate::model::{
    ConicSpecies, ConstraintKind, Construction, EntityId, FrameRelationKind, Geometry, HingeAxis,
    ProjectiveConic,
};
use crate::projection::{
    ProjectionLaw, Receiver, ReceiverGauge, ReceiverId, ReceiverOrientation, ReceiverRotationAxis,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LabScene {
    pub construction: Construction,
    pub receivers: Vec<Receiver>,
    pub primary_receiver: ReceiverId,
    pub bookmarks: BTreeMap<String, EntityId>,
}

impl LabScene {
    pub fn primary_receiver(&self) -> Option<&Receiver> {
        self.receivers
            .iter()
            .find(|receiver| receiver.id == self.primary_receiver)
    }

    pub fn primary_receiver_mut(&mut self) -> Option<&mut Receiver> {
        self.receivers
            .iter_mut()
            .find(|receiver| receiver.id == self.primary_receiver)
    }

    pub fn promote_receiver(&mut self, receiver: ReceiverId) -> bool {
        if self
            .receivers
            .iter()
            .any(|candidate| candidate.id == receiver)
        {
            self.primary_receiver = receiver;
            true
        } else {
            false
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SceneMoment {
    pub ordinal: usize,
    pub label: String,
    pub scene: LabScene,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SceneArchive {
    pub schema: String,
    pub moments: Vec<SceneMoment>,
    pub cursor: usize,
}

#[derive(Debug, Error)]
pub enum SceneArchiveError {
    #[error("scene archive has no moments")]
    Empty,
    #[error("scene archive cursor {cursor} exceeds its {moments} moments")]
    CursorOutOfRange { cursor: usize, moments: usize },
    #[error("scene archive could not be encoded: {0}")]
    Encode(ron::Error),
    #[error("scene archive could not be decoded: {0}")]
    Decode(ron::error::SpannedError),
}

impl SceneArchive {
    pub fn new(label: impl Into<String>, scene: LabScene) -> Self {
        Self {
            schema: "relational-geometry.scene-archive.v1".to_owned(),
            moments: vec![SceneMoment {
                ordinal: 0,
                label: label.into(),
                scene,
            }],
            cursor: 0,
        }
    }

    pub fn current(&self) -> &LabScene {
        &self.moments[self.cursor].scene
    }

    pub fn current_mut(&mut self) -> &mut LabScene {
        &mut self.moments[self.cursor].scene
    }

    pub fn commit(&mut self, label: impl Into<String>, scene: LabScene) {
        self.moments.truncate(self.cursor + 1);
        let ordinal = self.moments.len();
        self.moments.push(SceneMoment {
            ordinal,
            label: label.into(),
            scene,
        });
        self.cursor = ordinal;
    }

    pub fn move_to(&mut self, cursor: usize) -> bool {
        if cursor < self.moments.len() {
            self.cursor = cursor;
            true
        } else {
            false
        }
    }

    pub fn encode_pretty(&self) -> Result<String, SceneArchiveError> {
        let pretty = ron::ser::PrettyConfig::new()
            .depth_limit(64)
            .separate_tuple_members(true)
            .enumerate_arrays(true);
        ron::ser::to_string_pretty(self, pretty).map_err(SceneArchiveError::Encode)
    }

    pub fn decode(encoded: &str) -> Result<Self, SceneArchiveError> {
        let archive: Self = ron::from_str(encoded).map_err(SceneArchiveError::Decode)?;
        archive.validate()?;
        Ok(archive)
    }

    pub fn validate(&self) -> Result<(), SceneArchiveError> {
        if self.moments.is_empty() {
            return Err(SceneArchiveError::Empty);
        }
        if self.cursor >= self.moments.len() {
            return Err(SceneArchiveError::CursorOutOfRange {
                cursor: self.cursor,
                moments: self.moments.len(),
            });
        }
        Ok(())
    }
}

pub fn starter_archive() -> SceneArchive {
    let (mut construction, base_frame) = Construction::new("shared source sheet");

    let first_triangle = construction
        .add_entity(
            "source triangle",
            base_frame,
            Geometry::Triangle {
                vertices: [
                    RatVec3::from_i64(-4, -1, 0),
                    RatVec3::from_i64(-2, -1, 0),
                    RatVec3::from_i64(-3, 1, 0),
                ],
            },
        )
        .expect("base frame exists");
    let second_triangle = construction
        .add_entity(
            "hinged triangle",
            base_frame,
            Geometry::Triangle {
                vertices: [
                    RatVec3::from_i64(-2, -1, 0),
                    RatVec3::from_i64(0, -1, 0),
                    RatVec3::from_i64(-1, 1, 0),
                ],
            },
        )
        .expect("base frame exists");

    let conic = construction
        .add_entity(
            "conic phase",
            base_frame,
            Geometry::Conic(ProjectiveConic {
                center: RatVec3::from_i64(2, 0, 0),
                axis_u: RatVec3::from_i64(2, 0, 0),
                axis_v: RatVec3::from_i64(0, 2, 0),
                species: ConicSpecies::Circle,
            }),
        )
        .expect("base frame exists");

    let thread = construction
        .add_entity(
            "embedded closed thread",
            base_frame,
            Geometry::Thread {
                vertices: vec![
                    RatVec3::from_i64(-3, -2, -1),
                    RatVec3::from_i64(3, 2, 1),
                    RatVec3::from_i64(-3, 2, 3),
                    RatVec3::from_i64(3, -2, 1),
                ],
                closed: true,
            },
        )
        .expect("base frame exists");

    let chord = construction
        .add_entity(
            "reciprocal chord",
            base_frame,
            Geometry::Thread {
                vertices: vec![
                    RatVec3::new(rat(21, 53), rat(48, 53), rat(-8, 53)),
                    RatVec3::new(rat(21, 53), rat(48, 53), rat(8, 53)),
                ],
                closed: false,
            },
        )
        .expect("base frame exists");

    construction.add_constraint(
        "triangles share one founding vertex",
        ConstraintKind::SharedVertex {
            left: first_triangle,
            right: second_triangle,
            left_vertex: 1,
            right_vertex: 0,
        },
    );
    construction.add_constraint(
        "conic lives as a homogeneous quadratic relation",
        ConstraintKind::Declared {
            expression: "alpha^2 + mu beta^2 - omega^2 = 0".to_owned(),
        },
    );

    let primary = Receiver {
        id: ReceiverId(1),
        name: "precessing ray receiver".to_owned(),
        frame: base_frame,
        orientation: ReceiverOrientation::from_cayley_xyz(rat(1, 4), rat(-1, 5), rat(1, 2)),
        projection: ProjectionLaw::PerspectiveRay {
            focal_distance: rat(8, 1),
        },
        gauge: ReceiverGauge::default(),
        route_overrides: BTreeMap::new(),
    };
    let isometric = Receiver::new(
        ReceiverId(2),
        "isometric quotient",
        base_frame,
        ProjectionLaw::Isometric,
    );
    let mut opposed = Receiver::new(
        ReceiverId(3),
        "opposed orthographic receiver",
        base_frame,
        ProjectionLaw::Orthographic,
    );
    opposed
        .orientation
        .precess_cayley(ReceiverRotationAxis::Y, &rat(-1, 2));

    let bookmarks = BTreeMap::from([
        ("source_triangle".to_owned(), first_triangle),
        ("hinged_triangle".to_owned(), second_triangle),
        ("conic".to_owned(), conic),
        ("thread".to_owned(), thread),
        ("chord".to_owned(), chord),
    ]);
    let scene = LabScene {
        construction,
        receivers: vec![primary, isometric, opposed],
        primary_receiver: ReceiverId(1),
        bookmarks,
    };
    let mut archive = SceneArchive::new("circle phase founded", scene);

    let mut ellipse = archive.current().clone();
    set_conic(
        &mut ellipse,
        conic,
        ConicSpecies::Ellipse,
        RatVec3::from_i64(3, 0, 0),
        RatVec3::from_i64(0, 2, 0),
    );
    archive.commit("conic rebases as ellipse", ellipse);

    let mut discriminant = archive.current().clone();
    set_conic(
        &mut discriminant,
        conic,
        ConicSpecies::LinePair,
        RatVec3::from_i64(1, 0, 0),
        RatVec3::from_i64(0, 2, 0),
    );
    archive.commit("conic reaches its line-pair discriminant", discriminant);

    let mut hyperbola = archive.current().clone();
    set_conic(
        &mut hyperbola,
        conic,
        ConicSpecies::Hyperbola,
        RatVec3::from_i64(2, 0, 0),
        RatVec3::from_i64(0, 1, 0),
    );
    archive.commit("conic releases as hyperbola", hyperbola);

    let mut hinged = archive.current().clone();
    let hinge = hinged
        .construction
        .found_hinge(
            second_triangle,
            base_frame,
            RatVec3::from_i64(-2, -1, 0),
            HingeAxis::X,
            rat(1, 3),
        )
        .expect("starter hinge is valid");
    archive.commit(format!("triangle hinges through relation {hinge}"), hinged);

    let mut receiver_changed = archive.current().clone();
    receiver_changed
        .primary_receiver_mut()
        .expect("primary receiver exists")
        .orientation
        .precess_cayley(ReceiverRotationAxis::Z, &rat(-1, 3));
    archive.commit(
        "receiver precesses; structural construction remains unchanged",
        receiver_changed,
    );

    archive
}

fn set_conic(
    scene: &mut LabScene,
    entity: EntityId,
    species: ConicSpecies,
    axis_u: RatVec3,
    axis_v: RatVec3,
) {
    let Geometry::Conic(conic) = &mut scene
        .construction
        .entities
        .get_mut(&entity)
        .expect("starter conic exists")
        .geometry
    else {
        unreachable!("starter conic retains its geometry kind");
    };
    conic.species = species;
    conic.axis_u = axis_u;
    conic.axis_v = axis_v;
}

pub fn blank_scene() -> LabScene {
    let (construction, frame) = Construction::new("first receiver sheet");
    LabScene {
        construction,
        receivers: vec![Receiver::new(
            ReceiverId(1),
            "first receiver",
            frame,
            ProjectionLaw::Orthographic,
        )],
        primary_receiver: ReceiverId(1),
        bookmarks: BTreeMap::new(),
    }
}

pub fn declared_relation_scene() -> LabScene {
    let (mut construction, first) = Construction::new("first");
    let second = construction.add_frame("second", 3);
    construction
        .add_relation(
            "identity testimony",
            second,
            first,
            AffineMap3::identity(),
            FrameRelationKind::Declared {
                law: "explicit identity rechart".to_owned(),
            },
        )
        .expect("both frames exist");
    LabScene {
        construction,
        receivers: vec![Receiver::new(
            ReceiverId(1),
            "first",
            first,
            ProjectionLaw::Orthographic,
        )],
        primary_receiver: ReceiverId(1),
        bookmarks: BTreeMap::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::projection::{analyze_crossings, project_entity};
    use num_traits::Zero;

    #[test]
    fn exact_scene_archive_round_trips_structurally() {
        let archive = starter_archive();
        let encoded = archive.encode_pretty().unwrap();
        let decoded = SceneArchive::decode(&encoded).unwrap();
        assert_eq!(decoded, archive);
        assert_eq!(
            decoded.current().construction.archive_digest(),
            archive.current().construction.archive_digest()
        );
    }

    #[test]
    fn receiver_event_does_not_change_the_construction() {
        let archive = starter_archive();
        let before = &archive.moments[archive.moments.len() - 2].scene;
        let after = archive.current();
        assert_eq!(before.construction, after.construction);
        let thread = after.bookmarks["thread"];
        let before_face = project_entity(
            &before.construction,
            thread,
            before.primary_receiver().unwrap(),
            12,
        )
        .unwrap();
        let after_face = project_entity(
            &after.construction,
            thread,
            after.primary_receiver().unwrap(),
            12,
        )
        .unwrap();
        assert_ne!(before_face, after_face);
    }

    #[test]
    fn starter_contains_no_zero_focal_distance() {
        let archive = starter_archive();
        for receiver in &archive.current().receivers {
            if let ProjectionLaw::PerspectiveRay { focal_distance } = &receiver.projection {
                assert!(!focal_distance.is_zero());
            }
        }
    }

    #[test]
    fn starter_receiver_family_exposes_distinct_crossing_faces() {
        let scene = starter_archive().current().clone();
        let reports = scene
            .receivers
            .iter()
            .map(|receiver| {
                let analysis = analyze_crossings(&scene.construction, receiver).unwrap();
                (
                    receiver.name.clone(),
                    analysis.crossings.len(),
                    analysis.discriminants.len(),
                    analysis.exact,
                )
            })
            .collect::<Vec<_>>();

        assert!(reports.iter().any(|(_, crossings, _, _)| *crossings > 0));
        assert!(reports.iter().any(|(_, _, _, exact)| !exact));
        assert_ne!(reports[0].1, reports[2].1);
    }
}
