use std::collections::BTreeMap;

use holonic_engine::{
    AffineHingeForm, CausalWorld, ConicChart, ConicFamilyLaw, Edge, EventId, HingeEvent,
    HingeTransportNetwork, HingeWorldLaw, RayFamily, ReceiverFaceExtent, ReceiverFaceSpec,
    SimplicialComplex, receive_face_with_conics,
};
use relational_geometry::{
    Construction, Geometry, ProjectionLaw, RatVec3, Receiver, ReceiverId, integer,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let founding = EventId(1);
    let mut complex = SimplicialComplex::default();
    let a = complex.found_vertex("a", founding);
    let b = complex.found_vertex("b", founding);
    let c = complex.found_vertex("c", founding);
    let d = complex.found_vertex("d", founding);
    complex.found_face("left", founding, [a, b, c])?;
    complex.found_face("right", founding, [c, b, d])?;
    let hinge = complex.found_hinge("shared", founding, Edge::new(b, c)?)?;

    let (mut construction, frame) = Construction::new("conic source");
    construction.add_entity(
        "crossing sheet",
        frame,
        Geometry::Triangle {
            vertices: [
                RatVec3::from_i64(-2, 0, 2),
                RatVec3::from_i64(2, 0, 2),
                RatVec3::from_i64(0, 2, 2),
            ],
        },
    )?;
    let family = ConicFamilyLaw::new(
        "hinge-carried conic",
        founding,
        frame,
        ConicChart::new(
            RatVec3::from_i64(0, 0, 2),
            RatVec3::from_i64(1, 0, 0),
            RatVec3::from_i64(0, 1, 0),
        )?,
        [
            AffineHingeForm::constant(integer(1)),
            AffineHingeForm::constant(integer(0)),
            AffineHingeForm::constant(integer(1)),
            AffineHingeForm::constant(integer(0)),
            AffineHingeForm::constant(integer(0)),
            AffineHingeForm::constant(integer(-1)).plus_hinge(hinge, integer(1)),
        ],
    );
    let law = HingeWorldLaw::new(complex, HingeTransportNetwork::default(), vec![family])?;
    let standing = law.initial_standing(BTreeMap::from([(hinge, integer(0))]))?;
    let mut world = CausalWorld::new(law, standing);
    world.receive(&HingeEvent {
        event: EventId(2),
        pivot: hinge,
        parameter: integer(2),
    })?;

    let specification = ReceiverFaceSpec {
        receiver: Receiver::new(
            ReceiverId(1),
            "conic receiver",
            frame,
            ProjectionLaw::PerspectiveRay {
                focal_distance: integer(1),
            },
        ),
        extent: ReceiverFaceExtent {
            horizontal_span: integer(4),
            vertical_span: integer(3),
        },
        rays: RayFamily::Central {
            center: RatVec3::zero(),
            forward: RatVec3::from_i64(0, 0, 1),
            horizontal: RatVec3::from_i64(1, 0, 0),
            vertical: RatVec3::from_i64(0, 1, 0),
        },
        acceptance: None,
    };
    let face = receive_face_with_conics(&construction, &world.standing().conics, &specification)?;
    println!(
        "native conics={} exact arrangement relations={}",
        face.arrangement
            .primitives
            .iter()
            .filter(|primitive| matches!(primitive, holonic_engine::ReceiverPrimitive::Conic(_)))
            .count(),
        face.arrangement.relations.len()
    );
    Ok(())
}
