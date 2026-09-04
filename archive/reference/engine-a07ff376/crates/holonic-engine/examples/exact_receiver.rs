use holonic_engine::{
    CpuExecutor, PluralReceiverAssembly, PresentationBoundary, RayFamily, ReceiverFaceExtent,
    ReceiverFaceSpec, ReceiverStandingRelation, TerminalMatrixSpec, quotient_presentation,
    receive_face,
};
use relational_geometry::{
    Construction, Geometry, ProjectionLaw, RatVec3, Receiver, ReceiverId, integer,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (mut construction, frame) = Construction::new("caused local frame");
    construction.add_entity(
        "sheet",
        frame,
        Geometry::Triangle {
            vertices: [
                RatVec3::from_i64(-2, -1, 3),
                RatVec3::from_i64(2, -1, 3),
                RatVec3::from_i64(0, 2, 3),
            ],
        },
    )?;
    construction.add_entity(
        "thread",
        frame,
        Geometry::Thread {
            vertices: vec![
                RatVec3::from_i64(-1, 0, 2),
                RatVec3::from_i64(0, 1, 2),
                RatVec3::from_i64(1, 0, 2),
            ],
            closed: false,
        },
    )?;

    let specification = ReceiverFaceSpec {
        receiver: Receiver::new(
            ReceiverId(1),
            "participating receiver",
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
    let face = receive_face(&construction, &specification)?;
    let assembly = PluralReceiverAssembly::new(
        "one caused receiver face",
        vec![face],
        vec![ReceiverStandingRelation::identity(
            ReceiverId(1),
            holonic_engine::EventId(1),
        )],
    )?;
    let executed = quotient_presentation(
        &assembly,
        &TerminalMatrixSpec {
            width: 80,
            height: 45,
            boundary: PresentationBoundary {
                horizontal_span: integer(4),
                vertical_span: integer(9) / integer(4),
            },
        },
        &CpuExecutor::serial(),
    )?;
    println!(
        "continuous primitives={} relations={} terminal members={}",
        executed.continuous.primitives.len(),
        executed.continuous.relations.len(),
        executed.matrix.members.len()
    );
    Ok(())
}
