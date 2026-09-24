use std::collections::BTreeMap;

use num_traits::One;
use holonics::geometry::{AffineMap3, Rat, RatMat3, RatVec3, integer, rat, triangle_holonomy};

use super::*;
use crate::{Edge, EventId, ExactEventLaw, HingeEvent, HingeWorldLaw, ProjectiveTurn};

/// The tetrahedral boundary of `first_return_carries_one_compressed_generator_and_exact_holonomy`,
/// with three hinges sharing vertex `v0` and one transport per consecutive pair.
fn tetrahedron_with_turns(
    turns: [ProjectiveTurn; 3],
) -> (
    SimplicialComplex,
    HingeTransportNetwork,
    [HingeId; 3],
    [HingeTransportId; 3],
) {
    let source_event = EventId(1);
    let mut complex = SimplicialComplex::default();
    let v = (0..4)
        .map(|index| complex.found_vertex(format!("v{index}"), source_event))
        .collect::<Vec<_>>();
    for (name, face) in [
        ("front", [v[0], v[2], v[1]]),
        ("right", [v[0], v[1], v[3]]),
        ("left", [v[0], v[3], v[2]]),
        ("base", [v[1], v[2], v[3]]),
    ] {
        complex.found_face(name, source_event, face).unwrap();
    }
    let hinge = |complex: &mut SimplicialComplex, name: &str, other: usize| {
        complex
            .found_hinge(name, source_event, Edge::new(v[0], v[other]).unwrap())
            .unwrap()
    };
    let hinges = [
        hinge(&mut complex, "first", 1),
        hinge(&mut complex, "second", 2),
        hinge(&mut complex, "third", 3),
    ];
    let mut network = HingeTransportNetwork::default();
    let [t0, t1, t2] = turns;
    let relations = [
        network
            .add(&complex, "first to second", hinges[0], hinges[1], t0)
            .unwrap(),
        network
            .add(&complex, "second to third", hinges[1], hinges[2], t1)
            .unwrap(),
        network
            .add(&complex, "third to first", hinges[2], hinges[0], t2)
            .unwrap(),
    ];
    (complex, network, hinges, relations)
}

fn dilation(numerator: i64, denominator: i64) -> ProjectiveTurn {
    ProjectiveTurn::new(
        integer(numerator),
        integer(0),
        integer(0),
        integer(denominator),
    )
    .unwrap()
}

/// **The hinge world's cycle return is the core curvature face.** On dilation turns
/// `λ = 2, 3, 1/5` around the three hinges, the engine returns the entered parameter `2` as
/// `2 · 6/5 = 12/5`; the core walk transport of the same closed walk is `6/5` and its curvature
/// `hol − 1 = 1/5` is `(returned − entered) / entered`, and `cell_reading` on the potential
/// concentrated at the base reads the same face.
#[test]
fn the_cycle_return_of_dilation_turns_is_the_core_curvature_face() {
    let (complex, network, hinges, relations) =
        tetrahedron_with_turns([dilation(2, 1), dilation(3, 1), dilation(1, 5)]);
    let (chart, connection) = network.core_connection(&complex).unwrap();
    let walk: Vec<usize> = relations
        .iter()
        .map(|relation| chart.edge_position(*relation).unwrap())
        .collect();
    let base = chart.vertex_position(hinges[0]).unwrap();

    let law = HingeWorldLaw::new(complex.clone(), network, Vec::new()).unwrap();
    let standing = law
        .initial_standing(BTreeMap::from([
            (hinges[0], integer(0)),
            (hinges[1], integer(0)),
            (hinges[2], integer(0)),
        ]))
        .unwrap();
    let successor = law
        .enact(
            &standing,
            &HingeEvent {
                event: EventId(2),
                pivot: hinges[0],
                parameter: integer(2),
            },
        )
        .unwrap();
    let returned = &successor.radiation[0].cycle_returns[0];
    assert_eq!(returned.entered_parameter, integer(2));
    assert_eq!(returned.returned_parameter, rat(12, 5));
    assert!(
        returned.tree_to_target.is_empty(),
        "every crossing is along"
    );

    let holonomy = connection.walk_transport(&walk).unwrap();
    assert_eq!(
        &returned.returned_parameter,
        &(&holonomy * &returned.entered_parameter)
    );
    let curvature = connection.curvature(&walk, base).unwrap();
    assert_eq!(curvature, rat(1, 5));
    assert_eq!(
        curvature,
        (&returned.returned_parameter - &returned.entered_parameter) / &returned.entered_parameter
    );
    let mut potential = vec![Rat::zero(); connection.vertices()];
    potential[base] = returned.entered_parameter.clone();
    let (reading, side) = connection.cell_reading(&potential, &walk, base).unwrap();
    assert_eq!(reading, side);
    assert_eq!(
        reading,
        &returned.returned_parameter - &returned.entered_parameter
    );

    let (receipt, simplicial_chart) = complex.core_chart().unwrap();
    assert_eq!(simplicial_chart.complex().cells(0), receipt.vertices.len());
    assert_eq!(
        (0..=2)
            .map(|k| simplicial_chart.complex().betti(k).unwrap())
            .collect::<Vec<_>>(),
        vec![1, 0, 1],
        "the tetrahedral boundary is a sphere"
    );
}

/// A general projective turn is a matrix-valued transport; the scalar core connection refuses it.
#[test]
fn a_projective_turn_is_not_a_scalar_transport() {
    let translate = ProjectiveTurn::new(integer(1), integer(1), integer(0), integer(1)).unwrap();
    let (complex, network, _, _) =
        tetrahedron_with_turns([dilation(2, 1), translate, dilation(1, 2)]);
    assert_eq!(
        network.core_connection(&complex).unwrap_err(),
        CoreChartRefusal::NotAScalarTransport { edge: 1 }
    );
}

/// **The affine cell holonomy read by the core curvature face** (the reading of the fixed
/// machine's `CompiledOrientedCell::holonomy`, `holonics::geometry::triangle_holonomy`). Scalar
/// dilation transports have holonomy `(∏ λ) · 1`, whose scalar is the core walk transport; for
/// rotating and dilating transports the determinant line is a `ℚ^×` connection and its core
/// curvature is `det(hol) − 1`, unchanged by a vertex regauge.
#[test]
fn the_affine_cell_holonomy_is_read_by_the_core_curvature_face() {
    let dilate = |lambda: Rat, shift: i64| AffineMap3 {
        linear: RatMat3::identity().scale(&lambda),
        translation: RatVec3::from_i64(shift, 0, -shift),
    };
    let lambdas = [integer(2), rat(3, 7), integer(-5)];
    let holonomy = triangle_holonomy(
        &dilate(lambdas[0].clone(), 1),
        &dilate(lambdas[1].clone(), 2),
        &dilate(lambdas[2].clone(), 3),
    );
    let triangle =
        ConnectionIncidence::new(3, vec![0, 1, 2], vec![1, 2, 0], lambdas.to_vec()).unwrap();
    let hol = triangle.walk_transport(&[0, 1, 2]).unwrap();
    assert_eq!(holonomy.linear, RatMat3::identity().scale(&hol));
    assert_eq!(
        triangle.curvature(&[0, 1, 2], 0).unwrap(),
        &holonomy.linear.rows[0][0] - Rat::one()
    );

    // Rotations (Cayley, rational) composed with dilations: the determinant line.
    let rotate_dilate = |parameter: Rat, lambda: Rat| AffineMap3 {
        linear: holonics::geometry::cayley_rotation_x(&parameter).scale(&lambda),
        translation: RatVec3::from_i64(1, -1, 2),
    };
    let transports = [
        rotate_dilate(rat(1, 2), integer(2)),
        rotate_dilate(rat(2, 3), rat(1, 3)),
        rotate_dilate(integer(3), integer(-1)),
    ];
    let holonomy = triangle_holonomy(&transports[0], &transports[1], &transports[2]);
    let determinants: Vec<Rat> = transports.iter().map(|g| g.linear.determinant()).collect();
    let line = ConnectionIncidence::new(3, vec![0, 1, 2], vec![1, 2, 0], determinants).unwrap();
    assert_eq!(
        line.curvature(&[0, 1, 2], 0).unwrap(),
        holonomy.linear.determinant() - Rat::one()
    );
    let frame = rotate_dilate(rat(5, 4), integer(7));
    let regauged = holonics::geometry::regauge(&frame, &frame, &holonomy).unwrap();
    assert_eq!(regauged.linear.determinant(), holonomy.linear.determinant());
}
