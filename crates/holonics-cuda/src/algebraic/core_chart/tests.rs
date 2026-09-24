use std::collections::BTreeSet;

use holonics::complex::CellComplex;
use holonics::holon::HolonError;
use num_traits::{One, Zero};
use holonics::geometry::Rat;

use super::*;

fn tetrahedron() -> (GradedCausalComplex, crate::SimplexIncidenceReceipt) {
    let mut complex = GradedCausalComplex::default();
    let receipt = complex
        .found_simplex("tet", EventId(1), ["a", "b", "c", "d"])
        .expect("the simplex founds");
    (complex, receipt)
}

/// The chart's `∂_k` is the engine boundary, cell for cell, and its Betti numbers are the simplex's.
#[test]
fn a_simplex_reads_as_the_core_complex_with_its_own_boundary() {
    let (complex, _) = tetrahedron();
    let chart = complex.core_chart().expect("the chart stands");
    assert_eq!(chart.complex().dimension(), 3);
    assert_eq!(
        (0..=3).map(|k| chart.cells(k).len()).collect::<Vec<_>>(),
        vec![4, 6, 4, 1]
    );
    for degree in 1..=3 {
        let boundary = chart.complex().boundary(degree).unwrap();
        for (column, cell) in chart.cells(degree).iter().enumerate() {
            let engine = complex
                .boundary_of_chain(&CausalChain::default().plus(&{
                    let mut chain = CausalChain::default();
                    chain.add_term(*cell, ComparativeMultiplicity::positive(1_u8));
                    chain
                }))
                .unwrap();
            let read = chart.chain(degree - 1, &engine).unwrap();
            for (row, value) in read.iter().enumerate() {
                assert_eq!(boundary.get(row, column).unwrap(), value);
            }
        }
    }
    assert_eq!(
        (0..=3)
            .map(|k| chart.complex().betti(k).unwrap())
            .collect::<Vec<_>>(),
        vec![1, 0, 0, 0]
    );
    let direct = CellComplex::try_from(&complex).unwrap();
    assert_eq!(&direct, chart.complex());
}

/// A core complex founded as a graded causal complex reads back as itself; a non-integral boundary
/// has no occurrence reading and is refused by name.
#[test]
fn a_core_complex_round_trips_through_the_graded_presentation() {
    let (complex, _) = tetrahedron();
    let core = CellComplex::try_from(&complex).unwrap();
    let (founded, chart) = GradedCausalComplex::from_core(&core, "k", EventId(7)).unwrap();
    assert_eq!(chart.complex(), &core);
    assert_eq!(founded.f_vector(), complex.f_vector());

    let half = CellComplex::new(
        vec![2, 1],
        vec![
            ExactRatMatrix::shaped(
                2,
                1,
                vec![
                    vec![-Rat::new(1.into(), 2.into())],
                    vec![Rat::new(1.into(), 2.into())],
                ],
            )
            .unwrap(),
        ],
    )
    .unwrap();
    assert_eq!(
        GradedCausalComplex::from_core(&half, "half", EventId(1)).unwrap_err(),
        CoreChartRefusal::NonIntegralIncidence {
            degree: 1,
            row: 0,
            column: 0
        }
    );
}

/// A loop edge attaches `(1, 1)`: two passages the boundary map cannot see apart. The chart reads
/// the group completion, a zero column, while the engine keeps the attachment.
#[test]
fn a_loop_edge_reads_as_a_zero_boundary_column() {
    let mut complex = GradedCausalComplex::default();
    let events = BTreeSet::from([EventId(1)]);
    let vertex = complex
        .found_cell("v", events.clone(), 0, CausalChain::default())
        .unwrap();
    let mut boundary = CausalChain::default();
    boundary.add_term(vertex, ComparativeMultiplicity::positive(1_u8));
    boundary.add_term(vertex, ComparativeMultiplicity::negative(1_u8));
    let edge = complex.found_cell("loop", events, 1, boundary).unwrap();
    assert!(
        complex
            .cell(edge)
            .unwrap()
            .boundary
            .support()
            .contains(&vertex)
    );
    let chart = complex.core_chart().unwrap();
    assert!(
        chart
            .complex()
            .boundary(1)
            .unwrap()
            .get(0, 0)
            .unwrap()
            .is_zero()
    );
    assert_eq!(
        (
            chart.complex().betti(0).unwrap(),
            chart.complex().betti(1).unwrap()
        ),
        (1, 1)
    );
}

/// The empty complex is the core complex with no cells.
#[test]
fn the_empty_complex_is_a_core_complex() {
    let chart = GradedCausalComplex::default().core_chart().unwrap();
    assert_eq!(chart.complex().dimension(), 0);
    assert_eq!(chart.complex().cells(0), 0);
}

/// A graph chart is the core graph complex; its flat connection is `d₀`, and a bad endpoint or a
/// repeated edge identity is refused.
#[test]
fn a_graph_chart_is_the_core_graph_and_its_flat_connection() {
    let chart = GraphChart::new(
        [10_u64, 20, 30],
        [(1_u64, 10, 20), (2, 20, 30), (3, 30, 10)],
    )
    .unwrap();
    assert_eq!(
        chart.flat_connection().unwrap().matrix().unwrap(),
        chart.complex().incidence().unwrap()
    );
    assert_eq!(chart.vertex_position(30), Some(2));
    assert_eq!(chart.edge_position(2), Some(1));
    let curved = chart
        .connection(vec![Rat::from_integer(2.into()), Rat::one(), Rat::one()])
        .unwrap();
    assert_eq!(
        curved.curvature(&[0, 1, 2], 0).unwrap(),
        Rat::one(),
        "holonomy 2, curvature face 1"
    );
    assert_eq!(
        GraphChart::new([1_u64], [(1_u64, 1, 2)]).unwrap_err(),
        CoreChartRefusal::EndpointOutside { edge: 0 }
    );
    assert_eq!(
        GraphChart::new([1_u64, 2], [(1_u64, 1, 2), (1, 2, 1)]).unwrap_err(),
        CoreChartRefusal::RepeatedIdentity { what: "edges" }
    );
    assert!(matches!(
        chart.connection(vec![Rat::zero(), Rat::one(), Rat::one()]),
        Err(CoreChartRefusal::Holon(error)) if *error == HolonError::ZeroTransport { edge: 0 }
    ));
}
