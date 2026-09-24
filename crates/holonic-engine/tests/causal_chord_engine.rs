//! Cross-owner checks for the exact causal chord, kept beside the engine owners they compare.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::Zero;
use holonic_engine::lattice_gauge;
use holonic_engine::physical_constraint_complex::{ConstraintEdge, ConstraintVertexId};
use holonic_engine::physical_constraint_grading::EdgeProvenance;
use holonic_engine::rigidity_receiver::{ExactConfiguration, RigidityJacobian, rigidity_reading};
use holonics::receiver::causal_chord::*;
use holonics::exact_linear::ExactRatMatrix;
use holonics::geometry::Rat;

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn matrix(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().copied().map(integer).collect())
            .collect(),
    )
    .expect("a declared integer matrix is rectangular")
}

/// **The mode population agrees with the existing spectrum owner.**
///
/// [`rational_mode_supports`] reads its rational eigenvalues through the prime-lifting route
/// because `lattice_gauge::exact_spectrum`'s Sturm census descends from a Cauchy bound that a
/// physical network operator makes astronomically wide. On material where both routes are cheap
/// they must agree exactly, and this is what holds them to it.
#[test]
fn the_mode_population_agrees_with_the_existing_spectrum_owner() {
    for state in [
        matrix(&[&[1, 0], &[0, 2]]),
        matrix(&[&[2, 1, 0], &[0, 2, 0], &[0, 0, -3]]),
        matrix(&[&[0, 1], &[2, 0]]),
    ] {
        let base = Linearization::single_probe("spectrum", state.clone(), 0, 0)
            .expect("declared");
        let mine = rational_mode_supports(&base).expect("the modes return");
        let owner = lattice_gauge::exact_spectrum(&state).expect("the spectrum returns");
        let population = mine
            .iter()
            .map(|mode| (mode.eigenvalue.clone(), mode.algebraic_multiplicity))
            .collect::<Vec<_>>();
        assert_eq!(population, owner.rational_eigenvalues, "{state:?}");
    }
    // And a defective rational eigenvalue is reported as defective rather than as a second mode.
    let defective = Linearization::single_probe(
        "defective",
        matrix(&[&[2, 1, 0], &[0, 2, 0], &[0, 0, -3]]),
        0,
        0,
    )
    .expect("declared");
    let modes = rational_mode_supports(&defective).expect("the modes return");
    let doubled = modes
        .iter()
        .find(|mode| mode.eigenvalue == integer(2))
        .expect("2 is a rational eigenvalue");
    assert_eq!(doubled.algebraic_multiplicity, 2);
    assert_eq!(doubled.geometric_multiplicity, 1);
    assert!(doubled.is_defective());
}

// ---------------------------------------------------------------------------------------------
// the elastic network, synthetically
// ---------------------------------------------------------------------------------------------

fn place(coordinates: &[i64]) -> Vec<Rat> {
    coordinates.iter().copied().map(integer).collect()
}

fn triangle_jacobian() -> RigidityJacobian {
    let configuration = ExactConfiguration::declared(
        2,
        [
            (ConstraintVertexId(1), place(&[0, 0])),
            (ConstraintVertexId(2), place(&[4, 0])),
            (ConstraintVertexId(3), place(&[0, 3])),
        ],
    )
    .expect("a declared configuration");
    let mut constraints = BTreeMap::new();
    for (left, right) in [(1, 2), (1, 3), (2, 3)] {
        let (edge, _) = ConstraintEdge::new(
            ConstraintVertexId(left),
            ConstraintVertexId(right),
        )
        .expect("a well-formed edge");
        constraints.insert(edge, EdgeProvenance::Polygonal);
    }
    RigidityJacobian::found("synthetic-triangle", &configuration, &constraints)
        .expect("the Jacobian returns")
}

/// **The construction the M5 reading uses, with no fixture at all.**
///
/// `A = −JᵀJ` on a rigid planar triangle. Its kernel is exactly `ker J` — the infinitesimal motions
/// the rigidity receiver already returns — so the axis count of the chord's spectrum and `dim ker J`
/// are the same number computed two ways, and the operator is negative semidefinite with no
/// right-half-plane mode at all.
#[test]
fn the_elastic_network_of_a_rigid_triangle_has_its_motions_on_the_axis() {
    let jacobian = triangle_jacobian();
    let reading = rigidity_reading(&jacobian).expect("the rigidity reading returns");
    let network = elastic_network(
        "synthetic-triangle",
        &jacobian.matrix,
        NetworkForm::OverdampedRelaxation,
        0,
        4,
    )
    .expect("the network returns");
    let count = half_plane_from_symmetric(&network.state).expect("the inertia route returns");
    assert_eq!(count.right, 0, "−JᵀJ is negative semidefinite");
    assert_eq!(
        count.axis, reading.motion_dimension,
        "the axis modes are exactly the infinitesimal motions"
    );
    assert_eq!(count.left + count.axis, 6);

    let chord = causal_chord_read(&network, PoleReading::Named).expect("the chord returns");
    assert_eq!(chord.extent, 6);
    assert!(chord.semisimple, "a symmetric operator is semisimple");
    // Every returned component carries its whole provenance.
    for component in &chord.components {
        assert_eq!(component.lineage, "synthetic-triangle");
        assert_eq!(component.excitation, 0);
        assert_eq!(component.transport_path, 0);
        assert!(component.residual.is_zero());
    }
    // The transfer entry's certificate is exactly zero and the reduced denominator divides the
    // characteristic polynomial.
    let entry = &chord.transfer.entries[0];
    assert!(entry.residual.is_zero());
    assert!(
        entry
            .denominator
            .divided_exactly_by(&entry.reduced_denominator)
            .is_ok()
    );
}
