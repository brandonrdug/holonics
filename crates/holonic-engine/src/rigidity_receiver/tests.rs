//! The rigidity receiver's own checks.
//!
//! Everything about the laws — the two null spaces, the trivial motions including their
//! degenerate cases, the Maxwell relation and its bound, the clusters, the removal sensitivity and
//! the open family — is checked on synthetic exact configurations that need no fixture and run
//! everywhere. The last test is the measured M5 structure check: it refuses rather than passes
//! when the authenticated release is absent.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::Zero;

use super::*;
use crate::EventId;
use holonics::exact_value::ExactInterval;
use crate::physical_constraint_complex::{
    ComponentMaterial, ConstraintComponentId, ContactClass, CoordinateBox3, DistanceAperture,
    PairUncertainty, ResidueMaterial,
};
use crate::physical_constraint_grading::OpenResolution;

// ---------------------------------------------------------------------------------------------
// synthetic material
// ---------------------------------------------------------------------------------------------

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn ratio(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn place(coordinates: &[i64]) -> Vec<Rat> {
    coordinates.iter().copied().map(integer).collect()
}

fn configuration(dimension: usize, places: &[(u64, &[i64])]) -> ExactConfiguration {
    ExactConfiguration::declared(
        dimension,
        places
            .iter()
            .map(|(id, coordinates)| (ConstraintVertexId(*id), place(coordinates))),
    )
    .expect("the declared configuration stands")
}

fn bars(edges: &[(u64, u64)]) -> BTreeMap<ConstraintEdge, EdgeProvenance> {
    edges
        .iter()
        .map(|(left, right)| {
            (
                ConstraintEdge::new(ConstraintVertexId(*left), ConstraintVertexId(*right))
                    .expect("distinct occurrences found an edge")
                    .0,
                EdgeProvenance::AdmittedContact,
            )
        })
        .collect()
}

fn jacobian(
    lineage: &str,
    configuration: &ExactConfiguration,
    edges: &[(u64, u64)],
) -> RigidityJacobian {
    RigidityJacobian::found(lineage, configuration, &bars(edges)).expect("the Jacobian founds")
}

fn reading(
    lineage: &str,
    configuration: &ExactConfiguration,
    edges: &[(u64, u64)],
) -> (RigidityJacobian, RigidityReading) {
    let jacobian = jacobian(lineage, configuration, edges);
    let reading = rigidity_reading(&jacobian).expect("the reading returns");
    (jacobian, reading)
}

// ---------------------------------------------------------------------------------------------
// the Jacobian itself
// ---------------------------------------------------------------------------------------------

/// **The row law, entry by entry.** `2(q_i − q_j)` in the two occurrence blocks with opposite
/// sign, and exactly zero everywhere else.
#[test]
fn the_jacobian_row_of_one_bar_is_the_exact_gradient() {
    let configuration = configuration(2, &[(1, &[0, 0]), (2, &[3, 4])]);
    let jacobian = jacobian("one bar", &configuration, &[(1, 2)]);
    assert_eq!(jacobian.matrix.rows(), 1);
    assert_eq!(jacobian.matrix.columns(), 4);
    let row = jacobian.matrix.row(0).expect("the row stands");
    assert_eq!(
        row,
        [integer(-6), integer(-8), integer(6), integer(8)],
        "2(q_1 − q_2) = (−6,−8) at block one and its negative at block two"
    );
    assert_eq!(
        jacobian.constraints[0].squared_length,
        integer(25),
        "the constraint's own length is read from the configuration, never supplied"
    );
    assert!(jacobian.coincident_constraints.is_empty());
}

/// **A constraint between coincident occurrences has a zero row.** It is not a first-order
/// restriction at all, and it is named rather than dropped.
#[test]
fn a_coincident_constraint_is_named_and_carries_a_zero_row() {
    let configuration = configuration(3, &[(1, &[1, 2, 3]), (2, &[1, 2, 3])]);
    let jacobian = jacobian("coincident", &configuration, &[(1, 2)]);
    assert_eq!(jacobian.coincident_constraints.len(), 1);
    assert!(
        jacobian
            .matrix
            .row(0)
            .expect("the row stands")
            .iter()
            .all(Zero::is_zero)
    );
    let reading = rigidity_reading(&jacobian).expect("the reading returns");
    assert_eq!(reading.rank, 0);
    assert_eq!(
        reading.self_stress_dimension, 1,
        "a zero row is dependent on every other row, so it carries a self-stress by itself"
    );
}

// ---------------------------------------------------------------------------------------------
// the two null spaces and the Maxwell relation
// ---------------------------------------------------------------------------------------------

/// **A triangle in the plane is infinitesimally rigid and carries no self-stress.** Here, and only
/// here, the Maxwell count equals the motion dimension.
#[test]
fn a_triangle_in_the_plane_is_infinitesimally_rigid_and_carries_no_self_stress() {
    let configuration = configuration(2, &[(1, &[0, 0]), (2, &[4, 0]), (3, &[0, 3])]);
    let (_, reading) = reading("triangle", &configuration, &[(1, 2), (1, 3), (2, 3)]);
    assert_eq!(reading.maxwell.coordinate_freedoms, 6);
    assert_eq!(reading.constraint_count, 3);
    assert_eq!(reading.rank, 3);
    assert_eq!(reading.motion_dimension, 3);
    assert_eq!(reading.self_stress_dimension, 0);
    assert_eq!(reading.trivial.degeneracy, ConfigurationDegeneracy::Spanning);
    assert_eq!(reading.trivial.dimension_of_span, 3);
    assert_eq!(reading.internal_motion_dimension, 0);
    assert!(reading.is_infinitesimally_rigid());
    assert!(!reading.is_redundant());
    assert_eq!(reading.maxwell.counted_freedom, 3);
    assert!(
        !reading.maxwell.count_is_a_bound_only,
        "with no self-stress the count is the motion dimension exactly"
    );
}

/// **A four-bar in the plane keeps one internal motion.** The count is still exact because the
/// four-cycle is independent.
#[test]
fn a_four_bar_in_the_plane_keeps_one_internal_motion() {
    let configuration = configuration(
        2,
        &[(1, &[0, 0]), (2, &[2, 0]), (3, &[2, 2]), (4, &[0, 2])],
    );
    let (_, reading) = reading("four bar", &configuration, &[(1, 2), (2, 3), (3, 4), (1, 4)]);
    assert_eq!(reading.maxwell.coordinate_freedoms, 8);
    assert_eq!(reading.rank, 4);
    assert_eq!(reading.motion_dimension, 4);
    assert_eq!(reading.self_stress_dimension, 0);
    assert_eq!(reading.trivial.dimension_of_span, 3);
    assert_eq!(reading.internal_motion_dimension, 1);
    assert!(!reading.is_infinitesimally_rigid());
    assert_eq!(reading.maxwell.counted_freedom, 4);
    assert!(!reading.maxwell.count_is_a_bound_only);
}

/// **The point of item 3: a redundant system breaks the count.** `K_4` in the plane is
/// infinitesimally rigid with `dim ker J = 3`, while the Maxwell count returns `2`. A rigidity
/// verdict read from the count alone would be wrong here in the flexible direction, and the
/// self-stress is exactly the discrepancy.
#[test]
fn a_redundant_system_separates_the_maxwell_count_from_the_motion_dimension() {
    let configuration = configuration(
        2,
        &[(1, &[0, 0]), (2, &[4, 0]), (3, &[0, 3]), (4, &[4, 3])],
    );
    let (_, reading) = reading(
        "complete four",
        &configuration,
        &[(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)],
    );
    assert_eq!(reading.maxwell.coordinate_freedoms, 8);
    assert_eq!(reading.constraint_count, 6);
    assert_eq!(reading.rank, 5);
    assert_eq!(reading.motion_dimension, 3);
    assert_eq!(reading.self_stress_dimension, 1);
    assert_eq!(reading.internal_motion_dimension, 0);
    assert!(reading.is_infinitesimally_rigid());
    assert_eq!(reading.maxwell.counted_freedom, 2);
    assert!(
        reading.maxwell.count_is_a_bound_only,
        "a self-stress exists, so the count is a strict lower bound and decides nothing"
    );
    assert_eq!(
        reading.motion_dimension as i64 - reading.self_stress_dimension as i64,
        reading.maxwell.counted_freedom,
        "the exact Maxwell identity, which the count alone is a projection of"
    );
    // The self-stress really is one: a nonzero combination of the rows that vanishes.
    let stress = &reading.self_stresses[0];
    assert_eq!(stress.len(), 6);
    assert!(stress.iter().any(|entry| !entry.is_zero()));
}

// ---------------------------------------------------------------------------------------------
// the trivial motions, including the degenerate configurations
// ---------------------------------------------------------------------------------------------

/// **Six is not a constant.** A spanning configuration in three dimensions carries six.
#[test]
fn a_spanning_configuration_in_space_carries_six_trivial_motions() {
    let configuration = configuration(
        3,
        &[
            (1, &[0, 0, 0]),
            (2, &[1, 0, 0]),
            (3, &[0, 1, 0]),
            (4, &[0, 0, 1]),
        ],
    );
    let (_, reading) = reading("tetrahedron frame", &configuration, &[(1, 2), (1, 3), (1, 4)]);
    assert_eq!(reading.trivial.affine_span_dimension, 3);
    assert_eq!(reading.trivial.degeneracy, ConfigurationDegeneracy::Spanning);
    assert_eq!(reading.trivial.dimension_of_span, 6);
    assert_eq!(reading.trivial.closed_form, 6);
    assert!(reading.trivial.vanishing_generators.is_empty());
}

/// **A coplanar configuration in space still carries six.** The affine span is deficient and the
/// trivial count is untouched, which is why a degeneracy flag alone would be the wrong receiver.
#[test]
fn a_coplanar_configuration_in_space_still_carries_six_trivial_motions() {
    let configuration = configuration(
        3,
        &[
            (1, &[0, 0, 0]),
            (2, &[1, 0, 0]),
            (3, &[0, 1, 0]),
            (4, &[1, 1, 0]),
        ],
    );
    let (_, reading) = reading("coplanar frame", &configuration, &[(1, 2), (1, 3)]);
    assert_eq!(reading.trivial.affine_span_dimension, 2);
    assert_eq!(
        reading.trivial.degeneracy,
        ConfigurationDegeneracy::Deficient
    );
    assert_eq!(reading.trivial.dimension_of_span, 6);
    assert_eq!(reading.trivial.closed_form, 6);
}

/// **A collinear configuration in space carries five, not six.** The rotation about the line is
/// identically zero at this configuration, and the receiver measures that rather than subtracting
/// a constant.
#[test]
fn a_collinear_configuration_in_space_carries_five_trivial_motions() {
    let configuration = configuration(3, &[(1, &[0, 0, 0]), (2, &[1, 0, 0]), (3, &[2, 0, 0])]);
    let (_, reading) = reading("collinear chain", &configuration, &[(1, 2), (2, 3)]);
    assert_eq!(reading.trivial.affine_span_dimension, 1);
    assert_eq!(
        reading.trivial.degeneracy,
        ConfigurationDegeneracy::Collinear
    );
    assert_eq!(reading.trivial.dimension_of_span, 5);
    assert_eq!(reading.trivial.closed_form, 5);
    assert_eq!(
        reading.trivial.vanishing_generators,
        vec![5],
        "the third rotation generator, about the axis the occurrences lie on, is the zero vector"
    );
    assert_eq!(reading.maxwell.coordinate_freedoms, 9);
    assert_eq!(reading.rank, 2);
    assert_eq!(reading.motion_dimension, 7);
    assert_eq!(
        reading.internal_motion_dimension, 2,
        "subtracting six here would have under-reported the internal motions by one"
    );
}

/// **A coincident configuration in space carries three.** Every rotation generator is a
/// *translation* at this configuration — nonzero, but dependent — so a vanishing test alone would
/// also have been the wrong receiver. The rank is what decides.
#[test]
fn a_coincident_configuration_in_space_carries_three_trivial_motions() {
    let configuration = configuration(
        3,
        &[(1, &[1, 2, 3]), (2, &[1, 2, 3]), (3, &[1, 2, 3])],
    );
    let (_, reading) = reading("coincident", &configuration, &[(1, 2), (2, 3)]);
    assert_eq!(reading.trivial.affine_span_dimension, 0);
    assert_eq!(
        reading.trivial.degeneracy,
        ConfigurationDegeneracy::Coincident
    );
    assert_eq!(reading.trivial.dimension_of_span, 3);
    assert_eq!(reading.trivial.closed_form, 3);
    assert!(
        reading.trivial.vanishing_generators.is_empty(),
        "the rotation generators are nonzero here; they are merely dependent on the translations"
    );
    assert_eq!(reading.rank, 0);
    assert_eq!(reading.motion_dimension, 9);
    assert_eq!(reading.self_stress_dimension, 2);
}

/// **The trivial motions are proved, not asserted.** Every generator is applied to `J` and the
/// image is required to vanish, at a configuration with no symmetry to hide behind.
#[test]
fn every_trivial_generator_is_annihilated_by_the_jacobian() {
    let configuration = ExactConfiguration::declared(
        3,
        [
            (ConstraintVertexId(1), vec![ratio(1, 3), ratio(-5, 7), integer(2)]),
            (ConstraintVertexId(2), vec![integer(4), ratio(11, 13), ratio(-1, 2)]),
            (ConstraintVertexId(3), vec![ratio(-7, 5), integer(3), ratio(9, 4)]),
            (ConstraintVertexId(4), vec![integer(0), ratio(2, 9), integer(-6)]),
        ],
    )
    .expect("the declared configuration stands");
    let jacobian = jacobian(
        "irrational-looking but exact",
        &configuration,
        &[(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)],
    );
    let trivial = TrivialMotionReading::measure(&jacobian).expect("the trivial space measures");
    assert_eq!(trivial.generators.len(), 6);
    for (ordinal, generator) in trivial.generators.iter().enumerate() {
        let image = jacobian.matrix.apply(generator).expect("the product stands");
        assert!(
            image.iter().all(Zero::is_zero),
            "trivial generator {ordinal} is not in ker J"
        );
    }
    assert_eq!(trivial.dimension_of_span, 6);
}

// ---------------------------------------------------------------------------------------------
// rigid clusters
// ---------------------------------------------------------------------------------------------

/// **Two rigid bodies sharing a hinge are two clusters sharing an occurrence.** The cluster
/// relation is not transitive, and the return exhibits that rather than collapsing it into a
/// partition.
#[test]
fn rigid_clusters_of_a_hinge_overlap_at_the_shared_occurrence() {
    let configuration = configuration(
        2,
        &[
            (1, &[0, 0]),
            (2, &[2, 0]),
            (3, &[1, 2]),
            (4, &[3, 3]),
            (5, &[1, 4]),
        ],
    );
    let (jacobian, reading) = reading(
        "hinge",
        &configuration,
        &[(1, 2), (1, 3), (2, 3), (3, 4), (3, 5), (4, 5)],
    );
    assert_eq!(reading.motion_dimension, 4);
    assert_eq!(reading.trivial.dimension_of_span, 3);
    assert_eq!(
        reading.internal_motion_dimension, 1,
        "the hinge angle is the one internal motion"
    );
    let clusters = rigid_clusters(&jacobian, &reading, 64).expect("the clusters return");
    assert_eq!(
        clusters.clusters,
        vec![vec![0, 1, 2], vec![2, 3, 4]],
        "block 2 is the shared occurrence and belongs to both clusters"
    );
    assert!(clusters.pairs.coincident_pairs.is_empty());
    assert!(
        clusters.pairs.implied_without_constraint.is_empty(),
        "every implied pair here already carries a bar"
    );
}

/// **An implied pair with no bar is the structure holding a distance nobody asked it to.** Two
/// triangles sharing an edge are one rigid cluster, and the diagonal across them is implied.
#[test]
fn a_shared_edge_makes_one_cluster_and_implies_the_diagonal() {
    let configuration = configuration(
        2,
        &[(1, &[0, 0]), (2, &[4, 0]), (3, &[0, 3]), (4, &[4, 3])],
    );
    let (jacobian, reading) = reading(
        "two triangles on a shared edge",
        &configuration,
        &[(1, 2), (1, 3), (2, 3), (2, 4), (3, 4)],
    );
    assert!(reading.is_infinitesimally_rigid());
    assert_eq!(reading.self_stress_dimension, 0);
    let clusters = rigid_clusters(&jacobian, &reading, 64).expect("the clusters return");
    assert_eq!(clusters.clusters, vec![vec![0, 1, 2, 3]]);
    assert_eq!(
        clusters.pairs.implied_without_constraint,
        vec![(0, 3)],
        "the one pair the structure holds without a bar of its own"
    );
}

/// The enumeration ceiling is explicit and refuses rather than exhausting the machine.
#[test]
fn the_cluster_enumeration_refuses_above_its_declared_bound() {
    let configuration = configuration(
        2,
        &[
            (1, &[0, 0]),
            (2, &[2, 0]),
            (3, &[1, 2]),
            (4, &[3, 3]),
            (5, &[1, 4]),
        ],
    );
    let (jacobian, reading) = reading(
        "hinge",
        &configuration,
        &[(1, 2), (1, 3), (2, 3), (3, 4), (3, 5), (4, 5)],
    );
    assert_eq!(
        rigid_clusters(&jacobian, &reading, 1),
        Err(RigidityError::ClusterPopulationTooWide { bound: 1 })
    );
}

// ---------------------------------------------------------------------------------------------
// contact-removal sensitivity
// ---------------------------------------------------------------------------------------------

/// **Which bar carries the structure.** With no self-stress every bar is load-bearing, and
/// deleting any one of them raises the motion dimension by exactly one. The verification deletes
/// the row and recomputes the exact rank rather than trusting the criterion.
#[test]
fn removal_sensitivity_names_every_bar_of_an_independent_system() {
    let configuration = configuration(
        2,
        &[(1, &[0, 0]), (2, &[4, 0]), (3, &[0, 3]), (4, &[6, 7])],
    );
    let (jacobian, reading) = reading(
        "triangle with a pendant",
        &configuration,
        &[(1, 2), (1, 3), (2, 3), (3, 4)],
    );
    assert_eq!(reading.self_stress_dimension, 0);
    assert_eq!(reading.motion_dimension, 4);
    let sensitivity = removal_sensitivity(&jacobian, &reading).expect("the sensitivity returns");
    assert_eq!(sensitivity.load_bearing.len(), 4);
    assert!(sensitivity.redundant.is_empty());
    for constraint in &sensitivity.constraints {
        assert!(!constraint.carries_self_stress);
        assert_eq!(constraint.motion_dimension_after_removal, 5);
    }
    assert_eq!(
        verify_removal_sensitivity(&jacobian, &sensitivity, 16).expect("the deletion agrees"),
        4,
        "all four removals were re-derived by actually deleting the row"
    );
}

/// **A redundant bar's removal moves nothing**, and the self-stress support is what says so —
/// the same object item 2 already returned, with no second computation.
#[test]
fn removal_sensitivity_reads_redundancy_off_the_self_stress_support() {
    let configuration = configuration(
        2,
        &[(1, &[0, 0]), (2, &[4, 0]), (3, &[0, 3]), (4, &[4, 3])],
    );
    let (jacobian, reading) = reading(
        "complete four",
        &configuration,
        &[(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)],
    );
    assert_eq!(reading.self_stress_dimension, 1);
    let sensitivity = removal_sensitivity(&jacobian, &reading).expect("the sensitivity returns");
    assert_eq!(
        sensitivity.load_bearing.len() + sensitivity.redundant.len(),
        6
    );
    assert!(
        !sensitivity.redundant.is_empty(),
        "a system with a self-stress has at least one dependent constraint"
    );
    for constraint in &sensitivity.constraints {
        if constraint.carries_self_stress {
            assert_eq!(constraint.motion_dimension_after_removal, 3);
        } else {
            assert_eq!(constraint.motion_dimension_after_removal, 4);
        }
    }
    assert_eq!(
        verify_removal_sensitivity(&jacobian, &sensitivity, 16).expect("the deletion agrees"),
        6
    );
}

// ---------------------------------------------------------------------------------------------
// the open family
// ---------------------------------------------------------------------------------------------

fn undecided_uncertainty(left: usize, right: usize) -> BTreeMap<(u32, u32), PairUncertainty> {
    let mut result = BTreeMap::new();
    for row in 1..=left as u32 {
        for column in 1..=right as u32 {
            result.insert(
                (row, column),
                PairUncertainty {
                    source_lineage: "exact-testimony".to_owned(),
                    row_given_column_bits: 0x3c00,
                    column_given_row_bits: 0x3c00,
                    row_given_column: ExactInterval::point(integer(1)),
                    column_given_row: ExactInterval::point(integer(1)),
                    row_given_column_ulp: ratio(1, 1024),
                    column_given_row_ulp: ratio(1, 1024),
                },
            );
        }
    }
    result
}

/// One presentation carrying exactly one open contact, whose admission closes a triangle.
///
/// The partner's position box has width on one axis, which is what makes the second contact
/// undecided: `d²(1,3) ∈ [1, 121/100]` is inside an aperture of `51/10`, and
/// `d²(2,3) ∈ [5, 521/100]` straddles it.
fn undecided_presentation() -> PhysicalConstraintComplex {
    let material = vec![
        ComponentMaterial {
            lineage: "chain".to_owned(),
            residues: vec![
                ResidueMaterial {
                    source_ordinal: 1,
                    monomer: "A".to_owned(),
                    position: CoordinateBox3::point(integer(0), integer(0), integer(0)),
                },
                ResidueMaterial {
                    source_ordinal: 2,
                    monomer: "B".to_owned(),
                    position: CoordinateBox3::point(integer(2), integer(0), integer(0)),
                },
            ],
        },
        ComponentMaterial {
            lineage: "partner".to_owned(),
            residues: vec![ResidueMaterial {
                source_ordinal: 1,
                monomer: "C".to_owned(),
                position: CoordinateBox3 {
                    x: ExactInterval::point(integer(0)),
                    y: ExactInterval::new(integer(1), ratio(11, 10)).expect("ordered"),
                    z: ExactInterval::point(integer(0)),
                },
            }],
        },
    ];
    let mut complex = PhysicalConstraintComplex::found("undecided partner", EventId(1), material)
        .expect("the presentation founds");
    let aperture = DistanceAperture {
        lineage: "squared distance at or below fifty-one tenths".to_owned(),
        squared: ratio(51, 10),
    };
    let left = ConstraintComponentId(1);
    let right = ConstraintComponentId(2);
    let enacted = {
        let left_vertices = complex.component(left).expect("component").vertices.clone();
        let right_vertices = complex
            .component(right)
            .expect("component")
            .vertices
            .clone();
        left_vertices
            .iter()
            .flat_map(|a| {
                let aperture = &aperture;
                let complex = &complex;
                right_vertices.iter().map(move |b| {
                    aperture.classify(
                        &complex.vertices[a]
                            .position
                            .squared_distance(&complex.vertices[b].position),
                    )
                })
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        enacted,
        vec![ContactClass::Inside, ContactClass::Open],
        "one decided contact and one genuinely undecided one"
    );
    complex
        .found_contact_family(left, right, aperture, &enacted, &undecided_uncertainty(2, 1))
        .expect("the family founds");
    complex
}

fn undecided_configuration() -> ExactConfiguration {
    configuration(
        3,
        &[(1, &[0, 0, 0]), (2, &[2, 0, 0]), (3, &[0, 1, 0])],
    )
}

/// **The finding item 5 asks for.** The two bounds of the open family differ in `dim ker J`: the
/// refusing member is flexible and the admitting member is infinitesimally rigid. An `Open`
/// contact is therefore a rigidity question, and neither bound may be silently taken for the
/// answer.
#[test]
fn the_open_family_bounds_differ_in_motion_dimension() {
    let complex = undecided_presentation();
    let configuration = undecided_configuration();
    let family = rigidity_family(&complex, &configuration).expect("the family returns");

    assert!(!family.is_determinate());
    assert_eq!(family.open_contacts.len(), 1);
    assert_eq!(family.cardinality(), BigUint::from(2_u8));
    assert!(family.open_subsumed_by_inside.is_empty());

    assert_eq!(family.refusing.constraint_count, 2);
    assert_eq!(family.admitting.constraint_count, 3);
    assert_eq!(family.refusing.trivial.dimension_of_span, 6);
    assert_eq!(family.admitting.trivial.dimension_of_span, 6);
    assert_eq!(family.refusing.motion_dimension, 7);
    assert_eq!(family.admitting.motion_dimension, 6);
    assert_eq!(family.refusing.internal_motion_dimension, 1);
    assert_eq!(family.admitting.internal_motion_dimension, 0);
    assert!(!family.refusing.is_infinitesimally_rigid());
    assert!(family.admitting.is_infinitesimally_rigid());
    assert!(family.bounds_differ_in_motion_dimension());
    assert_eq!(family.motion_dimension_bounds(), (6, 7));
}

/// A named member is reachable by declaring the resolution, and a declaration that does not name
/// every open contact exactly once refuses through the adapter that owns that law.
#[test]
fn a_declared_resolution_selects_a_member_and_an_incomplete_one_refuses() {
    let complex = undecided_presentation();
    let configuration = undecided_configuration();
    let open = family_open_edge(&complex);

    let admitted = rigidity_member(
        &complex,
        &configuration,
        &OpenContactLaw::Declared(OpenResolution::declared([(open, true)])),
    )
    .expect("the declared member returns");
    assert_eq!(admitted.motion_dimension, 6);

    let refused = rigidity_member(
        &complex,
        &configuration,
        &OpenContactLaw::Declared(OpenResolution::declared([])),
    );
    assert!(
        matches!(refused, Err(RigidityError::Grading(_))),
        "a resolution that names no open contact is refused by the grading owner, not defaulted"
    );
}

fn family_open_edge(complex: &PhysicalConstraintComplex) -> ConstraintEdge {
    let family = graded_constraint_family(complex).expect("the graded family returns");
    family.open_contacts[0].edge
}

// ---------------------------------------------------------------------------------------------
// typed refusals on hostile and remounted input
// ---------------------------------------------------------------------------------------------

/// **An interval position is not a configuration.** It is refused by name with its occurrence and
/// axis rather than collapsed to a midpoint, an endpoint or a float.
#[test]
fn a_presented_position_with_width_is_refused_rather_than_collapsed() {
    let complex = undecided_presentation();
    assert_eq!(
        ExactConfiguration::from_presented(&complex),
        Err(RigidityError::ConfigurationIsNotAPoint {
            occurrence: ConstraintVertexId(3),
            axis: 1,
        })
    );
}

/// A declared configuration that does not lie inside the presentation it claims to describe is
/// refused, so a rigidity family cannot be read off coordinates from somewhere else.
#[test]
fn a_configuration_outside_the_presented_box_is_refused() {
    let complex = undecided_presentation();
    let elsewhere = configuration(
        3,
        &[(1, &[0, 0, 0]), (2, &[2, 0, 0]), (3, &[0, 9, 0])],
    );
    assert_eq!(
        rigidity_family(&complex, &elsewhere),
        Err(RigidityError::ConfigurationOutsideBox {
            occurrence: ConstraintVertexId(3),
            axis: 1,
        })
    );
}

#[test]
fn a_ragged_or_empty_configuration_refuses_by_name() {
    assert_eq!(
        ExactConfiguration::declared(
            3,
            [(ConstraintVertexId(1), vec![integer(0), integer(1)])]
        ),
        Err(RigidityError::RaggedConfiguration {
            occurrence: ConstraintVertexId(1),
            declared: 3,
            supplied: 2,
        })
    );
    assert_eq!(
        ExactConfiguration::declared(3, []),
        Err(RigidityError::EmptyConfiguration)
    );
    assert_eq!(
        ExactConfiguration::declared(0, [(ConstraintVertexId(1), vec![])]),
        Err(RigidityError::ZeroDimension)
    );
}

/// A remounted Jacobian whose matrix and constraint population disagree refuses by name rather
/// than indexing past the end of a row.
#[test]
fn a_remounted_jacobian_of_the_wrong_shape_refuses_rather_than_indexing() {
    let configuration = configuration(2, &[(1, &[0, 0]), (2, &[1, 0]), (3, &[0, 1])]);
    let mut jacobian = jacobian("triangle", &configuration, &[(1, 2), (1, 3), (2, 3)]);
    let duplicate = jacobian.constraints[0].clone();
    jacobian.constraints.push(duplicate);
    assert_eq!(
        rigidity_reading(&jacobian),
        Err(RigidityError::JacobianShapeDisagrees {
            rows: 3,
            columns: 6,
            expected_rows: 4,
            expected_columns: 6,
        })
    );
}

/// A remounted member whose `edge_provenance` and `edge_cells` disagree names the one-cell rather
/// than guessing a provenance for it.
#[test]
fn a_member_missing_a_constraint_provenance_refuses_by_name() {
    let complex = undecided_presentation();
    let configuration = undecided_configuration();
    let mut member = graded_constraint_member(&complex, &OpenContactLaw::RefuseEveryOpen)
        .expect("the member founds");
    let edge = *member
        .edge_provenance
        .keys()
        .next()
        .expect("the member carries one-cells");
    member.edge_provenance.remove(&edge);
    assert_eq!(
        RigidityJacobian::from_member(&member, &configuration),
        Err(RigidityError::ConstraintProvenanceAbsent(edge))
    );
}

/// A constraint naming an occurrence the configuration does not carry refuses by address.
#[test]
fn a_constraint_on_an_absent_occurrence_refuses_by_address() {
    let configuration = configuration(2, &[(1, &[0, 0]), (2, &[1, 0])]);
    assert_eq!(
        RigidityJacobian::found("absent", &configuration, &bars(&[(1, 9)])),
        Err(RigidityError::OccurrenceAbsent(ConstraintVertexId(9)))
    );
}

/// The reading round-trips through its serialized chart unchanged.
#[test]
fn a_rigidity_reading_remounts_from_its_serialized_chart() {
    let configuration = configuration(2, &[(1, &[0, 0]), (2, &[4, 0]), (3, &[0, 3])]);
    let (_, reading) = reading("triangle", &configuration, &[(1, 2), (1, 3), (2, 3)]);
    let remounted: RigidityReading =
        ron::from_str(&ron::to_string(&reading).expect("the reading serializes"))
            .expect("the reading remounts");
    assert_eq!(remounted, reading);
}

// ---------------------------------------------------------------------------------------------
// the measured M5 structures
// ---------------------------------------------------------------------------------------------

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
/// The RBX1 chain is the one component present in all three presentations.
const RBX1_RESIDUES: usize = 108;
/// The residue window the rigidity receiver is measured on. The whole chain is a larger exact
/// elimination than this check needs; the window is declared here rather than inferred.
const WINDOW: usize = 24;
/// Eight angstroms, squared, on the exact decimal wire the intake reads.
const CONTACT_SQUARED: i64 = 64;
/// The explicit ceiling on maximal-cluster enumeration. It refuses above this rather than
/// exhausting the machine, and the measured families stay far inside it.
const CLUSTER_BOUND: usize = 4096;

/// One alpha carbon, exactly: the deposited decimal is a rational and is used as one.
fn exact_decimal(token: &str) -> Result<Rat, String> {
    let token = token
        .strip_prefix('\'')
        .and_then(|body| body.strip_suffix('\''))
        .unwrap_or(token);
    let negative = token.starts_with('-');
    let unsigned = token.trim_start_matches(['-', '+']);
    let (whole, fraction) = unsigned.split_once('.').unwrap_or((unsigned, ""));
    if whole.is_empty()
        || !whole.chars().all(|character| character.is_ascii_digit())
        || !fraction.chars().all(|character| character.is_ascii_digit())
    {
        return Err(format!("coordinate token {token:?} is not a plain decimal"));
    }
    let digits = format!("{whole}{fraction}");
    let numerator = digits
        .parse::<BigInt>()
        .map_err(|error| error.to_string())?;
    let denominator = BigInt::from(10_u8).pow(fraction.len() as u32);
    let value = Rat::new(numerator, denominator);
    Ok(if negative { -value } else { value })
}

/// The alpha carbons of every chain, in residue order, as exact rational places.
fn read_alpha_carbons(path: &Path) -> Result<BTreeMap<String, Vec<Vec<Rat>>>, String> {
    let text = std::fs::read_to_string(path).map_err(|error| error.to_string())?;
    let lines = text.lines().collect::<Vec<_>>();
    let mut headers = Vec::<String>::new();
    let mut rows = Vec::<Vec<&str>>::new();
    let mut at = 0usize;
    while at < lines.len() {
        if lines[at].trim() != "loop_" {
            at += 1;
            continue;
        }
        let mut cursor = at + 1;
        let mut candidate = Vec::<String>::new();
        while cursor < lines.len() && lines[cursor].trim_start().starts_with('_') {
            candidate.push(lines[cursor].trim().to_owned());
            cursor += 1;
        }
        if !candidate.iter().any(|name| name.starts_with("_atom_site.")) {
            at = cursor;
            continue;
        }
        headers = candidate;
        while cursor < lines.len() {
            let line = lines[cursor].trim();
            if line == "#" || line == "loop_" || line.starts_with('_') {
                break;
            }
            if !line.is_empty() {
                let fields = line.split_whitespace().collect::<Vec<_>>();
                if fields.len() != headers.len() {
                    return Err(format!(
                        "{} atom_site row {} has {} fields under {} headers",
                        path.display(),
                        cursor + 1,
                        fields.len(),
                        headers.len()
                    ));
                }
                rows.push(fields);
            }
            cursor += 1;
        }
        break;
    }
    if headers.is_empty() || rows.is_empty() {
        return Err(format!("{} has no atom_site loop", path.display()));
    }
    let column = |name: &str| -> Result<usize, String> {
        headers
            .iter()
            .position(|candidate| candidate == name)
            .ok_or_else(|| format!("{} has no {name} atom_site face", path.display()))
    };
    let atom = column("_atom_site.label_atom_id")?;
    let chain = column("_atom_site.label_asym_id")?;
    let x = column("_atom_site.Cartn_x")?;
    let y = column("_atom_site.Cartn_y")?;
    let z = column("_atom_site.Cartn_z")?;

    let mut chains: BTreeMap<String, Vec<Vec<Rat>>> = BTreeMap::new();
    for row in rows {
        if row[atom] != "CA" {
            continue;
        }
        let mut point = Vec::with_capacity(3);
        for axis in [x, y, z] {
            point.push(exact_decimal(row[axis])?);
        }
        chains.entry(row[chain].to_owned()).or_default().push(point);
    }
    Ok(chains)
}

fn squared_distance(left: &[Rat], right: &[Rat]) -> Rat {
    left.iter()
        .zip(right)
        .fold(Rat::zero(), |sum, (a, b)| {
            let difference = a - b;
            sum + &difference * &difference
        })
}

struct MeasuredStructure {
    reading: RigidityReading,
    jacobian: RigidityJacobian,
}

fn measure_structure(lineage: &'static str, path: &Path) -> Result<MeasuredStructure, String> {
    let chains = read_alpha_carbons(path)?;
    let rbx1 = chains
        .values()
        .filter(|places| places.len() == RBX1_RESIDUES)
        .collect::<Vec<_>>();
    if rbx1.len() != 1 {
        return Err(format!(
            "{} carries {} chains of {RBX1_RESIDUES} alpha carbons, not one",
            path.display(),
            rbx1.len()
        ));
    }
    let window = &rbx1[0][..WINDOW];

    let configuration = ExactConfiguration::declared(
        3,
        window
            .iter()
            .enumerate()
            .map(|(at, point)| (ConstraintVertexId(at as u64 + 1), point.clone())),
    )
    .map_err(|error| error.to_string())?;

    let aperture = Rat::from_integer(BigInt::from(CONTACT_SQUARED));
    let mut constraints = BTreeMap::new();
    for left in 0..WINDOW {
        for right in (left + 1)..WINDOW {
            let backbone = right == left + 1;
            if !backbone && squared_distance(&window[left], &window[right]) > aperture {
                continue;
            }
            let (edge, _) = ConstraintEdge::new(
                ConstraintVertexId(left as u64 + 1),
                ConstraintVertexId(right as u64 + 1),
            )
            .map_err(|error| error.to_string())?;
            constraints.insert(
                edge,
                if backbone {
                    EdgeProvenance::Polygonal
                } else {
                    EdgeProvenance::AdmittedContact
                },
            );
        }
    }

    let jacobian = RigidityJacobian::found(lineage, &configuration, &constraints)
        .map_err(|error| error.to_string())?;
    let reading = rigidity_reading(&jacobian).map_err(|error| error.to_string())?;
    Ok(MeasuredStructure { reading, jacobian })
}

/// **The measured return on the authenticated M5 release.**
///
/// Absent the release this test refuses. The laws themselves are checked above on synthetic exact
/// configurations that need no fixture, so nothing here is the only check of anything.
#[test]
fn the_rigidity_receiver_measures_the_m5_structures() {
    let root = std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT));
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the measured rigidity reading \
         cannot be taken, and this test refuses to report success without taking it. Place the \
         authenticated release at that path, or set {STRUCTURE_ROOT_ENV} to the directory \
         carrying designed-free-rbx1.cif, ptxv2-free-rbx1-seed2.cif and \
         ptxv2-cul1-rbx1-seed0.cif. Every law this module owns is checked without any fixture by \
         the synthetic tests above.",
        root.display()
    );

    let structures = [
        ("designed-free", "designed-free-rbx1.cif"),
        ("protenix-free-seed2", "ptxv2-free-rbx1-seed2.cif"),
        ("protenix-cul1-seed0", "ptxv2-cul1-rbx1-seed0.cif"),
    ];
    for (lineage, file) in structures {
        let measured = measure_structure(lineage, &root.join(file))
            .unwrap_or_else(|error| panic!("{lineage}: {error}"));
        let reading = &measured.reading;
        assert_eq!(reading.dimension, 3);
        assert_eq!(reading.occurrences, WINDOW);
        assert_eq!(reading.maxwell.coordinate_freedoms, 3 * WINDOW);
        assert_eq!(
            reading.rank + reading.motion_dimension,
            reading.maxwell.coordinate_freedoms
        );
        assert_eq!(
            reading.rank + reading.self_stress_dimension,
            reading.constraint_count
        );
        assert_eq!(
            reading.trivial.degeneracy,
            ConfigurationDegeneracy::Spanning,
            "a folded chain window affinely spans space"
        );
        assert_eq!(reading.trivial.dimension_of_span, 6);
        assert!(reading.motion_dimension >= 6);

        let sensitivity =
            removal_sensitivity(&measured.jacobian, reading).expect("the sensitivity returns");
        let checked = verify_removal_sensitivity(&measured.jacobian, &sensitivity, 6)
            .expect("the deletion agrees with the self-stress support");
        assert_eq!(checked, 6);

        let clusters = rigid_clusters(&measured.jacobian, reading, CLUSTER_BOUND)
            .expect("the cluster reading returns inside its declared bound");
        let largest = clusters
            .clusters
            .iter()
            .map(Vec::len)
            .max()
            .expect("every occurrence lies in at least one maximal cluster");
        assert!(
            clusters
                .clusters
                .iter()
                .all(|cluster| cluster.iter().all(|block| *block < WINDOW))
        );

        println!(
            "rigidity_receiver M5 | {lineage} | occurrences {} | constraints {} | rank {} | \
             dim ker J {} | dim ker J^T {} | trivial {} | internal {} | Maxwell count {} | \
             count is a bound only {} | load-bearing {} | redundant {} | clusters {} | \
             largest cluster {} | implied pairs {} | implied without a bar {}",
            reading.occurrences,
            reading.constraint_count,
            reading.rank,
            reading.motion_dimension,
            reading.self_stress_dimension,
            reading.trivial.dimension_of_span,
            reading.internal_motion_dimension,
            reading.maxwell.counted_freedom,
            reading.maxwell.count_is_a_bound_only,
            sensitivity.load_bearing.len(),
            sensitivity.redundant.len(),
            clusters.clusters.len(),
            largest,
            clusters.pairs.implied_pairs.len(),
            clusters.pairs.implied_without_constraint.len(),
        );
    }
}
