//! The conditioned static response's own checks.
//!
//! Every fixture is a synthetic exact configuration that needs no deposited structure, so the
//! whole file runs anywhere. The measured RBX1 reading lives in the example
//! `crates/holonic-engine/examples/the_declared_force_returns_its_null_fibre_and_its_residual.rs`
//! and in `research/experiments/conditioned_rbx1_static_response/`, which is where a fixture that
//! can be absent belongs.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::*;
use crate::physical_constraint_complex::{ConstraintEdge, ConstraintVertexId};
use crate::physical_constraint_grading::EdgeProvenance;
use crate::rigidity_receiver::rigidity_reading;

// ---------------------------------------------------------------------------------------------
// synthetic material
// ---------------------------------------------------------------------------------------------

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

fn jacobian(lineage: &str, places: &ExactConfiguration, edges: &[(u64, u64)]) -> RigidityJacobian {
    RigidityJacobian::found(lineage, places, &bars(edges)).expect("the Jacobian founds")
}

/// The unit declaration used by every test: one stiffness unit per contact.
fn declaration(constraints: usize) -> ElasticDeclaration {
    ElasticDeclaration::uniform(
        constraints,
        Rat::one(),
        "declared stiffness unit (energy / length^2)",
        "angstrom",
        "declared energy unit",
    )
    .expect("a positive uniform stiffness is declared")
}

/// A braced triangular bipyramid in three dimensions: infinitesimally rigid, so `ker K` is exactly
/// the trivial motions of a spanning configuration.
fn braced_solid() -> (ExactConfiguration, RigidityJacobian) {
    let places = configuration(
        3,
        &[
            (0, &[0, 0, 0]),
            (1, &[4, 0, 0]),
            (2, &[0, 3, 0]),
            (3, &[1, 1, 5]),
            (4, &[1, 1, -5]),
        ],
    );
    let edges = [
        (0, 1),
        (0, 2),
        (1, 2),
        (0, 3),
        (1, 3),
        (2, 3),
        (0, 4),
        (1, 4),
        (2, 4),
    ];
    let jacobian = jacobian("braced-solid", &places, &edges);
    (places, jacobian)
}

/// A four-site open path in three dimensions. Its contact graph braces nothing, so the window has
/// genuine **internal floppy modes** beside the six rigid motions.
fn floppy_path() -> (ExactConfiguration, RigidityJacobian) {
    let places = configuration(
        3,
        &[
            (0, &[0, 0, 0]),
            (1, &[3, 0, 0]),
            (2, &[3, 4, 0]),
            (3, &[3, 4, 5]),
        ],
    );
    let jacobian = jacobian("floppy-path", &places, &[(0, 1), (1, 2), (2, 3)]);
    (places, jacobian)
}

fn stiffness_of(jacobian: &RigidityJacobian) -> ConditionedStiffness {
    ConditionedStiffness::declared(jacobian, declaration(jacobian.constraint_count()))
        .expect("the declared stiffness stands")
}

fn metric_of(stiffness: &ConditionedStiffness) -> DeclaredMetric {
    DeclaredMetric::cartesian_identity(stiffness.coordinate_freedoms, "angstrom")
        .expect("the identity metric is declared")
}

// ---------------------------------------------------------------------------------------------
// the counterexample that withholds the neck claim
// ---------------------------------------------------------------------------------------------

#[test]
fn the_stiffness_and_pseudoinverse_cross_blocks_have_different_ranks() {
    let (stiffness_rank, pseudo_rank, block) =
        neck_cross_block_counterexample().expect("the four-site witness recomputes");
    assert_eq!(
        stiffness_rank, 1,
        "K's cross block on the cut {{1,2}}|{{3,4}}"
    );
    assert_eq!(pseudo_rank, 2, "the Moore-Penrose cross block");

    let eighth = |numerator: i64| Rat::new(BigInt::from(numerator), BigInt::from(8));
    assert_eq!(block[0][0], eighth(-3));
    assert_eq!(block[0][1], eighth(-1));
    assert_eq!(block[1][0], eighth(-5));
    assert_eq!(block[1][1], eighth(-3));
}

#[test]
fn every_family_reading_withholds_the_neck_identification() {
    let (places, jacobian) = braced_solid();
    let stiffness = stiffness_of(&jacobian);
    let null = NullFibre::measure(&stiffness, &jacobian).expect("the null fibre measures");
    let metric = metric_of(&stiffness);
    let forcing = ForcingDeclaration::pinch_family(
        &places,
        &[(0, 3), (1, 4), (2, 3)],
        "a synthetic declared support",
        "unit magnitudes",
    )
    .expect("the pinch family founds");
    let reading = ResponseFamilyReading::read(
        &stiffness,
        &null,
        &metric,
        ResponseGauge::MetricComplement,
        &forcing,
    )
    .expect("the family reading returns");

    let NeckIdentification::WithheldSingularStiffness { null_dimension, .. } = reading.neck;
    assert_eq!(null_dimension, null.dimension);
    assert!(null.dimension > 0, "K is singular, so H(0) does not exist");
}

// ---------------------------------------------------------------------------------------------
// the stiffness
// ---------------------------------------------------------------------------------------------

#[test]
fn the_stiffness_is_self_adjoint_and_its_kernel_is_the_constraint_kernel() {
    let (_, jacobian) = braced_solid();
    let stiffness = stiffness_of(&jacobian);
    assert!(stiffness.self_adjoint_defect.is_zero());
    assert_eq!(stiffness.coordinate_freedoms, 15);

    let reading = rigidity_reading(&jacobian).expect("the rigidity reading returns");
    assert_eq!(
        stiffness.rank, reading.rank,
        "rank K = rank J for gamma > 0"
    );

    let null = NullFibre::measure(&stiffness, &jacobian).expect("the null fibre measures");
    assert!(null.equals_constraint_kernel, "ker K = ker J is verified");
    assert_eq!(null.dimension, reading.motion_dimension);
    assert_eq!(
        null.trivial_dimension, 6,
        "a spanning configuration in three dimensions"
    );
    assert_eq!(null.internal_floppy_dimension, 0, "the solid is braced");
}

#[test]
fn the_null_fibre_carries_the_internal_floppy_modes_and_not_only_the_rigid_motions() {
    let (_, jacobian) = floppy_path();
    let stiffness = stiffness_of(&jacobian);
    let null = NullFibre::measure(&stiffness, &jacobian).expect("the null fibre measures");
    assert_eq!(null.trivial_dimension, 6);
    assert_eq!(
        null.dimension, 9,
        "12 coordinates less 3 independent constraints"
    );
    assert_eq!(
        null.internal_floppy_dimension, 3,
        "a reading that took Z to be the six rigid motions would be wrong by three dimensions"
    );
    assert!(null.equals_constraint_kernel);
}

#[test]
fn the_elastic_energy_of_a_kernel_direction_is_exactly_zero() {
    let (_, jacobian) = floppy_path();
    let stiffness = stiffness_of(&jacobian);
    let null = NullFibre::measure(&stiffness, &jacobian).expect("the null fibre measures");
    for vector in &null.basis {
        assert!(
            stiffness
                .energy(vector)
                .expect("the energy reads")
                .is_zero(),
            "a null direction stores no elastic energy"
        );
    }
}

#[test]
fn a_loaded_coincident_constraint_is_refused_rather_than_divided_by() {
    let places = configuration(3, &[(0, &[0, 0, 0]), (1, &[0, 0, 0]), (2, &[1, 0, 0])]);
    let jacobian = jacobian("coincident", &places, &[(0, 1), (0, 2)]);
    let error = ConditionedStiffness::declared(&jacobian, declaration(2))
        .expect_err("a loaded zero-length spring is refused");
    assert!(matches!(
        error,
        StaticResponseError::CoincidentConstraintIsLoaded { .. }
    ));
}

#[test]
fn a_negative_spring_constant_is_refused() {
    let error = ElasticDeclaration::per_constraint(
        vec![Rat::one(), integer(-1)],
        "unit",
        "angstrom",
        "energy",
    )
    .expect_err("W must be positive semidefinite");
    assert!(matches!(
        error,
        StaticResponseError::NegativeStiffness { constraint: 1 }
    ));
}

// ---------------------------------------------------------------------------------------------
// the forcing
// ---------------------------------------------------------------------------------------------

#[test]
fn the_pinch_family_is_exactly_orthogonal_to_every_trivial_motion() {
    let (places, jacobian) = braced_solid();
    let trivial = TrivialMotionReading::measure(&jacobian).expect("the trivial motions measure");
    let mut forcing = ForcingDeclaration::pinch_family(
        &places,
        &[(0, 1), (0, 3), (2, 4), (3, 4)],
        "a synthetic declared support",
        "unit magnitudes",
    )
    .expect("the pinch family founds");
    assert!(
        forcing.self_equilibrated(&trivial).expect("the check runs"),
        "net force and net moment both vanish, so Z* f can fail only on a floppy mode"
    );
    assert!(!forcing.held_out_displacement_used);
}

#[test]
fn a_single_site_push_is_not_self_equilibrated_and_the_response_is_refused() {
    let (_places, jacobian) = braced_solid();
    let stiffness = stiffness_of(&jacobian);
    let null = NullFibre::measure(&stiffness, &jacobian).expect("the null fibre measures");
    let metric = metric_of(&stiffness);

    // A force on one site alone, along +x. Its net force does not vanish, so no static
    // equilibrium of the free body answers it.
    let mut force = vec![Rat::zero(); stiffness.coordinate_freedoms];
    force[0] = Rat::one();

    let response = StaticResponse::solve(
        &stiffness,
        &null,
        &metric,
        ResponseGauge::MetricComplement,
        &force,
    )
    .expect("the receiver returns rather than panics");
    assert!(!response.compatible);
    assert!(response.displacement.is_none());
    assert!(
        response.compatibility_pairing.iter().any(|e| !e.is_zero()),
        "Z* f is exhibited, not summarized"
    );
    assert!(
        response
            .retained_incompatible_force
            .iter()
            .any(|e| !e.is_zero()),
        "(I - P) f is retained and not projected away"
    );
    assert!(
        response.obstruction.is_some(),
        "an obstruction is a return: the cokernel covector witnesses the refusal"
    );

    // The projection receiver exists, answers a different question, and says so.
    let (projected, retained, label) = StaticResponse::least_squares_projection(
        &stiffness,
        &null,
        &metric,
        ResponseGauge::MetricComplement,
        &force,
    )
    .expect("the labelled projection receiver returns");
    assert!(projected.compatible);
    assert!(label.starts_with("LEAST-SQUARES PROJECTION RECEIVER"));
    assert_eq!(retained, response.retained_incompatible_force);
    // And the projected force really is a different force.
    assert_ne!(projected.force, force);
}

// ---------------------------------------------------------------------------------------------
// the response and its gauge
// ---------------------------------------------------------------------------------------------

#[test]
fn the_gauge_returns_one_representative_of_the_fibre_with_zero_residuals() {
    let (places, jacobian) = braced_solid();
    let stiffness = stiffness_of(&jacobian);
    let null = NullFibre::measure(&stiffness, &jacobian).expect("the null fibre measures");
    let metric = metric_of(&stiffness);
    let forcing = ForcingDeclaration::pinch_family(
        &places,
        &[(0, 1), (3, 4)],
        "a synthetic declared support",
        "unit magnitudes",
    )
    .expect("the pinch family founds");
    let force = forcing.force(&[Rat::one(), Rat::one()]).expect("f = B u");

    let response = StaticResponse::solve(
        &stiffness,
        &null,
        &metric,
        ResponseGauge::MetricComplement,
        &force,
    )
    .expect("the response returns");
    assert!(response.compatible);
    assert!(response.equilibrium_residual.iter().all(Rat::is_zero));
    assert!(response.gauge_residual.iter().all(Rat::is_zero));
    assert_eq!(response.null_fibre_dimension, null.dimension);
    let displacement = response
        .displacement
        .clone()
        .expect("a displacement returns");

    // The gauge really is a choice inside an affine fibre: adding any kernel direction keeps the
    // equilibrium and breaks only the gauge.
    let shifted: Vec<Rat> = displacement
        .iter()
        .zip(&null.basis[0])
        .map(|(a, b)| a + b)
        .collect();
    let image = stiffness.matrix.apply(&shifted).expect("K applies");
    assert_eq!(image, force, "every fibre representative is an equilibrium");
    assert!(
        null.basis
            .iter()
            .map(|vector| dot(vector, &shifted))
            .any(|pairing| !pairing.is_zero()),
        "but only one of them satisfies the declared gauge"
    );
}

#[test]
fn a_supplied_null_fibre_must_be_the_actual_kernel_not_only_the_same_dimension() {
    let places = configuration(1, &[(0, &[0]), (1, &[1])]);
    let jacobian = jacobian("two-site-unit-bar-null-validation", &places, &[(0, 1)]);
    let stiffness = stiffness_of(&jacobian);
    let mut null = NullFibre::measure(&stiffness, &jacobian).expect("the null fibre measures");
    null.basis[0] = vec![Rat::one(), Rat::zero()];
    let metric = metric_of(&stiffness);
    let error = StaticResponse::solve(
        &stiffness,
        &null,
        &metric,
        ResponseGauge::MetricComplement,
        &[Rat::one(), integer(-1)],
    )
    .expect_err("a same-dimension non-kernel basis is refused");
    assert!(matches!(
        error,
        StaticResponseError::NullFibreBasisVectorNotInKernel
    ));
}

#[test]
fn the_response_is_linear_and_an_opposite_forcing_returns_the_opposite_displacement() {
    let (places, jacobian) = braced_solid();
    let stiffness = stiffness_of(&jacobian);
    let null = NullFibre::measure(&stiffness, &jacobian).expect("the null fibre measures");
    let metric = metric_of(&stiffness);
    let forcing = ForcingDeclaration::pinch_family(
        &places,
        &[(0, 1), (3, 4)],
        "a synthetic declared support",
        "unit magnitudes",
    )
    .expect("the pinch family founds");

    let forward = forcing.force(&[Rat::one(), Rat::one()]).expect("f = B u");
    let backward = forcing
        .force(&[integer(-1), integer(-1)])
        .expect("f = B (-u)");
    let solve = |force: &[Rat]| {
        StaticResponse::solve(
            &stiffness,
            &null,
            &metric,
            ResponseGauge::MetricComplement,
            force,
        )
        .expect("the response returns")
        .displacement
        .expect("a displacement returns")
    };
    let positive = solve(&forward);
    let negative = solve(&backward);
    for (a, b) in positive.iter().zip(&negative) {
        assert_eq!(a, &-b.clone());
    }
}

#[test]
fn the_family_reading_rank_matches_the_admissible_force_rank() {
    let (places, jacobian) = braced_solid();
    let stiffness = stiffness_of(&jacobian);
    let null = NullFibre::measure(&stiffness, &jacobian).expect("the null fibre measures");
    let metric = metric_of(&stiffness);
    let forcing = ForcingDeclaration::pinch_family(
        &places,
        &[(0, 1), (0, 2), (1, 2), (0, 3), (1, 4)],
        "a synthetic declared support",
        "unit magnitudes",
    )
    .expect("the pinch family founds");
    let reading = ResponseFamilyReading::read(
        &stiffness,
        &null,
        &metric,
        ResponseGauge::MetricComplement,
        &forcing,
    )
    .expect("the family reading returns");
    assert_eq!(
        reading.admissible_generators, 5,
        "every pinch is admissible here"
    );
    assert!(reading.inadmissible_generators.is_empty());
    assert!(
        reading.response_rank_equals_force_rank,
        "the gauge-fixed response is a bijection on the admissible subspace"
    );
    assert!(reading.response_rank <= reading.stiffness_rank);
}

#[test]
fn the_family_reading_uses_the_full_kernel_of_z_star_b() {
    // A two-site unit bar gives K = [[1,-1],[-1,1]]. With B = I, neither e₁ nor e₂ is
    // compatible with the translation null mode, but e₁ - e₂ is. Filtering columns one at a
    // time would incorrectly report an empty admissible family.
    let places = configuration(1, &[(0, &[0]), (1, &[1])]);
    let jacobian = jacobian("two-site-unit-bar", &places, &[(0, 1)]);
    let stiffness = stiffness_of(&jacobian);
    let null = NullFibre::measure(&stiffness, &jacobian).expect("the null fibre measures");
    let metric = metric_of(&stiffness);
    let forcing = ForcingDeclaration::declared(
        ExactRatMatrix::identity(2).expect("the identity forcing map stands"),
        vec![
            ForcingGenerator {
                description: "first coordinate force".to_owned(),
                loaded_blocks: vec![0],
            },
            ForcingGenerator {
                description: "second coordinate force".to_owned(),
                loaded_blocks: vec![1],
            },
        ],
        "the two-site regression support",
        "the declared coordinate basis",
        "unit magnitudes",
    )
    .expect("the identity forcing map declares");

    let reading = ResponseFamilyReading::read(
        &stiffness,
        &null,
        &metric,
        ResponseGauge::MetricComplement,
        &forcing,
    )
    .expect("the full admissible family returns");
    assert_eq!(reading.inadmissible_generators, vec![0, 1]);
    assert_eq!(reading.admissible_generators, 1);
    assert_eq!(reading.force_rank, 1);
    assert_eq!(reading.response_rank, 1);
    assert!(reading.response_rank_equals_force_rank);
}

// ---------------------------------------------------------------------------------------------
// the oriented quadrance receiver
// ---------------------------------------------------------------------------------------------

#[test]
fn the_linearized_quadrance_change_differs_from_the_finite_one_by_exactly_the_quadratic_term() {
    let places = configuration(3, &[(0, &[0, 0, 0]), (1, &[2, 0, 0])]);
    // Move site 1 by (1, 0, 0): Q goes from 4 to 9, so the finite change is 5. The linearized
    // change is 2<q0 - q1, dq0 - dq1> = 2 * (-2) * (-1) = 4, and the quadratic term is 1.
    let displacement = vec![
        Rat::zero(),
        Rat::zero(),
        Rat::zero(),
        Rat::one(),
        Rat::zero(),
        Rat::zero(),
    ];
    let response = QuadranceResponse::measure(&places, &displacement, &[(0, 1)], "angstrom^2")
        .expect("the quadrance response returns");
    assert_eq!(response.linearized[0], integer(4));
    assert_eq!(response.quadratic_term[0], integer(1));
    assert_eq!(response.finite[0], integer(5));
    assert_ne!(
        response.linearized[0], response.finite[0],
        "the linearization is a different reading and is never reported as the finite change"
    );
}

#[test]
fn the_measured_quadrance_change_ignores_every_rigid_motion() {
    let source = configuration(3, &[(0, &[0, 0, 0]), (1, &[2, 0, 0]), (2, &[0, 3, 0])]);
    // The same shape, translated by (10, 10, 10) and rotated by the quarter turn (x,y) -> (-y,x).
    let moved = configuration(
        3,
        &[(0, &[10, 10, 10]), (1, &[10, 12, 10]), (2, &[7, 10, 10])],
    );
    let pairs = [(0, 1), (0, 2), (1, 2)];
    let change =
        QuadranceResponse::between(&source, &moved, &pairs).expect("the measured change returns");
    assert!(
        change.iter().all(Rat::is_zero),
        "the quadrance receiver needs no superposition and inherits none"
    );
}

#[test]
fn measured_quadrance_change_requires_the_callers_block_correspondence() {
    let source = configuration(1, &[(0, &[0]), (1, &[2]), (2, &[5])]);
    // The target carries the same shape translated by ten units, but its chart order is [source
    // block 1, source block 2, source block 0]. The explicit map restores the intended alignment.
    let target = configuration(1, &[(0, &[12]), (1, &[15]), (2, &[10])]);
    let correspondence = BlockCorrespondence::declared(3, 3, vec![2, 0, 1])
        .expect("the caller's chart alignment stands");
    let pairs = [(0, 1), (0, 2), (1, 2)];
    let aligned =
        QuadranceResponse::between_with_correspondence(&source, &target, &correspondence, &pairs)
            .expect("the aligned comparison returns");
    assert!(aligned.iter().all(Rat::is_zero));

    let positional = QuadranceResponse::between(&source, &target, &pairs)
        .expect("the identity convenience route returns");
    assert!(positional.iter().any(|change| !change.is_zero()));
}

#[test]
fn the_unoriented_face_cannot_tell_a_response_from_its_opposite() {
    let predicted = vec![integer(1), integer(2), integer(-1)];
    let opposite: Vec<Rat> = predicted.iter().map(|entry| -entry.clone()).collect();
    let measured = vec![integer(2), integer(3), integer(-2)];

    let agreeing = OrientedAgreement::between(&predicted, &measured).expect("the agreement reads");
    let opposing = OrientedAgreement::between(&opposite, &measured).expect("the agreement reads");

    assert_eq!(agreeing.sign, 1);
    assert_eq!(opposing.sign, -1);
    assert_eq!(
        agreeing.cosine_square, opposing.cosine_square,
        "cos^2 is blind to the orientation, which is why the sign is reported beside it"
    );
    assert!(agreeing.residual_quadrance < opposing.residual_quadrance);
    assert!(agreeing
        .scale_diagnostic
        .expect("a diagnostic scale")
        .is_positive());
    assert!(opposing
        .scale_diagnostic
        .expect("a diagnostic scale")
        .is_negative());
}

#[test]
fn an_orthogonal_prediction_scores_a_zero_sign_and_a_zero_cosine_square() {
    let predicted = vec![Rat::one(), Rat::zero()];
    let measured = vec![Rat::zero(), Rat::one()];
    let agreement = OrientedAgreement::between(&predicted, &measured).expect("the agreement reads");
    assert_eq!(agreement.sign, 0);
    assert_eq!(agreement.cosine_square, Some(Rat::zero()));
    assert_eq!(agreement.residual_quadrance, integer(2));
}

// ---------------------------------------------------------------------------------------------
// the whole passage, end to end, on a floppy window
// ---------------------------------------------------------------------------------------------

#[test]
fn a_pinch_on_a_floppy_window_can_still_be_incompatible_and_says_which_mode_refuses_it() {
    let (places, jacobian) = floppy_path();
    let stiffness = stiffness_of(&jacobian);
    let null = NullFibre::measure(&stiffness, &jacobian).expect("the null fibre measures");
    let metric = metric_of(&stiffness);
    assert_eq!(null.internal_floppy_dimension, 3);

    // A pinch between the two ends of the open path. It is self-equilibrated against every rigid
    // motion by construction, so any incompatibility it meets is an internal floppy mode.
    let mut forcing = ForcingDeclaration::pinch_family(
        &places,
        &[(0, 3)],
        "the two ends of the open path",
        "unit magnitude",
    )
    .expect("the pinch family founds");
    let trivial = TrivialMotionReading::measure(&jacobian).expect("the trivial motions measure");
    assert!(forcing.self_equilibrated(&trivial).expect("the check runs"));

    let force = forcing.force(&[Rat::one()]).expect("f = B u");
    let response = StaticResponse::solve(
        &stiffness,
        &null,
        &metric,
        ResponseGauge::MetricComplement,
        &force,
    )
    .expect("the receiver returns");
    assert!(
        !response.compatible,
        "pulling the ends of an unbraced path is answered by a mechanism, not by a stress"
    );
    assert!(response
        .retained_incompatible_force
        .iter()
        .any(|entry| !entry.is_zero()));
    assert!(response.obstruction.is_some());
}

#[test]
fn a_pinch_along_an_existing_contact_is_answered_and_its_response_is_read_as_quadrance() {
    let (places, jacobian) = braced_solid();
    let stiffness = stiffness_of(&jacobian);
    let null = NullFibre::measure(&stiffness, &jacobian).expect("the null fibre measures");
    let metric = metric_of(&stiffness);
    let forcing = ForcingDeclaration::pinch_family(
        &places,
        &[(0, 1)],
        "one declared contact",
        "unit magnitude",
    )
    .expect("the pinch family founds");
    let force = forcing.force(&[Rat::one()]).expect("f = B u");
    let response = StaticResponse::solve(
        &stiffness,
        &null,
        &metric,
        ResponseGauge::MetricComplement,
        &force,
    )
    .expect("the response returns");
    let displacement = response
        .displacement
        .clone()
        .expect("a displacement returns");

    let pairs: Vec<(usize, usize)> = vec![(0, 1), (0, 2), (1, 2), (3, 4)];
    let quadrance = QuadranceResponse::measure(&places, &displacement, &pairs, "angstrom^2")
        .expect("the quadrance response returns");
    assert_eq!(quadrance.linearized.len(), 4);
    assert!(
        quadrance.linearized[0].is_negative(),
        "a pinch with u = +1 places +(q_1 - q_0) at block 0 and its negative at block 1, so the \
         pair is squeezed along its own segment and its quadrance change is negative; the sign is \
         the content of the reading and an unoriented score would lose it"
    );
    assert!(
        quadrance
            .quadratic_term
            .iter()
            .all(|entry| !entry.is_negative()),
        "the dropped term is a sum of squares"
    );
    assert!(response
        .elastic_energy
        .expect("an energy returns")
        .is_positive());
}
