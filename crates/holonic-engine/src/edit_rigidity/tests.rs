//! T4's own checks.
//!
//! Every law — the identification with `rigidity_receiver`, the free/compensable/obstructed split,
//! the exact minimizer and its normal equation, entanglement as self-stress support, the edit
//! torque and its exact descent step, and the knot's nesting direction — is checked on synthetic
//! exact charts that need no fixture and run everywhere. The last test is the measured M5 contact
//! framework; it is `#[ignore]`d because it reads a large deposit, and it refuses rather than
//! passes when the authenticated release is absent.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::*;
use crate::physical_constraint_complex::{ConstraintEdge, ConstraintVertexId};
use crate::physical_constraint_grading::EdgeProvenance;
use crate::presentation_cost::Axis;
use crate::rigidity_receiver::{ExactConfiguration, rigidity_reading};

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

fn row(entries: &[i64]) -> Vec<Rat> {
    entries.iter().copied().map(integer).collect()
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

fn configuration(dimension: usize, places: &[(u64, &[i64])]) -> ExactConfiguration {
    ExactConfiguration::declared(
        dimension,
        places
            .iter()
            .map(|(id, coordinates)| (ConstraintVertexId(*id), place(coordinates))),
    )
    .expect("the declared configuration stands")
}

fn placement_jacobian(
    lineage: &str,
    dimension: usize,
    places: &[(u64, &[i64])],
    edges: &[(u64, u64)],
) -> (ExactConfiguration, RigidityJacobian) {
    let configuration = configuration(dimension, places);
    let jacobian = RigidityJacobian::found(lineage, &configuration, &bars(edges))
        .expect("the Jacobian founds");
    (configuration, jacobian)
}

/// **The six-slot role frame, on an embedding-placement chart.**
///
/// [definition] T3's six-slot receiver is *discrete*: `ConstraintRule::RoleAgreement` is a decidable
/// condition on integer token codes, and equality of token codes has no differential at all — a
/// token chart admits no tangent direction, so the discrete law has no first-order chart of its
/// own. The instance here is therefore built on an **embedding-placement chart**: the six slots are
/// points of `ℚ²`, the kept faces are declared pairwise squared separations and one declared linear
/// role-agreement form, and the edits are first-order displacements of a slot's placement. **The
/// discrete law is T3's `artifact_release`; this is its first-order chart and nothing here claims
/// the discrete constraint has a derivative.**
fn six_slot_frame() -> (ExactConfiguration, RigidityJacobian, KeptReceiverJacobian) {
    let (configuration, placement) = placement_jacobian(
        "six-slot-role-frame",
        2,
        &[
            (0, &[0, 0]),   // the pronoun slot
            (1, &[3, 4]),
            (2, &[6, 0]),   // the determiner slot
            (3, &[9, 4]),   // the noun slot: dog / cat
            (4, &[12, 0]),  // the name slot
            (5, &[15, 4]),  // the frame slot: is / why
        ],
        &[(2, 3), (0, 4), (1, 5)],
    );
    let separations = KeptReceiverJacobian::from_rigidity(&placement).expect("the kept family");
    // One declared linear role-agreement form: the frame slot's first coordinate must track the
    // first coordinate of slot 1. A linear form is its own differential.
    let mut form = vec![Rat::zero(); 12];
    form[10] = Rat::one();
    form[2] = -Rat::one();
    let role = KeptReceiverJacobian::from_linear_faces(
        "six-slot-role-agreement",
        12,
        vec![("frame-tracks-slot-one".to_owned(), form)],
    )
    .expect("the linear kept face");
    let kept = separations.joined(&role).expect("the joined kept family");
    (configuration, placement, kept)
}

fn unit_metric(extent: usize) -> ExactMetric {
    ExactMetric::unit("declared-unit", extent).expect("the unit metric is declared")
}

// ---------------------------------------------------------------------------------------------
// (1) the kept-receiver constraint map IS the rigidity Jacobian
// ---------------------------------------------------------------------------------------------

/// The kept-receiver Jacobian of a family of declared separations is `rigidity_receiver`'s own
/// matrix, entry for entry, and the two readings agree on every count.
#[test]
fn the_kept_receiver_jacobian_is_the_rigidity_jacobian() {
    let (_, placement) = placement_jacobian(
        "triangle",
        2,
        &[(1, &[0, 0]), (2, &[4, 0]), (3, &[0, 3])],
        &[(1, 2), (1, 3), (2, 3)],
    );
    let kept = KeptReceiverJacobian::from_rigidity(&placement).expect("the kept family");
    assert_eq!(kept.matrix(), &placement.matrix);
    assert_eq!(kept.dimension(), placement.coordinate_freedoms());
    assert_eq!(kept.face_count(), placement.constraint_count());

    let here = kept_reading(&kept).expect("the kept reading");
    let there = rigidity_reading(&placement).expect("the rigidity reading");
    identify_with_rigidity_reading(&here, &there).expect("the identification holds");
    assert_eq!(here.rank, 3);
    assert_eq!(here.free_dimension, 3, "a rigid triangle in the plane keeps its three rigid motions");
    assert_eq!(here.self_stress_dimension, 0);
    assert!(here.every_edit_is_seen() == (here.free_dimension == 0));
}

/// Every row's origin is named: a separation row is R4's, a linear row is a declared form.
#[test]
fn every_kept_face_names_where_its_row_came_from() {
    let (_, _, kept) = six_slot_frame();
    assert_eq!(kept.face_count(), 4);
    assert!(matches!(
        kept.origins()[0],
        KeptFaceOrigin::RigidityRow { .. }
    ));
    assert!(matches!(
        kept.origins()[3],
        KeptFaceOrigin::LinearForm { ref name } if name == "frame-tracks-slot-one"
    ));
}

/// The identification refuses by name when the two readings disagree.
#[test]
fn a_disagreeing_identification_is_refused_by_name() {
    let (_, placement) = placement_jacobian(
        "triangle",
        2,
        &[(1, &[0, 0]), (2, &[4, 0]), (3, &[0, 3])],
        &[(1, 2), (1, 3), (2, 3)],
    );
    let kept = KeptReceiverJacobian::from_rigidity(&placement).expect("the kept family");
    let mut here = kept_reading(&kept).expect("the kept reading");
    let there = rigidity_reading(&placement).expect("the rigidity reading");
    here.rank += 1;
    assert!(matches!(
        identify_with_rigidity_reading(&here, &there),
        Err(EditRigidityRefusal::IdentificationFails { what: "the rank", .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// (2) free, compensable, obstructed
// ---------------------------------------------------------------------------------------------

/// **`dog → cat`.** The noun slot moves perpendicular to the separation the receiver keeps, so no
/// kept receiver sees the edit at first order: it is free, `W² = 0`, and the zero compensation
/// suffices.
#[test]
fn the_noun_edit_is_free_and_costs_no_rethreading() {
    let (_, _, kept) = six_slot_frame();
    // slot 3 sits at (9,4) and slot 2 at (6,0), so the kept separation reads the direction (3,4);
    // the perpendicular (-4,3) is exactly rational and is the free edit.
    let mut vector = vec![Rat::zero(); 12];
    vector[6] = integer(-4);
    vector[7] = integer(3);
    let edit = EditDirection::declared("dog->cat", vector).expect("the edit is declared");

    let allowed = AllowedCompensation::complement_of("everything-else", 12, &edit.support())
        .expect("the allowed subspace");
    let receipt = rethreading_work(&kept, &edit, &allowed, &unit_metric(12))
        .expect("the rethreading returns");
    match &receipt.verdict {
        EditVerdict::Free { squared_work } => assert!(squared_work.is_zero()),
        other => panic!("the noun edit is free, not {}", other.arm()),
    }
    assert_eq!(receipt.cost.count(Axis::UpdateWork), &BigUint::zero());
    // The free edit lies in `ker J_keep`, which is the reading's own exhibited population.
    let reading = kept_reading(&kept).expect("the kept reading");
    let image = kept.matrix().apply(edit.vector()).expect("the image");
    assert!(image.iter().all(Zero::is_zero));
    assert!(reading.free_dimension > 0);
}

/// **The free edit is compensated by nothing.** `free_iff_zero_compensates`, executed.
#[test]
fn the_free_edit_is_compensated_by_nothing() {
    let (_, _, kept) = six_slot_frame();
    let mut vector = vec![Rat::zero(); 12];
    vector[6] = integer(-4);
    vector[7] = integer(3);
    let edit = EditDirection::declared("dog->cat", vector).expect("the edit is declared");
    // Even with a *narrow* allowed subspace the verdict is free, because nothing needs moving.
    let allowed = AllowedCompensation::coordinates("slot-two-only", 12, [4, 5])
        .expect("the allowed subspace");
    let receipt = rethreading_work(&kept, &edit, &allowed, &unit_metric(12))
        .expect("the rethreading returns");
    assert!(matches!(receipt.verdict, EditVerdict::Free { .. }));
    assert!(receipt.verdict.support().is_empty());
}

/// **A compensable edit.** Moving the noun *along* the kept separation is seen, and the exact
/// minimizer over the declared allowed subspace restores it with `W² = 25`.
#[test]
fn a_compensable_edit_returns_its_exact_minimizer_and_squared_work() {
    let (_, _, kept) = six_slot_frame();
    let mut vector = vec![Rat::zero(); 12];
    vector[6] = integer(3);
    vector[7] = integer(4);
    let edit = EditDirection::declared("noun-along-the-link", vector).expect("the edit");
    let allowed = AllowedCompensation::coordinates("determiner-may-move", 12, [4, 5])
        .expect("the allowed subspace");
    let receipt = rethreading_work(&kept, &edit, &allowed, &unit_metric(12))
        .expect("the rethreading returns");
    match &receipt.verdict {
        EditVerdict::Compensable {
            compensation,
            squared_work,
            support,
            ..
        } => {
            assert_eq!(squared_work, &integer(25));
            assert_eq!(support, &vec![4, 5]);
            assert_eq!(compensation[4], integer(3));
            assert_eq!(compensation[5], integer(4));
            for (at, entry) in compensation.iter().enumerate() {
                if at != 4 && at != 5 {
                    assert!(entry.is_zero(), "the compensation moves only what it may");
                }
            }
        }
        other => panic!("the edit is compensable, not {}", other.arm()),
    }
    assert_eq!(receipt.metric, "declared-unit");
}

/// **`is → why`.** The frame edit is seen by two kept faces that the declared allowed subspace
/// cannot reach, so no compensation exists and the return is the left-null certificate, checked.
#[test]
fn the_frame_edit_is_obstructed_and_returns_its_certificate() {
    let (_, _, kept) = six_slot_frame();
    let mut vector = vec![Rat::zero(); 12];
    vector[10] = integer(1);
    let edit = EditDirection::declared("is->why", vector).expect("the edit");
    // Only the name slot may move. No kept face reading the frame slot reads the name slot.
    let allowed = AllowedCompensation::coordinates("name-slot-only", 12, [8, 9])
        .expect("the allowed subspace");
    let receipt = rethreading_work(&kept, &edit, &allowed, &unit_metric(12))
        .expect("the rethreading returns");
    match &receipt.verdict {
        EditVerdict::Obstructed { certificate } => {
            assert!(!certificate.pairing.is_zero());
            assert!(!certificate.support.is_empty());
            // The certificate really annihilates every compensable defect.
            let allowed_matrix = allowed.matrix().expect("the allowed matrix");
            let system = kept
                .matrix()
                .multiply(&allowed_matrix)
                .expect("the compensable system");
            let annihilated = system
                .transpose()
                .expect("the transpose")
                .apply(&certificate.left_null)
                .expect("the pairing");
            assert!(annihilated.iter().all(Zero::is_zero));
            // And it reads the edit's own defect as nonzero.
            let defect = kept.matrix().apply(edit.vector()).expect("the defect");
            let pairing = certificate
                .left_null
                .iter()
                .zip(&defect)
                .fold(Rat::zero(), |sum, (left, right)| sum + left * right);
            assert_eq!(pairing, certificate.pairing);
        }
        other => panic!("the frame edit is obstructed, not {}", other.arm()),
    }
    assert!(receipt.verdict.squared_work().is_none(), "an obstructed edit has no work at all");
    // The receipt's residual axis carries one bit per kept face the certificate is supported at,
    // so an obstructed edit is separated from a compensable one on the receipt as well.
    let obstructed_faces = match &receipt.verdict {
        EditVerdict::Obstructed { certificate } => certificate.support.len(),
        _ => 0,
    };
    assert!(obstructed_faces >= 1);
    assert_eq!(
        receipt.cost.count(Axis::Residual),
        &BigUint::from(obstructed_faces)
    );
}

/// **Commuting separates nothing in the linear chart.** Both edits commute — first-order
/// directions add — and one is free while the other is obstructed. This is T3's finding (2) again,
/// at first order, in its sharpest form: only the constraint entanglement separates them.
#[test]
fn first_order_edits_commute_so_commuting_separates_nothing() {
    let (_, _, kept) = six_slot_frame();
    let mut free_vector = vec![Rat::zero(); 12];
    free_vector[6] = integer(-4);
    free_vector[7] = integer(3);
    let mut frame_vector = vec![Rat::zero(); 12];
    frame_vector[10] = integer(1);

    let sum_one: Vec<Rat> = free_vector
        .iter()
        .zip(&frame_vector)
        .map(|(left, right)| left + right)
        .collect();
    let sum_two: Vec<Rat> = frame_vector
        .iter()
        .zip(&free_vector)
        .map(|(left, right)| left + right)
        .collect();
    assert_eq!(sum_one, sum_two, "first-order edits always commute");

    let free_edit = EditDirection::declared("dog->cat", free_vector).expect("the edit");
    let frame_edit = EditDirection::declared("is->why", frame_vector).expect("the edit");
    let allowed = AllowedCompensation::coordinates("name-slot-only", 12, [8, 9])
        .expect("the allowed subspace");
    let metric = unit_metric(12);
    let free = rethreading_work(&kept, &free_edit, &allowed, &metric).expect("free");
    let obstructed = rethreading_work(&kept, &frame_edit, &allowed, &metric).expect("obstructed");
    assert_eq!(free.verdict.arm(), "free");
    assert_eq!(obstructed.verdict.arm(), "obstructed");
}

// ---------------------------------------------------------------------------------------------
// (2b) entanglement is self-stress support
// ---------------------------------------------------------------------------------------------

/// A redundantly braced framework carries a self-stress, and exactly the faces in its support are
/// the entangled ones. Dropping one of them frees nothing; dropping a load-bearing one frees an
/// edit no other face forbids, and that edit is exhibited.
#[test]
fn entanglement_is_the_support_of_a_self_stress() {
    // Four occurrences of a square with **both** diagonals: one bar more than rigidity needs.
    let (_, placement) = placement_jacobian(
        "braced-square",
        2,
        &[(1, &[0, 0]), (2, &[4, 0]), (3, &[4, 4]), (4, &[0, 4])],
        &[(1, 2), (2, 3), (3, 4), (1, 4), (1, 3), (2, 4)],
    );
    let kept = KeptReceiverJacobian::from_rigidity(&placement).expect("the kept family");
    let reading = kept_reading(&kept).expect("the kept reading");
    assert_eq!(reading.self_stress_dimension, 1, "six bars on four points in the plane are one too many");
    assert!(!reading.entangled_faces.is_empty());
    assert_eq!(
        reading.entangled_faces.len() + reading.load_bearing_faces.len(),
        reading.face_count
    );

    // The dropped reading agrees with the self-stress support at every face.
    let checked = verify_entanglement_by_dropping(&kept, &reading, 16)
        .expect("the dropped reading agrees");
    assert_eq!(checked, reading.face_count);

    for face in &reading.entangled_faces {
        assert!(
            face_own_edit(&kept, *face).expect("the drop returns").is_none(),
            "an entangled face forbids no edit of its own"
        );
    }
    for face in &reading.load_bearing_faces {
        let own = face_own_edit(&kept, *face)
            .expect("the drop returns")
            .expect("a load-bearing face forbids an edit of its own");
        let image = kept.matrix().apply(&own).expect("the image");
        assert!(!image[*face].is_zero());
        for (at, entry) in image.iter().enumerate() {
            if at != *face {
                assert!(entry.is_zero(), "the edit is free at every other kept face");
            }
        }
    }
}

/// The entanglement cross-check refuses an empty bound by name rather than passing vacuously.
#[test]
fn the_entanglement_cross_check_refuses_an_empty_probe() {
    let (_, _, kept) = six_slot_frame();
    let reading = kept_reading(&kept).expect("the kept reading");
    assert!(matches!(
        verify_entanglement_by_dropping(&kept, &reading, 0),
        Err(EditRigidityRefusal::EmptyProbe { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// (3) the scalar is one receiver of the edit, never its identity
// ---------------------------------------------------------------------------------------------

/// The two-face chart the Pareto instance lives on: `ρ₁ = x₀ + x₁` and `ρ₂ = x₂ + 3x₄ + 4x₅`.
fn pareto_chart() -> KeptReceiverJacobian {
    KeptReceiverJacobian::from_linear_faces(
        "pareto-chart",
        6,
        vec![
            ("rho-one".to_owned(), row(&[1, 1, 0, 0, 0, 0])),
            ("rho-two".to_owned(), row(&[0, 0, 1, 0, 3, 4])),
        ],
    )
    .expect("the kept family")
}

fn pareto_edits() -> (EditDirection, AllowedCompensation, EditDirection, AllowedCompensation) {
    let left = EditDirection::declared("edit-A", row(&[1, 0, 0, 1, 0, 0])).expect("A");
    let left_allowed =
        AllowedCompensation::coordinates("A-may-move-x1", 6, [1]).expect("A's allowed subspace");
    let right = EditDirection::declared("edit-B", row(&[0, 0, 5, 0, 0, 0])).expect("B");
    let right_allowed = AllowedCompensation::coordinates("B-may-move-x4-x5", 6, [4, 5])
        .expect("B's allowed subspace");
    (left, left_allowed, right, right_allowed)
}

/// **Equal `W²`, different compensation support, Pareto-incomparable receipts.** The scalar
/// identifies the two edits; the receipt separates them and orders neither.
#[test]
fn two_edits_with_equal_squared_work_have_incomparable_receipts() {
    let kept = pareto_chart();
    let metric = unit_metric(6);
    let (left, left_allowed, right, right_allowed) = pareto_edits();
    let a = rethreading_work(&kept, &left, &left_allowed, &metric).expect("A");
    let b = rethreading_work(&kept, &right, &right_allowed, &metric).expect("B");

    assert_eq!(a.verdict.squared_work(), Some(&Rat::one()));
    assert_eq!(b.verdict.squared_work(), Some(&Rat::one()));
    assert_eq!(a.verdict.support(), BTreeSet::from([1]));
    assert_eq!(b.verdict.support(), BTreeSet::from([4, 5]));

    let comparison = compare_edits(&a, &b);
    assert!(comparison.equal_squared_work);
    assert!(!comparison.equal_support);
    assert!(
        comparison.incomparable_receipts,
        "A touches two coordinates and compensates with one; B touches one and compensates with \
         two, so neither receipt dominates"
    );
    assert_eq!(a.cost.count(Axis::Bytes), &BigUint::from(2u32));
    assert_eq!(b.cost.count(Axis::Bytes), &BigUint::from(1u32));
    assert_eq!(a.cost.count(Axis::UpdateWork), &BigUint::from(1u32));
    assert_eq!(b.cost.count(Axis::UpdateWork), &BigUint::from(2u32));
    assert_eq!(a.cost.count(Axis::DecodeWork), b.cost.count(Axis::DecodeWork));
    assert_eq!(
        a.cost.count(Axis::CertificateWork),
        b.cost.count(Axis::CertificateWork)
    );
}

/// **Changing the declared metric reorders the two edits.** Friction is a declared receiver, not a
/// fact about the artifact: under one positive-definite metric `A < B` and under another `A > B`,
/// with the same edits, the same kept faces and the same allowed subspaces.
#[test]
fn a_second_declared_metric_reorders_the_edits() {
    let kept = pareto_chart();
    let (left, left_allowed, right, right_allowed) = pareto_edits();
    let soft = ExactMetric::diagonal(
        "soft-at-x1",
        vec![
            Rat::one(),
            ratio(1, 4),
            Rat::one(),
            Rat::one(),
            Rat::one(),
            Rat::one(),
        ],
    )
    .expect("the soft metric is positive definite");
    let stiff = ExactMetric::diagonal(
        "stiff-at-x1",
        vec![
            Rat::one(),
            integer(4),
            Rat::one(),
            Rat::one(),
            Rat::one(),
            Rat::one(),
        ],
    )
    .expect("the stiff metric is positive definite");

    let soft_a = rethreading_work(&kept, &left, &left_allowed, &soft).expect("A soft");
    let soft_b = rethreading_work(&kept, &right, &right_allowed, &soft).expect("B soft");
    let stiff_a = rethreading_work(&kept, &left, &left_allowed, &stiff).expect("A stiff");
    let stiff_b = rethreading_work(&kept, &right, &right_allowed, &stiff).expect("B stiff");

    assert_eq!(soft_a.verdict.squared_work(), Some(&ratio(1, 4)));
    assert_eq!(soft_b.verdict.squared_work(), Some(&Rat::one()));
    assert_eq!(stiff_a.verdict.squared_work(), Some(&integer(4)));
    assert_eq!(stiff_b.verdict.squared_work(), Some(&Rat::one()));

    let soft_order = order_by_squared_work(&[soft_a, soft_b]);
    let stiff_order = order_by_squared_work(&[stiff_a, stiff_b]);
    assert_eq!(soft_order[0].0, "edit-A");
    assert_eq!(stiff_order[0].0, "edit-B");
}

/// A Gram matrix that is not positive definite is refused by name with the offending exact pivot,
/// and a non-symmetric one is refused before the factorization is attempted.
#[test]
fn a_metric_that_is_not_positive_definite_is_refused_by_name() {
    assert!(matches!(
        ExactMetric::diagonal("has-a-zero", vec![Rat::one(), Rat::zero()]),
        Err(EditRigidityRefusal::MetricNotPositiveDefinite { coordinate: 1, .. })
    ));
    assert!(matches!(
        ExactMetric::diagonal("has-a-negative", vec![integer(-1), Rat::one()]),
        Err(EditRigidityRefusal::MetricNotPositiveDefinite { coordinate: 0, .. })
    ));
    let asymmetric = ExactRatMatrix::shaped(2, 2, vec![row(&[2, 1]), row(&[0, 2])])
        .expect("the matrix shapes");
    assert!(matches!(
        ExactMetric::declared("asymmetric", asymmetric),
        Err(EditRigidityRefusal::MetricNotSymmetric { .. })
    ));
    // An indefinite symmetric matrix is refused at the pivot that fails, not at a rounding.
    let indefinite = ExactRatMatrix::shaped(2, 2, vec![row(&[1, 2]), row(&[2, 1])])
        .expect("the matrix shapes");
    assert!(matches!(
        ExactMetric::declared("indefinite", indefinite),
        Err(EditRigidityRefusal::MetricNotPositiveDefinite { coordinate: 1, .. })
    ));
}

/// A non-diagonal positive-definite Gram matrix is accepted with its exact `LDLᵀ` certificate, and
/// the certificate reconstructs it.
#[test]
fn a_declared_gram_matrix_carries_its_exact_ldl_certificate() {
    let gram = ExactRatMatrix::shaped(3, 3, vec![row(&[4, 2, 0]), row(&[2, 5, 1]), row(&[0, 1, 3])])
        .expect("the matrix shapes");
    let metric = ExactMetric::declared("coupled", gram.clone()).expect("it is positive definite");
    assert_eq!(metric.certificate().factor_rank, 3);
    assert!(metric.certificate().pivots.iter().all(|pivot| pivot > &Rat::zero()));
    // The certificate's own reconstruction is checked inside the constructor; here the metric is
    // exercised on an actual reading.
    let reading = metric
        .squared_norm(&row(&[1, 1, 1]))
        .expect("the metric reads");
    assert_eq!(reading, integer(4 + 2 + 2 + 5 + 1 + 1 + 3));
}

// ---------------------------------------------------------------------------------------------
// (4) edit torque
// ---------------------------------------------------------------------------------------------

fn torque_setup() -> (KeptReceiverJacobian, GeneratorFamily) {
    let kept = pareto_chart();
    let generators = GeneratorFamily::declared(
        "two-admitted-generators",
        6,
        vec![
            EditDirection::declared("g0", row(&[1, 0, 0, 0, 0, 0])).expect("g0"),
            EditDirection::declared("g1", row(&[0, 0, 1, 0, 0, 0])).expect("g1"),
        ],
    )
    .expect("the generator family");
    (kept, generators)
}

/// **`τ = J_gᵀ r`, exact.** The adjoint pulls the residual back to the generators, and the torque
/// vanishes exactly when the residual is orthogonal to the image of the generators.
#[test]
fn the_edit_torque_is_the_adjoint_pullback_of_the_residual() {
    let (kept, generators) = torque_setup();
    let edit_metric = unit_metric(2);
    let receiver_metric = unit_metric(2);

    let residual = ReceiverResidual::declared("unresolved", row(&[3, 5])).expect("the residual");
    let torque = edit_torque(&kept, &generators, &residual, &edit_metric, &receiver_metric)
        .expect("the torque returns");
    // `J_g` has columns `J g0 = (1,0)` and `J g1 = (0,1)`, so `τ = r`.
    assert_eq!(torque.values, row(&[3, 5]));
    assert!(!torque.is_zero);
    assert!(torque.bare_transpose_agrees, "both declared metrics are the identity here");
    assert_eq!(torque.adjoint_pairs_checked, 4);

    // A residual orthogonal to the image: the torque vanishes and no first-order edit moves it.
    let orthogonal = ReceiverResidual::declared("orthogonal", row(&[0, 0])).expect("the residual");
    let zero = edit_torque(&kept, &generators, &orthogonal, &edit_metric, &receiver_metric)
        .expect("the torque returns");
    assert!(zero.is_zero);
    assert!(matches!(
        descent_step(
            &kept,
            &generators,
            &orthogonal,
            &edit_metric,
            &receiver_metric,
            &zero
        ),
        Err(EditRigidityRefusal::NoDescentFromZeroTorque)
    ));
}

/// **The exact descent step.** A nonzero torque admits an exact rational step whose decrease is
/// recomputed rather than predicted, and the recomputation is what the constructor checks.
#[test]
fn a_nonzero_torque_admits_an_exact_rational_descent_step() {
    let (kept, generators) = torque_setup();
    let edit_metric = unit_metric(2);
    let receiver_metric = unit_metric(2);
    let residual = ReceiverResidual::declared("unresolved", row(&[3, 5])).expect("the residual");
    let torque = edit_torque(&kept, &generators, &residual, &edit_metric, &receiver_metric)
        .expect("the torque returns");
    let descent = descent_step(
        &kept,
        &generators,
        &residual,
        &edit_metric,
        &receiver_metric,
        &torque,
    )
    .expect("the descent returns");
    // `J_g` is the identity here, so the step is one and the residual is driven to zero exactly.
    assert_eq!(descent.step, Rat::one());
    assert_eq!(descent.before, integer(34));
    assert_eq!(descent.decrease, integer(34));
    assert!(descent.after.is_zero());
}

/// **The adjoint uses the morphology that produced the forward carriers.** Under a declared
/// non-identity metric the bare transpose is *not* the adjoint, and the value carries the
/// difference rather than hiding it.
#[test]
fn the_bare_transpose_is_not_the_adjoint_under_a_declared_metric() {
    let (kept, generators) = torque_setup();
    let edit_metric = ExactMetric::diagonal("stiff-first-generator", vec![integer(4), Rat::one()])
        .expect("the edit metric");
    let receiver_metric = unit_metric(2);
    let residual = ReceiverResidual::declared("unresolved", row(&[3, 5])).expect("the residual");
    let torque = edit_torque(&kept, &generators, &residual, &edit_metric, &receiver_metric)
        .expect("the torque returns");
    assert!(!torque.bare_transpose_agrees);
    assert_eq!(torque.values, vec![ratio(3, 4), integer(5)]);
    assert_eq!(torque.bare_transpose, row(&[3, 5]));
    // The descent step under the declared metric is the one the metric names, not the Euclidean one.
    let descent = descent_step(
        &kept,
        &generators,
        &residual,
        &edit_metric,
        &receiver_metric,
        &torque,
    )
    .expect("the descent returns");
    assert_eq!(descent.before, integer(34));
    assert!(descent.after < descent.before);
    assert_eq!(&descent.before - &descent.decrease, descent.after);
}

/// **A vanishing torque is not cancellation.** At a kept face whose Jacobian row vanishes — two
/// occurrences at coincident places, `rigidity_receiver`'s own `coincident_constraints` — every
/// torque is zero for every residual, and yet the second-order edit moves the face by exactly `t²`.
/// First-order stationarity is necessary and not sufficient.
#[test]
fn a_vanishing_torque_is_not_cancellation() {
    let (configuration, placement) = placement_jacobian(
        "coincident-pair",
        2,
        &[(1, &[0, 0]), (2, &[0, 0])],
        &[(1, 2)],
    );
    assert_eq!(placement.coincident_constraints.len(), 1);
    let kept = KeptReceiverJacobian::from_rigidity(&placement).expect("the kept family");
    let generators = GeneratorFamily::declared(
        "separate-the-pair",
        4,
        vec![EditDirection::declared("separate", row(&[1, 0, 0, 0])).expect("the generator")],
    )
    .expect("the generator family");
    let metric_one = unit_metric(1);
    for value in [1_i64, -7, 1_000] {
        let residual =
            ReceiverResidual::declared("anything", vec![integer(value)]).expect("the residual");
        let torque = edit_torque(&kept, &generators, &residual, &metric_one, &metric_one)
            .expect("the torque returns");
        assert!(torque.is_zero, "a vanishing row gives a vanishing torque for every residual");
    }
    // And the second-order edit changes the kept face exactly.
    let places = configuration.ordered_places();
    let before = (0..2)
        .map(|axis| {
            let difference = &places[0][axis] - &places[1][axis];
            &difference * &difference
        })
        .fold(Rat::zero(), |sum, entry| sum + entry);
    assert!(before.is_zero());
    let step = integer(3);
    let moved = [&places[0][0] + &step, places[0][1].clone()];
    let after = (0..2)
        .map(|axis| {
            let difference = &moved[axis] - &places[1][axis];
            &difference * &difference
        })
        .fold(Rat::zero(), |sum, entry| sum + entry);
    assert_eq!(after, integer(9), "the face moves by exactly t^2 at second order");
}

// ---------------------------------------------------------------------------------------------
// (5) the knot
// ---------------------------------------------------------------------------------------------

/// **The knot's nesting direction.** Three occurrences on a line with the two consecutive
/// separations kept: the outer pair is held by the whole region's induced faces and by **nothing**
/// inside the subregion carrying only its two endpoints. So induced implication ascends under
/// coarsening and does not descend.
#[test]
fn the_induced_implication_does_not_descend() {
    let (configuration, placement) =
        placement_jacobian("line-chain", 1, &[(0, &[0]), (1, &[1]), (2, &[2])], &[(0, 1), (1, 2)]);
    let kept = KeptReceiverJacobian::from_rigidity(&placement).expect("the kept family");
    let places = configuration.ordered_places();
    let pair = pair_row(&places, 1, 0, 2).expect("the virtual pair row");
    assert_eq!(pair, row(&[-4, 0, 4]));

    let whole = BTreeSet::from([0usize, 1, 2]);
    let outer = BTreeSet::from([0usize, 2]);
    assert!(
        pair_is_implied_at(&kept, &whole, &pair).expect("the region reading"),
        "the outer pair is held by the region's own faces"
    );
    assert!(
        !pair_is_implied_at(&kept, &outer, &pair).expect("the subregion reading"),
        "the subregion induces no face at all and holds nothing"
    );

    // The ascending direction, checked on the actual data.
    let ascent = knot_ascent(&kept, &[outer.clone(), whole.clone()]).expect("the ascent returns");
    assert_eq!(ascent.pairs_checked, 1);
    assert!(ascent.ascends);
    assert!(ascent.failure.is_none());
}

/// The knot reading at a declared word/sentence/breath ladder: a self-stress dimension per scale.
#[test]
fn the_knot_reading_returns_a_self_stress_dimension_per_scale() {
    let (_, placement) = placement_jacobian(
        "braced-square",
        2,
        &[(1, &[0, 0]), (2, &[4, 0]), (3, &[4, 4]), (4, &[0, 4])],
        &[(1, 2), (2, 3), (3, 4), (1, 4), (1, 3), (2, 4)],
    );
    let kept = KeptReceiverJacobian::from_rigidity(&placement).expect("the kept family");
    let reading = rigidity_reading(&placement).expect("the rigidity reading");
    let ladder = RegionLadder::declared(
        "word-sentence-breath",
        8,
        vec![
            (
                "word".to_owned(),
                vec![
                    BTreeSet::from([0usize, 1]),
                    BTreeSet::from([2usize, 3]),
                    BTreeSet::from([4usize, 5]),
                    BTreeSet::from([6usize, 7]),
                ],
            ),
            (
                "sentence".to_owned(),
                vec![BTreeSet::from([0usize, 1, 2, 3]), BTreeSet::from([4usize, 5, 6, 7])],
            ),
            ("breath".to_owned(), vec![(0usize..8).collect()]),
        ],
    )
    .expect("the ladder is declared");

    let knots = artifact_knots(&placement, &reading, &kept, &ladder, 4096).expect("the knots");
    assert_eq!(knots.self_stress_dimension, 1);
    assert_eq!(knots.scales.len(), 7);
    // A single occurrence's word region induces no kept face: a knot needs at least a pair.
    let word = knots.scales.iter().find(|scale| scale.scale == "word").expect("a word region");
    assert!(word.induced_faces.is_empty());
    assert_eq!(word.self_stress_dimension, 0);
    // The breath region induces every face and carries the whole self-stress.
    let breath = knots
        .scales
        .iter()
        .find(|scale| scale.scale == "breath")
        .expect("the breath region");
    assert_eq!(breath.induced_faces.len(), 6);
    assert_eq!(breath.self_stress_dimension, 1);
    assert!(!breath.redundant_faces.is_empty());
    // The cluster reading is R4's own and is not recomputed here.
    assert!(!knots.clusters.clusters.is_empty());
}

/// The ladder and the ascent check both refuse an empty declaration by name.
#[test]
fn an_empty_ladder_and_an_empty_ascent_probe_are_refused_by_name() {
    assert!(matches!(
        RegionLadder::declared("empty", 4, vec![]),
        Err(EditRigidityRefusal::EmptyLadder)
    ));
    assert!(matches!(
        RegionLadder::declared("empty-scale", 4, vec![("word".to_owned(), vec![])]),
        Err(EditRigidityRefusal::EmptyScale { .. })
    ));
    let kept = pareto_chart();
    assert!(matches!(
        knot_ascent(&kept, &[]),
        Err(EditRigidityRefusal::EmptyProbe { .. })
    ));
    // Regions that contain none of each other check nothing, which is refused rather than reported
    // as an ascent that held.
    assert!(matches!(
        knot_ascent(&kept, &[BTreeSet::from([0usize]), BTreeSet::from([1usize])]),
        Err(EditRigidityRefusal::EmptyProbe { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// the plural reading over an Open kept face
// ---------------------------------------------------------------------------------------------

/// **An `Open` kept face makes the verdict plural, and both bounds are carried.** The refusing
/// bound admits an edit the admitting bound obstructs; neither is promoted.
#[test]
fn an_open_kept_face_returns_both_bounds_and_resolves_neither() {
    let refusing = KeptReceiverJacobian::from_linear_faces(
        "open-refusing",
        3,
        vec![("kept".to_owned(), row(&[1, 1, 0]))],
    )
    .expect("the refusing bound");
    let open = KeptReceiverJacobian::from_linear_faces(
        "open-face",
        3,
        vec![("open".to_owned(), row(&[0, 0, 1]))],
    )
    .expect("the open face");
    let admitting = refusing.joined(&open).expect("the admitting bound");

    let edit = EditDirection::declared("touches-the-open-face", row(&[1, 0, 1])).expect("the edit");
    let allowed = AllowedCompensation::coordinates("only-x1", 3, [1]).expect("the allowed subspace");
    let metric = unit_metric(3);
    let plural = plural_rethreading(&refusing, &admitting, &edit, &allowed, &metric)
        .expect("the plural reading returns");
    assert_eq!(plural.refusing.verdict.arm(), "compensable");
    assert_eq!(plural.admitting.verdict.arm(), "obstructed");
    assert!(plural.arms_differ, "the open class is an edit question, not bookkeeping");
    assert!(plural.work_differs);

    // The other side of the same field: a determinate family — the two bounds coinciding — reads
    // the same arm and the same work, so `arms_differ` is content and not a standing claim.
    let determinate = plural_rethreading(&refusing, &refusing, &edit, &allowed, &metric)
        .expect("the plural reading returns");
    assert!(!determinate.arms_differ);
    assert!(!determinate.work_differs);
}

// ---------------------------------------------------------------------------------------------
// hostile declarations
// ---------------------------------------------------------------------------------------------

/// Every caller-declared extent is bounded before the work it sizes, and a width disagreement is a
/// typed refusal rather than a panic.
#[test]
fn hostile_declarations_are_refused_before_they_allocate() {
    assert!(matches!(
        KeptReceiverJacobian::from_linear_faces("too-wide", CHART_CEILING + 1, vec![]),
        Err(EditRigidityRefusal::DeclarationAboveCeiling { .. })
    ));
    assert!(matches!(
        KeptReceiverJacobian::from_linear_faces("empty", 0, vec![]),
        Err(EditRigidityRefusal::EmptyChart)
    ));
    assert!(matches!(
        KeptReceiverJacobian::from_linear_faces("no-face", 3, vec![]),
        Err(EditRigidityRefusal::EmptyKeptFamily)
    ));
    assert!(matches!(
        KeptReceiverJacobian::from_linear_faces(
            "ragged",
            3,
            vec![("short".to_owned(), row(&[1, 1]))]
        ),
        Err(EditRigidityRefusal::WidthDisagrees { .. })
    ));
    assert!(matches!(
        AllowedCompensation::coordinates("outside", 3, [7]),
        Err(EditRigidityRefusal::CoordinateOutsideChart { coordinate: 7, dimension: 3 })
    ));
    assert!(matches!(
        GeneratorFamily::declared("empty", 3, vec![]),
        Err(EditRigidityRefusal::EmptyProbe { .. })
    ));
    assert!(matches!(
        ReceiverResidual::declared("empty", vec![]),
        Err(EditRigidityRefusal::EmptyProbe { .. })
    ));
    let kept = pareto_chart();
    let edit = EditDirection::declared("wrong-width", row(&[1, 1])).expect("the edit");
    let allowed = AllowedCompensation::coordinates("ok", 6, [1]).expect("the allowed subspace");
    assert!(matches!(
        rethreading_work(&kept, &edit, &allowed, &unit_metric(6)),
        Err(EditRigidityRefusal::WidthDisagrees { .. })
    ));
    let wide = EditDirection::declared("ok", row(&[1, 0, 0, 0, 0, 0])).expect("the edit");
    assert!(matches!(
        rethreading_work(&kept, &wide, &allowed, &unit_metric(5)),
        Err(EditRigidityRefusal::WidthDisagrees { .. })
    ));
    assert!(matches!(
        face_own_edit(&kept, 9),
        Err(EditRigidityRefusal::FaceOutsideFamily { face: 9, faces: 2 })
    ));
    // A caller's coordinate iterator is walked under its own ceiling, so an endless one is refused
    // rather than followed.
    assert!(matches!(
        AllowedCompensation::coordinates("endless", 6, std::iter::repeat_n(0, CHART_CEILING + 1)),
        Err(EditRigidityRefusal::DeclarationAboveCeiling {
            what: "an allowed-coordinate declaration",
            ..
        })
    ));
    // A declared metric's cubic factorization is bounded before a pivot is formed.
    assert!(matches!(
        ExactMetric::unit("too-wide-to-factor", 1024),
        Err(EditRigidityRefusal::DeclarationAboveCeiling {
            what: "a declared metric factorization",
            ..
        })
    ));
}

/// A torque that is not this residual's own adjoint pullback is refused rather than stepped along.
#[test]
fn a_descent_step_refuses_a_torque_from_elsewhere() {
    let (kept, generators) = torque_setup();
    let metric = unit_metric(2);
    let residual = ReceiverResidual::declared("unresolved", row(&[3, 5])).expect("the residual");
    let mut torque = edit_torque(&kept, &generators, &residual, &metric, &metric)
        .expect("the torque returns");
    torque.values = row(&[1, 0]);
    assert!(matches!(
        descent_step(&kept, &generators, &residual, &metric, &metric, &torque),
        Err(EditRigidityRefusal::CertificateFails { .. })
    ));
}

/// The receipts serialize; nothing in this module carries a float on its wire.
#[test]
fn the_receipt_serializes_with_its_name_and_schema() {
    let kept = pareto_chart();
    let (left, left_allowed, _, _) = pareto_edits();
    let receipt = rethreading_work(&kept, &left, &left_allowed, &unit_metric(6)).expect("A");
    let wire = serde_json::to_string(&receipt).expect("the receipt serializes");
    assert!(wire.contains("edit-A"));
    assert!(wire.contains(RETHREADING_SCHEMA));
    assert_eq!(receipt.normal_equation_directions_checked, 0);
}

// ---------------------------------------------------------------------------------------------
// the measured M5 contact framework
// ---------------------------------------------------------------------------------------------

/// **The pinned measured reading of one deposit.**
///
/// [measured] Every field was measured on the authenticated release at the declared eight angstrom
/// aperture over the first `WINDOW` residues of the RBX1 chain; a change in any of them is a change
/// in the deposit or in the reading, and either is worth failing for.
struct PinnedReading {
    file: &'static str,
    faces: usize,
    rank: usize,
    free: usize,
    self_stress: usize,
    entangled: usize,
    one_shell: usize,
    one_shell_arm: &'static str,
    two_shell: usize,
    two_shell_arm: &'static str,
    wide_arm: &'static str,
    support: usize,
}

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
/// The RBX1 chain is the one component present in all three presentations.
const RBX1_RESIDUES: usize = 108;
/// The residue window the edit reading is taken on, declared here rather than inferred.
const WINDOW: usize = 24;
/// Eight angstroms, squared, on the exact decimal wire the deposit carries.
const CONTACT_SQUARED: i64 = 64;
/// The residue the edit displaces.
const EDITED_RESIDUE: usize = 12;

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
    for record in rows {
        if record[atom] != "CA" {
            continue;
        }
        let mut point = Vec::with_capacity(3);
        for axis in [x, y, z] {
            point.push(exact_decimal(record[axis])?);
        }
        chains.entry(record[chain].to_owned()).or_default().push(point);
    }
    Ok(chains)
}

fn squared_distance(left: &[Rat], right: &[Rat]) -> Rat {
    left.iter().zip(right).fold(Rat::zero(), |sum, (a, b)| {
        let difference = a - b;
        sum + &difference * &difference
    })
}

struct M5Window {
    jacobian: RigidityJacobian,
    kept: KeptReceiverJacobian,
    /// The contact adjacency of the window, one entry per residue.
    adjacency: Vec<BTreeSet<usize>>,
}

impl M5Window {
    /// The residues within `radius` contacts of the edited one, excluding it.
    fn shell(&self, radius: usize) -> BTreeSet<usize> {
        let mut reached = BTreeSet::from([EDITED_RESIDUE]);
        let mut frontier = BTreeSet::from([EDITED_RESIDUE]);
        for _ in 0..radius {
            let mut next = BTreeSet::new();
            for residue in &frontier {
                for neighbour in &self.adjacency[*residue] {
                    if reached.insert(*neighbour) {
                        next.insert(*neighbour);
                    }
                }
            }
            frontier = next;
        }
        reached.remove(&EDITED_RESIDUE);
        reached
    }

    /// Every residue but the edited one.
    fn everything_else(&self) -> BTreeSet<usize> {
        (0..WINDOW).filter(|residue| *residue != EDITED_RESIDUE).collect()
    }
}

fn m5_window(lineage: &'static str, path: &Path) -> Result<M5Window, String> {
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
    let mut adjacency = vec![BTreeSet::new(); WINDOW];
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
            adjacency[left].insert(right);
            adjacency[right].insert(left);
        }
    }
    let jacobian = RigidityJacobian::found(lineage, &configuration, &constraints)
        .map_err(|error| error.to_string())?;
    let kept = KeptReceiverJacobian::from_rigidity(&jacobian).map_err(|error| error.to_string())?;
    Ok(M5Window {
        jacobian,
        kept,
        adjacency,
    })
}

/// **The measured return on the authenticated M5 release.**
///
/// [measured] The RBX1 window's contact framework is the kept receiver family; the edit displaces
/// one residue along `x`; the allowed compensation is exactly that residue's contact neighbours.
/// Absent the release this test refuses. Every law is checked without any fixture by the synthetic
/// tests above, so nothing here is the only check of anything. It is `#[ignore]`d because the three
/// deposits are large; run it with `--ignored`.
#[test]
#[ignore = "reads the authenticated M5 deposit; the laws are checked without a fixture above"]
fn the_edit_receiver_measures_the_m5_contact_framework() {
    let root = std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT));
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the measured edit reading cannot be \
         taken, and this test refuses to report success without taking it. Place the authenticated \
         release at that path, or set {STRUCTURE_ROOT_ENV} to the directory carrying \
         designed-free-rbx1.cif, ptxv2-free-rbx1-seed2.cif and ptxv2-cul1-rbx1-seed0.cif.",
        root.display()
    );

    const PINNED: [PinnedReading; 3] = [
        PinnedReading {
            file: "designed-free-rbx1.cif",
            faces: 70,
            rank: 62,
            free: 10,
            self_stress: 8,
            entangled: 53,
            one_shell: 7,
            one_shell_arm: "obstructed",
            two_shell: 13,
            two_shell_arm: "obstructed",
            wide_arm: "compensable",
            support: 69,
        },
        PinnedReading {
            file: "ptxv2-free-rbx1-seed2.cif",
            faces: 59,
            rank: 53,
            free: 19,
            self_stress: 6,
            entangled: 30,
            one_shell: 4,
            one_shell_arm: "obstructed",
            two_shell: 10,
            two_shell_arm: "obstructed",
            wide_arm: "compensable",
            support: 69,
        },
        PinnedReading {
            file: "ptxv2-cul1-rbx1-seed0.cif",
            faces: 50,
            rank: 50,
            free: 22,
            self_stress: 0,
            entangled: 0,
            one_shell: 5,
            one_shell_arm: "obstructed",
            two_shell: 9,
            two_shell_arm: "compensable",
            wide_arm: "compensable",
            support: 69,
        },
    ];

    let structures = [
        ("designed-free", "designed-free-rbx1.cif"),
        ("protenix-free-seed2", "ptxv2-free-rbx1-seed2.cif"),
        ("protenix-cul1-seed0", "ptxv2-cul1-rbx1-seed0.cif"),
    ];
    for (lineage, file) in structures {
        let pinned = PINNED
            .iter()
            .find(|entry| entry.file == file)
            .expect("every measured deposit carries a pinned reading");
        let measured =
            m5_window(lineage, &root.join(file)).unwrap_or_else(|error| panic!("{lineage}: {error}"));
        let reading = kept_reading(&measured.kept).expect("the kept reading");
        let rigidity = rigidity_reading(&measured.jacobian).expect("the rigidity reading");
        identify_with_rigidity_reading(&reading, &rigidity)
            .expect("the kept family is rigidity_receiver's own object");
        assert_eq!(reading.dimension, 3 * WINDOW);
        assert!(reading.free_dimension >= 6, "the six rigid motions are always free");
        assert_eq!(reading.face_count, pinned.faces, "{lineage}: kept faces");
        assert_eq!(reading.rank, pinned.rank, "{lineage}: rank");
        assert_eq!(reading.free_dimension, pinned.free, "{lineage}: free dimension");
        assert_eq!(reading.self_stress_dimension, pinned.self_stress, "{lineage}: self-stress dimension");
        assert_eq!(reading.entangled_faces.len(), pinned.entangled, "{lineage}: entangled faces");

        // The edit: displace one residue along `x` by one exact unit.
        let mut vector = vec![Rat::zero(); 3 * WINDOW];
        vector[EDITED_RESIDUE * 3] = Rat::one();
        let edit = EditDirection::declared("displace-one-residue", vector).expect("the edit");

        let one_shell = measured.shell(1);
        let two_shell = measured.shell(2);
        let everything = measured.everything_else();
        assert!(
            !one_shell.is_empty(),
            "the edited residue has at least its backbone neighbours"
        );
        assert!(one_shell.is_subset(&two_shell));
        assert!(two_shell.is_subset(&everything));
        assert_eq!(one_shell.len(), pinned.one_shell, "{lineage}: first contact shell");
        assert_eq!(two_shell.len(), pinned.two_shell, "{lineage}: second contact shell");

        let unit = ExactMetric::unit("declared-unit", 3 * WINDOW).expect("the unit metric");
        // A second declared metric: every residue of the first contact shell four times as stiff.
        let weights = (0..3 * WINDOW)
            .map(|coordinate| {
                if one_shell.contains(&(coordinate / 3)) {
                    integer(4)
                } else {
                    Rat::one()
                }
            })
            .collect::<Vec<_>>();
        let stiff = ExactMetric::diagonal("stiff-first-shell", weights).expect("the stiff metric");

        let allowed_of = |name: &'static str, residues: &BTreeSet<usize>| {
            AllowedCompensation::coordinates(
                name,
                3 * WINDOW,
                residues
                    .iter()
                    .flat_map(|residue| (0..3).map(move |axis| residue * 3 + axis))
                    .collect::<Vec<_>>(),
            )
            .expect("the allowed subspace")
        };

        // **The first contact shell is not enough.** Displacing a contacted residue breaks faces
        // its neighbours share with residues outside the shell, so the compensating family is
        // empty and the return is the checked left-null certificate.
        let near = allowed_of("the first contact shell may move", &one_shell);
        let near_receipt =
            rethreading_work(&measured.kept, &edit, &near, &unit).expect("the near reading");
        match &near_receipt.verdict {
            EditVerdict::Obstructed { certificate } => {
                assert!(!certificate.pairing.is_zero());
                assert!(!certificate.support.is_empty());
            }
            other => panic!("{lineage}: the one-shell reading is obstructed, not {}", other.arm()),
        }
        assert_eq!(near_receipt.verdict.arm(), pinned.one_shell_arm, "{lineage}: one-shell arm");

        // Widening the allowed region until the edit can be carried is the rethreading itself.
        let wide = allowed_of("everything but the edited residue may move", &everything);
        let wide_unit =
            rethreading_work(&measured.kept, &edit, &wide, &unit).expect("the wide unit reading");
        let wide_stiff =
            rethreading_work(&measured.kept, &edit, &wide, &stiff).expect("the wide stiff reading");
        assert_eq!(wide_unit.verdict.arm(), wide_stiff.verdict.arm());
        assert_eq!(wide_unit.verdict.arm(), pinned.wide_arm, "{lineage}: all-but-one arm");
        assert_eq!(
            wide_unit.verdict.support().len(),
            pinned.support,
            "{lineage}: the rethreading propagates through the whole window"
        );

        let two = allowed_of("the first two contact shells may move", &two_shell);
        let two_receipt =
            rethreading_work(&measured.kept, &edit, &two, &unit).expect("the two-shell reading");
        assert_eq!(two_receipt.verdict.arm(), pinned.two_shell_arm, "{lineage}: two-shell arm");

        let unit_work = wide_unit.verdict.squared_work().cloned();
        let stiff_work = wide_stiff.verdict.squared_work().cloned();
        if let (Some(unit_work), Some(stiff_work)) = (&unit_work, &stiff_work) {
            assert!(
                unit_work > &Rat::zero(),
                "displacing a contacted residue is never free"
            );
            assert!(
                stiff_work >= unit_work,
                "weighting allowed coordinates up cannot lower the minimum"
            );
            let support = wide_unit.verdict.support();
            for coordinate in &support {
                assert!(
                    coordinate / 3 != EDITED_RESIDUE,
                    "the compensation never moves the residue the edit moved"
                );
            }
            assert!(
                !support.is_empty(),
                "a compensable edit that is not free moves something"
            );
        }

        println!(
            "edit_rigidity M5 | {lineage} | coordinates {} | kept faces {} | rank {} | free {} | \
             self-stress {} | entangled faces {} | load-bearing faces {} | one-shell {} residues \
             -> {} | two-shell {} residues -> {} | all-but-one {} residues -> {} | \
             compensation support {} | W^2 unit {} | W^2 stiff first shell {}",
            reading.dimension,
            reading.face_count,
            reading.rank,
            reading.free_dimension,
            reading.self_stress_dimension,
            reading.entangled_faces.len(),
            reading.load_bearing_faces.len(),
            one_shell.len(),
            near_receipt.verdict.arm(),
            two_shell.len(),
            two_receipt.verdict.arm(),
            everything.len(),
            wide_unit.verdict.arm(),
            wide_unit.verdict.support().len(),
            unit_work.as_ref().map_or_else(
                || "none".to_owned(),
                |work| format!("{}/{}", work.numer(), work.denom())
            ),
            stiff_work.as_ref().map_or_else(
                || "none".to_owned(),
                |work| format!("{}/{}", work.numer(), work.denom())
            ),
        );
    }
}

/// **A region with no coordinate is refused by name.** It induces no framework, and read through
/// it every kept face is a zero row: a self-stress dimension with no redundant face behind it.
#[test]
fn a_ladder_region_with_no_coordinate_is_refused_by_name() {
    assert!(matches!(
        RegionLadder::declared(
            "empty-region",
            4,
            vec![("word".to_owned(), vec![BTreeSet::new()])]
        ),
        Err(EditRigidityRefusal::EmptyRegion { .. })
    ));
}

/// **A repeated pass is bounded as a product, before the first pass.** Each factor sits inside its
/// own ceiling — 1,024 regions, 300 faces, 1,000 coordinates — and their product does not. The old
/// code bounded the region family's square and then scanned the chart once per region.
#[test]
fn a_repeated_pass_past_its_product_ceiling_is_refused_before_it_runs() {
    let dimension = 1_000;
    let faces = (0..300)
        .map(|face| {
            let mut row = vec![Rat::zero(); dimension];
            row[face] = Rat::one();
            (format!("face-{face}"), row)
        })
        .collect();
    let kept = KeptReceiverJacobian::from_linear_faces("wide", dimension, faces).expect("declared");
    let regions: Vec<BTreeSet<usize>> = (0..1_024).map(|at| BTreeSet::from([at % dimension])).collect();
    assert!(matches!(
        knot_ascent(&kept, &regions),
        Err(EditRigidityRefusal::DeclarationAboveCeiling { .. })
    ));
    let ladder = RegionLadder::declared("wide", dimension, vec![("word".to_owned(), regions)])
        .expect("each factor is inside its own ceiling");
    assert!(matches!(
        scale_knot_readings(&kept, &ladder),
        Err(EditRigidityRefusal::DeclarationAboveCeiling { .. })
    ));
}

/// **No float carries or decides anything in this owner.** A real scan of the sources: comment
/// lines are excluded because the header names the forbidden words in the sentence forbidding
/// them, the tokens are assembled at run time so this test does not contain them, and the scanned
/// line count is asserted so the scan cannot pass by covering nothing.
#[test]
fn no_float_token_occurs_in_this_owners_sources() {
    let banned: Vec<String> = [32u8, 64u8]
        .iter()
        .map(|width| format!("{}{width}", 'f'))
        .collect();
    for (name, source) in [
        ("edit_rigidity.rs", include_str!("../edit_rigidity.rs")),
        ("edit_rigidity/tests.rs", include_str!("tests.rs")),
    ] {
        let mut scanned = 0usize;
        for line in source.lines() {
            if line.trim_start().starts_with("//") {
                continue;
            }
            scanned += 1;
            for forbidden in &banned {
                assert!(
                    !line.contains(forbidden.as_str()),
                    "{name} line `{line}` names `{forbidden}`"
                );
            }
        }
        assert!(scanned > 200, "{name}: the scan covered only {scanned} lines");
    }
}
