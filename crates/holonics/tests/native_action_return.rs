//! Native interface law controls, not a trained task or a scientific holdout.
//!
//! The fixed identity R below is a declared observer in this mechanics fixture. Actual
//! observations come only from the coupled Holon's executed states. No expected class
//! or request is installed as a teacher, and no acquired task relation is asserted.

use holonics::compression::landmark::context::{BaseMeasure, StopPrior};
use holonics::geometry::{RatVec3, screw::ScrewGenerator};
use holonics::hnn::constitution::CAMPAIGN_ONE_BUDGET;
use holonics::hnn::field::{
    ContactDeclaration, CribDeclaration, FieldMaterial, ReceiverDeclaration,
};
use holonics::hnn::physical::PhysicalReceiver;
use holonics::hnn::physical::action::{ActionCommunication, BoundJointWorld};
use holonics::hnn::ratio::{Face, Faces, ReceivingFaceRatio};
use holonics::hnn::receiving::ReceivingRead;
use holonics::hnn::ring::ResonatorMaterial;
use holonics::hnn::word::action::PortPreparation;
use holonics::hnn::{
    Constitution, Current, Encoded, Field, FieldDeclaration, RingDeclaration, WordOpening,
};
use holonics::holarchy::terrain::KnownTruth;
use holonics::holon::law::{ReferenceHolon, Scheme};
use holonics::holon::{Holon, HolonState, PortHolon};
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::linear::inertia::SymmetricForm;
use holonics::ratio::{Rat, integer, rat};
use holonics::receiver::receipt::{ReceiptLaw, RegionChart};
use holonics::receiver::reception::{JointLaw, ReceiverFace};
use num_bigint::BigInt;
use num_traits::Zero;

fn fixture() -> (Field, Constitution, Encoded) {
    let ring = |source| RingDeclaration {
        period: 2,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..2)
            .map(|node| FieldDeclaration::quarter_turn(node, 2))
            .collect(),
        lock: if source { vec![0, 1] } else { vec![] },
        reflector: vec![0, 1],
        admittance: integer(2),
        initial: 0,
    };
    let field = Field::declare(
        FieldDeclaration {
            rings: vec![ring(true), ring(false)],
            contacts: vec![ContactDeclaration {
                from: 0,
                to: 1,
                channel: vec![(0, 0), (1, 1)],
                admittance: integer(2),
                exponent: integer(0),
            }],
            loops: vec![],
            sources: vec![0],
            offsets: vec![],
            alphabet: 2,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 1,
                aperture: 2,
                tolerance: rat(1, 16),
                depth: 2,
                prior: StopPrior::half(),
                mass: 1,
                base: BaseMeasure::Even,
                receiving_prior: 0,
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap();
    let mut theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET)
        .unwrap()
        .with_ports(1, None, None, Some(ExactRatMatrix::identity(4).unwrap()))
        .unwrap();
    // The source is terminated by the actual World; only the receiving ring is loaded.
    for g in [1] {
        theta = theta
            .with_ring_resonator(
                &field,
                g,
                ResonatorMaterial::new(
                    ExactRatMatrix::identity(4).unwrap(),
                    ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 8)),
                    ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 16)),
                    None,
                )
                .unwrap(),
            )
            .unwrap();
    }
    let truth = KnownTruth::uniform(2, 0, 1, 1).unwrap();
    let source = Encoded::identity(&truth, &field).unwrap().remove(0);
    (field, theta, source)
}

fn bound_world(field: &Field, chart: Encoded, native_origin: usize) -> BoundJointWorld {
    bound_world_with_history(field, chart, native_origin, None)
}

// Independent mechanical fixtures, not branches/replays of an active participating World.
// Each history is produced by one actual JointLaw interaction at the same earlier clock.
fn bound_world_with_history(
    field: &Field,
    chart: Encoded,
    native_origin: usize,
    prior_effort: Option<&[Rat]>,
) -> BoundJointWorld {
    // Two four-coordinate participants share the native skew gyrator. The input acts
    // at the four source ports; the receiving face reads the actual second participant.
    // Every state coordinate declares the native log-amplitude/phase-lift units.
    let n = 4;
    let structure = ExactRatMatrix::new(
        (0..2 * n)
            .map(|i| {
                (0..2 * n)
                    .map(|j| {
                        if i < n && j == n + i {
                            -integer(1)
                        } else if i >= n && j == i - n {
                            integer(1)
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .unwrap();
    let input = ExactRatMatrix::new(
        (0..2 * n)
            .map(|i| {
                (0..n)
                    .map(|j| if i == j { integer(1) } else { Rat::zero() })
                    .collect()
            })
            .collect(),
    )
    .unwrap();
    let holon = Holon::new(
        PortHolon::medium(
            &structure,
            &ExactRatMatrix::zero(8, 8).unwrap(),
            SymmetricForm::from_rows(
                (0..8)
                    .map(|i| {
                        (0..8)
                            .map(|j| if i == j { integer(1) } else { Rat::zero() })
                            .collect()
                    })
                    .collect(),
            )
            .unwrap(),
            &input,
            false,
        )
        .unwrap(),
    )
    .unwrap();
    let law = JointLaw::new(
        ReferenceHolon::new(holon, field.step().clone(), Scheme::Midpoint).unwrap(),
        n,
    )
    .unwrap();
    let mut initial = vec![Rat::zero(); 8];
    initial[0] = integer(1);
    let readers = (0..8)
        .map(|i| {
            (0..8)
                .map(|j| if i == j { integer(1) } else { Rat::zero() })
                .collect()
        })
        .collect();
    let receipt = ReceiptLaw::new(
        8,
        readers,
        vec![RegionChart::new(integer(1), field.step().clone(), 0).unwrap(); 8],
    )
    .unwrap();
    let face = ReceiverFace::receiver_state(4, 4).unwrap();
    let state = match prior_effort {
        None => HolonState::at(initial, 0),
        Some(input) => law
            .interact(&HolonState::at(initial, 0), input, &face, &receipt)
            .unwrap()
            .forward
            .into_present()
            .unwrap()
            .next_state(),
    };
    BoundJointWorld::new(
        law,
        state,
        face,
        receipt,
        vec![integer(2); 4],
        chart,
        native_origin,
    )
    .unwrap()
}

#[test]
fn paired_actual_faces_keep_mass_phase_and_unobserved_regions() {
    let p = ReceivingRead::of_logits(vec![integer(0); 4], 1);
    let q = Face::of_read(
        &ReceivingRead::of_logits(vec![integer(1), integer(1), integer(0), integer(-1)], 1),
        1,
    )
    .unwrap();
    let ratio = ReceivingFaceRatio::compare_partition(
        Faces::of_reads(&[p.clone(), p], 1).unwrap(),
        vec![None, Some(q)],
        BigInt::from(0),
    )
    .unwrap();
    assert_eq!(ratio.stations(), &[1]);
    assert_eq!(ratio.covector().unwrap().logits()[0], vec![Rat::zero(); 4]);
    assert_eq!(
        ratio.covector().unwrap().logits()[1],
        vec![rat(-1, 6), rat(-1, 6), rat(1, 6), rat(1, 12)]
    );
    assert_eq!(ratio.excess().unwrap(), rat(1, 8));
    assert_eq!(ratio.phase_gap(1, 0).unwrap().turns(), rat(1, 2));
    assert!(ratio.phase_gap(0, 0).is_err());
    let p = ratio.faces().clone();
    let equal = ReceivingFaceRatio::compare_partition(
        p.clone(),
        p.faces.into_iter().map(Some).collect(),
        BigInt::from(0),
    )
    .unwrap();
    assert!(
        equal
            .covector()
            .unwrap()
            .logits()
            .iter()
            .flatten()
            .all(Zero::is_zero)
    );
}

#[test]
fn an_actual_world_face_changes_r_then_the_later_native_prospect() {
    let (field, theta, source) = fixture();
    let declared = &field.receivers()[0];
    let mut receiver =
        PhysicalReceiver::new(&field, theta, Current::at_rest(&field), WordOpening::Rest).unwrap();
    let preparation =
        PortPreparation::new(&field, 0, ExactRatMatrix::identity(4).unwrap()).unwrap();
    // A declared nonzero native carrier condition. The World remains an independent
    // physical law; this condition is never used as the later observed target.
    let request = vec![
        vec![Rat::zero(); 4],
        vec![rat(1, 4), rat(1, 8), rat(1, 16), rat(-1, 32)],
    ];
    let compared = [false, true];
    let world = bound_world(&field, source.part(0..0).unwrap(), 0);
    let before_world = world.state().clone();
    receiver.bind_world(world).unwrap();
    let before_r = receiver.constitution().receiving_map(1).cloned();
    let first = receiver
        .prepare_action(&source, declared, &preparation, &request, &compared)
        .unwrap();
    assert!(first.prospective().unique_control().is_some());
    let received = match first.encounter().unwrap() {
        ActionCommunication::Received(r) => r,
        other => panic!("actual law control: {other:?}"),
    };
    assert!(received.closes());
    assert_ne!(
        receiver.participating_world().unwrap().state(),
        &before_world
    );
    assert_eq!(
        receiver.participating_world().unwrap().state().commit,
        received.carry.ticks as u64
    );
    assert_eq!(
        received
            .encounter
            .observed()
            .iter()
            .filter(|q| q.is_some())
            .count(),
        1
    );
    for step in received.encounter.steps() {
        assert!(step.closes(&vec![integer(2); 4], field.step()));
        assert_eq!(step.joint.boundary().effort(), step.effort);
        assert_eq!(step.joint.boundary().flow(), step.flow);
        assert_eq!(step.receipt.regions(), 8);
    }
    assert!(received.comparison.as_ref().unwrap().publication.is_some());
    assert_ne!(before_r, receiver.constitution().receiving_map(1).cloned());
    let snapshot = receiver.receiving_snapshot(declared).unwrap();
    let next = receiver
        .plan_action(&source, declared, &preparation, &request, &compared)
        .unwrap();
    let second = receiver
        .prepare_action(&source, declared, &preparation, &request, &compared)
        .unwrap();
    assert_eq!(second.prospective().response(), next.response());
    let _second = second.encounter().unwrap();
    let frozen = receiver
        .plan_action_with_receiving(
            &snapshot,
            &source,
            declared,
            &preparation,
            &request,
            &compared,
        )
        .unwrap();
    let now = receiver
        .plan_action(&source, declared, &preparation, &request, &compared)
        .unwrap();
    assert_ne!(frozen.response(), now.response());
    assert_eq!(
        receiver
            .participating_world()
            .unwrap()
            .native_tick()
            .unwrap(),
        receiver.resident().carried().unwrap().ticks
    );
}

#[test]
fn a_held_preimage_or_foreign_clock_changes_neither_actual_participant() {
    let (field, theta, source) = fixture();
    let declared = &field.receivers()[0];
    let mut receiver =
        PhysicalReceiver::new(&field, theta, Current::at_rest(&field), WordOpening::Rest).unwrap();
    let world = bound_world(&field, source.part(0..0).unwrap(), 0);
    let actual = world.state().clone();
    // A foreign affine clock is refused before either actual participant is mutated.
    let foreign = bound_world(&field, source.part(0..0).unwrap(), 1);
    assert!(receiver.bind_world(foreign).is_err());
    assert!(receiver.participating_world().is_none());
    receiver.bind_world(world).unwrap();
    let request = vec![vec![Rat::zero(); 4]; 2];
    let compared = [false, true];
    let no_actuator = PortPreparation::new(&field, 0, ExactRatMatrix::zero(4, 1).unwrap()).unwrap();
    let before = receiver.opening();
    let commit = receiver.constitution().commit();
    assert!(matches!(
        receiver
            .prepare_action(&source, declared, &no_actuator, &request, &compared)
            .unwrap()
            .encounter()
            .unwrap(),
        ActionCommunication::Held { .. }
    ));
    assert_eq!(receiver.opening(), before);
    assert_eq!(receiver.constitution().commit(), commit);
    assert_eq!(receiver.participating_world().unwrap().state(), &actual);
    assert!(receiver.resident().continuing_state(0).is_err());
    let section =
        holonics::hnn::prediction::DamagedSection::of_runs(2, &source, vec![(0, source.clone())])
            .unwrap();
    assert!(receiver.read(&section, declared).is_err());
    assert!(
        receiver
            .begin_continuing_contact_variation(holonics::hnn::word::variation::VariationBudget {
                ratios: 432,
                bits: 1 << 20,
                column_ticks: 8
            })
            .is_err()
    );
    assert_eq!(receiver.opening(), before);
    let copied = PhysicalReceiver::from_resident(&field, receiver.resident().clone()).unwrap();
    let copied_actual = copied.participating_world().unwrap().state().clone();
    let mut copied = copied;
    let prep = PortPreparation::new(&field, 0, ExactRatMatrix::identity(4).unwrap()).unwrap();
    assert!(
        copied
            .prepare_action(&source, declared, &prep, &request, &compared)
            .unwrap()
            .encounter()
            .is_err()
    );
    assert_eq!(
        copied.participating_world().unwrap().state(),
        &copied_actual
    );
    let resident = receiver.into_resident();
    assert_eq!(resident.participating_world().unwrap().state(), &actual);
    let receiver = PhysicalReceiver::from_resident(&field, resident).unwrap();
    assert_eq!(receiver.participating_world().unwrap().state(), &actual);
}

#[test]
fn actual_prior_world_history_changes_native_carry_and_matched_later_choice() {
    let (field, theta, source) = fixture();
    let declared = &field.receivers()[0];
    let preparation =
        PortPreparation::new(&field, 0, ExactRatMatrix::identity(4).unwrap()).unwrap();
    let request = vec![
        vec![Rat::zero(); 4],
        vec![rat(1, 4), rat(1, 8), rat(1, 16), rat(-1, 32)],
    ];
    let compared = [false, true];
    let mut a = PhysicalReceiver::new(
        &field,
        theta.clone(),
        Current::at_rest(&field),
        WordOpening::Rest,
    )
    .unwrap();
    let mut b =
        PhysicalReceiver::new(&field, theta, Current::at_rest(&field), WordOpening::Rest).unwrap();
    let chart = source.part(0..0).unwrap();
    let world_a = bound_world_with_history(&field, chart.clone(), 0, Some(&vec![Rat::zero(); 4]));
    let world_b = bound_world_with_history(
        &field,
        chart,
        0,
        Some(&[integer(1), integer(0), integer(0), integer(0)]),
    );
    assert_ne!(world_a.state(), world_b.state());
    assert_eq!(world_a.state().commit, world_b.state().commit);
    assert_eq!(a.opening(), b.opening());
    assert_eq!(a.constitution(), b.constitution());
    a.bind_world(world_a).unwrap();
    b.bind_world(world_b).unwrap();
    let pa = a
        .prepare_action(&source, declared, &preparation, &request, &compared)
        .unwrap();
    let pb = b
        .prepare_action(&source, declared, &preparation, &request, &compared)
        .unwrap();
    assert_eq!(pa.prospective().baseline(), pb.prospective().baseline());
    assert_eq!(
        pa.prospective().unique_control(),
        pb.prospective().unique_control()
    );
    let ActionCommunication::Received(ra) = pa.encounter().unwrap() else {
        panic!("fixture A");
    };
    let ActionCommunication::Received(rb) = pb.encounter().unwrap() else {
        panic!("fixture B");
    };
    assert!(ra.closes() && rb.closes());
    assert_ne!(
        ra.source_returns[0].reflected,
        rb.source_returns[0].reflected
    );
    assert_ne!(
        ra.boundary.readings()[0].read.logits,
        rb.boundary.readings()[0].read.logits
    );
    assert_ne!(ra.carry, rb.carry);
    assert_eq!(
        ra.word.boundary,
        -ra.encounter
            .steps()
            .iter()
            .map(|s| &s.port_work)
            .sum::<Rat>()
    );
    assert_eq!(
        rb.word.boundary,
        -rb.encounter
            .steps()
            .iter()
            .map(|s| &s.port_work)
            .sum::<Rat>()
    );
    assert_eq!(
        ra.carry.change.storage[0],
        ra.source_returns.last().unwrap().reflected
    );
    // The same ACTUALLY learned R is used at both contemporary physical carries. This is a
    // read-only attribution control; neither World nor native current is reset/replayed.
    let r = a.receiving_snapshot(declared).unwrap();
    let next_a = a
        .plan_action_with_receiving(&r, &source, declared, &preparation, &request, &compared)
        .unwrap();
    let next_b = b
        .plan_action_with_receiving(&r, &source, declared, &preparation, &request, &compared)
        .unwrap();
    assert_eq!(next_a.response(), next_b.response());
    assert_ne!(next_a.baseline(), next_b.baseline());
    assert_ne!(next_a.unique_control(), next_b.unique_control());
    // Moving through the ordinary view retains the actual World's accumulated state/clock.
    let state = a.participating_world().unwrap().state().clone();
    let carry = a.resident().carried().unwrap().clone();
    let a = PhysicalReceiver::from_resident(&field, a.into_resident()).unwrap();
    assert_eq!(a.participating_world().unwrap().state(), &state);
    assert_eq!(a.resident().carried().unwrap(), &carry);
}
