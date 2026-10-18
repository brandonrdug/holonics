//! Exact cold-continuation equivalence for the one arrived comparison.
//! Fixed law fixtures only; no generated training, private data or unseen-family claim.

use holonics::compression::landmark::context::{BaseMeasure, StopPrior};
use holonics::geometry::{RatVec3, screw::ScrewGenerator};
use holonics::hnn::Encoded;
use holonics::hnn::constitution::ContinuingState;
use holonics::hnn::field::{ContactDeclaration, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::port::{ExecutionPort, Handle};
use holonics::hnn::receiving::ReceivingPhases;
use holonics::hnn::reference::{Reference, Resident};
use holonics::hnn::{Constitution, Current, Field, FieldDeclaration, RingDeclaration};
use holonics::holarchy::terrain::{CyclicLaw, KnownTruth};
use holonics::ratio::{integer, rat};

fn chain() -> Field {
    let ring = |period: u64, lock: Vec<u64>| RingDeclaration {
        period,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..period)
            .map(|node| FieldDeclaration::quarter_turn(node, period))
            .collect(),
        lock,
        reflector: (0..period)
            .map(|p| ((period - p) % period) as usize)
            .collect(),
        admittance: integer(2),
        initial: 0,
    };
    let contact = |from, to, exponent| ContactDeclaration {
        from,
        to,
        channel: vec![(0, 0), (1, 1)],
        admittance: integer(2),
        exponent: integer(exponent),
    };
    let mut declaration = FieldDeclaration {
        rings: vec![ring(2, vec![0]), ring(3, vec![0]), ring(2, vec![])],
        contacts: vec![contact(0, 1, 2), contact(1, 2, 0)],
        loops: Vec::new(),
        sources: vec![0],
        offsets: vec![1],
        alphabet: 4,
        step: integer(1),
        exponent_grain: 1,
        receivers: vec![ReceiverDeclaration {
            ring: 2,
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
    .by_lattice_rule();
    let probe = Field::declare(declaration.clone()).unwrap();
    declaration.population = probe.capacity().n_star();
    Field::declare(declaration).unwrap()
}

/// A run of `count` zeros: the line terrain on one class (ℤ/1), through its declared identity
/// (THE_MACHINE guard 9).
fn zeros(field: &Field, count: usize) -> Encoded {
    let truth = KnownTruth::cyclic(CyclicLaw::Line, 1, 0, 1, count).unwrap();
    Encoded::identity(&truth, field).unwrap().remove(0)
}

/// The target word [1, 0]: the line terrain on ℤ/2 whose drawn start and step are both 1.
fn target(field: &Field) -> Encoded {
    let truth = KnownTruth::cyclic(CyclicLaw::Line, 2, 2_026_100_983, 1, 2).unwrap();
    assert_eq!(truth.passages(), &[vec![1, 0]]);
    Encoded::identity(&truth, field).unwrap().remove(0)
}

/// A contained future receiver that changes the exact family witness without changing this
/// fixture's retained causal loci. Depth is not part of containment or the causal diamond.
fn changed_future_family(field: &Field, resident: &Resident) -> Vec<ReceivingPhases> {
    let mut declaration = field.receivers()[0].clone();
    assert!(declaration.depth > 0);
    declaration.depth -= 1;
    let phases = ReceivingPhases::declare(
        field,
        resident.constitution(),
        resident.current(),
        &declaration,
    )
    .unwrap();
    assert_ne!(phases, resident.admitted()[0]);
    vec![phases]
}

fn assert_same_endpoint(reference: &Reference, left: &Resident, right: &Resident) {
    let (_, left_current, left_handles) = reference.read(left).unwrap();
    let (_, right_current, right_handles) = reference.read(right).unwrap();
    assert_eq!(right_current, left_current);
    assert_eq!(right_handles, left_handles);
    assert_eq!(right.constitution(), left.constitution());
    assert_eq!(right.carried(), left.carried());
    assert_eq!(right.address(), left.address());
    assert_eq!(right.admitted(), left.admitted());
    assert_eq!(right.ledger().balance(), left.ledger().balance());
}

fn compare_twice(
    reference: &Reference,
    resident: &mut holonics::hnn::reference::Resident,
    moment: holonics::hnn::port::MomentId,
) {
    let phases = resident.admitted()[0].clone();
    for _ in 0..2 {
        let (pending, _) = reference.refine(resident, &moment, &phases).unwrap();
        let (staged, _) = reference
            .compare(resident, pending, &target(resident.field()))
            .unwrap();
        reference.discard(resident, Handle::Staged(staged)).unwrap();
    }
}

fn cold_equivalence(ingest_after_restore: bool, discard_moment: bool, remount_after_close: bool) {
    let field = chain();
    let reference = Reference::new(64, u64::MAX);
    let mut original = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let count = if ingest_after_restore {
        1
    } else {
        usize::try_from(field.population()).unwrap()
    };
    let (moment, ingested) = reference
        .ingest(&mut original, None, &zeros(&field, count))
        .unwrap();
    assert_eq!(
        ingested.forward.present().unwrap().carry_out,
        !ingest_after_restore,
        "the fixture must save at its declared side of carry-out"
    );
    compare_twice(&reference, &mut original, moment);
    if discard_moment {
        reference
            .discard(&mut original, Handle::Moment(moment))
            .unwrap();
    }
    let source = field.sources()[0];
    let state = original.continuing_state(source).unwrap();
    assert!(state.passage().is_some());
    let state = ContinuingState::from_text(&state.to_text()).unwrap();
    // The cold mount reads only the immutable field, a fresh founding constitution and saved
    // exact text. No predecessor material, clock, moment, address, chart or comparison is borrowed.
    let mut restored = reference
        .mount_continued(
            &field,
            &Current::at_rest(&field),
            Constitution::initial(&field, u64::MAX).unwrap(),
            &state,
        )
        .unwrap();
    assert_eq!(restored.continuing_state(source).unwrap(), state);
    let (_, original_current, original_handles) = reference.read(&original).unwrap();
    let (_, restored_current, restored_handles) = reference.read(&restored).unwrap();
    assert_eq!(restored_current, original_current);
    assert_eq!(restored_handles, original_handles);
    assert_eq!(restored.constitution(), original.constitution());
    assert_eq!(restored.carried(), original.carried());
    assert_eq!(restored.address(), original.address());
    assert_eq!(restored.admitted(), original.admitted());
    assert_eq!(restored.ledger().balance(), original.ledger().balance());
    if ingest_after_restore {
        let cells = zeros(&field, usize::try_from(field.population()).unwrap());
        let (_, uninterrupted) = reference
            .ingest(&mut original, Some(&moment), &cells)
            .unwrap();
        let (_, resumed) = reference
            .ingest(&mut restored, Some(&moment), &cells)
            .unwrap();
        assert!(uninterrupted.forward.present().unwrap().carry_out);
        assert!(resumed.forward.present().unwrap().carry_out);
        assert_eq!(
            uninterrupted.forward.present().unwrap().cells,
            resumed.forward.present().unwrap().cells
        );
        // No compare occurs between restoration and close: the saved Arrived is still required.
    }
    let exchanges = original.ledger().balance().exchanges;
    let whole = reference.close_aeon(&mut original, &[]).unwrap();
    let resumed = reference.close_aeon(&mut restored, &[]).unwrap();
    let whole = whole.forward.present().unwrap();
    let resumed = resumed.forward.present().unwrap();
    assert!(!whole.collapse.released.is_empty());
    assert_eq!(
        whole.first_law.exchanges,
        exchanges + 1,
        "the original must actually reread the arrived comparison on release"
    );
    assert_eq!(resumed.first_law, whole.first_law);
    assert_eq!(resumed.collapse, whole.collapse);
    assert_eq!(resumed.literal, whole.literal);
    assert_eq!(restored.constitution(), original.constitution());
    assert_eq!(restored.current(), original.current());
    assert_eq!(restored.carried(), original.carried());
    assert_eq!(restored.address(), original.address());
    assert_eq!(restored.admitted(), original.admitted());
    if remount_after_close {
        // No moment may remain, and the newly restricted admitted family is empty. The saved
        // resident still retains its next action operands rather than falling back to a material save.
        let state =
            ContinuingState::from_text(&restored.continuing_state(source).unwrap().to_text())
                .unwrap();
        let resumed_again = reference
            .mount_continued(
                &field,
                &Current::at_rest(&field),
                Constitution::initial(&field, u64::MAX).unwrap(),
                &state,
            )
            .unwrap();
        assert_eq!(resumed_again.continuing_state(source).unwrap(), state);
        assert_same_endpoint(&reference, &restored, &resumed_again);

        // Repeat the cold mount from the post-close endpoint and check the same exact operands.
        let state =
            ContinuingState::from_text(&resumed_again.continuing_state(source).unwrap().to_text())
                .unwrap();
        let resumed_twice = reference
            .mount_continued(
                &field,
                &Current::at_rest(&field),
                Constitution::initial(&field, u64::MAX).unwrap(),
                &state,
            )
            .unwrap();
        assert_eq!(resumed_twice.continuing_state(source).unwrap(), state);
        assert_same_endpoint(&reference, &resumed_again, &resumed_twice);
    }
}

#[test]
fn cold_restore_preserves_an_immediate_arrived_release() {
    cold_equivalence(false, false, false);
}

#[test]
fn cold_restore_preserves_arrived_through_ingest_to_close() {
    cold_equivalence(true, false, false);
}

#[test]
fn cold_restore_preserves_arrived_without_an_open_moment() {
    cold_equivalence(false, true, false);
}

/// The post-close save remounts: the constitution the aeon's collapse returns is charted on each
/// contact's storage factor (`Field::contact_holon`), so a released channel's zero storage mounts
/// as the pure transmission the word executes.
#[test]
fn post_close_save_remounts() {
    cold_equivalence(false, false, true);
}

#[test]
fn pending_producer_survives_close_under_a_changed_future_family() {
    let field = chain();
    let reference = Reference::new(64, u64::MAX);
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let producing_phases = resident.admitted()[0].clone();
    let future = changed_future_family(&field, &resident);
    let count = usize::try_from(field.population()).unwrap();
    let (moment, ingested) = reference
        .ingest(&mut resident, None, &zeros(&field, count))
        .unwrap();
    assert!(ingested.forward.present().unwrap().carry_out);

    let (pending, _) = reference
        .refine(&mut resident, &moment, &producing_phases)
        .unwrap();
    let closed = reference.close_aeon(&mut resident, &future).unwrap();
    let boundary = closed.forward.present().unwrap();
    assert_eq!(boundary.carried, vec![pending]);
    assert!(boundary.refused.is_empty());
    assert!(boundary.collapse.released.is_empty());
    assert_eq!(resident.admitted(), future);

    // The carried comparison still executes at the exact receiver that produced it, even though
    // the boundary has admitted a different future family.
    let (staged, compared) = reference
        .compare(&mut resident, pending, &target(&field))
        .unwrap();
    assert_eq!(compared.phases.present().unwrap(), &[producing_phases]);
    // Open pending and staged handles are deliberately not passage-saveable. Retire the stage;
    // its Arrived operand remains the resident's first-law endpoint and is saved below.
    reference
        .discard(&mut resident, Handle::Staged(staged))
        .unwrap();

    let source = field.sources()[0];
    let state =
        ContinuingState::from_text(&resident.continuing_state(source).unwrap().to_text()).unwrap();
    let restored = reference
        .mount_continued(
            &field,
            &Current::at_rest(&field),
            Constitution::initial(&field, u64::MAX).unwrap(),
            &state,
        )
        .unwrap();
    assert_eq!(restored.continuing_state(source).unwrap(), state);
    assert_same_endpoint(&reference, &resident, &restored);
    let mut restored = restored;
    let future_phases = restored.admitted()[0].clone();
    let (future_pending, _) = reference
        .refine(&mut restored, &moment, &future_phases)
        .unwrap();
    reference
        .discard(&mut restored, Handle::Pending(future_pending))
        .unwrap();
}

#[test]
fn staged_survivor_deposits_after_close_with_arrived_intact() {
    let field = chain();
    let reference = Reference::new(64, u64::MAX);
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let producing_phases = resident.admitted()[0].clone();
    let future = changed_future_family(&field, &resident);
    let count = usize::try_from(field.population()).unwrap();
    let (moment, ingested) = reference
        .ingest(&mut resident, None, &zeros(&field, count))
        .unwrap();
    assert!(ingested.forward.present().unwrap().carry_out);
    let (pending, _) = reference
        .refine(&mut resident, &moment, &producing_phases)
        .unwrap();
    let (staged, _) = reference
        .compare(&mut resident, pending, &target(&field))
        .unwrap();

    let before_close = resident.constitution().clone();
    let closed = reference.close_aeon(&mut resident, &future).unwrap();
    let boundary = closed.forward.present().unwrap();
    assert!(boundary.refused_staged.is_empty());
    assert!(boundary.collapse.released.is_empty());
    assert_eq!(resident.constitution(), &before_close);
    assert!(
        reference
            .read(&resident)
            .unwrap()
            .2
            .iter()
            .any(|(handle, _)| *handle == Handle::Staged(staged))
    );

    // A successful successor needs the sealed Arrived operand. This proves close carried both
    // the staged survivor and its original receipt rather than clearing the endpoint.
    let before_deposit = resident.ledger().balance().clone();
    assert_eq!(before_deposit.closing, boundary.first_law.closing);
    reference.deposit(&mut resident, staged).unwrap();
    assert_eq!(
        resident.ledger().balance().depositions,
        before_deposit.depositions + 1
    );
    assert_eq!(
        resident.ledger().balance().arrivals,
        before_deposit.arrivals
    );
    assert_eq!(resident.ledger().balance().arrived, before_deposit.arrived);
    assert_eq!(resident.ledger().balance().opening, before_deposit.opening);

    let source = field.sources()[0];
    let state =
        ContinuingState::from_text(&resident.continuing_state(source).unwrap().to_text()).unwrap();
    let restored = reference
        .mount_continued(
            &field,
            &Current::at_rest(&field),
            Constitution::initial(&field, u64::MAX).unwrap(),
            &state,
        )
        .unwrap();
    assert_eq!(restored.continuing_state(source).unwrap(), state);
    assert_same_endpoint(&reference, &resident, &restored);
    let mut restored = restored;
    let future_phases = restored.admitted()[0].clone();
    let (future_pending, _) = reference
        .refine(&mut restored, &moment, &future_phases)
        .unwrap();
    reference
        .discard(&mut restored, Handle::Pending(future_pending))
        .unwrap();
}

#[test]
fn version_two_resident_passage_is_refused() {
    let field = chain();
    let reference = Reference::new(64, u64::MAX);
    let resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let state = resident.continuing_state(field.sources()[0]).unwrap();
    let passage = state.passage().unwrap();
    assert!(passage.starts_with("resident-passage 3\n"));
    let old = passage.replacen("resident-passage 3", "resident-passage 2", 1);
    assert!(matches!(
        state
            .clone()
            .with_passage(Some(old))
            .resident_passage(&field, resident.constitution()),
        Err(holonics::hnn::HnnError::ContinuingState { .. })
    ));
    let unversioned = passage.lines().skip(1).collect::<Vec<_>>().join("\n");
    assert!(matches!(
        state
            .with_passage(Some(unversioned))
            .resident_passage(&field, resident.constitution()),
        Err(holonics::hnn::HnnError::ContinuingState { .. })
    ));
}
