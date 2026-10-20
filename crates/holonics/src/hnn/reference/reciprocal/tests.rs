use super::*;
use crate::hnn::reference::observed::{ObservedEpochDepositionScope, ObservedStream};
use crate::hnn::tests::support::{contact, small_field_of};
use std::time::Instant;

fn menu() -> Vec<PairRelation> {
    vec![PairRelation::new(1, vec![Some(1), Some(0), Some(3), Some(2)]).unwrap()]
}
fn bound() -> JointBound {
    JointBound {
        members: 64,
        visits: 1024,
    }
}
fn family(testimony: [usize; 2], channel: JointChannel, copies: usize) -> JointFamily {
    JointFamily::declare(
        (0..copies).map(|_| menu().remove(0)).collect(),
        [0, 1],
        testimony,
        [(0..4).collect(), (0..4).collect()],
        channel,
        bound(),
    )
    .unwrap()
    .0
}
fn origin() -> ReturnOrigin {
    ReturnOrigin::Entailed {
        family: "synthetic-finite".into(),
        menu: "sigma01-23".into(),
        channel: "explicit".into(),
        source: "fixture".into(),
    }
}

#[test]
fn complete_joint_family_channels_transpose_support_and_exact_reuse() {
    let start = Instant::now();
    let one = family([0, 2], JointChannel::AtMostOneChanged, 1);
    assert_eq!(
        one.members
            .iter()
            .map(|m| (m.antecedent, m.consequence))
            .collect::<Vec<_>>(),
        vec![(0, 1), (3, 2)]
    );
    let both = family([0, 2], JointChannel::BothMayChange, 1);
    assert_eq!(both.members.len(), 4); // Not its 4x4 marginal product.
    assert_eq!(both.swapped().swapped(), both);
    let future = one.relational_future().unwrap();
    assert_eq!(
        future.iter().map(|(_, z)| *z).collect::<Vec<_>>(),
        vec![0, 3]
    );
    let (refined, first) = one.refine_return([0, 1], &one.members[..1]).unwrap();
    let (again, reused) = refined.refine_return([0, 1], &one.members[..1]).unwrap();
    assert_eq!(again, refined);
    assert!(first.tuple_visits > 0);
    assert_eq!(
        reused,
        CompatibilityWork {
            reused: true,
            ..Default::default()
        }
    );
    assert!(one.refine_return([1, 2], &one.members[..1]).is_err());
    assert!(one.refine_return([0, 1], &[]).unwrap().0.members.is_empty());
    assert!(
        JointFamily::declare(
            menu(),
            [0, 1],
            [0, 2],
            [(0..4).collect(), (0..4).collect()],
            JointChannel::BothMayChange,
            JointBound {
                members: 1,
                visits: 16
            }
        )
        .is_err()
    );
    println!(
        "V93_COMPATIBILITY elapsed_ns={} whole_members={} spurious_marginal_product=16 repeat_visits={} repeated_relation_reads={} no_native_model_data=true",
        start.elapsed().as_nanos(),
        both.members.len(),
        reused.tuple_visits,
        reused.relation_reads
    );
}

fn fixture(
    input: &[usize],
) -> (
    Reference,
    Resident,
    ObservedCrib,
    PairingDeclaration,
    Constitution,
    ExactRatMatrix,
) {
    let base = small_field_of(
        &[5, 2, 3],
        vec![contact(0, 1, 1, 0), contact(1, 2, 1, 0)],
        2,
        4,
    );
    let mut d = base.declaration().clone();
    d.rings[0].lock = (0..4).collect();
    d.rings[1].lock.clear();
    d.rings[2].lock.clear();
    d.offsets = vec![1, 2];
    d.lattice.clear();
    let field = Field::declare(d.by_lattice_rule()).unwrap();
    let pairing = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
    };
    let opening = PairedCarrier::found(
        &field,
        Constitution::initial(&field, 1 << 40).unwrap(),
        0,
        &pairing,
    )
    .unwrap()
    .0;
    let prior = opening.source_port(0).unwrap().clone();
    let reference = Reference::new(16, 1 << 40);
    let mut resident = reference
        .mount_with(&field, &Current::at_rest(&field), opening.clone())
        .unwrap();
    let boundary = PairedObservation::admit(&field, &opening, &pairing).unwrap();
    reference
        .ingest(&mut resident, None, &boundary.encode(&[]).unwrap())
        .unwrap();
    let mut crib = ObservedCrib::new(0);
    for &class in input {
        reference
            .ingest_class_continuing(&mut resident, &mut crib, &pairing, class, None)
            .unwrap();
    }
    // An actual native Word runs at this current; no class loss or fitting transaction.
    let id = *resident.moments.keys().next().unwrap();
    let phases = resident.admitted[0].clone();
    let (pending, _) = reference.refine(&mut resident, &id, &phases).unwrap();
    reference
        .discard(&mut resident, Handle::Pending(pending))
        .unwrap();
    (reference, resident, crib, pairing, opening, prior)
}

#[test]
fn common_packet_is_one_paired_deposit_preserves_live_state_cold_and_future() {
    let start = Instant::now();
    let (reference, mut resident, crib, pairing, opening, prior) = fixture(&[0, 1]);
    let mut family = family([0, 1], JointChannel::Exact, 2);
    // Distinct hypotheses agree on this encountered0->1 and differ at the next consequence.
    family.menu[1] = PairRelation::new(1, vec![Some(1), Some(2), Some(3), Some(0)]).unwrap();
    assert_eq!(
        family
            .relational_future()
            .unwrap()
            .iter()
            .map(|(_, z)| *z)
            .collect::<Vec<_>>(),
        vec![0, 2]
    );
    let before = resident.clone();
    let old = PairedObservation::admit(&resident.field, &resident.constitution, &pairing).unwrap();
    let cut = reference
        .bind_source_return(&resident, &crib, &pairing, &prior, 0, &family, origin())
        .unwrap();
    let outcome = cut.publish(&reference, &mut resident, &crib).unwrap();
    let ReciprocalOutcome::Published(receipt) = outcome else {
        panic!("common packet held");
    };
    assert_eq!(receipt.compatible_branches, 2);
    assert_eq!(family.members.len(), 2);
    let single = super::tests::family([0, 1], JointChannel::Exact, 1);
    let mut one = before.clone();
    reference
        .bind_source_return(&one, &crib, &pairing, &prior, 0, &single, origin())
        .unwrap()
        .publish(&reference, &mut one, &crib)
        .unwrap();
    assert_eq!(resident.constitution, one.constitution); // Full NormalLaw/stats, not a count label.
    let swapped = family.swapped();
    let mut reverse = before.clone();
    let result = reference
        .bind_source_return(&reverse, &crib, &pairing, &prior, 0, &swapped, origin())
        .unwrap()
        .publish(&reference, &mut reverse, &crib)
        .unwrap();
    let ReciprocalOutcome::Published(reverse_read) = result else {
        panic!("swapped packet held")
    };
    assert_eq!(reverse_read.packet.turns, -receipt.packet.turns.clone());
    assert_eq!(reverse.constitution, resident.constitution);

    assert_eq!(receipt.paired_batches, 1);
    assert_eq!(receipt.normal_preparations, 2);
    assert!(receipt.slip_after < receipt.slip_before);
    assert_ne!(
        resident.constitution.source_port(0),
        before.constitution.source_port(0)
    );
    assert_eq!(resident.current, before.current);
    assert_eq!(resident.carried, before.carried);
    assert_eq!(resident.moments, before.moments);
    assert_eq!(resident.address, before.address);
    assert_eq!(resident.charts, before.charts);
    assert_eq!(
        resident.observed_epoch_ingress,
        before.observed_epoch_ingress
    );
    assert_eq!(
        resident.constitution.landmarks(2),
        before.constitution.landmarks(2)
    );
    assert_eq!(
        resident.constitution.population(2),
        before.constitution.population(2)
    );
    assert!(old.check_material(&resident.constitution).is_err());
    let saved = resident.continuing_state(0).unwrap();
    let parsed = ContinuingState::from_text(&saved.to_text(), 1 << 40).unwrap();
    let cold = reference
        .mount_continued(&resident.field, &resident.current, opening, &parsed)
        .unwrap();
    assert_eq!(cold.continuing_state(0).unwrap(), saved);
    assert!(
        reference
            .bind_source_return(&resident, &crib, &pairing, &prior, 0, &family, origin())
            .is_err()
    );
    assert!(
        reference
            .bind_source_return(&cold, &crib, &pairing, &prior, 0, &family, origin())
            .is_err()
    );
    let source = resident.moments.values().next().unwrap();
    let (mut warm, _) = Word::open_exact_received(
        &resident.field,
        &resident.constitution,
        &resident.current,
        source,
        &resident.reception_opening(),
    )
    .unwrap();
    let (mut restored, _) = Word::open_exact_received(
        &cold.field,
        &cold.constitution,
        &cold.current,
        cold.moments.values().next().unwrap(),
        &cold.reception_opening(),
    )
    .unwrap();
    let (mut control, _) = Word::open_exact_received(
        &before.field,
        &before.constitution,
        &before.current,
        before.moments.values().next().unwrap(),
        &before.reception_opening(),
    )
    .unwrap();
    warm.tick().unwrap();
    restored.tick().unwrap();
    control.tick().unwrap();
    assert_eq!(warm.change().unwrap(), restored.change().unwrap());
    assert_ne!(warm.change().unwrap(), control.change().unwrap());
    assert!(warm.field_balances().last().unwrap().closes());
    println!(
        "V93_NATIVE elapsed_ns={} paired_batches=1 normal_preparations=2 validation_word_openings=1 score_calls=0 fixture_classes=2 cold=true changed_future=true slip_before={} slip_after={}",
        start.elapsed().as_nanos(),
        receipt.slip_before,
        receipt.slip_after
    );
}

#[test]
fn differing_packet_holds_but_current_continues_and_stale_cut_and_false_observed_refuse() {
    let (reference, mut resident, mut crib, pairing, _, prior) = fixture(&[0, 2]);
    let ambiguous = family([0, 2], JointChannel::AtMostOneChanged, 1);
    let before = resident.continuing_state(0).unwrap();
    assert!(
        reference
            .bind_source_return(
                &resident,
                &crib,
                &pairing,
                &prior,
                0,
                &ambiguous,
                ReturnOrigin::Observed
            )
            .is_err()
    );
    let cut = reference
        .bind_source_return(&resident, &crib, &pairing, &prior, 0, &ambiguous, origin())
        .unwrap();
    assert!(matches!(
        cut.publish(&reference, &mut resident, &crib).unwrap(),
        ReciprocalOutcome::Hold { branches: 2 }
    ));
    assert_eq!(before, resident.continuing_state(0).unwrap());
    let stale = reference
        .bind_source_return(&resident, &crib, &pairing, &prior, 0, &ambiguous, origin())
        .unwrap();
    reference
        .ingest_class_continuing(&mut resident, &mut crib, &pairing, 3, None)
        .unwrap();
    let id = *resident.moments.keys().next().unwrap();
    let phases = resident.admitted[0].clone();
    let (pending, _) = reference.refine(&mut resident, &id, &phases).unwrap();
    reference
        .discard(&mut resident, Handle::Pending(pending))
        .unwrap();
    assert_ne!(before, resident.continuing_state(0).unwrap());
    assert_eq!(ambiguous.members.len(), 2);
    assert!(stale.publish(&reference, &mut resident, &crib).is_err());
    // A newly ingressed actual class3 at occurrence2 separates the hypothetical images0/3.
    let (separated, reading) = reference
        .refine_joint_exact_return(&resident, &crib, &ambiguous, 0, 2)
        .unwrap();
    assert_eq!(reading.relation_reads, 2);
    assert_eq!(separated.members[0].antecedent, 3);
    assert_eq!(separated.separating_return.as_ref().unwrap().1, 3);
    let fresh = reference
        .bind_source_return(&resident, &crib, &pairing, &prior, 0, &separated, origin())
        .unwrap();
    assert!(matches!(
        fresh.publish(&reference, &mut resident, &crib).unwrap(),
        ReciprocalOutcome::Published(_)
    ));
}

#[test]
fn late_validation_failure_rolls_back_and_pending_six_is_preserved() {
    let (reference, mut resident, crib, pairing, _, prior) = fixture(&[0, 1]);
    let family = family([0, 1], JointChannel::Exact, 1);
    let cut = reference
        .bind_source_return(&resident, &crib, &pairing, &prior, 0, &family, origin())
        .unwrap();
    let before = resident.continuing_state(0).unwrap();
    assert!(
        cut.publish_checked(&reference, &mut resident, &crib, |_| Err(refused(
            "synthetic late refusal"
        )))
        .is_err()
    );
    assert_eq!(before, resident.continuing_state(0).unwrap());
    let mut stream = ObservedStream::restore(
        resident,
        crib,
        ObservedEpochDepositionScope::NormalMaps,
        vec![0, 1, 2, 3, 0, 1],
    )
    .unwrap();
    assert_eq!(stream.accepted_cells().unwrap(), 8);
    let pending = stream.pending_classes().to_vec();
    let crib = stream.crib().clone();
    assert!(matches!(
        stream
            .return_source_relation(&reference, &pairing, &prior, 0, &family, origin())
            .unwrap(),
        ReciprocalOutcome::Published(_)
    ));
    assert_eq!(stream.pending_classes(), pending);
    assert_eq!(stream.crib(), &crib);
    assert_eq!(stream.accepted_cells().unwrap(), 8);
    let saved = stream.resident().continuing_state(0).unwrap();
    let text = stream.pending_checkpoint();
    let copied =
        ObservedStream::restore_checkpoint(stream.resident().clone(), stream.crib().clone(), &text)
            .unwrap();
    assert_eq!(copied.resident().continuing_state(0).unwrap(), saved);
    assert_eq!(copied.pending_classes(), pending);
    let combined = ReciprocalCheckpoint::capture(&stream, &family, origin(), 0).unwrap();
    let text = combined.to_text();
    let restored = ReciprocalCheckpoint::from_text(&text, text.len(), 1 << 40, bound()).unwrap();
    assert_eq!(restored.family, family);
    assert_eq!(restored.origin, origin());
    assert_eq!(restored.to_text(), text);
    let opening = fixture(&[]).4;
    let cold = restored
        .restore(&reference, stream.resident().field(), opening)
        .unwrap();
    assert_eq!(cold.resident().continuing_state(0).unwrap(), saved);
    assert_eq!(cold.pending_classes(), pending);
    assert_eq!(cold.crib(), stream.crib());
}

#[test]
fn immutable_same_cut_preparation_reuses_native_work_and_changed_context_invalidates() {
    let (reference, resident, mut crib, pairing, _, prior) = fixture(&[0, 1]);
    let family = family([0, 1], JointChannel::Exact, 1);
    let mut cold_ns = Vec::new();
    let mut warm_ns = Vec::new();
    let mut all = None;
    for _ in 0..5 {
        let cut = reference
            .bind_source_return(&resident, &crib, &pairing, &prior, 0, &family, origin())
            .unwrap();
        let at = Instant::now();
        let (value, reused) = cut.prepare_reading(&resident, &crib).unwrap();
        cold_ns.push(at.elapsed().as_nanos());
        assert!(!reused);
        let at = Instant::now();
        let (again, reused) = cut.prepare_reading(&resident, &crib).unwrap();
        warm_ns.push(at.elapsed().as_nanos());
        assert!(reused);
        assert_eq!(value, again);
        if let Some(prior) = &all {
            assert_eq!(prior, &value);
        }
        all = Some(value);
    }
    let cut = reference
        .bind_source_return(&resident, &crib, &pairing, &prior, 0, &family, origin())
        .unwrap();
    cut.prepare_reading(&resident, &crib).unwrap();
    let mut changed = resident.clone();
    reference
        .ingest_class_continuing(&mut changed, &mut crib, &pairing, 2, None)
        .unwrap();
    assert!(cut.prepare_reading(&changed, &crib).is_err());
    cold_ns.sort();
    warm_ns.sort();
    println!(
        "V93_REUSE cold_ns={cold_ns:?} repeated_ns={warm_ns:?} cold_paired_batches=5 repeated_paired_batches=0 cold_normal_preparations=10 repeated_normal_preparations=0 scoring_calls=0 root_calls_uninstrumented=true memoization_not_learning=true"
    );
    // Same-work result equality is required; no timing speedup is asserted from noisy samples.
}
