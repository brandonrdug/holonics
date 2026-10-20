//! R4b publication: one atomic field/constitution/current/moment continuation.
use super::*;
use crate::hnn::field::FoundedRing;

fn fixture(budget: u64) -> (Reference, Resident, MomentId) {
    fixture_with_family(budget, false)
}

fn fixture_with_family(budget: u64, contact_family: bool) -> (Reference, Resident, MomentId) {
    fixture_with_material(budget, contact_family, None)
}

/// `source_scale` mounts R2's fixed carried-state construction (a zero receiving map) with ring
/// 0's source map scaled by it; `None` mounts the field's opening constitution.
fn fixture_with_material(
    budget: u64,
    contact_family: bool,
    source_scale: Option<&Rat>,
) -> (Reference, Resident, MomentId) {
    let nonzero_operand_control = source_scale.is_some();
    let mut declaration = crate::hnn::tests::learning::chain_declaration(4096);
    declaration.founding = true;
    // One class-independent source clock; the later declared rings take carry only.
    for ring in &mut declaration.rings {
        ring.lock.clear();
    }
    declaration.rings[0].lock = (0..4).collect();
    if nonzero_operand_control {
        // The legacy radius-sqrt(65) placements shield contact 0 at the 128-cell cut:
        // phases (0,2) give Q=52, beta=2, G=2^-51. The current placement rule gives
        // Q=4, G=1/8, so the two-hop path's exponent is 4 at receiver grain 16.
        // This is the fixture's causal construction, not an assumed nonzero read.
        for ring in &mut declaration.rings {
            ring.placements = (0..ring.period)
                .map(|node| crate::hnn::FieldDeclaration::quarter_turn(node, ring.period))
                .collect();
        }
        declaration = declaration.by_lattice_rule();
    }
    let mut field = Field::declare(declaration).unwrap();
    if contact_family {
        let family = crate::hnn::receiving::FeatureFamily::new(vec![
            crate::hnn::receiving::Feature::contact(&field, 0),
        ])
        .unwrap();
        field = field.with_letter_family(family).unwrap();
    }
    let budget = if budget == 1 {
        Constitution::initial(&field, 1 << 40).unwrap().exact_bits()
    } else {
        budget
    };
    let reference = Reference::new(4, budget);
    let mut resident = if nonzero_operand_control {
        // R2's fixed carried-state construction, not a learning/output-quality control.
        // Its reach on this chain remains an explicit assertion, never an assumed value.
        let receiver = field.receivers()[0].ring;
        let material = crate::hnn::tests::learning::generic_within(&field, 81, budget)
            .with_ports(
                receiver,
                None,
                None,
                Some(
                    ExactRatMatrix::zero(2 * field.alphabet(), field.ring(receiver).width())
                        .unwrap(),
                ),
            )
            .unwrap();
        let scale = source_scale.unwrap();
        let source = material
            .source_port(0)
            .expect("ring 0 carries the class source")
            .clone();
        let rows = (0..source.rows())
            .map(|i| {
                (0..source.columns())
                    .map(|j| source.get(i, j).unwrap() * scale)
                    .collect()
            })
            .collect();
        let material = material
            .with_ports(
                0,
                None,
                Some(ExactRatMatrix::shaped(source.rows(), source.columns(), rows).unwrap()),
                None,
            )
            .unwrap();
        reference
            .mount_with(&field, &Current::at_rest(&field), material)
            .unwrap()
    } else {
        reference.mount(&field, &Current::at_rest(&field)).unwrap()
    };
    resident.open_founding().unwrap();
    let prefix = (0..128).map(|k| [0, 0, 1, 0, 2][k % 5]).collect::<Vec<_>>();
    let mut at = 0;
    let mut moment = None;
    while at < prefix.len() {
        let encoded = crate::hnn::tests::support::encoded(&field, &prefix[at..]);
        let (id, returned) = reference
            .ingest(&mut resident, moment.as_ref(), &encoded)
            .unwrap();
        let ingested = returned.forward.present().unwrap();
        at += ingested.cells;
        moment = Some(id);
        if ingested.carry_out {
            let phases = resident.admitted.clone();
            reference.close_aeon(&mut resident, &phases).unwrap();
        }
    }
    assert_eq!(resident.founding.as_ref().unwrap().cells(), 128);
    assert_eq!(resident.read_founding().unwrap().founded, Some(5));
    assert_eq!(resident.staged_founding, Some(5));
    assert_eq!(resident.read_founding().unwrap().founded, None);
    (reference, resident, moment.unwrap())
}

#[test]
fn r4b_saved_state_names_its_open_founding_law() {
    // The predicate a realization without the founding law reads before it resumes a state.
    let mut declaration = crate::hnn::tests::learning::chain_declaration(1 << 16);
    declaration.founding = true;
    let field = Field::declare(declaration).unwrap();
    let reference = Reference::new(4, 1 << 40);
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    assert!(!resident.continuing_state(0).unwrap().founding_open());
    resident.open_founding().unwrap();
    assert!(resident.continuing_state(0).unwrap().founding_open());
    let (_, mut staged, _) = fixture(1 << 40);
    assert!(staged.continuing_state(0).unwrap().founding_open());
    staged.publish_founding().unwrap().unwrap();
    // The published field's law reopens empty for the next founding, and is still carried.
    assert!(staged.continuing_state(0).unwrap().founding_open());
}

#[test]
fn r4b_14_publication_refusals_keep_the_complete_resident_and_staging() {
    let (reference, mut pending, moment) = fixture(1 << 40);
    let phases = pending.admitted[0].clone();
    let (id, _) = reference.refine(&mut pending, &moment, &phases).unwrap();
    // The Debug face omits a mode view's rotor bindings; the ratios' own equality reads them.
    let ratios = |resident: &Resident| {
        resident
            .pending
            .values()
            .map(|slot| slot.ratio.clone())
            .collect::<Vec<_>>()
    };
    let held = ratios(&pending);
    let before = format!("{pending:?}");
    assert!(pending.publish_founding().is_err());
    assert_eq!(format!("{pending:?}"), before);
    assert_eq!(ratios(&pending), held);
    assert_eq!(pending.staged_founding, Some(5));
    let targets = crate::hnn::tests::support::encoded(&pending.field, &vec![0; phases.aperture()]);
    reference.compare(&mut pending, id, &targets).unwrap();
    let before = format!("{pending:?}");
    assert!(pending.publish_founding().is_err());
    assert_eq!(format!("{pending:?}"), before);
    assert_eq!(pending.staged_founding, Some(5));
    let (_, mut small, _) = fixture(1);
    let before = format!("{small:?}");
    assert!(matches!(
        small.publish_founding(),
        Err(HnnError::ConstitutionBudget { .. })
    ));
    assert_eq!(format!("{small:?}"), before);
    assert_eq!(small.staged_founding, Some(5));
    // A refusal at the last check, after the field, constitution, moments, address and arrived
    // read were all extended on the staged copy, keeps the resident whole too. The contact family
    // makes the address read the aeon's opening winding; one whole turn of ring 0 moved into the
    // opening is the disagreement.
    let (_, mut late, _) = fixture_with_family(1 << 40, true);
    let turn = BigInt::from(late.field.ring(0).period());
    late.aeon.opening[0] += turn;
    let (field, constitution) = (late.field.clone(), late.constitution.clone());
    let before = format!("{late:?}");
    let refused = late.publish_founding();
    assert!(
        matches!(
            refused,
            Err(HnnError::Founding {
                what: "the extended address and current disagree"
            })
        ),
        "{refused:?}"
    );
    assert_eq!(format!("{late:?}"), before);
    assert_eq!(late.field, field);
    assert_eq!(late.constitution, constitution);
    assert_eq!(late.staged_founding, Some(5));
}

#[test]
fn r4b_15_next_cell_reaches_the_phase_the_founding_evidence_binned() {
    let (reference, mut resident, moment) = fixture(1 << 40);
    let n = resident.founding.as_ref().unwrap().cells();
    let founded = resident.publish_founding().unwrap().unwrap();
    assert_eq!(
        founded,
        FoundedRing {
            period: 5,
            key: (n - 1) % 5
        }
    );
    assert_eq!(resident.staged_founding, None);
    assert_eq!(resident.founding.as_ref().unwrap().cells(), 0);
    resident.admit_exact_current().unwrap();
    let cell = crate::hnn::tests::support::encoded(&resident.field, &[3]);
    reference
        .ingest(&mut resident, Some(&moment), &cell)
        .unwrap();
    let source = resident.moments.get(&moment).unwrap();
    for phase in 0..5 {
        assert_eq!(
            source.phase_counts(3, phase).unwrap().iter().sum::<u64>(),
            u64::from(phase as u64 == n % 5)
        );
    }
    assert_eq!(source.phase_counts(3, (n % 5) as usize).unwrap()[3], 1);
}

#[test]
fn r4b_16_save_and_continue_keeps_every_reading_and_rejects_the_old_field() {
    let (reference, mut direct, moment) = fixture(1 << 40);
    let old_field = direct.field.clone();
    direct.publish_founding().unwrap().unwrap();
    let state = direct.continuing_state(0).unwrap();
    let text = state.to_text();
    let parsed = ContinuingState::from_text(&text, direct.constitution().budget()).unwrap();
    assert_eq!(state, parsed);
    let field = direct.field.clone();
    let opening = Constitution::initial(&field, 1 << 40).unwrap();
    let mut mounted = reference
        .mount_continued(&field, &Current::at_rest(&field), opening, &parsed)
        .unwrap();
    assert_eq!(mounted.continuing_state(0).unwrap().to_text(), text);
    assert!(
        reference
            .mount_continued(
                &old_field,
                &Current::at_rest(&old_field),
                Constitution::initial(&old_field, 1 << 40).unwrap(),
                &parsed
            )
            .is_err()
    );
    for k in 0..256 {
        let cell = crate::hnn::tests::support::encoded(&field, &[[0, 0, 1, 0, 2][(128 + k) % 5]]);
        let a = reference.ingest(&mut direct, Some(&moment), &cell).unwrap();
        let b = reference
            .ingest(&mut mounted, Some(&moment), &cell)
            .unwrap();
        assert_eq!(a, b);
        if direct.aeon.awaiting {
            let phases = direct.admitted.clone();
            assert_eq!(
                reference.close_aeon(&mut direct, &phases).unwrap(),
                reference.close_aeon(&mut mounted, &phases).unwrap()
            );
        }
        assert_eq!(direct.current, mounted.current);
        assert_eq!(direct.constitution, mounted.constitution);
        assert_eq!(direct.founding, mounted.founding);
        assert_eq!(
            direct.read_founding().unwrap(),
            mounted.read_founding().unwrap()
        );
        assert_eq!(
            direct.continuing_state(0).unwrap().to_text(),
            mounted.continuing_state(0).unwrap().to_text()
        );
    }
}

#[test]
fn r4b_17_publication_keeps_all_old_motion_and_never_coarsens_the_word() {
    let (reference, mut resident, moment) = fixture(1 << 40);
    let phases = resident.admitted[0].clone();
    let (id, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    reference
        .discard(&mut resident, Handle::Pending(id))
        .unwrap();
    let before = resident
        .carried
        .clone()
        .expect("the actual refine carries its end");
    let old_word = *resident.field.word_lattice().unwrap();
    let tally = resident.tally.clone();
    let old_field = resident.field.clone();
    let old_current = resident.current.clone();
    resident.publish_founding().unwrap().unwrap();
    let after = resident.carried.as_ref().unwrap();
    assert_eq!(after.ticks, before.ticks);
    assert_eq!(&after.change.storage[..3], before.change.storage);
    assert_eq!(&after.change.arrivals[..2], before.change.arrivals);
    assert_eq!(&after.change.states[..2], before.change.states);
    assert_eq!(&after.change.resonators[..3], before.change.resonators);
    assert_eq!(
        &after.change.resonator_phases[..3],
        before.change.resonator_phases
    );
    assert_eq!(&after.conductances[..2], before.conductances);
    assert_eq!(&after.momenta[..2], before.momenta);
    assert_eq!(&after.resonator_momenta[..3], before.resonator_momenta);
    let expected_phase = resident
        .constitution
        .ring_resonator(3)
        .unwrap()
        .pump()
        .unwrap()
        .phase_at(before.ticks.saturating_sub(1));
    assert!(after.change.storage[3].iter().all(Zero::is_zero));
    assert_eq!(after.change.resonator_phases[3], Some(expected_phase));
    assert!(
        after.change.resonators[3]
            .as_ref()
            .unwrap()
            .iter()
            .flatten()
            .all(Zero::is_zero)
    );
    assert_eq!(&resident.current.lift()[..3], old_current.lift());
    assert_eq!(resident.tally, tally);
    let word = resident.field.word_lattice().unwrap();
    assert!(word.chart_exponent() >= old_word.chart_exponent());
    assert!(word.target_exponent() >= old_word.target_exponent());
    assert!(word.transient_exponent() >= old_word.transient_exponent());
    assert_eq!(&resident.field.rings()[..3], old_field.rings());
}

#[test]
fn r4b_ingest_refusal_does_not_receive_a_founding_cell() {
    let (reference, mut resident, _) = fixture(1 << 40);
    let law = resident.founding.clone();
    let cell = crate::hnn::tests::support::encoded(&resident.field, &[0]);
    assert!(
        reference
            .ingest(&mut resident, Some(&MomentId(u64::MAX)), &cell)
            .is_err()
    );
    assert_eq!(resident.founding, law);
    assert!(resident.open_founding().is_err());
}

#[test]
fn r4b_contact_family_and_arrived_restore_on_the_founded_field_only() {
    let (reference, mut resident, moment) = fixture_with_family(1 << 40, true);
    let old_field = resident.field.clone();
    // Keep the first-law operand so the saved arrived address crosses the same field change.
    let phases = resident.admitted[0].clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let targets = crate::hnn::tests::support::encoded(&resident.field, &vec![0; phases.aperture()]);
    let (staged, _) = reference.compare(&mut resident, pending, &targets).unwrap();
    reference
        .discard(&mut resident, Handle::Staged(staged))
        .unwrap();
    let letters = resident.address.letters().to_vec();
    let founded = resident.publish_founding().unwrap().unwrap();
    assert_eq!(resident.address.letters(), letters);
    assert!(resident.address.reader().agrees(
        &resident.field,
        &resident.current,
        &resident.aeon.opening
    ));
    assert_eq!(
        resident.current.phase(&resident.field, 3).unwrap(),
        founded.key
    );
    let state = resident.continuing_state(0).unwrap();
    let text = state.to_text();
    let parsed = ContinuingState::from_text(&text, resident.constitution().budget()).unwrap();
    let opening = Constitution::initial(&resident.field, 1 << 40).unwrap();
    let restored = reference
        .mount_continued(
            &resident.field,
            &Current::at_rest(&resident.field),
            opening,
            &parsed,
        )
        .unwrap();
    assert_eq!(restored.continuing_state(0).unwrap().to_text(), text);
    assert_eq!(restored.address, resident.address);
    let restored_arrived = restored.arrived.as_ref().unwrap();
    let arrived = resident.arrived.as_ref().unwrap();
    // The producing receiver's phases are carried inside the ratio (`PendingRatio`), so the
    // ratio's equality covers them.
    assert_eq!(restored_arrived.ratio, arrived.ratio);
    assert_eq!(restored_arrived.opening, arrived.opening);
    assert_eq!(restored_arrived.targets, arrived.targets);
    assert!(
        reference
            .mount_continued(
                &old_field,
                &Current::at_rest(&old_field),
                Constitution::initial(&old_field, 1 << 40).unwrap(),
                &parsed
            )
            .is_err()
    );
}

fn arrived_features(resident: &Resident) -> Vec<Vec<Rat>> {
    let arrived = resident.arrived.as_ref().unwrap();
    let (word, _) = arrived
        .ratio
        .read_successor_against_on(
            &resident.field,
            &resident.constitution,
            &mut resident.charts.clone(),
            &arrived.targets,
            &arrived.opening,
        )
        .unwrap();
    word.receiving_anchors(arrived.ratio.phases()).unwrap()
}

/// The carried-state fixture at `source_scale`, its arrived operand read twice and then carried
/// across one founding publication, with the publication's ledger exchange checked; returns the
/// ledger balance before the founding.
fn arrived_across_founding(
    source_scale: &Rat,
) -> (Reference, Resident, MomentId, crate::aeon::EnclosedBalance) {
    let (reference, mut resident, moment) =
        fixture_with_material(1 << 40, false, Some(source_scale));
    let phases = &resident.admitted[0];
    let contact =
        crate::hnn::propagation::contact_exponent(&resident.field, 0, resident.current.lift())
            .unwrap();
    assert_eq!(contact.quadrance, crate::ratio::integer(4));
    assert_eq!(contact.exponent, crate::ratio::integer(-4));
    let path = path_attenuation(
        &resident.field,
        resident.current.lift(),
        phases.ring(),
        phases.last_epoch(),
        phases.grain(),
    )
    .unwrap();
    assert_eq!(path.exponent, crate::ratio::integer(4));
    assert!(
        path.open,
        "the fixture's declared path must be open at its receiver grain"
    );
    for _ in 0..2 {
        let phases = resident.admitted[0].clone();
        let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
        let targets =
            crate::hnn::tests::support::encoded(&resident.field, &vec![0; phases.aperture()]);
        let (staged, _) = reference.compare(&mut resident, pending, &targets).unwrap();
        reference
            .discard(&mut resident, Handle::Staged(staged))
            .unwrap();
    }
    assert!(matches!(
        resident.arrived.as_ref().unwrap().opening,
        WordOpening::Received { .. }
    ));
    assert!(
        arrived_features(&resident)
            .iter()
            .flatten()
            .any(|x| !x.is_zero()),
        "the actual pre-founding arrived operand must reach a nonzero feature"
    );
    let before = resident.ledger.balance().clone();
    resident.publish_founding().unwrap().unwrap();
    let arrived = resident.arrived.as_ref().unwrap();
    let reread = arrived
        .code_length(
            &resident.field,
            &resident.constitution,
            &mut resident.charts.clone(),
        )
        .unwrap()
        .0;
    let after = resident.ledger.balance();
    assert_eq!(after.closing.as_ref(), Some(&reread));
    assert_eq!(after.exchanges, before.exchanges + 1);
    assert_eq!(
        (after.arrivals, after.cells),
        (before.arrivals, before.cells)
    );
    let old = before.closing.as_ref().unwrap();
    let step = ExactInterval {
        lower: &reread.lower - &old.upper,
        upper: &reread.upper - &old.lower,
    };
    assert_eq!(after.exchange.lower, &before.exchange.lower + &step.lower);
    assert_eq!(after.exchange.upper, &before.exchange.upper + &step.upper);
    println!(
        "r4b_founding_exchange lower={} upper={} arrivals={} cells={} exchanges={}",
        step.lower, step.upper, after.arrivals, after.cells, after.exchanges
    );
    assert_eq!(after.total().lower, after.change().lower - &after.widening);
    assert_eq!(after.total().upper, after.change().upper + &after.widening);

    (reference, resident, moment, before)
}

#[test]
fn r4b_arrived_crosses_the_founding_then_precision_and_collapse() {
    // A receiving precision event refines only a read strictly above the receiver's grain
    // `1/(2 L_R)`, and within the lattice rule none is (REQ-056). As 056's publication fixture
    // does, the source map's scale is found by doubling from one and re-reading the real word
    // after the founding, until the seeded quarter-unit remainder's read lies above the grain.
    // Each doubling must widen the reach; the declared budget bounds the scaled material (the
    // mount refuses past it), so the search ends at a read or at that refusal.
    let mut source_scale = Rat::one();
    let mut previous = Rat::zero();
    let (reference, mut resident, moment, before) = loop {
        let (reference, resident, moment, before) = arrived_across_founding(&source_scale);
        let receiver = resident.field.receivers()[0].ring;
        let unit = resident
            .constitution
            .lattice(Locus::ReceivingMap(receiver))
            .unwrap()
            .unit();
        let grain = Rat::new(
            BigInt::one(),
            BigInt::from(
                crate::hnn::field::receiver_grain(&resident.field.receivers()[0].tolerance)
                    .unwrap(),
            ) << 1usize,
        );
        let reached = arrived_features(&resident)
            .iter()
            .flatten()
            .map(|x| x.abs())
            .max()
            .unwrap();
        if &unit / crate::ratio::integer(4) * &reached > grain {
            break (reference, resident, moment, before);
        }
        assert!(
            reached > previous,
            "source scale {source_scale} widens no reach ({reached}, grain {grain})"
        );
        previous = reached;
        source_scale *= crate::ratio::integer(2);
    };
    println!("r4b_founding_source_scale {source_scale}");

    // As in R2's fixed carried-state control, seed a legal retained remainder in a zero map.
    // This witnesses transport/accounting, not production of the remainder by learning.
    let receiver = resident.field.receivers()[0].ring;
    let features = arrived_features(&resident);
    // The largest reached feature, the one the scale above was found for.
    let (phase, column) = features
        .iter()
        .enumerate()
        .flat_map(|(phase, feature)| (0..feature.len()).map(move |column| (phase, column)))
        .max_by(|&(p, c), &(q, d)| features[p][c].abs().cmp(&features[q][d].abs()))
        .expect("the receiving word must reach a feature");
    let unit = resident
        .constitution
        .lattice(Locus::ReceivingMap(receiver))
        .unwrap()
        .unit();
    let retained = if features[phase][column] > Rat::zero() {
        -&unit / crate::ratio::integer(4)
    } else {
        &unit / crate::ratio::integer(4)
    };
    let mut text = resident.constitution.continuing_state(0).unwrap().to_text();
    let start = text
        .find(&format!(
            "receiving {} {}\n",
            2 * resident.field.alphabet(),
            resident.field.ring(receiver).width()
        ))
        .unwrap();
    let at = start + text[start..].find("map-carry 0\n").unwrap();
    text.replace_range(
        at..at + "map-carry 0\n".len(),
        &format!("map-carry 1\n{column} {retained}\n"),
    );
    // A quarter unit needs precision 2 on the receiving clock; gamma_length(2) = 3, and
    // gamma_length(1) = 1 carries only the half cell.
    super::precision_publication_tests::receiving_carry_clock(&mut text, receiver, 2);
    let opening = resident.constitution.clone();
    let text = ContinuingState::stamped(&text, &opening).unwrap();
    resident.constitution = opening
        .continued(&ContinuingState::from_text(&text, resident.constitution().budget()).unwrap())
        .unwrap();
    let event = resident
        .constitution
        .receiving_precision_event(
            receiver,
            &arrived_features(&resident),
            &resident.field.receivers()[0].tolerance,
        )
        .unwrap()
        .expect("the retained component must need precision");
    resident.publish_receiving_precision(&event).unwrap();
    assert_eq!(
        resident.ledger.balance().publications,
        before.publications + 1
    );
    let now = resident
        .arrived
        .as_ref()
        .unwrap()
        .code_length(
            &resident.field,
            &resident.constitution,
            &mut resident.charts.clone(),
        )
        .unwrap()
        .0;
    assert_eq!(resident.ledger.balance().closing.as_ref(), Some(&now));
    let cells = crate::hnn::tests::support::encoded(&resident.field, &[0; 16]);
    assert!(
        reference
            .ingest(&mut resident, Some(&moment), &cells)
            .unwrap()
            .1
            .forward
            .present()
            .unwrap()
            .carry_out
    );
    let phases = resident.admitted.clone();
    reference.close_aeon(&mut resident, &phases).unwrap();
    resident
        .arrived
        .as_ref()
        .unwrap()
        .code_length(
            &resident.field,
            &resident.constitution,
            &mut resident.charts.clone(),
        )
        .unwrap();
}

/// [the #398 review] **A founded `Own` source builds no resident pair face.** Its counts open
/// leaky at the founding modulus (`SourceMoment::found_ring`), and REQ-055's face holds only
/// unit-modulus counts, so the founded ring's pair read stays the transported whole-table read.
/// The `Lock` sources' faces are read on the retained moment before the pending ratio copies
/// it, and a second refine at the same reads builds none.
#[test]
fn r4b_founded_own_source_keeps_the_transported_pair_read() {
    let (reference, mut resident, moment) = fixture(1 << 40);
    resident.publish_founding().unwrap().unwrap();
    let own = resident.field.rings().len() - 1;
    assert_eq!(
        resident.field.ring(own).advance(),
        crate::hnn::RingAdvance::Own
    );
    assert!(resident.field.is_source(own));
    let phases = resident.admitted[0].clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    reference
        .discard(&mut resident, Handle::Pending(pending))
        .unwrap();
    let source = resident.moments.get(&moment).unwrap();
    let (mut own_ports, mut lock_faces) = (0, 0);
    for &ring in resident.field.sources() {
        for &offset in resident.field.offsets() {
            let Some(port) = resident.constitution.pair_port(ring, offset) else {
                continue;
            };
            let face = source.resident_pair_face(ring, offset, port).unwrap();
            if ring == own {
                assert!(
                    face.is_none(),
                    "offset {offset}: a leaky count builds no face"
                );
                assert_eq!(source.pair_face_read_matches(ring, offset, port), None);
                own_ports += 1;
            } else {
                assert!(face.is_some(), "ring {ring} offset {offset}: a Lock face");
                assert_eq!(
                    source.pair_face_read_matches(ring, offset, port),
                    Some(true)
                );
                lock_faces += 1;
            }
        }
    }
    assert!(own_ports > 0 && lock_faces > 0);
    let builds = source.pair_face_total_builds();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    reference
        .discard(&mut resident, Handle::Pending(pending))
        .unwrap();
    assert_eq!(
        resident
            .moments
            .get(&moment)
            .unwrap()
            .pair_face_total_builds(),
        builds
    );
}
