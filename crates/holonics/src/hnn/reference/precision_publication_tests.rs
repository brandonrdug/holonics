//! Fixed carried-state controls for publication accounting, not a learning/output-quality gate.
use super::*;
use crate::hnn::constitution::{ContinuingState, Lattice};
use crate::hnn::tests::{learning, support};
use crate::ratio::integer;

fn difference(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower - &b.upper,
        upper: &a.upper - &b.lower,
    }
}

/// A seeded remainder must lie on the native fine lattice of its declared clock.
/// This constructs an explicit carried-state control; it does not claim a learning history.
pub(super) fn receiving_carry_clock(text: &mut String, ring: usize, clock: u64) {
    let start = text.find("\nclocks ").unwrap() + 1;
    let head_end = start + text[start..].find('\n').unwrap();
    let count: usize = text[start..head_end]
        .strip_prefix("clocks ")
        .unwrap()
        .parse()
        .unwrap();
    let entries_start = head_end + 1;
    let mut entries: Vec<_> = text[entries_start..]
        .lines()
        .take(count)
        .map(str::to_owned)
        .collect();
    let end = entries_start + entries.iter().map(|line| line.len() + 1).sum::<usize>();
    let prefix = format!("receiving {ring} ");
    let line = format!("{prefix}{clock}");
    match entries.iter_mut().find(|entry| entry.starts_with(&prefix)) {
        Some(entry) => *entry = line,
        None => entries.push(line),
    }
    text.replace_range(
        start..end,
        &format!("clocks {}\n{}\n", entries.len(), entries.join("\n")),
    );
}

fn features(resident: &Resident) -> Vec<Vec<Rat>> {
    let arrived = resident.arrived.as_ref().unwrap();
    let mut charts = resident.charts.clone();
    let (word, _) = arrived
        .ratio
        .read_successor_against_on(
            &resident.field,
            &resident.constitution,
            &mut charts,
            &arrived.targets,
            &arrived.opening,
        )
        .unwrap();
    word.receiving_anchors(arrived.ratio.phases()).unwrap()
}

fn compare(reference: &Reference, resident: &mut Resident, moment: MomentId) -> ExactInterval {
    let phases = resident.admitted[0].clone();
    let (pending, _) = reference.refine(resident, &moment, &phases).unwrap();
    let target = support::encoded(&resident.field, &[0]);
    let (staged, result) = reference.compare(resident, pending, &target).unwrap();
    let ReceiptDetail::Compare { code_length, .. } = &result.receipt.detail else {
        panic!("comparison receipt")
    };
    let code = code_length.clone();
    reference.discard(resident, Handle::Staged(staged)).unwrap();
    code
}

/// Seed a legal sub-lattice remainder in a zero row, opposing the reached feature so its
/// promotion crosses the receiver's zero grain boundary. The orientation uses no target.
/// The fixture witnesses accounting of retained mass, not production of that mass by learning.
fn fixture() -> (Reference, Resident, MomentId, ReceivingPrecision) {
    fixture_with_budget(1 << 40)
}

fn fixture_with_budget(budget: u64) -> (Reference, Resident, MomentId, ReceivingPrecision) {
    let field = support::small_field(&[2], vec![], 0);
    let reference = Reference::new(64, budget);
    let width = field.ring(0).width();
    let unscaled = learning::generic_within(&field, 81, budget)
        .with_ports(
            0,
            None,
            None,
            Some(ExactRatMatrix::zero(2 * field.alphabet(), width).unwrap()),
        )
        .unwrap();
    let unit = Lattice::new(unscaled.lattice(Locus::ReceivingMap(0)).unwrap().exponent()).unit();
    let grain = Rat::new(
        num_bigint::BigInt::from(1),
        num_bigint::BigInt::from(crate::hnn::field::receiver_grain(
            &field.receivers()[0].tolerance,
        )) << 1usize,
    );
    let source = unscaled.source_port(0).unwrap().clone();
    let mut source_scale = Rat::one();
    let (founding, reached, column) = loop {
        let rows = (0..source.rows())
            .map(|i| {
                (0..source.columns())
                    .map(|j| source.get(i, j).unwrap() * &source_scale)
                    .collect()
            })
            .collect();
        let founding = unscaled
            .clone()
            .with_ports(
                0,
                None,
                Some(ExactRatMatrix::shaped(source.rows(), source.columns(), rows).unwrap()),
                None,
            )
            .unwrap();
        eprintln!("publication fixture: actual-word pilot at source scale {source_scale}");
        let mut pilot = reference
            .mount_with(&field, &Current::at_rest(&field), founding.clone())
            .unwrap();
        let (moment, _) = reference
            .ingest(&mut pilot, None, &support::encoded(&field, &[0]))
            .unwrap();
        compare(&reference, &mut pilot, moment);
        compare(&reference, &mut pilot, moment);
        let reached = features(&pilot);
        let column = reached[0]
            .iter()
            .enumerate()
            .max_by(|(_, a), (_, b)| a.abs().cmp(&b.abs()))
            .map(|(column, _)| column)
            .expect("a receiving feature");
        let retained_read = &unit / integer(4) * reached[0][column].abs();
        let norm: Rat = reached[0].iter().map(|x| x.abs()).sum();
        let declared_bound = Rat::from_integer(num_bigint::BigInt::from(width));
        eprintln!(
            "publication fixture: scale={source_scale} feature_l1={norm} X={declared_bound} retained_read={retained_read} grain={grain}"
        );
        if retained_read > grain && norm > declared_bound {
            break (founding, reached, column);
        }
        source_scale *= integer(2);
    };
    let retained = if reached[0][column] > Rat::zero() {
        -&unit / integer(4)
    } else {
        &unit / integer(4)
    };
    let mut text = founding.continuing_state(0).unwrap().to_text();
    let start = text
        .find(&format!("receiving {} {}\n", 2 * field.alphabet(), width))
        .unwrap();
    let at = start + text[start..].find("map-carry 0\n").unwrap();
    text.replace_range(
        at..at + "map-carry 0\n".len(),
        &format!("map-carry 1\n{column} {retained}\n"),
    );
    let at = start + text[start..].find("gram-carry 0\n").unwrap();
    text.replace_range(
        at..at + "gram-carry 0\n".len(),
        &format!("gram-carry 1\n0 {}\n", &unit / integer(8)),
    );
    // unit/8 needs precision 3; gamma_length(2) = 3.
    receiving_carry_clock(&mut text, 0, 2);
    let text = ContinuingState::stamped(&text, &founding).unwrap();
    let state = ContinuingState::from_text(&text).unwrap();
    let theta = founding.continued(&state).unwrap();
    let mut resident = reference
        .mount_with(&field, &Current::at_rest(&field), theta)
        .unwrap();
    let (moment, _) = reference
        .ingest(&mut resident, None, &support::encoded(&field, &[0]))
        .unwrap();
    compare(&reference, &mut resident, moment);
    compare(&reference, &mut resident, moment);
    assert!(!matches!(
        resident.arrived.as_ref().unwrap().opening,
        WordOpening::Rest
    ));
    let reached = features(&resident);
    let feature_l1: Rat = reached[0].iter().map(|x| x.abs()).sum();
    assert!(feature_l1 > Rat::from_integer(num_bigint::BigInt::from(width)));
    let retained_reads = resident
        .constitution
        .receiving_law(0)
        .unwrap()
        .map_remainder()
        .apply(&reached[0])
        .unwrap();
    assert!(retained_reads[0].abs() > grain);
    let event = resident
        .constitution
        .receiving_precision_event(0, &reached, &field.receivers()[0].tolerance)
        .unwrap()
        .unwrap();
    assert!(resident.carried.is_some());
    assert!(!resident.aeon.awaiting);
    (reference, resident, moment, event)
}

fn fresh(resident: &Resident) -> ExactInterval {
    resident
        .arrived
        .as_ref()
        .unwrap()
        .code_length(
            &resident.field,
            &resident.constitution,
            &mut resident.charts.clone(),
        )
        .unwrap()
        .0
}

fn conserved(before: &Constitution, after: &Constitution) {
    let a = before.receiving_law(0).unwrap();
    let b = after.receiving_law(0).unwrap();
    for ((x, rx), (y, ry)) in a
        .map()
        .entries()
        .iter()
        .zip(a.map_remainder().entries())
        .zip(b.map().entries().iter().zip(b.map_remainder().entries()))
    {
        assert_eq!(x + rx, y + ry, "W + r_W");
    }
    for ((x, rx), (y, ry)) in a
        .gram()
        .entries()
        .iter()
        .zip(a.gram_remainder().entries())
        .zip(b.gram().entries().iter().zip(b.gram_remainder().entries()))
    {
        assert_eq!(x + rx, y + ry, "Gram + r_Gram");
    }
}

fn telescope(balance: &crate::aeon::EnclosedBalance) {
    assert_eq!(
        balance.total().lower,
        balance.change().lower - &balance.widening
    );
    assert_eq!(
        balance.total().upper,
        balance.change().upper + &balance.widening
    );
}

#[test]
fn receiving_precision_accounts_changed_face_with_open_moment_and_carry_then_closes() {
    let (reference, mut resident, moment, event) = fixture();
    let before = resident.clone();
    resident.publish_receiving_precision(&event).unwrap();
    let balance = resident.ledger.balance();
    let now = fresh(&resident); // BEFORE collapse: a later collapse may itself reread.
    assert_ne!(
        Some(&now),
        before.ledger.balance().closing.as_ref(),
        "promotion must change the scored face"
    );
    assert_eq!(balance.closing.as_ref(), Some(&now));
    assert_eq!(
        balance.published,
        difference(&now, before.ledger.balance().closing.as_ref().unwrap())
    );
    assert_eq!(balance.publications, 1);
    assert_eq!(balance.depositions, before.ledger.balance().depositions);
    assert_eq!(balance.exchange, before.ledger.balance().exchange);
    assert_eq!(balance.arrived, before.ledger.balance().arrived);
    assert_eq!(
        (balance.arrivals, balance.cells),
        (
            before.ledger.balance().arrivals,
            before.ledger.balance().cells
        )
    );
    assert_eq!(resident.current, before.current);
    assert_eq!(resident.moments, before.moments);
    assert_eq!(resident.address, before.address);
    assert_eq!(resident.carried, before.carried);
    assert_eq!(resident.admitted, before.admitted);
    assert_eq!(
        format!("{:?}", resident.arrived),
        format!("{:?}", before.arrived)
    );
    conserved(&before.constitution, &resident.constitution);
    telescope(balance);
    let saved = resident.continuing_state(0).unwrap();
    let saved = ContinuingState::from_text(&saved.to_text()).unwrap();
    let field = resident.field.clone();
    let mut cold = reference
        .mount_continued(
            &field,
            &Current::at_rest(&field),
            Constitution::initial(&field, 1 << 40).unwrap(),
            &saved,
        )
        .unwrap();
    let next = support::encoded(&field, &[0]);
    let warm_ingest = reference
        .ingest(&mut resident, Some(&moment), &next)
        .unwrap();
    assert!(warm_ingest.1.forward.present().unwrap().carry_out);
    assert_eq!(
        reference.ingest(&mut cold, Some(&moment), &next).unwrap(),
        warm_ingest
    );
    let phases = resident.admitted.clone();
    let closed = reference.close_aeon(&mut resident, &phases).unwrap();
    assert_eq!(reference.close_aeon(&mut cold, &phases).unwrap(), closed);
    let closed = &closed.forward.present().unwrap().first_law;
    assert_eq!(
        closed.published,
        difference(&now, before.ledger.balance().closing.as_ref().unwrap())
    );
    telescope(closed);
    assert_eq!(resident.ledger.balance().publications, 0);
    assert_eq!(resident.ledger.balance().closing, closed.closing);
    assert_eq!(
        resident.continuing_state(0).unwrap(),
        cold.continuing_state(0).unwrap()
    );
    assert_eq!(
        compare(&reference, &mut resident, moment),
        compare(&reference, &mut cold, moment)
    );
}

#[test]
fn receiving_precision_next_compare_exchanges_from_the_published_endpoint() {
    let (reference, mut resident, moment, event) = fixture();
    resident.publish_receiving_precision(&event).unwrap();
    let before = resident.ledger.balance().clone();
    let code = compare(&reference, &mut resident, moment);
    let after = resident.ledger.balance();
    assert_eq!(
        after.exchange,
        interval_sum(
            &before.exchange,
            &difference(&code, before.closing.as_ref().unwrap())
        )
        .unwrap()
    );
    assert_eq!(after.published, before.published);
    assert_eq!(after.publications, before.publications);
    telescope(after);
    let next = support::encoded(&resident.field, &[0]);
    reference
        .ingest(&mut resident, Some(&moment), &next)
        .unwrap();
    let phases = resident.admitted.clone();
    let closed = reference.close_aeon(&mut resident, &phases).unwrap();
    telescope(&closed.forward.present().unwrap().first_law);
}

#[test]
fn receiving_precision_refusals_leave_the_whole_resident_unchanged() {
    let (reference, resident, moment, event) = fixture();
    let unchanged = |resident: &mut Resident, event: &ReceivingPrecision| {
        let before = format!("{resident:?}");
        assert!(resident.publish_receiving_precision(event).is_err());
        assert_eq!(format!("{resident:?}"), before);
    };
    let mut missing = resident.clone();
    missing.arrived = None;
    assert!(matches!(
        missing.publish_receiving_precision(&event),
        Err(HnnError::PrecisionOccurrence {
            occurrence: true,
            arrived: false
        })
    ));
    unchanged(&mut missing, &event);
    let mut missing = resident.clone();
    missing.ledger = EnclosedLedger::new();
    unchanged(&mut missing, &event);
    let mut invalid_reread = resident.clone();
    invalid_reread.arrived.as_mut().unwrap().targets[0] = resident.field.alphabet();
    unchanged(&mut invalid_reread, &event);
    let mut pending = resident.clone();
    let phases = pending.admitted[0].clone();
    let (id, _) = reference.refine(&mut pending, &moment, &phases).unwrap();
    unchanged(&mut pending, &event);
    let target = support::encoded(&pending.field, &[0]);
    reference.compare(&mut pending, id, &target).unwrap();
    unchanged(&mut pending, &event);
    let mut stale = resident;
    stale.publish_receiving_precision(&event).unwrap();
    unchanged(&mut stale, &event);
}

#[test]
fn receiving_precision_without_an_occurrence_takes_no_accounting_step() {
    let (reference, resident, _, event) = fixture();
    let mut fresh = reference
        .mount_with(
            &resident.field,
            &Current::at_rest(&resident.field),
            resident.constitution.clone(),
        )
        .unwrap();
    let (moment, _) = reference
        .ingest(&mut fresh, None, &support::encoded(&resident.field, &[0]))
        .unwrap();
    let before = fresh.ledger.clone();
    let open = fresh.moment(&moment).unwrap().clone();
    fresh.publish_receiving_precision(&event).unwrap();
    assert_eq!(fresh.ledger, before);
    assert_eq!(fresh.moment(&moment), Some(&open));
    assert!(fresh.arrived.is_none());
}

#[test]
fn receiving_precision_budget_refusal_is_atomic() {
    let (_, resident, _, event) = fixture();
    let next = resident
        .constitution
        .rebased(
            Locus::ReceivingMap(0),
            event.levels(),
            &resident.retention(),
        )
        .unwrap();
    let budget = next.bits_within(&resident.retention()) - 1;
    assert!(
        budget >= resident.constitution.exact_bits(),
        "the carried fixture must fit while its refined chart does not"
    );
    let (_, mut limited, _, event) = fixture_with_budget(budget);
    let before = format!("{limited:?}");
    assert!(matches!(
        limited.publish_receiving_precision(&event),
        Err(HnnError::ConstitutionBudget { .. })
    ));
    assert_eq!(format!("{limited:?}"), before);
}

#[test]
fn receiving_precision_at_carry_out_accounts_before_immediate_close() {
    let (reference, mut resident, moment, event) = fixture();
    let next = support::encoded(&resident.field, &[0]);
    reference
        .ingest(&mut resident, Some(&moment), &next)
        .unwrap();
    assert!(resident.aeon.awaiting);
    resident.publish_receiving_precision(&event).unwrap();
    assert_eq!(resident.ledger.balance().closing, Some(fresh(&resident)));
    let published = resident.ledger.balance().published.clone();
    let phases = resident.admitted.clone();
    let closed = reference.close_aeon(&mut resident, &phases).unwrap();
    let balance = &closed.forward.present().unwrap().first_law;
    assert_eq!(balance.published, published);
    telescope(balance);
}
