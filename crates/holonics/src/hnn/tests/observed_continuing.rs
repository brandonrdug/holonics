//! Bounded host observed continuation, using the same source/learning/retention owners.
use super::learning::{OPEN_BUDGET, chain_declaration};
use crate::hnn::HnnError;
use crate::hnn::constitution::Constitution;
use crate::hnn::encoding::observed::PairedObservation;
use crate::hnn::encoding::placement::OccurrencePlacement;
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::paired::{PairedCarrier, PairingDeclaration};
use crate::hnn::port::{ExecutionPort, Handle, ReceiptDetail};
use crate::hnn::reference::observed::ObservedCrib;
use crate::hnn::reference::{ExposedResident, Reference, Resident};
use crate::ratio::integer;
use crate::ratio::linear::ExactRatMatrix;

fn fixture(aperture: usize) -> (Reference, Resident, PairingDeclaration) {
    fixture_population(aperture, 1 << 16)
}

fn fixture_population(
    aperture: usize,
    population: u64,
) -> (Reference, Resident, PairingDeclaration) {
    fixture_receiver(aperture, population, 2)
}

fn fixture_receiver(
    aperture: usize,
    population: u64,
    receiver: usize,
) -> (Reference, Resident, PairingDeclaration) {
    fixture_crib_offset(aperture, population, receiver, 1)
}

fn fixture_crib_offset(
    aperture: usize,
    population: u64,
    receiver: usize,
    crib_offset: usize,
) -> (Reference, Resident, PairingDeclaration) {
    // One predeclared population, independent of the content or its chunk lengths.
    let mut declaration = chain_declaration(population);
    declaration.receivers[0].aperture = aperture;
    declaration.receivers[0].ring = receiver;
    declaration.crib.offset = crib_offset;
    declaration.lattice.clear();
    let field = Field::declare(declaration.by_lattice_rule()).unwrap();
    let pairing = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
    };
    let free = ExactRatMatrix::shaped(
        8,
        4,
        (0..8)
            .map(|r| {
                (0..4)
                    .map(|c| integer(i64::from((r == 2 && c == 0) || (r == 3 && c == 2))))
                    .collect()
            })
            .collect(),
    )
    .unwrap();
    let port = PairedCarrier::complete_port(&field, 0, &pairing, &free).unwrap();
    let carrier = PairedCarrier::admit(&field, 0, &pairing, &port).unwrap();
    let material = Constitution::initial(&field, OPEN_BUDGET)
        .unwrap()
        .with_symmetric_source(0, port, carrier.symmetry())
        .unwrap();
    // A source-local control has a declared nonzero receiving map so its adjoint
    // reaches E immediately. The ordinary chain's receiving map is founded at zero.
    let material = if receiver == 0 {
        material
            .with_ports(0, None, None, Some(ExactRatMatrix::identity(8).unwrap()))
            .unwrap()
    } else {
        material
    };
    let reference = Reference::new(4, OPEN_BUDGET);
    let resident = reference
        .mount_with(&field, &Current::at_rest(&field), material)
        .unwrap();
    (reference, resident, pairing)
}

fn assert_continuing_admission_refuses(
    reference: &Reference,
    resident: &Resident,
    crib: &ObservedCrib,
    pairing: &PairingDeclaration,
    target: (usize, Option<&OccurrencePlacement>),
    expected: HnnError,
) {
    let before = format!("{resident:?}");
    let (class, placement) = target;
    for observed in [false, true] {
        let mut tried = resident.clone();
        let mut tried_crib = crib.clone();
        let refusal = if observed {
            reference
                .observe_cell_continuing(
                    &mut tried,
                    &mut tried_crib,
                    pairing,
                    class,
                    placement,
                    |_, _, _, _, _| panic!("admission must refuse before the observer"),
                )
                .map(|_| ())
        } else {
            reference
                .ingest_class_continuing(&mut tried, &mut tried_crib, pairing, class, placement)
                .map(|_| ())
        };
        assert_eq!(refusal.as_ref().unwrap_err(), &expected);
        assert_eq!(format!("{tried:?}"), before);
        assert_eq!(&tried_crib, crib);
    }
}

#[test]
fn observed_continuation_reencodes_the_same_cell_after_a_source_deposit() {
    // The aperture-one receiver shares the source ring so its return reaches E in this
    // one-tick fixture; the distant receiver's first short words need not change E.
    let (reference, mut resident, pairing) = fixture_receiver(1, 1 << 16, 0);
    let mut crib = ObservedCrib::new(0);
    reference
        .observe_cell_continuing(
            &mut resident,
            &mut crib,
            &pairing,
            0,
            None,
            |_, _, _, _, _| {},
        )
        .unwrap();
    let (field, _, _) = reference.read(&resident).unwrap();
    let stale = PairedObservation::admit(&field, resident.constitution(), &pairing)
        .unwrap()
        .encode(&[2])
        .unwrap();
    let before_port = resident.constitution().source_port(0).unwrap().clone();
    let receipt = reference
        .observe_cell_continuing(
            &mut resident,
            &mut crib,
            &pairing,
            2,
            None,
            |_, _, _, _, _| {},
        )
        .unwrap();
    assert_eq!(receipt.cells, 2);
    assert_ne!(
        resident.constitution().source_port(0).unwrap(),
        &before_port,
        "the fixture must actually change E, not merely reencode an unchanged boundary"
    );
    assert!(
        stale
            .check_observed_material(resident.constitution())
            .is_err()
    );
    let before = format!("{resident:?}");
    let (moment, _) = resident.continuing().unwrap();
    assert!(
        reference
            .ingest(&mut resident, Some(&moment), &stale)
            .is_err()
    );
    assert_eq!(
        format!("{resident:?}"),
        before,
        "all state is unchanged on stale refusal"
    );
    let source = resident.moment(&moment).unwrap();
    assert_eq!(source.cells(), 2);
    assert_eq!(source.phase_counts(0, 1).unwrap(), &[1, 0, 0, 0]);
    assert_eq!(source.phase_counts(0, 2).unwrap(), &[0, 0, 1, 0]);
}

#[test]
fn observed_continuation_two_external_chunks_equal_one_and_fork_leaves_trunk_exact() {
    let (reference, trunk, pairing) = fixture(1);
    let trunk_before = format!("{trunk:?}");
    let mut whole = trunk.clone();
    let mut split = trunk.clone();
    let mut whole_crib = ObservedCrib::new(0);
    let mut split_crib = ObservedCrib::new(0);
    let classes = [0, 2];
    let whole_receipts: Vec<_> = classes
        .iter()
        .map(|&class| {
            reference
                .observe_cell_continuing(
                    &mut whole,
                    &mut whole_crib,
                    &pairing,
                    class,
                    None,
                    |_, _, _, _, _| {},
                )
                .unwrap()
        })
        .collect();
    let mut split_receipts = Vec::new();
    for chunk in classes.chunks(1) {
        for &class in chunk {
            split_receipts.push(
                reference
                    .observe_cell_continuing(
                        &mut split,
                        &mut split_crib,
                        &pairing,
                        class,
                        None,
                        |_, _, _, _, _| {},
                    )
                    .unwrap(),
            );
        }
    }
    assert_eq!(whole_receipts, split_receipts);
    assert_eq!(whole.constitution(), split.constitution());
    assert_eq!(whole.current(), split.current());
    assert_eq!(whole.carried(), split.carried());
    assert_eq!(whole.charts(), split.charts());
    assert_eq!(whole.address(), split.address());
    assert_eq!(
        whole.continuing_state(0).unwrap(),
        split.continuing_state(0).unwrap()
    );
    assert_eq!(
        format!("{trunk:?}"),
        trunk_before,
        "fork changes no trunk state or caches"
    );
    let learned_trunk = format!("{whole:?}");
    let mut generation = whole.clone();
    let (moment, _) = generation.continuing().unwrap();
    let phases = generation.admitted()[0].clone();
    reference.refine(&mut generation, &moment, &phases).unwrap();
    assert_eq!(
        format!("{whole:?}"),
        learned_trunk,
        "a generation fork's carry, handles and chart reads never mutate its learned trunk"
    );
}

#[test]
fn observed_continuation_is_blind_and_preserves_occurrence_placement() {
    let (reference, trunk, pairing) = fixture(1);
    let (field, _, _) = reference.read(&trunk).unwrap();
    let mut a = trunk.clone();
    let mut b = trunk.clone();
    let mut a_crib = ObservedCrib::new(0);
    let mut b_crib = ObservedCrib::new(0);
    let placement = OccurrencePlacement::at(&field, trunk.current(), &[vec![1, 1, 1]]).unwrap();
    let ra = reference
        .observe_cell_continuing(
            &mut a,
            &mut a_crib,
            &pairing,
            0,
            Some(&placement),
            |_, _, _, _, _| {},
        )
        .unwrap();
    let rb = reference
        .observe_cell_continuing(&mut b, &mut b_crib, &pairing, 2, None, |_, _, _, _, _| {})
        .unwrap();
    assert_eq!(ra.prediction, rb.prediction);
    assert_eq!(
        ra.refine, rb.refine,
        "current target and placement cannot affect blind refine"
    );
    assert_eq!(a.current().lift(), placement.arrivals()[0]);
    let (moment, _) = a.continuing().unwrap();
    assert_eq!(
        a.moment(&moment).unwrap().phase_counts(0, 1).unwrap(),
        &[1, 0, 0, 0]
    );
    let before = format!("{a:?}");
    let before_crib = a_crib.clone();
    assert!(
        reference
            .observe_cell_continuing(
                &mut a,
                &mut a_crib,
                &pairing,
                0,
                Some(&placement),
                |_, _, _, _, _| {}
            )
            .is_err()
    );
    assert_eq!(
        format!("{a:?}"),
        before,
        "wrong opening cannot consume or deposit a cell"
    );
    assert_eq!(
        a_crib, before_crib,
        "wrong opening cannot alter the caller crib"
    );
}

#[test]
fn observed_continuation_refuses_wider_apertures_without_state_change() {
    let (reference, mut resident, pairing) = fixture(2);
    let mut crib = ObservedCrib::new(0);
    let before = format!("{resident:?}");
    assert!(
        reference
            .observe_cell_continuing(
                &mut resident,
                &mut crib,
                &pairing,
                0,
                None,
                |_, _, _, _, _| {}
            )
            .is_err()
    );
    assert_eq!(format!("{resident:?}"), before);
}

#[test]
fn observed_continuation_keeps_its_cumulative_count_across_joint_clock_closure() {
    use num_bigint::BigInt;
    let (reference, mounted, pairing) = fixture(1);
    let field = mounted.field();
    let opening = Current::at(
        field,
        field
            .rings()
            .iter()
            .map(|ring| BigInt::from(ring.period() - 1))
            .collect(),
    )
    .unwrap();
    let mut resident = reference
        .mount_with(field, &opening, mounted.constitution().clone())
        .unwrap();
    let mut crib = ObservedCrib::new(0);
    let first = reference
        .observe_cell_continuing(
            &mut resident,
            &mut crib,
            &pairing,
            0,
            None,
            |_, _, _, _, _| {},
        )
        .unwrap();
    assert!(first.close.is_some(), "the fixture crosses the joint clock");
    let (moment, aeon_cells) = resident.continuing().unwrap();
    assert_eq!(aeon_cells, 0);
    assert_eq!(resident.moment(&moment).unwrap().cells(), 1);
    let second = reference
        .observe_cell_continuing(
            &mut resident,
            &mut crib,
            &pairing,
            2,
            None,
            |_, _, _, _, _| {},
        )
        .unwrap();
    assert_eq!(second.cells, 2);
    assert_eq!(
        resident.continuing().unwrap().0,
        moment,
        "never discard and reopen"
    );
}

#[test]
fn observed_close_locates_on_exact_shared_crib() {
    use num_bigint::BigInt;
    let (reference, mounted, pairing) = fixture(1);
    let field = mounted.field().clone();
    let mut lift: Vec<_> = field
        .rings()
        .iter()
        .map(|ring| BigInt::from(ring.period() - 1))
        .collect();
    lift[0] = BigInt::from(1);
    let opening = Current::at(&field, lift).unwrap();
    let mut resident = reference
        .mount_with(&field, &opening, mounted.constitution().clone())
        .unwrap();
    let mut crib = ObservedCrib::new(0);
    let first = reference
        .observe_cell_continuing(
            &mut resident,
            &mut crib,
            &pairing,
            2,
            None,
            |_, _, _, _, _| {},
        )
        .unwrap();
    assert!(first.close.is_none());
    let placement = OccurrencePlacement::at(&field, resident.current(), &[vec![0, 0]]).unwrap();
    let mut closing_material = None;
    let second = reference
        .observe_cell_continuing(
            &mut resident,
            &mut crib,
            &pairing,
            0,
            Some(&placement),
            |_, material, _, _, _| closing_material = Some(material.clone()),
        )
        .unwrap();
    let closed = second
        .close
        .as_ref()
        .expect("the second cell closes the joint clock");
    assert_eq!(closed.crib_len, 2);
    assert_eq!(
        crate::hnn::reference::closing_crib(0, 2, field.crib().window, &[]),
        0..2
    );
    assert_eq!(crib.opening(), 2);
    assert_eq!(crib.next_position(), 2);
    assert!(crib.entries().is_empty());
    assert_eq!(
        resident
            .moment(&resident.continuing().unwrap().0)
            .unwrap()
            .cells(),
        2
    );
    let material = closing_material.expect("the observer sees the post-deposit material");
    let boundary = PairedObservation::admit(&field, &material, &pairing).unwrap();
    let placed =
        OccurrencePlacement::observed_crib(&field, &opening, &[(2, None), (0, Some(placement))])
            .unwrap();
    let encoded = boundary.encode_placed(&[2, 0], &placed).unwrap();
    let carry = Current::at(&field, closed.boundary.carry_out.clone()).unwrap();
    let located =
        crate::hnn::keys::locate_closing(&field, &carry, &encoded, field.crib().offset).unwrap();
    let expected_fibres: Vec<_> = located.rings.iter().map(|ring| ring.fibre.len()).collect();
    let expected_orbits: Vec<_> = located.rings.iter().map(|ring| ring.orbits).collect();
    let expected_fallback: Vec<_> = located.rings.iter().map(|ring| ring.fell_back).collect();
    let mut rekeyed = carry.clone();
    let expected_jumps = located.rekey(&field, &mut rekeyed).unwrap();
    assert_eq!(resident.current(), &rekeyed);
    let ReceiptDetail::Keys {
        fibres,
        orbits,
        fell_back,
        jumps,
        ..
    } = &closed.key.as_ref().unwrap().detail
    else {
        panic!("close did not return the key report")
    };
    assert_eq!(fibres, &expected_fibres);
    assert_eq!(orbits, &expected_orbits);
    assert_eq!(fell_back, &expected_fallback);
    assert!(fell_back[2], "the ring with an empty menu falls back on Ok");
    assert_eq!(jumps, &expected_jumps);
}

/// A malformed external crib is refused by the shared owner before it closes,
/// without a test port, staging in the test, or production injection.
#[test]
fn shared_close_refuses_foreign_field_crib_before_any_state_change() {
    use num_bigint::BigInt;
    let (reference, mounted, pairing) = fixture(1);
    let field = mounted.field().clone();
    let mut lift: Vec<_> = field
        .rings()
        .iter()
        .map(|ring| BigInt::from(ring.period() - 1))
        .collect();
    lift[0] = BigInt::from(field.ring(0).period() - 2);
    let opening = Current::at(&field, lift).unwrap();
    let mut resident = reference
        .mount_with(&field, &opening, mounted.constitution().clone())
        .unwrap();
    let mut crib = ObservedCrib::new(0);
    let first = reference
        .ingest_class_continuing(&mut resident, &mut crib, &pairing, 2, None)
        .unwrap();
    assert!(first.close.is_none());
    assert_eq!(crib.entries().len(), 1);
    // Put the real resident at its carry, before the owner has closed it.
    let observation = PairedObservation::admit(&field, resident.constitution(), &pairing).unwrap();
    let last = observation.encode(&[0]).unwrap();
    let moment = resident.continuing().unwrap().0;
    let (_, ingested) = reference
        .ingest(&mut resident, Some(&moment), &last)
        .unwrap();
    assert!(ingested.forward.into_present().unwrap().carry_out);

    let mut foreign = chain_declaration(field.population());
    foreign.rings[0] = super::support::ring(5, vec![0, 2]);
    foreign.lattice.clear();
    let foreign = Field::declare(foreign.by_lattice_rule()).unwrap();
    let encoded_crib = super::support::encoded(&foreign, &[2, 0]);
    assert!(encoded_crib.len() > field.crib().offset);
    let before = resident.continuing_state(0).unwrap().to_text();
    let before_debug = format!("{resident:?}");
    let before_crib = crib.clone();
    let admitted = resident.admitted().to_vec();
    let refusal = crate::hnn::reference::close_and_locate(
        &reference,
        &mut resident,
        &admitted,
        &encoded_crib,
    )
    .unwrap_err();
    assert!(matches!(
        refusal,
        crate::hnn::HnnError::Unadmitted {
            reason: "it was encoded against another field's source rings"
        }
    ));
    assert_eq!(resident.continuing_state(0).unwrap().to_text(), before);
    assert_eq!(format!("{resident:?}"), before_debug);
    assert_eq!(crib, before_crib);
}

#[test]
fn observed_continuation_refuses_past_the_predeclared_population_atomically() {
    let (_, opening, _) = fixture(1);
    let population = opening.field().capacity().n_star();
    let (reference, mut resident, pairing) = fixture_population(1, population);
    let mut crib = ObservedCrib::new(population as usize);
    let cell = PairedObservation::admit(resident.field(), resident.constitution(), &pairing)
        .unwrap()
        .encode(&[0])
        .unwrap();
    let mut moment = None;
    for _ in 0..population {
        let (id, fed) = reference
            .ingest(&mut resident, moment.as_ref(), &cell)
            .unwrap();
        moment = Some(id);
        if fed.forward.into_present().unwrap().carry_out {
            let family = resident.admitted().to_vec();
            reference.close_aeon(&mut resident, &family).unwrap();
        }
    }
    assert_eq!(
        resident.moment(&moment.unwrap()).unwrap().cells(),
        population
    );
    let before = format!("{resident:?}");
    let source_operand_bound = resident
        .field()
        .source_operand_bound(crate::hnn::constitution::Locus::SourcePort(0))
        .unwrap();
    assert_eq!(
        source_operand_bound,
        u128::from(population).max(resident.field().alphabet() as u128)
    );
    let before_crib = crib.clone();
    assert!(
        matches!(reference.observe_cell_continuing(&mut resident, &mut crib, &pairing, 2, None, |_, _, _, _, _| {}),
            Err(crate::hnn::HnnError::Horizon { population: p, source_operand_bound: b })
                if p == population && b == source_operand_bound)
    );
    assert_eq!(format!("{resident:?}"), before);
    assert_eq!(crib, before_crib, "horizon cannot alter the caller crib");
}

#[test]
fn observed_continuation_admits_crib_position_before_observer() {
    let (reference, mut resident, pairing) = fixture(1);
    let target = PairedObservation::admit(resident.field(), resident.constitution(), &pairing)
        .unwrap()
        .encode(&[0])
        .unwrap();
    reference.ingest(&mut resident, None, &target).unwrap();
    assert_continuing_admission_refuses(
        &reference,
        &resident,
        &ObservedCrib::new(0),
        &pairing,
        (2, None),
        HnnError::Shape {
            what: "the observed crib's position against the continuing moment",
            expected: 1,
            found: 0,
        },
    );
}

#[test]
fn observed_continuation_admits_awaiting_aeon_before_observer() {
    use num_bigint::BigInt;
    let (reference, mounted, pairing) = fixture(1);
    let field = mounted.field();
    let opening = Current::at(
        field,
        field
            .rings()
            .iter()
            .map(|ring| BigInt::from(ring.period() - 1))
            .collect(),
    )
    .unwrap();
    let mut resident = reference
        .mount_with(field, &opening, mounted.constitution().clone())
        .unwrap();
    let target = PairedObservation::admit(field, resident.constitution(), &pairing)
        .unwrap()
        .encode(&[0])
        .unwrap();
    let (_, fed) = reference.ingest(&mut resident, None, &target).unwrap();
    assert!(fed.forward.into_present().unwrap().carry_out);
    assert!(resident.awaiting_boundary());
    assert_continuing_admission_refuses(
        &reference,
        &resident,
        &ObservedCrib::new(1),
        &pairing,
        (2, None),
        HnnError::AeonAwaitingClose,
    );
}

#[test]
fn observed_continuation_admits_located_capacity_before_observer() {
    let (_, mounted, _) = fixture(1);
    let population = mounted.field().capacity().n_star();
    let (reference, resident, pairing) = fixture_population(1, population);
    let placement =
        OccurrencePlacement::at(resident.field(), resident.current(), &[vec![1, 1, 1]]).unwrap();
    let target = PairedObservation::admit(resident.field(), resident.constitution(), &pairing)
        .unwrap()
        .encode_placed(&[0], &placement)
        .unwrap();
    let expected = resident.field().capacity_for(&target).unwrap_err();
    assert!(matches!(
        &expected,
        HnnError::BelowCapacity { population: p, n_star } if *p == population && *n_star > population
    ));
    assert_continuing_admission_refuses(
        &reference,
        &resident,
        &ObservedCrib::new(0),
        &pairing,
        (0, Some(&placement)),
        expected,
    );
}

#[test]
fn continuing_paths_refuse_a_second_open_moment() {
    let (reference, mut resident, pairing) = fixture(1);
    let empty = PairedObservation::admit(resident.field(), resident.constitution(), &pairing)
        .unwrap()
        .encode(&[])
        .unwrap();
    let first = reference.ingest(&mut resident, None, &empty).unwrap().0;
    let second = reference.ingest(&mut resident, None, &empty).unwrap().0;
    assert_ne!(first, second);
    assert_eq!(reference.read(&resident).unwrap().2.len(), 2);
    assert_continuing_admission_refuses(
        &reference,
        &resident,
        &ObservedCrib::new(0),
        &pairing,
        (0, None),
        HnnError::Unadmitted {
            reason: "observed continuation requires at most one moment",
        },
    );
}

#[test]
fn observed_continuation_releases_observer_view_only_in_successful_receipt() {
    let (reference, mut resident, pairing) = fixture(1);
    let mut crib = ObservedCrib::new(0);
    // Moving a non-Copy value out of the closure requires only FnOnce.
    let marker = String::from("the committed cell's exterior view");
    let receipt = reference
        .observe_cell_continuing(
            &mut resident,
            &mut crib,
            &pairing,
            0,
            None,
            move |_, material, moment, _, _| (marker, material.commit(), moment.cells()),
        )
        .unwrap();
    assert_eq!(receipt.view.0, "the committed cell's exterior view");
    assert_eq!(receipt.view.1, receipt.ingestion_commit);
    assert_eq!(receipt.view.2, 0, "the view is read before ingestion");
    assert_eq!(receipt.cells, 1);
    assert_eq!(crib.next_position(), 1);
    let moment = resident.continuing().unwrap().0;
    assert_eq!(resident.moment(&moment).unwrap().cells(), receipt.cells);
    assert_eq!(resident.constitution().commit(), receipt.ingestion_commit);
}

#[test]
fn observed_continuation_drops_observer_view_on_later_location_refusal() {
    use num_bigint::BigInt;
    use std::cell::Cell;
    use std::rc::Rc;

    #[derive(Debug)]
    struct View(Rc<Cell<usize>>);
    impl Drop for View {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    let (reference, mounted, pairing) = fixture(1);
    let field = mounted.field();
    // This caller's crib has seen two cells in one still-open aeon.
    let mut other = mounted.clone();
    let mut crib = ObservedCrib::new(0);
    for _ in 0..2 {
        assert!(
            reference
                .ingest_class_continuing(&mut other, &mut crib, &pairing, 0, None)
                .unwrap()
                .close
                .is_none()
        );
    }
    let opening = Current::at(
        field,
        field
            .rings()
            .iter()
            .map(|ring| BigInt::from(ring.period() - 1))
            .collect(),
    )
    .unwrap();
    let mut resident = reference
        .mount_with(field, &opening, mounted.constitution().clone())
        .unwrap();
    let placed = OccurrencePlacement::at(field, &opening, &[vec![2, 0, 1]]).unwrap();
    let mut own_crib = ObservedCrib::new(0);
    let first = reference
        .ingest_class_continuing(&mut resident, &mut own_crib, &pairing, 0, Some(&placed))
        .unwrap();
    assert!(first.close.is_some(), "the placement closes the first aeon");
    let second = reference
        .ingest_class_continuing(&mut resident, &mut own_crib, &pairing, 0, None)
        .unwrap();
    assert!(second.close.is_none());
    assert_eq!(resident.continuing().unwrap().1, 1);
    assert_eq!(crib.next_position(), own_crib.next_position());
    // The positions agree, but the other crib spans an earlier aeon. Its three
    // closing cells exceed this resident's two-cell aeon only at key location.
    let before = format!("{resident:?}");
    let before_crib = crib.clone();
    let calls = Cell::new(0);
    let drops = Rc::new(Cell::new(0));
    let refusal = reference.observe_cell_continuing(
        &mut resident,
        &mut crib,
        &pairing,
        0,
        None,
        |_, _, _, _, _| {
            calls.set(calls.get() + 1);
            View(Rc::clone(&drops))
        },
    );
    assert!(matches!(
        refusal,
        Err(HnnError::Shape {
            what: "a closing crib's cells against the closed aeon's",
            expected: 2,
            found: 3,
        })
    ));
    assert_eq!(calls.get(), 1);
    assert_eq!(drops.get(), 1, "a refused cell cannot release its view");
    assert_eq!(format!("{resident:?}"), before);
    assert_eq!(crib, before_crib);
}

#[test]
fn shared_close_uses_its_fields_declared_crib_offset() {
    use num_bigint::BigInt;
    for offset in [1, 2] {
        let (reference, mounted, pairing) = fixture_crib_offset(1, 1 << 16, 2, offset);
        let field = mounted.field();
        let mut lift: Vec<_> = field
            .rings()
            .iter()
            .map(|ring| BigInt::from(ring.period() - 1))
            .collect();
        lift[0] = BigInt::from(field.ring(0).period() - 2);
        let opening = Current::at(field, lift).unwrap();
        let mut resident = reference
            .mount_with(field, &opening, mounted.constitution().clone())
            .unwrap();
        let crib = PairedObservation::admit(field, resident.constitution(), &pairing)
            .unwrap()
            .encode(&[2, 0])
            .unwrap();
        let (_, fed) = reference.ingest(&mut resident, None, &crib).unwrap();
        let fed = fed.forward.into_present().unwrap();
        assert_eq!(fed.cells, crib.len());
        assert!(fed.carry_out);
        let admitted = resident.admitted().to_vec();
        let closed =
            crate::hnn::reference::close_and_locate(&reference, &mut resident, &admitted, &crib)
                .unwrap();
        assert_eq!(closed.crib_len, 2);
        assert_eq!(closed.key.is_some(), crib.len() > offset);
        assert!(!resident.awaiting_boundary());
    }
}

/// G2: discarding every comparison's deposit must leave the same continuing
/// moment, address and answer-cell code as block ingestion of the question.
#[test]
fn discarded_cell_comparisons_equal_block_question_and_answer_codes() {
    fn one_without_deposit(
        reference: &Reference,
        resident: &mut Resident,
        pairing: &PairingDeclaration,
        class: usize,
    ) -> crate::ratio::algebraic::ExactInterval {
        let field = resident.field().clone();
        let observation =
            PairedObservation::admit(&field, resident.constitution(), pairing).unwrap();
        let moment = match resident.continuing() {
            Some((moment, _)) => moment,
            None => {
                reference
                    .ingest(resident, None, &observation.encode(&[]).unwrap())
                    .unwrap()
                    .0
            }
        };
        let phases = resident.admitted()[0].clone();
        let (pending, _) = reference.refine(resident, &moment, &phases).unwrap();
        let target = observation.encode(&[class]).unwrap();
        let (staged, compared) = reference.compare(resident, pending, &target).unwrap();
        let code = match compared.receipt.detail {
            ReceiptDetail::Compare { model, .. } => model[0].clone(),
            other => panic!("comparison returned {other:?}"),
        };
        reference.discard(resident, Handle::Staged(staged)).unwrap();
        let (_, ingested) = reference.ingest(resident, Some(&moment), &target).unwrap();
        let ingested = ingested.forward.into_present().unwrap();
        assert_eq!(ingested.cells, 1);
        assert!(!ingested.carry_out);
        code
    }

    let (reference, mounted, pairing) = fixture(1);
    let mut block = mounted.clone();
    let mut cells = mounted.clone();
    let question = [0, 2];
    let answer = [1, 3];
    let boundary = PairedObservation::admit(block.field(), block.constitution(), &pairing).unwrap();
    let (block_moment, fed) = reference
        .ingest(&mut block, None, &boundary.encode(&question).unwrap())
        .unwrap();
    let fed = fed.forward.into_present().unwrap();
    assert_eq!(fed.cells, question.len());
    assert!(!fed.carry_out);
    for class in question {
        one_without_deposit(&reference, &mut cells, &pairing, class);
    }
    let block_codes: Vec<_> = answer
        .iter()
        .map(|&class| one_without_deposit(&reference, &mut block, &pairing, class))
        .collect();
    let cell_codes: Vec<_> = answer
        .iter()
        .map(|&class| one_without_deposit(&reference, &mut cells, &pairing, class))
        .collect();
    assert_eq!(block_codes, cell_codes, "G2 answer-cell codes differ");
    assert_eq!(
        block.moment(&block_moment),
        cells.moment(&cells.continuing().unwrap().0),
        "G2 moments differ"
    );
    assert_eq!(block.address(), cells.address(), "G2 addresses differ");
}
