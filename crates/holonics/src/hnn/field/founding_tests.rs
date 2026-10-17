//! R4b's field expansion and clock/capacity controls (Refs #73 #62).
use super::*;

pub(crate) fn listener(places: usize, population: u64) -> FieldDeclaration {
    let classes = 16 * places;
    let periods = [classes as u64 + 1, 7, 11];
    let mut declaration = FieldDeclaration::campaign_one(population);
    declaration.rings = periods
        .iter()
        .enumerate()
        .map(|(g, &period)| RingDeclaration {
            period,
            screw: declaration.rings[0].screw.clone(),
            placements: (0..period)
                .map(|n| FieldDeclaration::quarter_turn(n, period))
                .collect(),
            lock: if g == 0 {
                (0..classes as u64).collect()
            } else {
                Vec::new()
            },
            reflector: (0..period)
                .map(|n| ((period - n) % period) as usize)
                .collect(),
            admittance: integer(2),
            initial: 0,
        })
        .collect();
    declaration.contacts = [(0, 1), (1, 2)]
        .iter()
        .map(|&(from, to)| ContactDeclaration {
            from,
            to,
            channel: (0..periods[from].min(periods[to]) as usize)
                .map(|n| (n, n))
                .collect(),
            admittance: integer(2),
            exponent: integer(2),
        })
        .collect();
    declaration.loops.clear();
    declaration.sources = vec![0];
    declaration.offsets = vec![1, 2];
    declaration.alphabet = classes;
    declaration.receivers[0].ring = 2;
    declaration.receivers[0].aperture = 1;
    declaration.receivers[0].depth = 6;
    declaration.receivers[0].tolerance = rat(1, classes as i64);
    declaration.founding = true;
    declaration.by_lattice_rule()
}

#[test]
fn r4b_08_expansion_matches_the_anchor_and_rules() {
    let base = Field::declare(listener(2, 1 << 16)).unwrap();
    assert_eq!(base.founding_anchor().unwrap(), (0, 1, 0));
    let expanded = base.found(FoundedRing { period: 2, key: 1 }).unwrap();
    assert_eq!(&expanded.rings()[..3], base.rings());
    assert_eq!(&expanded.contacts()[..2], base.contacts());
    let ring = expanded.ring(3);
    assert_eq!(ring.period(), 2);
    assert_eq!(ring.initial(), 1);
    assert_eq!(ring.advance(), RingAdvance::Own);
    assert_eq!(ring.screw(), base.ring(0).screw());
    assert_eq!(
        ring.placements(),
        &[
            FieldDeclaration::quarter_turn(0, 2),
            FieldDeclaration::quarter_turn(1, 2)
        ]
    );
    assert_eq!(ring.reflector().images(), &[0, 1]);
    assert_eq!(ring.admittance(), base.ring(0).admittance());
    assert!(ring.notches().is_empty());
    assert_eq!(expanded.sources(), &[0, 3]);
    assert_eq!(expanded.contact(2).ends(), (3, 1));
    assert_eq!(expanded.contact(2).channel(), &[(0, 0), (1, 1)]);
    assert_eq!(
        expanded.contact(2).admittance(),
        base.contact(0).admittance()
    );
    assert_eq!(expanded.contact(2).exponent(), base.contact(0).exponent());
    for (locus, lattice) in base.lattices() {
        assert_eq!(expanded.lattice(*locus), Some(*lattice));
    }
    let mut rule = expanded.declaration().clone();
    rule.rings.push(RingDeclaration {
        period: 2,
        screw: ring.screw().clone(),
        placements: ring.placements().to_vec(),
        lock: vec![],
        reflector: ring.reflector().images().to_vec(),
        admittance: ring.admittance().clone(),
        initial: 1,
    });
    rule.sources.push(3);
    rule.contacts.push(ContactDeclaration {
        from: 3,
        to: 1,
        channel: vec![(0, 0), (1, 1)],
        admittance: integer(2),
        exponent: integer(2),
    });
    for (locus, exponent) in rule.lattice_by_rule() {
        if !base.lattices().contains_key(&locus) {
            assert_eq!(expanded.lattice(locus).unwrap().exponent(), exponent);
        }
    }
    let old = base.word_lattice().unwrap();
    let next = expanded.word_lattice().unwrap();
    assert!(next.chart_exponent() >= old.chart_exponent());
    assert!(next.target_exponent() >= old.target_exponent());
    assert!(next.transient_exponent() >= old.transient_exponent());
    assert_eq!(expanded.cell_clock_period(), 66);
}

#[test]
fn r4b_09_own_clock_leaves_the_declared_carry_chain_unchanged() {
    for places in [1, 2] {
        let base = Field::declare(listener(places, 1 << 16)).unwrap();
        let expanded = base.found(FoundedRing { period: 2, key: 1 }).unwrap();
        // All phase classes of every ring, every boundary class, and two whole-winding lifts.
        for a in 0..base.ring(0).period() {
            for b in 0..7 {
                for c in 0..11 {
                    for own in 0..2 {
                        for winding in 0..2 {
                            for class in 0..base.alphabet() {
                                let mut old = vec![
                                    BigInt::from(a + winding * base.ring(0).period()),
                                    BigInt::from(b + winding * 7),
                                    BigInt::from(c + winding * 11),
                                ];
                                let mut new = old.clone();
                                new.push(BigInt::from(own + 2 * winding));
                                let before = new[3].clone();
                                let old_step = base.step_class(&mut old, class, None).unwrap();
                                let new_step = expanded.step_class(&mut new, class, None).unwrap();
                                assert_eq!(&new[..3], old);
                                assert_eq!(&new_step.ticks[..3], old_step.ticks);
                                assert_eq!(new_step.carry_out, old_step.carry_out);
                                assert_eq!(new_step.ticks[3], 1);
                                assert_eq!(new[3], before + 1);
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn r4b_10_capacity_is_monotone_and_candidates_stop_at_its_boundary() {
    for places in [1, 2] {
        let field = Field::declare(listener(places, 1 << 16)).unwrap();
        let mut previous = 0;
        for period in 2..=40 {
            let mut declaration = listener(places, u64::MAX);
            declaration.founded.push(FoundedRing {
                period,
                key: period - 1,
            });
            let expanded = Field::declare(declaration).unwrap();
            let n = expanded.capacity().n_star();
            assert!(
                n >= previous,
                "period={period} n*={n} predecessor={previous}"
            );
            previous = n;
        }
        let candidates = field.founding_candidates().unwrap();
        let mut maximum = 1;
        while field
            .found(FoundedRing {
                period: maximum + 1,
                key: maximum,
            })
            .is_ok()
        {
            maximum += 1;
        }
        println!("r4b_capacity places={places} l_max={maximum}");
        assert_eq!(
            candidates.iter().map(|c| c.period).collect::<Vec<_>>(),
            (2..=maximum)
                .filter(|l| !field.cell_clock_period().is_multiple_of(*l))
                .collect::<Vec<_>>()
        );
        assert!(matches!(
            field.found(FoundedRing {
                period: maximum + 1,
                key: maximum
            }),
            Err(HnnError::BelowCapacity { .. })
        ));
    }
}

#[test]
fn r4b_declaration_and_located_route_refusals_are_typed() {
    let field = Field::declare(listener(1, 1 << 16)).unwrap();
    for ring in [
        FoundedRing { period: 1, key: 0 },
        FoundedRing { period: 2, key: 2 },
    ] {
        assert!(matches!(field.found(ring), Err(HnnError::Founding { .. })));
    }
    let expanded = field.found(FoundedRing { period: 2, key: 1 }).unwrap();
    assert!(matches!(
        expanded.helix_lift(Current::at_rest(&expanded).lift()),
        Err(HnnError::Founding {
            what: "the founding's located route is owed"
        })
    ));
    let mut declaration = listener(1, 1 << 16);
    declaration.receivers.clear();
    assert!(matches!(
        Field::declare(declaration.by_lattice_rule())
            .unwrap()
            .found(FoundedRing { period: 2, key: 0 }),
        Err(HnnError::Founding { .. })
    ));
    let mut declaration = listener(1, 1 << 16);
    declaration.receivers[0].ring = 0;
    assert!(matches!(
        Field::declare(declaration.by_lattice_rule())
            .unwrap()
            .found(FoundedRing { period: 2, key: 0 }),
        Err(HnnError::Founding { .. })
    ));
}

#[test]
fn r4b_12_cost_is_the_closed_form_declaration_difference() {
    let base = Field::declare(listener(2, u64::MAX)).unwrap();
    assert_eq!(base.founding_cost(2), 8);
    let base_code = base.describe(12345, 7);
    for period in 2..=40 {
        let cost = base.founding_cost(period);
        let largest = base
            .found(FoundedRing {
                period,
                key: period - 1,
            })
            .unwrap();
        assert_eq!(
            largest.describe(12345, 7).len() - base_code.len(),
            cost as usize
        );
        for key in 0..period {
            let field = base.found(FoundedRing { period, key }).unwrap();
            assert!(field.describe(12345, 7).len() - base_code.len() <= cost as usize);
        }
    }
    let one = base.found(FoundedRing { period: 2, key: 0 }).unwrap();
    let two = one.found(FoundedRing { period: 3, key: 1 }).unwrap();
    let mut rings = Vec::new();
    natural(&mut rings, base.rings().len() as u64);
    // The insertion point is the complete original ring block: find it by describing the
    // actual per-ring declaration with the same code primitives, not by searching bit patterns.
    for ring in base.rings() {
        natural(&mut rings, ring.period());
        naturals(&mut rings, &ring.notches());
        naturals(
            &mut rings,
            &ring
                .reflector()
                .images()
                .iter()
                .map(|&p| p as u64)
                .collect::<Vec<_>>(),
        );
        for v in [ring.screw().angular(), ring.screw().advance()] {
            vector3(&mut rings, v);
        }
        for v in ring.placements() {
            vector3(&mut rings, v);
        }
        rational(&mut rings, ring.admittance());
        natural(&mut rings, ring.initial());
    }
    let at = rings.len();
    let mut expected = base_code[..at].to_vec();
    natural(&mut expected, 2);
    natural(&mut expected, 2);
    natural(&mut expected, 0);
    natural(&mut expected, 3);
    natural(&mut expected, 1);
    expected.extend_from_slice(&base_code[at + 1..]);
    assert_eq!(two.describe(12345, 7), expected);
    assert!(
        two.describe(12345, 7).len() - one.describe(12345, 7).len()
            <= one.founding_cost(3) as usize
    );
}

#[test]
fn r4b_11_guard_nine_reads_only_lock_ports_and_keeps_phase_witnesses() {
    use crate::hnn::constitution::Constitution;
    use crate::hnn::encoding::observed::PairedObservation;
    use crate::hnn::encoding::{EncodingError, holding_sources};
    use crate::hnn::paired::{PairedCarrier, PairingDeclaration};
    let base = Field::declare(listener(2, 1 << 16)).unwrap();
    let field = base.found(FoundedRing { period: 2, key: 1 }).unwrap();
    assert_eq!(holding_sources(&field, 32).unwrap(), vec![(0, 33), (3, 2)]);
    let pairing = PairingDeclaration::Family {
        table: (0..32).map(|c| (c, c ^ 1)).collect(),
    };
    let free = ExactRatMatrix::shaped(
        66,
        32,
        (0..66)
            .map(|r| {
                (0..32)
                    .map(|c| integer(i64::from(c % 2 == 0 && r == 2 * (c / 2 + 1))))
                    .collect()
            })
            .collect(),
    )
    .unwrap();
    let port = PairedCarrier::complete_port(&field, 0, &pairing, &free).unwrap();
    let carrier = PairedCarrier::admit(&field, 0, &pairing, &port).unwrap();
    let material = Constitution::initial(&field, 1 << 40)
        .unwrap()
        .with_symmetric_source(0, port, carrier.symmetry())
        .unwrap();
    let observation = PairedObservation::admit(&field, &material, &pairing).unwrap();
    assert_eq!(observation.ports().len(), 1);
    assert_eq!(observation.witnesses().len(), 1);
    let encoded = observation.encode(&[0, 31]).unwrap();
    field.admit(&encoded).unwrap();
    let changed = material
        .clone()
        .with_ports(3, None, Some(ExactRatMatrix::zero(4, 32).unwrap()), None)
        .unwrap();
    assert!(observation.check_material(&changed).is_err());
    let mut lock = field.clone();
    lock.rings[3].advance = RingAdvance::Lock;
    assert!(matches!(
        holding_sources(&lock, 32),
        Err(EncodingError::Fold { ring: 3, .. })
    ));
    assert!(matches!(
        PairedObservation::admit(&lock, &material, &pairing),
        Err(EncodingError::Fold { ring: 3, .. })
    ));
    assert!(
        lock.admit(&encoded).is_err(),
        "a phase witness cannot migrate into a class-reading clock"
    );
    let mut none = field.clone();
    none.sources = vec![3];
    assert!(PairedObservation::admit(&none, &material, &pairing).is_err());
    let current = Current::at_rest(&field);
    assert!(
        matches!(crate::hnn::encoding::placement::OccurrencePlacement::at(&field,&current,&[vec![0]]),Err(EncodingError::Hnn(error)) if matches!(*error,HnnError::Founding {what:"the founding's located route is owed"}))
    );
}

#[test]
fn r4b_aeon_closing_belongs_to_the_last_lock_ring() {
    let base = Field::declare(crate::hnn::tests::learning::chain_declaration(4096)).unwrap();
    let expanded = base.found(FoundedRing { period: 5, key: 2 }).unwrap();
    let opening = Current::at_rest(&expanded);
    let end = Current::at(
        &expanded,
        vec![
            BigInt::from(4),
            BigInt::from(3),
            BigInt::from(2),
            BigInt::from(30),
        ],
    )
    .unwrap();
    let (_, _, closing) = crate::hnn::retention::aeon_readings(
        &expanded,
        &expanded.parametric(),
        opening.lift(),
        end.lift(),
    )
    .unwrap();
    let old_open = Current::at_rest(&base);
    let old_end = Current::at(&base, end.lift()[..3].to_vec()).unwrap();
    let (_, _, expected) = crate::hnn::retention::aeon_readings(
        &base,
        &base.parametric(),
        old_open.lift(),
        old_end.lift(),
    )
    .unwrap();
    assert_eq!(closing, expected);
    assert!(matches!(
        closing,
        crate::receiver::reception::Component::Present(_)
    ));
}
