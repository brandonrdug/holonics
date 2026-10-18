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

#[derive(Clone, Copy, Debug)]
struct CapacityProbe {
    period: u64,
    n_star: u64,
}

#[derive(Clone, Copy, Debug)]
struct WholeCapacity {
    kind: &'static str,
    period: u64,
    n_star: u64,
}

struct CapacityReadings {
    places: usize,
    probes: Vec<CapacityProbe>,
    whole: Vec<WholeCapacity>,
}

thread_local! {
    static CAPACITY_PROBES: std::cell::RefCell<Option<CapacityReadings>> =
        const { std::cell::RefCell::new(None) };
}

pub(super) fn record_capacity_probe(period: u64, n_star: u64, elapsed_ns: u128) {
    CAPACITY_PROBES.with(|record| {
        if let Some(reading) = record.borrow_mut().as_mut() {
            let places = reading.places;
            println!(
                "R4B_CAPACITY places={places} l={period} n_star={n_star} elapsed_ns={elapsed_ns}"
            );
            reading.probes.push(CapacityProbe { period, n_star });
        }
    });
}

pub(super) fn record_capacity_whole(
    kind: &'static str,
    period: u64,
    n_star: u64,
    elapsed_ns: u128,
) {
    CAPACITY_PROBES.with(|record| {
        if let Some(reading) = record.borrow_mut().as_mut() {
            let places = reading.places;
            println!("R4B_CAPACITY_WHOLE places={places} l={period} key={} n_star={n_star} elapsed_ns={elapsed_ns} kind={kind}", period - 1);
            reading.whole.push(WholeCapacity { kind, period, n_star });
        }
    });
}

struct CapacityProbeScope;

impl CapacityProbeScope {
    fn open(places: usize) -> Self {
        CAPACITY_PROBES.with(|record| {
            assert!(record.borrow().is_none());
            *record.borrow_mut() = Some(CapacityReadings {
                places,
                probes: Vec::new(),
                whole: Vec::new(),
            });
        });
        Self
    }

    fn readings(&self) -> Vec<CapacityProbe> {
        CAPACITY_PROBES.with(|record| record.borrow().as_ref().unwrap().probes.clone())
    }

    fn whole(&self) -> Vec<WholeCapacity> {
        CAPACITY_PROBES.with(|record| record.borrow().as_ref().unwrap().whole.clone())
    }
}

impl Drop for CapacityProbeScope {
    fn drop(&mut self) {
        CAPACITY_PROBES.with(|record| *record.borrow_mut() = None);
    }
}

fn capacity_control(places: usize) {
    // A monotone-only invocation is the seven-unit development read, not the full control.
    // Search-only and all are validation partitions; the external receipt wrapper fixes their
    // measured growth projection and stop budget before launch. No test reads its own timings.
    let phase = std::env::var("R4B_CAPACITY_PHASE").unwrap_or_else(|_| "all".into());
    assert!(matches!(phase.as_str(), "monotone" | "search" | "all"));
    let field = Field::declare(listener(places, 1 << 16)).unwrap();
    let probes = CapacityProbeScope::open(places);
    let started = std::time::Instant::now();
    let first_whole = field.found(FoundedRing { period: 2, key: 1 }).unwrap();
    record_capacity_whole(
        if phase == "monotone" {
            "development"
        } else {
            "first"
        },
        2,
        first_whole.capacity().n_star(),
        started.elapsed().as_nanos(),
    );
    drop(first_whole);
    let mut previous = 0;
    let first = if phase == "search" { 8 } else { 2 };
    let last = if phase == "monotone" { 8 } else { 9 };
    for period in first..=last {
        let started = std::time::Instant::now();
        let n = field.founding_n_star(period).unwrap();
        record_capacity_probe(period, n, started.elapsed().as_nanos());
        assert!(
            n >= previous,
            "places={places} period={period} n*={n} predecessor={previous}"
        );
        previous = n;
    }
    if phase == "monotone" {
        assert_eq!(probes.whole()[0].n_star, probes.readings()[0].n_star);
        println!("R4B_CAPACITY_READ places={places} units=7 development_only=true");
        return;
    }
    let before_search = probes.readings().len();
    let started = std::time::Instant::now();
    // The public consumer's law, observed through its existing capacity-call seam.
    let candidates = field
        .founding_candidates_with(|period| {
            let started = std::time::Instant::now();
            let n = field.founding_n_star(period)?;
            record_capacity_probe(period, n, started.elapsed().as_nanos());
            Ok(n)
        })
        .unwrap();
    println!(
        "R4B_CAPACITY_SEARCH places={places} elapsed_ns={}",
        started.elapsed().as_nanos()
    );
    let readings = probes.readings();
    let search = &readings[before_search..];
    let maximum = search
        .iter()
        .filter(|reading| reading.n_star <= field.population())
        .map(|reading| reading.period)
        .max()
        .unwrap_or(2);
    let log_bound = u64::BITS - maximum.leading_zeros();
    assert!(search.len() as u32 <= 2 * log_bound + 1);
    let mut ordered = BTreeMap::new();
    for reading in &readings {
        if let Some(old) = ordered.insert(reading.period, reading.n_star) {
            assert_eq!(
                old, reading.n_star,
                "a repeated exact capacity call must agree"
            );
        }
    }
    for pair in ordered.iter().collect::<Vec<_>>().windows(2) {
        assert!(
            pair[0].1 <= pair[1].1,
            "capacity must be monotone at every probed pair: {pair:?}"
        );
    }
    let started = std::time::Instant::now();
    let confirmed = field
        .found(FoundedRing {
            period: maximum,
            key: maximum - 1,
        })
        .unwrap();
    record_capacity_whole(
        "confirmed",
        maximum,
        confirmed.capacity().n_star(),
        started.elapsed().as_nanos(),
    );
    drop(confirmed);
    let whole = probes.whole();
    assert_eq!((whole[0].kind, whole[0].period), ("first", 2));
    assert_eq!((whole[1].kind, whole[1].period), ("confirmed", maximum));
    assert!(whole.iter().all(|read| read.n_star <= field.population()));
    for read in &whole {
        if let Some(n_star) = ordered.get(&read.period) {
            assert_eq!(
                read.n_star, *n_star,
                "whole and capacity-only declarations agree"
            );
        }
    }
    let next = maximum.checked_add(1).unwrap();
    let started = std::time::Instant::now();
    let n_star = match field.found(FoundedRing {
        period: next,
        key: maximum,
    }) {
        Err(HnnError::BelowCapacity { n_star, .. }) => n_star,
        other => panic!("the next whole declaration must refuse BelowCapacity: {other:?}"),
    };
    record_capacity_whole("refused", next, n_star, started.elapsed().as_nanos());
    assert!(n_star > field.population());
    assert_eq!(ordered.get(&next), Some(&n_star));
    println!(
        "R4B_CAPACITY_BOUNDARY places={places} l_max={maximum} probes={}",
        search.len()
    );
    assert_eq!(
        candidates.iter().map(|c| c.period).collect::<Vec<_>>(),
        (2..=maximum)
            .filter(|l| !field.cell_clock_period().is_multiple_of(*l))
            .collect::<Vec<_>>()
    );
    for candidate in candidates {
        assert_eq!(candidate.cost, field.founding_cost(candidate.period));
    }
}

#[test]
fn r4b_10_capacity_places_one() {
    capacity_control(1);
}

#[test]
fn r4b_10_capacity_places_two() {
    capacity_control(2);
}

#[test]
fn r4b_capacity_search_propagates_probe_errors_and_checked_overflow() {
    let field = Field::declare(listener(1, 1 << 16)).unwrap();
    assert!(matches!(
        field.founding_candidates_with(|_| Err(HnnError::CountOverflow)),
        Err(HnnError::CountOverflow)
    ));
    assert!(matches!(
        field.founding_candidates_with(|_| Ok(0)),
        Err(HnnError::CountOverflow)
    ));
    let mut declaration = field.declaration().clone();
    declaration.receivers.clear();
    let unanchored = Field::declare(declaration.by_lattice_rule()).unwrap();
    assert!(
        unanchored
            .founding_candidates_with(|_| panic!("a refused first declaration has no probes"))
            .unwrap()
            .is_empty()
    );
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
    let started = std::time::Instant::now();
    let base = Field::declare(listener(1, u64::MAX)).unwrap();
    println!(
        "R4B_COST l=0 key=0 elapsed_ns={} base=true",
        started.elapsed().as_nanos()
    );
    assert_eq!(base.founding_cost(2), 8);
    let base_code = base.describe(12345, 7);
    let mut first = None;
    for period in [2, 3, 5] {
        let cost = base.founding_cost(period);
        for key in 0..period {
            let started = std::time::Instant::now();
            let field = base.found(FoundedRing { period, key }).unwrap();
            println!(
                "R4B_COST l={period} key={key} elapsed_ns={}",
                started.elapsed().as_nanos()
            );
            let difference = field.describe(12345, 7).len() - base_code.len();
            assert!(difference <= cost as usize);
            if key == period - 1 {
                assert_eq!(difference, cost as usize);
            }
            if period == 2 && key == 0 {
                first = Some(field);
            }
        }
    }
    let one = first.unwrap();
    let started = std::time::Instant::now();
    let two = one.found(FoundedRing { period: 3, key: 1 }).unwrap();
    println!(
        "R4B_COST l=3 key=1 elapsed_ns={} founded_count=2",
        started.elapsed().as_nanos()
    );
    let started = std::time::Instant::now();
    for n in 0..=(1u64 << 16) {
        let mut code = Vec::new();
        natural(&mut code, n);
        let bitlen = u64::BITS - (n + 1).leading_zeros();
        assert_eq!(code.len(), (2 * bitlen - 1) as usize, "natural({n})");
    }
    println!(
        "R4B_COST_LENGTH maximum=65536 count=65537 elapsed_ns={}",
        started.elapsed().as_nanos()
    );
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
