//! Bounded native invariants, not a curriculum or scientific validation.

use holonics::compression::keys::transport::{CarryHelix, SteppedTerrain, TransportLocation};
use holonics::geometry::RatVec3;
use holonics::geometry::screw::ScrewGenerator;
use holonics::hnn::encoding::{Encoded, Encoding, PassageChart};
use holonics::hnn::field::{ContactDeclaration, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::moment::{CapacityClock, SourceCapacity, capacity, capacity_located};
use holonics::hnn::{Current, Field, FieldDeclaration, HnnError, RingDeclaration, SourceMoment};
use holonics::holarchy::terrain::{Draw, KnownTruth};
use holonics::ratio::{integer, rat};
use num_bigint::{BigInt, BigUint};

fn field() -> Field {
    field_with([2, 3, 5], 5, vec![1, 3], vec![2])
}

fn field_with(
    periods: [u64; 3],
    alphabet: usize,
    offsets: Vec<usize>,
    sources: Vec<usize>,
) -> Field {
    field_at(periods, alphabet, offsets, sources, 1 << 16)
}

fn field_at(
    periods: [u64; 3],
    alphabet: usize,
    offsets: Vec<usize>,
    sources: Vec<usize>,
    population: u64,
) -> Field {
    let rings = periods
        .into_iter()
        .map(|period| RingDeclaration {
            period,
            screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
            placements: (0..period)
                .map(|node| FieldDeclaration::quarter_turn(node, period))
                .collect(),
            lock: vec![0],
            reflector: (0..period)
                .map(|p| ((period - p) % period) as usize)
                .collect(),
            admittance: integer(2),
            initial: 0,
        })
        .collect();
    Field::declare(
        FieldDeclaration {
            rings,
            contacts: [(0usize, 1usize, 2usize), (1, 2, 3)]
                .into_iter()
                .map(|(from, to, nodes)| ContactDeclaration {
                    from,
                    to,
                    channel: (0..nodes).map(|node| (node, node)).collect(),
                    admittance: integer(2),
                    exponent: integer(0),
                })
                .collect(),
            loops: Vec::new(),
            sources,
            offsets,
            alphabet,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 2,
                aperture: 5,
                tolerance: rat(1, 16),
                depth: 2,
                prior: holonics::compression::landmark::context::StopPrior::half(),
                mass: 1,
                base: holonics::compression::landmark::context::BaseMeasure::Even,
                receiving_prior: 0,
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

#[test]
fn the_located_bound_has_its_own_exact_crossover_and_identity_is_unchanged() {
    let old = capacity(&[2, 3, 5], &[2], 5, &[1, 3]).unwrap();
    let full = capacity_located(&[2, 3, 5], &[2], 5, &[1, 3]).unwrap();
    assert_eq!(old.clock(), CapacityClock::Identity);
    assert_eq!(old.advance_bounds(), &[2, 2, 2]);
    assert_eq!(old.n_star(), 436);
    assert_eq!(full.clock(), CapacityClock::Located);
    assert_eq!(full.advance_bounds(), &[2, 3, 5]);
    assert_eq!(full.n_star(), 438);
    for certificate in [&old, &full] {
        assert!(!certificate.certifies(certificate.n_star() - 1).unwrap());
        assert!(certificate.certifies(certificate.n_star()).unwrap());
        for n in certificate.n_star()..certificate.n_star() + 8 {
            assert!(certificate.certifies(n).unwrap());
        }
    }
    assert_eq!(
        capacity(&[3, 4, 5], &[0, 1, 2], 2, &[]).unwrap().n_star(),
        137
    );
    assert_eq!(
        capacity(&[5, 7, 11, 13], &[0], 5, &[1]).unwrap().n_star(),
        190
    );
}

#[test]
fn the_lift_factor_widens_before_the_word_sized_rate_and_count_are_multiplied() {
    let maximum = u64::MAX;
    let full = capacity_located(&[maximum], &[], 2, &[]).unwrap();
    assert_eq!(
        full.states(maximum),
        (BigUint::from(1u32) << 128usize) - (BigUint::from(1u32) << 64usize)
    );
    let old = capacity(&[maximum], &[], 2, &[]).unwrap();
    assert_eq!(
        old.states(maximum),
        BigUint::from(3u32) * BigUint::from(maximum)
    );
    assert_eq!(capacity(&[2], &[], 2, &[]).unwrap().state_bits(0), 1);
    assert_eq!(capacity(&[4], &[], 2, &[]).unwrap().state_bits(0), 2);
    assert!(matches!(
        full.certifies(u64::from(u32::MAX) + 1),
        Err(HnnError::CountOverflow)
    ));
}

#[test]
fn malformed_capacity_declarations_and_lifts_are_typed_refusals() {
    for bad in [
        capacity_located(&[1], &[0], 2, &[]),
        capacity_located(&[2], &[0], 1, &[]),
        capacity_located(&[2], &[0], 2, &[0]),
    ] {
        assert!(matches!(bad, Err(HnnError::NonpositiveDeclaration)));
    }
    assert!(matches!(
        capacity_located(&[2], &[1], 2, &[]),
        Err(HnnError::Shape { .. })
    ));
    let full = capacity_located(&[2, 3, 5], &[2], 5, &[1, 3]).unwrap();
    let turn = BigInt::from(1u32) << 80usize;
    let opening = vec![&turn * 2 + 1, &turn * 3 + 2, &turn * 5 + 4];
    let reached: Vec<BigInt> = opening.iter().zip([2, 3, 5]).map(|(x, d)| x + d).collect();
    full.check_lift(&opening, &reached, 1).unwrap();
    assert!(matches!(
        capacity(&[2, 3, 5], &[2], 5, &[1, 3])
            .unwrap()
            .check_lift(&opening, &reached, 1),
        Err(HnnError::Unadmitted { .. })
    ));
    let mut beyond = reached.clone();
    beyond[2] += 1;
    assert!(matches!(
        full.check_lift(&opening, &beyond, 1),
        Err(HnnError::Unadmitted { .. })
    ));
    assert!(matches!(
        full.check_lift(&opening, &reached[..2], 1),
        Err(HnnError::Shape { .. })
    ));
}

#[test]
fn the_complete_leaky_read_counts_the_retained_coordinates_and_keeps_the_histogram_crossover_separate()
 {
    use holonics::hnn::Constitution;
    use holonics::hnn::moment::PopulationChart;
    let field = field();
    let mut current = Current::at_rest(&field);
    let material = Constitution::initial(&field, 1 << 33)
        .unwrap()
        .with_transport(2, rat(1, 2))
        .unwrap();
    let mut moment = SourceMoment::open_with(&field, &current, &material).unwrap();
    let encoded = Encoded::identity(&KnownTruth::uniform(5, 21, 1, 2).unwrap(), &field)
        .unwrap()
        .remove(0);
    let position = encoded.classes_read().position(|code| code != 0).unwrap();
    let no_tick = encoded.part(position..position + 1).unwrap();
    let opening = current.clone();
    for _ in 0..8 {
        assert_eq!(
            moment.ingest(&field, &mut current, &no_tick).unwrap().cells,
            1
        );
        assert_eq!(current, opening, "no ring lock fits this class");
    }
    let unit = PopulationChart::of(&field).exponent() + 1;
    let expected_extra = 275 * (4 + u64::from(unit));
    assert_eq!(
        SourceCapacity::checked_of(&moment, &field, &current).unwrap(),
        SourceCapacity::Retained {
            clock: CapacityClock::Identity,
            state_bits_upper: field.capacity().state_bits(8) + expected_extra,
            histogram_n_star: 436,
        }
    );
    // The saved-map reader does not turn malformed coordinates into a count certificate.
    let mut text = String::new();
    moment.write(&mut text);
    for replacement in [
        "map 0 -1".to_string(),
        "map 0 0".to_string(),
        "map 25 1".to_string(),
        format!("map 0 {}", (BigInt::from(9) << unit as usize)),
    ] {
        let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
        let metadata = lines
            .iter()
            .position(|line| line.starts_with("leaky "))
            .unwrap();
        lines[metadata + 1] = replacement;
        let mut input = lines.iter().map(String::as_str);
        let head = input.next().unwrap();
        match SourceMoment::read(&field, head, &mut |what| {
            input.next().ok_or(HnnError::ContinuingState { what })
        }) {
            Err(_) => {}
            Ok(bad) => assert!(matches!(
                SourceCapacity::checked_of(&bad, &field, &current),
                Err(HnnError::Unadmitted { .. })
            )),
        }
    }
}

#[test]
fn a_continued_station_carrier_is_never_given_the_ingest_box() {
    let field = field();
    let current = Current::at_rest(&field);
    let moment = SourceMoment::open(&field, &current);
    assert!(SourceCapacity::checked_of(&moment, &field, &current).is_ok());
    assert_eq!(field.capacity().states(1), BigUint::from(437500u32));
    for station in [0usize, 1, 32, 128] {
        let mut section = vec![None; station + 1];
        section[station] = Some(0);
        let continued = moment.continued(&field, &current, 2, &section).unwrap();
        assert_eq!(continued.cells(), 1);
        assert!(matches!(
            SourceCapacity::checked_of(&continued, &field, &current),
            Err(HnnError::Unadmitted { .. })
        ));
    }
}

#[test]
fn a_capacity_read_checks_its_actual_producing_partition_including_hidden_rings() {
    let producer = field();
    let current = Current::at_rest(&producer);
    let moment = SourceMoment::open(&producer, &current);
    for other in [
        field_with([2, 3, 5], 6, vec![1, 3], vec![2]),
        field_with([2, 3, 5], 5, vec![1], vec![2]),
        field_with([2, 3, 5], 5, vec![1, 3], vec![1]),
        field_with([2, 4, 5], 5, vec![1, 3], vec![2]),
    ] {
        assert!(matches!(
            SourceCapacity::checked_of(&moment, &other, &current),
            Err(HnnError::Unadmitted { .. })
        ));
    }
}

/// The located passages on the helix `[2, 3, 5]`, located by loop closure on a stepped terrain
/// and encoded through their own chart.
fn located_passages(field: &Field) -> Vec<Encoded> {
    let helix = CarryHelix::new(vec![2, 3, 5]).unwrap();
    let mut draw = Draw::new(2_026_100_962);
    let terrain = SteppedTerrain::draw(helix.clone(), &mut draw);
    let mut keys: Vec<u64> = (0..helix.period()).collect();
    let passages: Vec<Vec<usize>> = (0..helix.period())
        .map(|_| {
            let key = keys.remove(draw.below(keys.len()));
            terrain.passage(key, 60)
        })
        .collect();
    let location = TransportLocation::locate(helix, 5, &passages).unwrap();
    let chart = PassageChart::located(&location, &passages).unwrap();
    let encoding = Encoding::found(&chart).unwrap();
    Encoded::through(&encoding, &chart, field, &passages).unwrap()
}

/// [definition; agent-inferred, October 6] **The capacity preflight refuses before anything moves**
/// (`hnn::moment`, "The checked reading"; the ports' ingest). The declared population 436 is the
/// identity crossover and lies below the located one, 438. A located passage is refused by the
/// host port before its ingest, on a fresh open and on a continuing identity moment, and the
/// resident (lift, moments and handles, address, aeon) reads back unchanged; an identity passage
/// still enters.
#[test]
fn a_located_passage_below_its_crossover_is_refused_before_the_resident_moves() {
    use holonics::hnn::port::ExecutionPort;
    use holonics::hnn::reference::Reference;
    let field = field_at([2, 3, 5], 5, vec![1, 3], vec![2], 436);
    assert_eq!(field.capacity().n_star(), 436);
    let located = located_passages(&field).remove(0);
    let below = |result: &Result<_, HnnError>| {
        matches!(
            result,
            Err(HnnError::BelowCapacity {
                population: 436,
                n_star: 438
            })
        )
    };
    assert!(below(&field.capacity_for(&located).map(|_| ())));
    let reference = Reference::new(64, u64::MAX);
    let mut resident = reference
        .mount(&field, &Current::at_rest(&field))
        .unwrap();
    let mounted = format!("{resident:?}");
    assert!(below(
        &reference.ingest(&mut resident, None, &located).map(|_| ())
    ));
    assert_eq!(format!("{resident:?}"), mounted, "a fresh open moved nothing");
    let (moment, _) = reference
        .ingest(&mut resident, None, &located.part(0..0).unwrap())
        .unwrap();
    let opened = format!("{resident:?}");
    let at = resident.current().clone();
    let address = resident.address().clone();
    assert!(below(
        &reference
            .ingest(&mut resident, Some(&moment), &located)
            .map(|_| ())
    ));
    assert_eq!(resident.current(), &at);
    assert_eq!(resident.address(), &address);
    assert_eq!(format!("{resident:?}"), opened, "a continuing moment moved nothing");
    let identity = Encoded::identity(&KnownTruth::uniform(5, 21, 1, 2).unwrap(), &field)
        .unwrap()
        .remove(0);
    let (_, entered) = reference
        .ingest(&mut resident, Some(&moment), &identity)
        .unwrap();
    let cells = entered.forward.present().unwrap().cells;
    assert!(cells > 0);
    assert_eq!(resident.moment(&moment).unwrap().cells(), cells as u64);
}

#[test]
fn the_consuming_capacity_keeps_winding_prefix_and_offset_invariants_across_charts() {
    let field = field();
    let encoded = located_passages(&field);
    let bound = field.capacity_for(&encoded[0]).unwrap();
    assert_eq!(bound.clock(), CapacityClock::Located);
    assert_eq!(bound.advance_bounds(), &[2, 3, 5]);
    assert!(matches!(
        field.capacity().admit(&encoded[0]),
        Err(HnnError::Unadmitted { .. })
    ));
    let turn = BigInt::from(1u32) << 80usize;
    let opening = Current::at(&field, vec![&turn * 2 + 1, &turn * 3 + 2, &turn * 5 + 4]).unwrap();
    let mut current = opening.clone();
    let mut moment = SourceMoment::open(&field, &opening);
    let mut stopped = 0;
    let mut total = 0u64;
    for passage in encoded.iter().take(2) {
        let mut fed = 0;
        while fed < passage.len() {
            let request = passage.part(fed..passage.len()).unwrap();
            let ingested = moment.ingest(&field, &mut current, &request).unwrap();
            assert!(ingested.cells > 0);
            if ingested.carry_out {
                stopped += 1;
            }
            fed += ingested.cells;
            total += ingested.cells as u64;
            assert_eq!(moment.cells(), total);
            bound
                .check_lift(opening.lift(), current.lift(), moment.cells())
                .unwrap();
            assert!(matches!(
                SourceCapacity::checked_of(&moment, &field, &current).unwrap(),
                SourceCapacity::Located { .. }
            ));
            let source = field.sources()[0];
            let first: u64 = (0..field.ring(source).period() as usize)
                .flat_map(|phase| moment.phase_counts(source, phase).unwrap().iter())
                .sum();
            assert_eq!(first, moment.cells());
            for offset in [1, 3] {
                let pairs: u64 = (0..field.ring(source).period() as usize)
                    .flat_map(|phase| moment.offset_counts(source, offset, phase).unwrap().iter())
                    .sum();
                assert_eq!(pairs, moment.cells().saturating_sub(offset as u64));
            }
        }
    }
    assert!(stopped > 1);
    assert_eq!(moment.cells(), 120);
    // A subsequent identity or empty passage does not erase the moment's earlier ranged motion.
    let identity = Encoded::identity(&KnownTruth::uniform(5, 21, 1, 2).unwrap(), &field)
        .unwrap()
        .remove(0);
    let identity_bound = field.capacity_for(&identity).unwrap();
    assert_eq!(identity_bound.clock(), CapacityClock::Identity);
    assert_eq!(
        moment.capacity(&field, &current).unwrap(),
        SourceCapacity::Located {
            state_bits: bound.state_bits(moment.cells()),
            n_star: bound.n_star()
        }
    );
    let empty = identity.part(0..0).unwrap();
    assert_eq!(field.capacity_for(&empty).unwrap(), identity_bound);
    assert_eq!(
        moment.capacity(&field, &current).unwrap(),
        SourceCapacity::Located {
            state_bits: bound.state_bits(moment.cells()),
            n_star: bound.n_star()
        }
    );
    let before = (current.clone(), moment.clone());
    assert_eq!(
        moment.ingest(&field, &mut current, &empty).unwrap().cells,
        0
    );
    assert_eq!((current.clone(), moment.clone()), before);
    let taken = moment.ingest(&field, &mut current, &identity).unwrap();
    bound
        .check_lift(opening.lift(), current.lift(), moment.cells())
        .unwrap();
    assert_eq!(moment.cells(), 120 + taken.cells as u64);
}
