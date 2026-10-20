//! The source moment: the capacity by counting, the phase-binned counts against their clocked
//! closed form, the encoder contract and its tape-free covector, the pair buffer, the carry-out, and
//! the encoding loop's tests of the pin of September 29, acceptance 2: the moment of a long source
//! equals the moment accumulated across every split, and nothing of the source is discarded by
//! length.

use num_bigint::{BigInt, BigUint};
use num_traits::{Signed, Zero};

use super::learning::chain;
use super::support::{Draw, Medium, Parts, contact, small_field};
use crate::compression::keys::transport::{CarryHelix, SteppedTerrain, TransportLocation};
use crate::geometry::RatVec3;
use crate::geometry::screw::ScrewGenerator;
use crate::hnn::HnnError;
use crate::hnn::encoding::{Encoded, Encoding, EncodingError, PassageChart};
use crate::hnn::field::{
    ConstitutionRead, CribDeclaration, Current, Field, FieldDeclaration, ReceiverDeclaration,
    RingDeclaration,
};
use crate::hnn::moment::{
    CapacityClock, ExactPairContraction, OffsetTable, PairPort, SourceCapacity, SourceMoment,
    capacity,
};
use crate::hnn::tests::support::encoded;
use crate::ratio::Rat;
use crate::ratio::linear::vector::{add, dot};
use crate::ratio::{integer, rat};

mod resident_pair_face_controls {
    use super::*;
    use crate::hnn::constitution::{FactorGradient, FactorStep};
    use crate::hnn::port::ExecutionPort;
    use crate::hnn::reference::{Reference, compose_pair_return, whole_pair_gradient};
    use crate::hnn::tests::learning::{OPEN_BUDGET, chain_two_declaration, generic_within};
    use crate::ratio::linear::vector::integral;
    use num_traits::One;

    /// The smaller two-class, rank-four chain; both offsets are read at the real port of a
    /// constitution after a certified comparison and deposition, not a fabricated gradient.
    fn deposited() -> (Field, crate::hnn::Constitution) {
        let mut declared = chain_two_declaration(1 << 16);
        declared.offsets = vec![1, 2];
        // Every class fits the source ring, so its physical sections have one declared tick
        // per station. This is the source clock required by station_section's admission.
        declared.rings[0].lock = (0..declared.rings[0].period).collect();
        let field = Field::declare(declared.by_lattice_rule()).unwrap();
        let reference = Reference::new(4, OPEN_BUDGET);
        let before = generic_within(&field, 301, OPEN_BUDGET);
        let mut resident = reference
            .mount_with(&field, &Current::at_rest(&field), before.clone())
            .unwrap();
        let (moment, _) = reference
            .ingest(&mut resident, None, &encoded(&field, &[1, 0, 0, 1, 1]))
            .unwrap();
        let phases = resident.admitted()[0].clone();
        let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
        let (staged, _) = reference
            .compare(&mut resident, pending, &encoded(&field, &[1, 0]))
            .unwrap();
        reference.deposit(&mut resident, staged).unwrap();
        let material = resident.constitution().clone();
        assert!(material.commit() > before.commit());
        // A committed deposit need not publish a pair move. Read the successor's actual
        // nonzero operands even when that small step leaves the pair values unchanged.
        for &offset in field.offsets() {
            let pair = material.pair_port(0, offset).unwrap();
            for rows in [pair.outputs(), pair.current_reads(), pair.earlier_reads()] {
                assert!(rows.iter().flatten().any(|value| !value.is_zero()));
            }
        }
        assert_eq!(material.transport(0), Rat::one());
        (field, material)
    }

    /// Y1 and Y2' of a pair ray, interpolated from four exact table contractions:
    /// `y(t) = y₀ + t Y1 + t² Y2 + t³ Y3` read at `t = 0, 1, 2, 3`. Y2' is the quadratic
    /// coefficient with the base output set to zero, where the `e Q` term vanishes. No resident
    /// face or ray-speed reader supplies these values.
    fn interpolated_ray_speed(
        field: &Field,
        moment: &SourceMoment,
        offset: usize,
        pair: &PairPort,
        direction: [&[Vec<Rat>]; 3],
    ) -> [Rat; 2] {
        let Some(table) = moment.offset_table(field, 0, offset).unwrap() else {
            return [Rat::zero(), Rat::zero()];
        };
        let (alphabet, width) = (field.alphabet(), field.ring(0).width());
        let phases = field.ring(0).placements().len();
        let coefficients = |outputs: &[Vec<Rat>]| -> [Vec<Rat>; 2] {
            let base = [outputs, pair.current_reads(), pair.earlier_reads()];
            let values: Vec<Vec<Rat>> = (0..4i64)
                .map(|at| {
                    let t = integer(at);
                    let [e, a, b]: [Vec<Vec<Rat>>; 3] = std::array::from_fn(|k| {
                        base[k]
                            .iter()
                            .zip(direction[k])
                            .map(|(row, d)| row.iter().zip(d).map(|(x, dx)| x + &t * dx).collect())
                            .collect()
                    });
                    let port = PairPort::new(e, a, b).unwrap();
                    (0..phases)
                        .flat_map(|c| port.apply_table(&table, c, alphabet, width))
                        .collect()
                })
                .collect();
            let n = values[0].len();
            let third: Vec<Rat> = (0..n)
                .map(|i| {
                    (&values[3][i] - integer(3) * &values[2][i] + integer(3) * &values[1][i]
                        - &values[0][i])
                        / integer(6)
                })
                .collect();
            let second: Vec<Rat> = (0..n)
                .map(|i| {
                    (&values[2][i] - integer(2) * &values[1][i] + &values[0][i]) / integer(2)
                        - integer(3) * &third[i]
                })
                .collect();
            let first = (0..n)
                .map(|i| &values[1][i] - &values[0][i] - &second[i] - &third[i])
                .collect();
            [first, second]
        };
        let zero = vec![vec![Rat::zero(); width]; pair.rank()];
        let [first, _] = coefficients(pair.outputs());
        let [_, second] = coefficients(zero.as_slice());
        [
            first.iter().map(|x| x * x).sum(),
            second.iter().map(|x| x * x).sum(),
        ]
    }

    fn code(index: usize) -> usize {
        (index * index + 3 * index + index / 7) % 2
    }

    fn feed(field: &Field, current: &mut Current, moment: &mut SourceMoment, index: usize) {
        assert_eq!(
            moment
                .ingest(field, current, &encoded(field, &[code(index)]))
                .unwrap()
                .cells,
            1
        );
    }

    fn passage(field: &Field) -> (Current, SourceMoment) {
        let mut current = Current::at_rest(field);
        let mut moment = SourceMoment::open(field, &current);
        for index in 0..400 {
            feed(field, &mut current, &mut moment, index);
        }
        (current, moment)
    }

    fn text(moment: &SourceMoment) -> String {
        let mut text = String::new();
        moment.write(&mut text);
        text
    }

    fn cold(field: &Field, moment: &SourceMoment) -> SourceMoment {
        let serialized = text(moment);
        let mut lines = serialized.lines();
        let head = lines.next().unwrap();
        SourceMoment::read(field, head, &mut |what| {
            lines.next().ok_or(HnnError::ContinuingState { what })
        })
        .unwrap()
    }

    fn assert_reads(
        field: &Field,
        material: &crate::hnn::Constitution,
        current: &Current,
        moment: &SourceMoment,
    ) {
        let (ring, width, alphabet) = (0, field.ring(0).width(), field.alphabet());
        let chart = crate::hnn::moment::PopulationChart::of(field);
        for &offset in field.offsets() {
            let pair = material.pair_port(ring, offset).unwrap();
            let face = moment
                .resident_pair_face(ring, offset, pair)
                .unwrap()
                .unwrap();
            let series = face
                .output_series(pair, width, &chart.value(face.population()))
                .unwrap();
            let table = moment.offset_table(field, ring, offset).unwrap();
            for (phase, row) in series.iter().enumerate() {
                let expected = table.as_ref().map_or_else(
                    || vec![Rat::zero(); width],
                    |table| pair.apply_table_termwise(table, phase, alphabet, width),
                );
                assert_eq!(
                    *row,
                    expected,
                    "cell{} offset{offset} phase{phase}",
                    moment.cells()
                );
            }
        }
        let (reads, pairs) = moment
            .moment_parts_whole_table_oracle(field, material, ring)
            .unwrap();
        let geometry = field.ring(ring);
        let lifted_reads: Vec<_> = reads
            .iter()
            .map(|(phase, read)| (*phase, geometry.rotate(read, &current.lift()[ring])))
            .collect();
        assert_eq!(
            moment.open_parts(field, material, current, ring).unwrap(),
            (lifted_reads, geometry.rotate(&pairs, &current.lift()[ring]))
        );
        let weights = moment
            .phase_weights(field, ring, &material.transport(ring))
            .unwrap();
        let mut encoded = pairs;
        for (phase, read) in reads {
            for (sum, entry) in encoded.iter_mut().zip(read) {
                *sum += entry * &weights[phase];
            }
        }
        assert_eq!(moment.encode(field, material, ring).unwrap(), encoded);
    }

    #[test]
    fn pair_face_reads_the_whole_table() {
        let (field, material) = deposited();
        let mut current = Current::at_rest(&field);
        let mut moment = SourceMoment::open(&field, &current);
        // First read at zero, then every binding must increment the same live face.
        assert_reads(&field, &material, &current, &moment);
        for index in 0..400 {
            feed(&field, &mut current, &mut moment, index);
            assert_reads(&field, &material, &current, &moment);
        }
        assert!(
            moment
                .pair_face_summary()
                .iter()
                .all(|row| row.4 == BigUint::one())
        );
    }

    #[test]
    fn pair_face_gradient_equals_the_whole_table() {
        let (field, material) = deposited();
        let mut current = Current::at_rest(&field);
        let mut moment = SourceMoment::open(&field, &current);
        let width = field.ring(0).width();
        let turned: Vec<Vec<Rat>> = (0..field.ring(0).period() as usize)
            .map(|c| {
                (0..width)
                    .map(|j| rat((3 * c + j) as i64 - 5, (c + j + 1) as i64))
                    .collect()
            })
            .collect();
        let charts: Vec<_> = turned.iter().map(|r| integral(r)).collect();
        for index in 0..400 {
            feed(&field, &mut current, &mut moment, index);
            for &offset in field.offsets() {
                let pair = material.pair_port(0, offset).unwrap();
                let old = whole_pair_gradient(&field, &moment, 0, offset, pair, &turned, &charts)
                    .unwrap();
                let expected = FactorStep {
                    gradient: FactorGradient::PairPort {
                        ring: 0,
                        offset,
                        outputs: old
                            .outputs
                            .iter()
                            .map(|r| r.iter().map(|v| -v).collect())
                            .collect(),
                        current: old
                            .current
                            .iter()
                            .map(|r| r.iter().map(|v| -v).collect())
                            .collect(),
                        earlier: old
                            .earlier
                            .iter()
                            .map(|r| r.iter().map(|v| -v).collect())
                            .collect(),
                        speed: crate::hnn::reference::whole_pair_ray_speed(
                            &field,
                            &moment,
                            0,
                            offset,
                            pair,
                            [&old.outputs, &old.current, &old.earlier],
                        )
                        .unwrap(),
                    },
                    energy: old.energy,
                    covector: old.covector,
                };
                let (step, pullback) =
                    compose_pair_return(&field, &moment, 0, offset, pair, &turned, &charts)
                        .unwrap();
                assert_eq!(step, expected, "cell{index} offset{offset}");
                // The step's speed is the ray's exact derivative, read by an independent route.
                if index % 100 == 99 {
                    let FactorGradient::PairPort { speed, .. } = &step.gradient else {
                        unreachable!("a pair return composes a pair step")
                    };
                    let direction = [&old.outputs[..], &old.current[..], &old.earlier[..]];
                    let exact = interpolated_ray_speed(&field, &moment, offset, pair, direction);
                    // Both readings are live: the base output and both read directions move.
                    assert!(
                        exact.iter().all(|v| !v.is_zero()),
                        "cell{index} offset{offset}"
                    );
                    assert_eq!(*speed, exact, "cell{index} offset{offset}");
                }
                assert_eq!(pullback, [old.outputs, old.current, old.earlier]);
            }
        }
    }

    #[test]
    fn pair_ray_integer_chart_matches_whole_table_and_polynomial_with_wide_denominators() {
        let (field, material) = deposited();
        let mut current = Current::at_rest(&field);
        let mut moment = SourceMoment::open(&field, &current);
        let wide = (BigInt::one() << 137usize) + BigInt::from(11);
        let mut fed = 0;
        for count in [0, 1, 8, 31] {
            while fed < count { feed(&field, &mut current, &mut moment, fed); fed += 1; }
            for &offset in field.offsets() {
                let base = material.pair_port(0, offset).unwrap();
                let adjusted: [Vec<Vec<Rat>>; 3] = std::array::from_fn(|k| {
                    [base.outputs(), base.current_reads(), base.earlier_reads()][k].iter()
                        .enumerate().map(|(i, row)| row.iter().enumerate().map(|(j, value)|
                            value + rat((i + 2*j + k) as i64 - 3, [3,5,7][(i+j+k)%3]))
                        .collect()).collect()
                });
                let pair = PairPort::new(adjusted[0].clone(), adjusted[1].clone(), adjusted[2].clone()).unwrap();
                let bases = [pair.outputs(), pair.current_reads(), pair.earlier_reads()];
                let direction: [Vec<Vec<Rat>>; 3] = std::array::from_fn(|k| bases[k].iter()
                    .enumerate().map(|(i,row)| row.iter().enumerate().map(|(j,_)|
                        Rat::new(BigInt::from(((17*k + 7*i + j)%13) as i64 - 6),
                                 &wide * BigInt::from([3,5,7][(i+j+k)%3])))
                    .collect()).collect());
                let d = [&direction[0][..], &direction[1][..], &direction[2][..]];
                let actual = crate::hnn::reference::pair_ray_speed(&field, &moment, 0, offset, &pair, d).unwrap();
                let table = crate::hnn::reference::whole_pair_ray_speed(&field, &moment, 0, offset, &pair, d).unwrap();
                assert_eq!(actual, table, "count{count} offset{offset}");
                assert_eq!(actual, interpolated_ray_speed(&field, &moment, offset, &pair, d));
                let face = moment.resident_pair_face(0, offset, &pair).unwrap().unwrap();
                assert_eq!(face.ray_speed(&pair, d, &Rat::zero()).unwrap(), [Rat::zero(),Rat::zero()]);
                assert_eq!(face.ray_speed(&pair,d,&Rat::one()).unwrap(),
                           face.ray_speed(&pair,d,&-Rat::one()).unwrap());
                let bad = [&direction[0][..direction[0].len()-1], &direction[1][..], &direction[2][..]];
                assert!(face.ray_speed(&pair,bad,&Rat::one()).is_err());
                let mut changed = pair.current_reads().to_vec(); changed[0][0] += Rat::one();
                let stale = PairPort::new(pair.outputs().to_vec(),changed,pair.earlier_reads().to_vec()).unwrap();
                assert!(face.ray_speed(&stale,d,&Rat::one()).is_err());
            }
        }
    }

    #[test]
    fn prepared_pair_ray_sum_matches_mixed_faces_and_whole_tables() {
        let (field, material) = deposited();
        let mut current = Current::at_rest(&field);
        let mut moment = SourceMoment::open(&field, &current);
        let mut moments = vec![moment.clone()];
        for n in 0..31 {
            feed(&field, &mut current, &mut moment, n);
            if [0, 7, 30].contains(&n) { moments.push(moment.clone()); }
        }
        let leaky = material.clone().with_transport(0, rat(3, 4)).unwrap();
        let mut current = Current::at_rest(&field);
        let mut transported = SourceMoment::open_with(&field, &current, &leaky).unwrap();
        transported.ingest(&field, &mut current, &encoded(&field, &[1,0,1,1,0,1,0,0,1])).unwrap();
        moments.push(transported);
        let wide = (BigInt::one() << 137usize) + BigInt::from(11);
        for &offset in field.offsets() {
            let pair = material.pair_port(0, offset).unwrap();
            assert!(moments.last().unwrap().resident_pair_face(0, offset, pair).unwrap().is_none());
            let bases = [pair.outputs(), pair.current_reads(), pair.earlier_reads()];
            let direction: [Vec<Vec<Rat>>; 3] = std::array::from_fn(|k| bases[k].iter()
                .enumerate().map(|(i,row)| row.iter().enumerate().map(|(j,_)|
                    Rat::new(BigInt::from(((17*k + 7*i + j)%13) as i64 - 6),
                             &wide * BigInt::from([3,5,7][(i+j+k)%3])))
                .collect()).collect());
            let zeros: [Vec<Vec<Rat>>; 3] = std::array::from_fn(|k| bases[k].iter()
                .map(|row| vec![Rat::zero(); row.len()]).collect());
            for d in [[&direction[0][..], &direction[1][..], &direction[2][..]],
                      [&zeros[0][..], &zeros[1][..], &zeros[2][..]]] {
                for end in 0..=moments.len() {
                    let mut expected = [Rat::zero(), Rat::zero()];
                    for m in &moments[..end] {
                        let speed = crate::hnn::reference::whole_pair_ray_speed(&field,m,0,offset,pair,d).unwrap();
                        expected[0] += &speed[0]; expected[1] += &speed[1];
                    }
                    assert_eq!(crate::hnn::reference::pair_ray_speed_sum(&field,&moments[..end],0,offset,pair,d).unwrap(),expected);
                }
            }
            let bad = [&direction[0][..direction[0].len()-1],&direction[1][..],&direction[2][..]];
            assert!(crate::hnn::reference::pair_ray_speed_sum(&field,&moments,0,offset,pair,bad).is_err());
            assert_eq!(crate::hnn::reference::pair_ray_speed_sum(&field,&[],0,offset,pair,bad).unwrap(),[Rat::zero(),Rat::zero()]);
            let face = moments[3].resident_pair_face(0,offset,pair).unwrap().unwrap();
            let mut reads = pair.current_reads().to_vec(); reads[0][0] += Rat::one();
            let changed = PairPort::new(pair.outputs().to_vec(),reads,pair.earlier_reads().to_vec()).unwrap();
            let d = [&direction[0][..],&direction[1][..],&direction[2][..]];
            let prepared = crate::hnn::moment::PreparedPairRay::new(&changed,d).unwrap();
            assert!(face.ray_speed_prepared(&prepared,&Rat::one()).is_err());
        }
    }

    #[test]
    fn pair_face_rebuilds_on_changed_reads() {
        let (field, material) = deposited();
        let (current, moment) = passage(&field);
        assert_reads(&field, &material, &current, &moment);
        let original = material.pair_port(0, 1).unwrap();
        let mut reads = original.current_reads().to_vec();
        reads[0][0] += rat(1, 2);
        let changed = material
            .clone()
            .with_pair(
                0,
                1,
                PairPort::new(
                    original.outputs().to_vec(),
                    reads,
                    original.earlier_reads().to_vec(),
                )
                .unwrap(),
            )
            .unwrap();
        assert_reads(&field, &changed, &current, &moment);
        let counts = moment.pair_face_summary();
        assert_eq!(
            counts.iter().find(|r| r.1 == 1).unwrap().4,
            BigUint::from(2u8)
        );
        assert_eq!(counts.iter().find(|r| r.1 == 2).unwrap().4, BigUint::one());
        let pair = changed.pair_port(0, 1).unwrap();
        // A finer exact chart has the same values, including a separately allocated port.
        let recharted = pair
            .current_reads()
            .iter()
            .map(|row| {
                row.iter()
                    .map(|v| Rat::new(v.numer() * 2, v.denom() * 2))
                    .collect()
            })
            .collect();
        let changed = changed
            .clone()
            .with_pair(
                0,
                1,
                PairPort::new(
                    pair.outputs().to_vec(),
                    recharted,
                    pair.earlier_reads().to_vec(),
                )
                .unwrap(),
            )
            .unwrap();
        assert_reads(&field, &changed, &current, &moment);
        assert_eq!(moment.pair_face_summary(), counts);
    }

    #[test]
    fn pair_face_follows_sections() {
        let (field, material) = deposited();
        let (current, moment) = passage(&field);
        assert_reads(&field, &material, &current, &moment);
        let retained = text(&moment);
        let summary = moment.pair_face_summary();
        let cells: Vec<_> = (0..400).map(|i| (i % 11 != 0).then(|| code(i))).collect();
        let continued = moment.continued(&field, &current, 0, &cells).unwrap();
        let opening = SourceMoment::open(&field, &current);
        assert_reads(&field, &material, &current, &opening);
        let opening_text = text(&opening);
        let opening_summary = opening.pair_face_summary();
        let section = opening
            .station_section(&field, &current, 0, &cells)
            .unwrap();
        assert_reads(&field, &material, &current, &continued);
        assert_reads(&field, &material, &current, &section);
        assert_ne!(
            continued.pair_population(0, 1).unwrap(),
            section.pair_population(0, 1).unwrap()
        );
        assert_eq!(text(&moment), retained);
        assert_eq!(
            moment.pair_face_summary(),
            summary,
            "a clone's write cannot change its parent face"
        );
        assert_eq!(text(&opening), opening_text);
        assert_eq!(opening.pair_face_summary(), opening_summary);
    }

    #[test]
    fn pair_face_is_not_retained() {
        let (field, material) = deposited();
        let (current, moment) = passage(&field);
        let retained = text(&moment);
        let bits = moment.dense_bits();
        let capacity = moment.capacity(&field, &current).unwrap();
        let parsed = cold(&field, &moment);
        assert!(parsed.pair_face_summary().is_empty());
        assert_reads(&field, &material, &current, &moment);
        assert_eq!(moment, parsed);
        assert_eq!(text(&moment), retained);
        assert_eq!(moment.dense_bits(), bits);
        assert_eq!(moment.capacity(&field, &current).unwrap(), capacity);
        // The clone's time is the listener's per-cell receipt (`clone_ns`), not this test's.
        let base_clone = parsed.clone();
        let face_clone = moment.clone();
        assert_eq!(face_clone, base_clone);
        assert_reads(&field, &material, &current, &parsed);
        assert_eq!(text(&parsed), retained);
        assert_reads(&field, &material, &current, &face_clone);
    }

    #[test]
    fn pair_face_physical_source_move_equals_two_contractions() {
        let (field, material) = deposited();
        let (_, moment) = passage(&field);
        let (width, alphabet) = (field.ring(0).width(), field.alphabet());
        let mut nonzero = false;
        for &offset in field.offsets() {
            let old = material.pair_port(0, offset).unwrap();
            let outputs = old
                .outputs()
                .iter()
                .enumerate()
                .map(|(r, row)| {
                    row.iter()
                        .enumerate()
                        .map(|(j, value)| value + rat((r + j + 1) as i64, 2))
                        .collect()
                })
                .collect();
            let new = PairPort::new(
                outputs,
                old.current_reads().to_vec(),
                old.earlier_reads().to_vec(),
            )
            .unwrap();
            let actual = crate::hnn::prediction::pair_output_move_series(
                &field, &moment, 0, offset, old, &new,
            )
            .unwrap();
            let table = moment.offset_table(&field, 0, offset).unwrap().unwrap();
            for (phase, row) in actual.iter().enumerate() {
                let before = old.apply_table_termwise(&table, phase, alphabet, width);
                let after = new.apply_table_termwise(&table, phase, alphabet, width);
                let expected: Vec<_> = after.iter().zip(&before).map(|(a, b)| a - b).collect();
                nonzero |= row.iter().any(|v| !v.is_zero());
                assert_eq!(*row, expected);
            }
        }
        assert!(
            nonzero,
            "the physical move control cannot be a zero comparison"
        );
    }
}

/// Lean `HNN/Moment.moment_capacity` on the three-ring control (periods 3, 4, 5, `|A| = 2`, every
/// ring a source, no offsets): `n* = 137`, and `log₂N(n)` per source bit is at least 1 below it and
/// below 1 past it, at every `n` from 2 to 4,096 (R3 H1).
#[test]
fn the_capacity_is_the_least_lossy_population_by_counting() {
    let control = capacity(
        &[3, 4, 5],
        &[crate::hnn::RingAdvance::Lock; 3],
        &[0, 1, 2],
        2,
        &[],
    )
    .unwrap();
    assert_eq!(control.n_star(), 137);
    for n in 2..=4096u64 {
        let bound = BigUint::from(2u32).pow(n as u32);
        assert_eq!(control.states(n) < bound, n >= 137, "n = {n}");
    }
}

/// Campaign 1's declared source state (periods 5, 7, 11, 13; source ring 0; its five classes,
/// THE_MACHINE guard 9; `Δ = {1}`), counted without declaring the field: `n* = 190 = 2·5·19`,
/// certified by exact integers at `n* − 1` and `n*`. [historical] On the bytes it read through the
/// residue chart, `|A| = 256`, the count was `6,148`; the formula still reads it.
#[test]
fn campaign_one_capacity_is_certified_at_its_crossover() {
    let capacity = capacity(
        &[5, 7, 11, 13],
        &[crate::hnn::RingAdvance::Lock; 4],
        &[0],
        5,
        &[1],
    )
    .unwrap();
    assert_eq!(capacity.n_star(), 190);
    assert!(!capacity.lossy_at(189));
    assert!(capacity.lossy_at(190));
    assert_eq!(
        crate::hnn::moment::capacity(
            &[5, 7, 11, 13],
            &[crate::hnn::RingAdvance::Lock; 4],
            &[0],
            256,
            &[1]
        )
        .unwrap()
        .n_star(),
        6_148
    );
}

/// The clocked closed form of selective stepping, computed independently: ring `g`'s lift after
/// cell `k` is its opening lift plus its lock steps plus its predecessor's wraps on cells `0 … k`.
fn closed_form_lifts(field: &Field, opening: &[BigInt], cells: &[usize]) -> Vec<Vec<BigInt>> {
    let rings = field.rings().len();
    let mut per_ring: Vec<Vec<BigInt>> = Vec::with_capacity(rings);
    for g in 0..rings {
        let ring = field.ring(g);
        let d = BigInt::from(ring.period());
        let mut lifts = Vec::with_capacity(cells.len());
        let mut lock_steps = 0i64;
        let mut carries = 0i64;
        for (k, &code) in cells.iter().enumerate() {
            lock_steps += i64::from(ring.fits(ring.port(code)));
            if g > 0 {
                let before: &BigInt = if k == 0 {
                    &opening[g - 1]
                } else {
                    &per_ring[g - 1][k - 1]
                };
                let after = &per_ring[g - 1][k];
                let wraps = after / BigInt::from(field.ring(g - 1).period())
                    - before / BigInt::from(field.ring(g - 1).period());
                carries += i64::try_from(wraps).unwrap();
            }
            let _ = &d;
            lifts.push(&opening[g] + lock_steps + carries);
        }
        per_ring.push(lifts);
    }
    (0..cells.len())
        .map(|k| (0..rings).map(|g| per_ring[g][k].clone()).collect())
        .collect()
}

/// Lean `HNN/Moment.{closingRing_moment_is_phaseBinned, selective_position}`: per-cell ingest
/// equals the clocked closed form, bin by bin, and the lift point it reaches.
#[test]
fn per_cell_ingest_equals_the_clocked_closed_form() {
    let field = &chain();
    let (a, d) = (field.alphabet(), field.ring(0).period() as usize);
    let mut draw = Draw::new(21);
    let cells: Vec<usize> = (0..400).map(|_| draw.below(a)).collect();
    let opening = Current::at(field, vec![1.into(), 2.into(), 1.into()]).unwrap();
    let mut current = opening.clone();
    let mut moment = SourceMoment::open(field, &current);
    // The moment keeps counting across the joint clock's carry-outs.
    let mut fed = 0;
    while fed < cells.len() {
        fed += moment
            .ingest(field, &mut current, &encoded(field, &cells[fed..]))
            .unwrap()
            .cells;
    }
    let lifts = closed_form_lifts(field, opening.lift(), &cells);
    assert_eq!(current.lift(), &lifts[399][..]);
    let mut expected = vec![vec![0u64; a]; d];
    let mut offset = vec![vec![0u64; a * a]; d];
    for (k, &code) in cells.iter().enumerate() {
        let phase = (&lifts[k][0] % BigInt::from(d))
            .to_string()
            .parse::<usize>()
            .unwrap();
        expected[phase][code] += 1;
        if k > 0 {
            offset[phase][code * a + cells[k - 1]] += 1;
        }
    }
    for phase in 0..d {
        assert_eq!(moment.phase_counts(0, phase).unwrap(), &expected[phase][..]);
        assert_eq!(
            moment.offset_counts(0, 1, phase).unwrap(),
            &offset[phase][..]
        );
    }
    assert_eq!(moment.cells(), 400);
    assert_eq!(moment.opening(), opening.lift());
}

/// Lean `HNN/Moment.encoderMoment_contract` with `HNN/Encoding.whole_pair_read_offset_moment` (the
/// normalized open, reading no held cell): for any rational
/// encoder and pair port, the open storage from the counts equals the streamed sum
/// `Σ_k P^(τ_cut − τ_k)(ν̂(n) E x_k + [k ≥ 1] ν̂(n − 1) E^(1)(x_k, x_(k−1)))`: the marginal over its
/// population `n`, and the pair port read on every pair of the passage over the pair population
/// `n − 1` (the open reads no held cell).
#[test]
fn the_moment_contracts_to_the_streamed_encoder_sum() {
    let field = small_field(&[3, 2], vec![contact(0, 1, 1, 0)], 1);
    let medium = Medium::generic(&field, 5, Parts::default());
    let mut draw = Draw::new(8);
    let cells: Vec<usize> = (0..60).map(|_| draw.below(2)).collect();
    let mut current = Current::at_rest(&field);
    let mut moment = SourceMoment::open(&field, &current);
    // Stop only at a carry-out; feed the rest after.
    let mut fed = 0;
    let mut phases = Vec::new();
    let mut probe = current.clone();
    for &code in &cells {
        probe.step(&field, &encoded(&field, &[code]), 0).unwrap();
        phases.push(probe.lift()[0].clone());
    }
    while fed < cells.len() {
        fed += moment
            .ingest(&field, &mut current, &encoded(&field, &cells[fed..]))
            .unwrap()
            .cells;
    }
    let ring = field.ring(0);
    let port = medium.source_port(0).unwrap();
    let pair = medium.pair_port(0, 1).unwrap();
    let chart = crate::hnn::moment::PopulationChart::of(&field);
    let pairs = cells.len() as u64 - 1;
    assert_eq!(moment.population(0).unwrap(), cells.len() as u64);
    assert_eq!(moment.pair_population(0, 1).unwrap(), pairs);
    let (nu, nu_pairs) = (chart.value(cells.len() as u64), chart.value(pairs));
    let mut streamed = vec![Rat::zero(); ring.width()];
    for (k, &code) in cells.iter().enumerate() {
        let mut x = vec![Rat::zero(); 2];
        x[code] = Rat::from_integer(1.into());
        let mut driven: Vec<Rat> = port.apply(&x).unwrap().iter().map(|v| v * &nu).collect();
        if k > 0 {
            let earlier = cells[k - 1];
            for rho in 0..pair.rank() {
                let weight = &pair.current_reads()[rho][code]
                    * &pair.earlier_reads()[rho][earlier]
                    * &nu_pairs;
                driven = add(
                    &driven,
                    &crate::ratio::linear::vector::scale(&weight, &pair.outputs()[rho]),
                );
            }
        }
        let shift = &current.lift()[0] - &phases[k];
        streamed = add(&streamed, &ring.rotate(&driven, &shift));
    }
    let open = moment.open_storage(&field, &medium, &current).unwrap();
    assert_eq!(open[0], streamed);
    assert!(open[1].iter().all(Zero::is_zero));
}

fn exact_pair_port_fixture(alphabet: usize, rank: usize, width: usize) -> PairPort {
    let denominator = [3, 5, 7, 11, 13, 17, 19];
    let factor = |row: usize, column: usize| {
        let numerator = ((row * 13 + column * 7 + 3) % 17) as i64 - 8;
        rat(
            numerator,
            denominator[(row * 5 + column * 3) % denominator.len()],
        )
    };
    PairPort::new(
        (0..rank)
            .map(|rho| (0..width).map(|j| factor(rho + 2, j + 5)).collect())
            .collect(),
        (0..rank)
            .map(|rho| (0..alphabet).map(|x| factor(rho + 1, x + 1)).collect())
            .collect(),
        (0..rank)
            .map(|rho| (0..alphabet).map(|a| factor(rho + 4, a + 2)).collect())
            .collect(),
    )
    .unwrap()
}

/// The integer contraction equals the former termwise rational expression for both the declared
/// population-chart weight and a leaky table with non-dyadic carried entries. The factors also
/// have non-dyadic denominators, so this exercises shared-denominator reduction rather than only
/// parity-valued examples.
#[test]
fn pair_port_integer_contraction_matches_termwise_dyadic_and_leaky_tables() {
    let pair = exact_pair_port_fixture(3, 2, 3);
    let prepared = ExactPairContraction::of(&pair);
    let mut counts = vec![0u64; 3 * 3 * 3];
    counts[9 + 1] = 2;
    counts[9 + 5] = 3;
    counts[9 + 8] = 1;
    let chart = crate::hnn::moment::PopulationChart::of(&chain());
    let population_table = OffsetTable {
        counts,
        population: 6,
        weight: chart.value(6),
        transported: None,
    };
    for phase in 0..3 {
        assert_eq!(
            pair.apply_table(&population_table, phase, 3, 3),
            pair.apply_table_termwise(&population_table, phase, 3, 3),
            "population-chart phase {phase}"
        );
        assert_eq!(
            prepared.apply_table(&population_table, phase, 3, 3),
            pair.apply_table_termwise(&population_table, phase, 3, 3),
            "prepared population-chart phase {phase}"
        );
    }

    let mut transported = std::collections::BTreeMap::new();
    transported.insert(18 + 1, rat(2, 7));
    transported.insert(18 + 5, rat(4, 9));
    transported.insert(18 + 8, rat(5, 13));
    let leaky_table = OffsetTable {
        counts: vec![0; 3 * 3 * 3],
        population: 3,
        weight: rat(0, 1),
        transported: Some(transported),
    };
    assert_eq!(
        prepared.apply_table(&leaky_table, 2, 3, 3),
        pair.apply_table_termwise(&leaky_table, 2, 3, 3)
    );
    assert_eq!(
        prepared.apply_table(&leaky_table, 1, 3, 3),
        pair.apply_table_termwise(&leaky_table, 1, 3, 3),
        "an unoccupied leaky phase remains exactly zero"
    );
}

/// Synthetic-only microbenchmark for arithmetic equivalence and bit volume. It deliberately does
/// not stand in for MNIST proposal/open_storage timing; the actual learning path has its own runner
/// profile. Run explicitly with `cargo test -p holonics benchmark_pair_port_contraction_synthetic
/// -- --ignored --nocapture`.
#[test]
#[ignore = "synthetic pair-contraction microbenchmark; not an MNIST learning measurement"]
fn benchmark_pair_port_contraction_synthetic() {
    use std::hint::black_box;
    use std::time::Instant;

    let pair = exact_pair_port_fixture(16, 4, 8);
    let prepared = ExactPairContraction::of(&pair);
    let mut counts = vec![0u64; 2 * 16 * 16];
    for (slot, count) in counts[..16 * 16].iter_mut().enumerate() {
        *count = (slot % 7 + 1) as u64;
    }
    let table = OffsetTable {
        counts,
        population: (16 * 16 * 4) as u64,
        weight: rat(1, 257),
        transported: None,
    };
    let input_factor_bits: u64 = pair
        .outputs()
        .iter()
        .chain(pair.current_reads())
        .chain(pair.earlier_reads())
        .flatten()
        .map(|value| value.numer().magnitude().bits() + value.denom().bits())
        .sum();
    let output = pair.apply_table(&table, 0, 16, 8);
    assert_eq!(output, pair.apply_table_termwise(&table, 0, 16, 8));
    let output_bits: u64 = output
        .iter()
        .map(|value| value.numer().magnitude().bits() + value.denom().bits())
        .sum();
    let bit_volume = prepared.bit_volume(&table, 0, 16);

    let repetitions = 128;
    let start = Instant::now();
    for _ in 0..repetitions {
        black_box(pair.apply_table_termwise(black_box(&table), 0, 16, 8));
    }
    let termwise = start.elapsed();
    let start = Instant::now();
    for _ in 0..repetitions {
        black_box(prepared.apply_table(black_box(&table), 0, 16, 8));
    }
    let integral = start.elapsed();
    eprintln!(
        "synthetic pair contraction: alphabet=16 rank=4 occupied=256 output=8 reps={repetitions}; termwise={termwise:?}; shared-denominator={integral:?}; input_factor_bits={input_factor_bits}; factor_chart_integer_bits={}; factor_chart_payload_bytes_ceiling={}; phase_weight_denominator_bits={}; feature_denominator_bits={}; output_denominator_bits={}; final_denominator_bits={}; exact_output_bits={output_bits}; not MNIST",
        bit_volume.chart_integer_bits,
        bit_volume.chart_integer_bits.div_ceil(8),
        bit_volume.phase_weight_denominator_bits,
        bit_volume.feature_denominator_bits,
        bit_volume.output_denominator_bits,
        bit_volume.final_denominator_bits,
    );
}

/// Lean `HNN/Moment.encoder_covector_tape_free`: the encoder covector, read from the counts and the
/// covector alone, equals the exact directional derivative of `⟨g, s(0)⟩` in `E`.
#[test]
fn the_encoder_covector_is_the_exact_directional_derivative() {
    let field = &chain();
    let mut medium = Medium::generic(field, 9, Parts::default());
    let mut draw = Draw::new(10);
    let cells: Vec<usize> = (0..10).map(|_| draw.below(4)).collect();
    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open(field, &current);
    moment
        .ingest(field, &mut current, &encoded(field, &cells))
        .unwrap();
    let covector = draw.vector(field.ring(0).width());
    let base = dot(
        &covector,
        &moment.open_storage(field, &medium, &current).unwrap()[0],
    );
    let gradient = moment
        .encoder_covector(field, &current, 0, &covector, &crate::ratio::integer(1))
        .unwrap();
    let direction = draw.matrix(field.ring(0).width(), field.alphabet());
    let pairing: Rat = gradient
        .entries()
        .iter()
        .zip(direction.entries())
        .map(|(g, e)| g * e)
        .sum();
    medium.source[0] = Some(medium.source[0].as_ref().unwrap().add(&direction).unwrap());
    let moved = dot(
        &covector,
        &moment.open_storage(field, &medium, &current).unwrap()[0],
    );
    assert_eq!(moved - base, pairing);
}

/// The pair buffer is a delay line of raw cells, each overwritten once its pairs are counted; its
/// bits are counted in the moment's dense code, which is sized once.
#[test]
fn the_pair_buffer_overwrites_and_its_bits_are_counted() {
    let field = &chain();
    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open(field, &current);
    assert_eq!(moment.window(), vec![None]);
    let empty = moment.dense_bits();
    moment
        .ingest(field, &mut current, &encoded(field, &[3, 1, 2]))
        .unwrap();
    assert_eq!(moment.window(), vec![Some(2)]);
    // Slots are fixed: only their widths change. The held cell's 3 bits are in the empty code too
    // (`d = 4`, `|A| = 4`).
    assert!(moment.dense_bits() >= empty);
    assert_eq!(empty, 2 * (4 * 4 + 4 * 4 * 4) + 3);
}

/// Ingest stops at the joint clock's carry-out: the aeon boundary belongs to the winding.
#[test]
fn ingest_stops_at_the_carry_out() {
    let field = small_field(&[2, 2], vec![contact(0, 1, 1, 0)], 1);
    let mut current = Current::at_rest(&field);
    let mut moment = SourceMoment::open(&field, &current);
    // Code 0 steps both rings: ring 1 wraps at the second cell (1 + 1 + carry).
    let ingested = moment
        .ingest(&field, &mut current, &encoded(&field, &[0, 0, 0, 0]))
        .unwrap();
    assert!(ingested.carry_out);
    assert_eq!(ingested.cells, 2);
    assert_eq!(moment.cells(), 2);
    let rest = moment
        .ingest(&field, &mut current, &encoded(&field, &[1, 1]))
        .unwrap();
    assert!(!rest.carry_out);
    assert_eq!(rest.cells, 2);
}

/// **The population chart and the normalized open that reads no held cell** (Lean
/// `HNN/IndexedOpen.{normalized_phase_counts_mass, normalized_zero_population}`,
/// `HNN/Encoding.whole_pair_read_counts`): `ν̂(n)` is the nearest point of `2^(−L_ν)ℤ` to `1/n`
/// (`|ν̂ − 1/n| ≤ 2^(−L_ν−1)`), zero at `n = 0`; `L_ν = ⌈log₂(2 L_R n*)⌉` (18 on campaign 1:
/// `2 · 16 · 6,148 = 196,736 ≤ 2^18`); the normalized phase counts carry the mass `n ν̂(n)`, within
/// `n 2^(−L_ν−1)` of 1; the offset moment is read whole over its pair population, every pair of the
/// passage; and before any pair there is no table, so the pair port contributes nothing.
#[test]
fn the_open_reads_the_normalized_counts_and_no_window() {
    use crate::hnn::field::FieldDeclaration;
    use crate::hnn::moment::PopulationChart;
    use crate::ratio::rat;
    let campaign = Field::declare(FieldDeclaration::campaign_one(6_148)).unwrap();
    assert_eq!(PopulationChart::of(&campaign).exponent(), 18);
    let field = &chain();
    let chart = PopulationChart::of(field);
    let scale = BigInt::from(1u64 << chart.exponent());
    for n in [1u64, 2, 3, 7, 13, 1_000, 65_536] {
        let exact = Rat::new(BigInt::from(1), BigInt::from(n));
        let read = chart.value(n);
        assert!((&read - &exact).abs() <= chart.residual());
        // The nearest point: one lattice step either way is farther.
        let step = Rat::new(BigInt::from(1), scale.clone());
        assert!((&read + &step - &exact).abs() >= (&read - &exact).abs());
        assert!((&read - &step - &exact).abs() >= (&read - &exact).abs());
    }
    assert_eq!(chart.value(0), Rat::zero());
    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open(field, &current);
    assert_eq!(moment.offset_table(field, 0, 1).unwrap(), None);
    let cells = [1usize, 3, 1, 1, 0, 3, 1, 2, 1];
    let mut fed = 0;
    while fed < cells.len() {
        fed += moment
            .ingest(field, &mut current, &encoded(field, &cells[fed..]))
            .unwrap()
            .cells;
    }
    let n = cells.len() as u64;
    assert_eq!(moment.population(0).unwrap(), n);
    let mass: Rat = (0..field.ring(0).period() as usize)
        .flat_map(|phase| {
            moment
                .normalized_counts(field, 0, phase, &crate::ratio::integer(1))
                .unwrap()
        })
        .sum();
    assert_eq!(mass, Rat::from_integer(BigInt::from(n)) * chart.value(n));
    assert!(
        (&mass - Rat::from_integer(1.into())).abs()
            <= Rat::from_integer(BigInt::from(n)) * chart.residual()
    );
    // Every pair of the passage, whatever cell came last: 8 pairs over 9 cells.
    let table = moment.offset_table(field, 0, 1).unwrap().unwrap();
    assert_eq!(table.population, 8);
    assert_eq!(table.counts.iter().sum::<u64>(), 8);
    assert_eq!(table.weight, chart.value(8));
    assert_eq!(chart.value(8), rat(1, 8));
}

/// Ingest every cell of `cells`, feeding past each carry-out, in the chunks `splits` cuts.
fn ingest_split(field: &Field, cells: &[usize], splits: &[usize]) -> (SourceMoment, Current) {
    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open(field, &current);
    let mut bounds = splits.to_vec();
    bounds.push(cells.len());
    let mut start = 0;
    for end in bounds {
        let mut fed = start;
        while fed < end {
            fed += moment
                .ingest(field, &mut current, &encoded(field, &cells[fed..end]))
                .unwrap()
                .cells;
        }
        start = end;
    }
    (moment, current)
}

/// **Acceptance 2: the moment of a long source equals the moment accumulated across any split of
/// it.** On the chain (`|A| = 4`, `Δ = {1}`), a drawn source of 4,096 cells ingested whole, cell by
/// cell, at every split point of its first 128 cells and across 32 drawn splits gives one moment:
/// every phase count, every offset count, the pair buffer, the lift point and the open storage.
#[test]
fn the_moment_is_one_across_every_split() {
    let field = &chain();
    let medium = Medium::generic(field, 11, Parts::default());
    let mut draw = Draw::new(29);
    let cells: Vec<usize> = (0..4096)
        .map(|_| draw.below(super::support::classes(&field)))
        .collect();
    let (whole, lift) = ingest_split(field, &cells, &[]);
    let open = whole.open_storage(field, &medium, &lift).unwrap();
    let same = |(moment, current): (SourceMoment, Current)| {
        assert_eq!(moment, whole);
        assert_eq!(current.lift(), lift.lift());
        assert_eq!(moment.open_storage(field, &medium, &current).unwrap(), open);
    };
    same(ingest_split(
        field,
        &cells,
        &(1..cells.len()).collect::<Vec<_>>(),
    ));
    for split in 1..128 {
        same(ingest_split(field, &cells, &[split]));
    }
    let mut splits: Vec<usize> = (0..32).map(|_| 1 + draw.below(cells.len() - 1)).collect();
    splits.sort_unstable();
    splits.dedup();
    same(ingest_split(field, &cells, &splits));
}

/// **Acceptance 2: nothing of the source is discarded by length.** Over a drawn source of 4,096
/// cells, 4,096 times the pair buffer's length: every cell is counted once in the source ring's
/// phase counts (their symbol totals are the source's histogram) and every pair at the declared
/// offset once in its offset counts (their totals are the source's adjacent-pair histogram); and a
/// source that differs only in its first cell has another moment at the end.
#[test]
fn nothing_of_the_source_is_discarded_by_length() {
    let field = &chain();
    let a = field.alphabet();
    let d = field.ring(0).period() as usize;
    let mut draw = Draw::new(31);
    let cells: Vec<usize> = (0..4096).map(|_| draw.below(a)).collect();
    let (moment, _) = ingest_split(field, &cells, &[]);
    assert_eq!(moment.cells(), cells.len() as u64);
    assert_eq!(moment.window().len(), 1);
    let mut histogram = vec![0u64; a];
    for &cell in &cells {
        histogram[cell] += 1;
    }
    let mut pairs = vec![0u64; a * a];
    for k in 1..cells.len() {
        pairs[cells[k] * a + cells[k - 1]] += 1;
    }
    let mut counted = vec![0u64; a];
    let mut paired = vec![0u64; a * a];
    for phase in 0..d {
        for (total, count) in counted
            .iter_mut()
            .zip(moment.phase_counts(0, phase).unwrap())
        {
            *total += count;
        }
        for (total, count) in paired
            .iter_mut()
            .zip(moment.offset_counts(0, 1, phase).unwrap())
        {
            *total += count;
        }
    }
    assert_eq!(counted, histogram);
    assert_eq!(paired, pairs);
    assert_eq!(
        moment.pair_population(0, 1).unwrap(),
        cells.len() as u64 - 1
    );
    let mut changed = cells.clone();
    changed[0] = (changed[0] + 1) % a;
    let (other, _) = ingest_split(field, &changed, &[]);
    assert_ne!(
        other, moment,
        "the first of 4,096 cells is still in the moment"
    );
}

/// The leaky count (`hnn::moment`, "The leaky count"): on campaign 1's field at the founded
/// transport, a 400-cell passage of many turns reads each phase's normalized decayed counts within
/// one population-chart unit of the exact transported weights `Σ_k ρ^(a_k) [slot_k] / Σ_k ρ^(a_k)`
/// (a measurement on this passage: the read has no general one-unit bound, the module header); no
/// age aliases, and at modulus one the moment opened at the constitution reads what the plain
/// moment reads.
#[test]
fn the_leaky_count_reads_the_transported_weights_over_many_turns() {
    use crate::hnn::constitution::Constitution;
    use crate::hnn::field::FieldDeclaration;
    use crate::hnn::moment::PopulationChart;
    let field = &Field::declare(FieldDeclaration::campaign_one(6_148)).unwrap();
    let lossless = Constitution::initial(field, 1 << 33).unwrap();
    let founded = lossless.clone().founded_transport(field, 0).unwrap();
    let modulus = founded.transport(0);
    assert!(modulus < Rat::from_integer(1.into()));
    let mut draw = Draw::new(24);
    let cells: Vec<usize> = (0..400)
        .map(|_| draw.below(super::support::classes(&field)))
        .collect();
    let chart = PopulationChart::of(field);
    let unit = Rat::new(BigInt::from(1), BigInt::from(1u64 << chart.exponent()));

    // The exact transported weights, by brute force over the passage's ticks.
    let mut walk = Current::at_rest(field);
    let mut entered = Vec::new();
    let mut ticks = 0u64;
    for &code in &cells {
        let step = walk.step(field, &encoded(field, &[code]), 0).unwrap();
        ticks += u64::from(step.ticks[0]);
        entered.push((walk.phase(field, 0).unwrap() as usize, code, ticks));
        if step.carry_out {
            break;
        }
    }
    let fed = entered.len();
    assert!(
        ticks > 5 * field.ring(0).period(),
        "a passage of many turns: {ticks} ticks"
    );
    let weight = |age: u64| {
        if age > 64 {
            Rat::zero()
        } else {
            crate::hnn::moment::modulus_power(&modulus, age)
        }
    };
    let mass: Rat = entered.iter().map(|(_, _, t)| weight(ticks - t)).sum();

    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open_with(field, &current, &founded).unwrap();
    moment
        .ingest(field, &mut current, &encoded(field, &cells[..fed]))
        .unwrap();
    let mut plain_current = Current::at_rest(field);
    let mut plain = SourceMoment::open_with(field, &plain_current, &lossless).unwrap();
    plain
        .ingest(field, &mut plain_current, &encoded(field, &cells[..fed]))
        .unwrap();
    let mut reference_current = Current::at_rest(field);
    let mut reference = SourceMoment::open(field, &reference_current);
    reference
        .ingest(
            field,
            &mut reference_current,
            &encoded(field, &cells[..fed]),
        )
        .unwrap();
    let one = Rat::from_integer(1.into());
    for phase in 0..field.ring(0).period() as usize {
        let read = moment.normalized_counts(field, 0, phase, &modulus).unwrap();
        for (code, value) in read.iter().enumerate() {
            let exact: Rat = entered
                .iter()
                .filter(|(c, x, _)| *c == phase && *x == code)
                .map(|(_, _, t)| weight(ticks - t))
                .sum::<Rat>()
                / &mass;
            assert!(
                (value - &exact).abs() <= unit,
                "phase {phase}, class {code}"
            );
        }
        assert_eq!(
            plain.normalized_counts(field, 0, phase, &one).unwrap(),
            reference.normalized_counts(field, 0, phase, &one).unwrap()
        );
    }
    assert_eq!(
        plain
            .open_storage(field, &lossless, &plain_current)
            .unwrap(),
        reference
            .open_storage(field, &lossless, &reference_current)
            .unwrap()
    );
    // The phase weights read the leaky count, not the aliased phases; another modulus is refused.
    assert!(moment.phase_weights(field, 0, &modulus).is_ok());
    assert!(moment.normalized_counts(field, 0, 0, &one).is_err());

    // The leaky `open_storage` pair path is still the exact termwise read of its carried table,
    // returned through each phase rotation and the current lift. This exercises the actual founded
    // table, rather than only the synthetic rational-table oracle above.
    let alphabet = field.alphabet();
    let geometry = field.ring(0);
    let source = founded.source_port(0).unwrap();
    let pair = founded.pair_port(0, 1).unwrap();
    let table = moment.offset_table(field, 0, 1).unwrap().unwrap();
    let mut unlifted = vec![Rat::zero(); geometry.width()];
    for phase in 0..geometry.period() as usize {
        let marginal = moment.normalized_counts(field, 0, phase, &modulus).unwrap();
        let mut driven = source.apply(&marginal).unwrap();
        for (slot, count) in table.normalized(phase, alphabet) {
            let (current, earlier) = (slot / alphabet, slot % alphabet);
            for rho in 0..pair.rank() {
                let weight = &count
                    * &pair.current_reads()[rho][current]
                    * &pair.earlier_reads()[rho][earlier];
                for (value, entry) in driven.iter_mut().zip(&pair.outputs()[rho]) {
                    *value += &weight * entry;
                }
            }
        }
        let returned = geometry.rotate(&driven, &-BigInt::from(phase));
        unlifted = add(&unlifted, &returned);
    }
    let mut expected: Vec<Vec<Rat>> = field
        .rings()
        .iter()
        .map(|ring| vec![Rat::zero(); ring.width()])
        .collect();
    expected[0] = geometry.rotate(&unlifted, &current.lift()[0]);
    assert_eq!(
        moment.open_storage(field, &founded, &current).unwrap(),
        expected
    );
}

/// A field of one closing source ring of period 256 at the quarter turns, its lock `{0}`, reading
/// 256 classes (each its own port: no fold), over campaign 1's population.
fn wide_field() -> Field {
    use crate::geometry::RatVec3;
    use crate::geometry::screw::ScrewGenerator;
    use crate::hnn::field::{
        CribDeclaration, FieldDeclaration, ReceiverDeclaration, RingDeclaration,
    };
    let d = 256u64;
    Field::declare(
        FieldDeclaration {
            founded: Vec::new(),
            founding: false,
            rings: vec![RingDeclaration {
                period: d,
                screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
                placements: (0..d)
                    .map(|node| FieldDeclaration::quarter_turn(node, d))
                    .collect(),
                lock: vec![0],
                reflector: (0..d).map(|port| ((d - port) % d) as usize).collect(),
                admittance: crate::ratio::integer(2),
                initial: 0,
            }],
            contacts: Vec::new(),
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: 256,
            step: crate::ratio::integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 0,
                aperture: 1,
                tolerance: crate::ratio::rat(1, 16),
                depth: 2,
                prior: crate::compression::landmark::context::StopPrior::half(),
                mass: 1,
                base: crate::compression::landmark::context::BaseMeasure::Even,
                receiving_prior: 0,
            }],
            crib: CribDeclaration {
                window: 64,
                offset: 1,
            },
            population: 6_148,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

/// The leaky read is not within one chart unit in general, on the ingest's own path (Lean
/// `HNN/IndexedOpen.leaky_read_exceeds_chart_unit`). On a ring of period 256 reading 256 classes
/// (each its own port: THE_MACHINE guard 9; the counterexample was built on campaign 1's bytes
/// through the residue port chart until October 5), at campaign 1's founded transport
/// `ρ₀ = 10809/2^17` (chart `2^(−18)` at its population), ring 0 ticks only at class 0, and each
/// tick's datum enters at the new phase. Class 0 and the 204 classes `1 … 204` the lock does not
/// select enter 205 slots of phase 1; two more cells of class 0 tick the ring to phases 2 and 3.
/// Each phase-1 slot carries `3566` against its exact `ρ₀² 2^19 = 116834481/2^15`, phase 2's
/// carries `43236 = ρ₀ 2^19` exactly, and the newest datum's read
/// `chart(2^19/(2^19 + 43236 + 205 · 3566)) = 105840/2^18` is more than eight chart units below its
/// transported weight `1/(1 + ρ₀ + 205 ρ₀²)`.
#[test]
fn the_leaky_read_is_not_within_one_chart_unit_in_general() {
    use crate::hnn::constitution::{Constitution, Locus};
    use crate::hnn::moment::PopulationChart;
    let field = &wide_field();
    let dyadic = |numerator: u64, exponent: u32| {
        Rat::new(BigInt::from(numerator), BigInt::from(1u64 << exponent))
    };
    let modulus = dyadic(10_809, 17);
    let founded = Constitution::initial(field, 1 << 33)
        .unwrap()
        .with_transport(0, modulus.clone())
        .unwrap();
    assert_eq!(
        founded.lattice(Locus::SourcePort(0)).unwrap().exponent(),
        18
    );
    assert_eq!(PopulationChart::of(field).exponent(), 18);

    let mut cells = vec![0usize];
    cells.extend(1..205);
    cells.extend([0, 0]);
    let mut walk = Current::at_rest(field);
    let phases: Vec<u64> = (0..cells.len())
        .map(|k| {
            walk.step(field, &encoded(field, &cells[k..=k]), 0).unwrap();
            walk.phase(field, 0).unwrap()
        })
        .collect();
    assert!(phases[..205].iter().all(|&phase| phase == 1));
    assert_eq!(phases[205..], [2, 3]);

    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open_with(field, &current, &founded).unwrap();
    let ingested = moment
        .ingest(field, &mut current, &encoded(field, &cells))
        .unwrap();
    assert_eq!((ingested.cells, ingested.carry_out), (207, false));
    let newest = moment.normalized_counts(field, 0, 3, &modulus).unwrap()[0].clone();
    assert_eq!(newest, dyadic(105_840, 18));
    let one = Rat::from_integer(1.into());
    let weight =
        one.clone() / (one + &modulus + Rat::from_integer(205.into()) * &modulus * &modulus);
    assert!(weight - &newest > Rat::from_integer(8.into()) * dyadic(1, 18));
}

// -------------------------------------------------------------------------------------------
// a refused occurrence, and the located route's capacity

/// The helix `(2, 3, 5)` as a field: the rings in carry order on the quarter turns, chained on
/// their common nodes, source ring 2 holding the five classes, `Δ = {1, 3}`.
pub(crate) fn helix_field() -> Field {
    let rings = [2u64, 3, 5]
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
            founded: Vec::new(),
            founding: false,
            rings,
            contacts: vec![contact(0, 1, 2, 0), contact(1, 2, 3, 0)],
            loops: Vec::new(),
            sources: vec![2],
            offsets: vec![1, 3],
            alphabet: 5,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 2,
                aperture: 5,
                tolerance: rat(1, 16),
                depth: 2,
                prior: crate::compression::landmark::context::StopPrior::half(),
                mass: 1,
                base: crate::compression::landmark::context::BaseMeasure::Even,
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
    .unwrap()
}

/// [agent-inferred, October 5] **A founded partial-span passage**: a stepped terrain on the helix
/// `(2, 3, 5)` whose five advances are nonzero multiples of 5, so they generate `5ℤ/30`, of index 5,
/// which does not divide the receiving grain `D_low = 6` (an index dividing it reads every coset
/// alike, and its read set stays plural). Located from a passage at every key, the read set is one
/// gauge class; the chart founded on the first passage's key alone reaches that key's coset, six of
/// the thirty lifts. Returns the encoded passage and its opening key. The draw: the first of
/// `2_026_100_990 … 2_026_101_189` (a range no ref, tree or receipt held) whose read set locates
/// one gauge class.
pub(crate) fn partial_span(field: &Field) -> (Encoded, u64) {
    let helix = CarryHelix::new(vec![2, 3, 5]).unwrap();
    let mut draw = Draw::new(2_026_100_995);
    let advances: Vec<u64> = (0..5).map(|_| 5 * (1 + draw.below(5)) as u64).collect();
    let mut left: Vec<usize> = (0..5).collect();
    let labels: Vec<usize> = (0..5)
        .map(|_| left.remove(draw.below(left.len())))
        .collect();
    let terrain = SteppedTerrain::new(helix.clone(), advances, labels).unwrap();
    let passages: Vec<Vec<usize>> = (0..helix.period())
        .map(|key| terrain.passage(key, 60))
        .collect();
    let location = TransportLocation::locate(helix, 5, &passages).unwrap();
    let chart = PassageChart::located(&location, &passages[..1]).unwrap();
    let encoding = Encoding::found(&chart).unwrap();
    assert_eq!(
        encoding.reached(),
        6,
        "the chart reaches one coset of 5ℤ/30"
    );
    let key = chart.openings()[0]
        .iter()
        .position(|entry| !entry.is_zero())
        .expect("an opening is a lift") as u64;
    let encoded = Encoded::through(&encoding, &chart, field, &passages[..1])
        .unwrap()
        .remove(0);
    (encoded, key)
}

/// The lift point whose helix lift is `ℓ = τ_0 + 2τ_1 + 6τ_2`.
pub(crate) fn at_helix(field: &Field, lift: u64) -> Current {
    let lift = lift % 30;
    Current::at(
        field,
        vec![
            BigInt::from(lift % 2),
            BigInt::from(lift / 2 % 3),
            BigInt::from(lift / 6),
        ],
    )
    .unwrap()
}

/// [implemented-exact] **A refused occurrence leaves the Current and the moment as they were**
/// (`Field::step_occurrence`, atomic; `SourceMoment::ingest` counts an occurrence only after its
/// step returns). A founded partial-span passage ([`partial_span`]) steps from a lift on its reached
/// coset; from a lift off it, its first occurrence's located step is refused
/// (`EncodingError::Unreached`, the square `D E = ρ` read where the encoding is not founded), and the
/// lift point, the moment and its text are unchanged. A part of the passage is refused alike.
#[test]
fn a_refused_located_step_leaves_the_current_and_the_moment_unchanged() {
    let field = helix_field();
    let (encoded, key) = partial_span(&field);
    for part in [
        encoded.part(0..encoded.len()).unwrap(),
        encoded.part(7..31).unwrap(),
    ] {
        // On the reached coset the passage steps.
        let mut current = at_helix(&field, key);
        let mut moment = SourceMoment::open(&field, &current);
        assert!(moment.ingest(&field, &mut current, &part).unwrap().cells > 0);
        // Off it, the first occurrence is refused and nothing moves.
        let mut current = at_helix(&field, key + 1);
        let mut moment = SourceMoment::open(&field, &current);
        let (opened, held) = (current.clone(), moment.clone());
        assert_eq!(
            moment.ingest(&field, &mut current, &part),
            Err(HnnError::from(EncodingError::Unreached))
        );
        assert_eq!(current, opened);
        assert_eq!(moment, held);
        let mut lift = current.lift().to_vec();
        assert_eq!(
            field.selective_step(&mut lift, &part, 0),
            Err(HnnError::from(EncodingError::Unreached))
        );
        assert_eq!(lift, opened.lift());
    }
}

/// [definition; agent-inferred, October 6] **A located moment reads the located clock's capacity,
/// persistently** (`hnn::moment`, "The capacity on an admitted clock" and "The checked reading"): a
/// moment that has counted a located occurrence reads the located certificate at its cells, checked
/// against its partition and reached lift, and a later identity or empty ingest does not downgrade
/// it. A moment of identity-route cells reads the field's identity certificate.
#[test]
fn a_located_moment_refuses_the_identity_capacity() {
    let field = helix_field();
    let (passage, key) = partial_span(&field);
    let mut current = at_helix(&field, key);
    let mut moment = SourceMoment::open(&field, &current);
    let identity_at = |cells: u64| SourceCapacity::Identity {
        state_bits: field.capacity().state_bits(cells),
        n_star: field.capacity().n_star(),
    };
    assert_eq!(moment.capacity(&field, &current), Ok(identity_at(0)));
    let empty = passage.part(0..0).unwrap();
    moment.ingest(&field, &mut current, &empty).unwrap();
    assert_eq!(
        moment.capacity(&field, &current),
        Ok(identity_at(0)),
        "no located cell is counted"
    );
    moment.ingest(&field, &mut current, &passage).unwrap();
    let located = field.capacity_for(&passage).unwrap();
    assert_eq!(located.clock(), CapacityClock::Located);
    let located_at = |cells: u64| SourceCapacity::Located {
        state_bits: located.state_bits(cells),
        n_star: located.n_star(),
    };
    assert_eq!(
        moment.capacity(&field, &current),
        Ok(located_at(moment.cells()))
    );
    assert!(matches!(
        field.capacity().admit(&passage),
        Err(HnnError::Unadmitted { .. })
    ));
    // A later identity-route or empty ingest does not downgrade the moment.
    moment.ingest(&field, &mut current, &empty).unwrap();
    assert_eq!(
        moment.capacity(&field, &current),
        Ok(located_at(moment.cells()))
    );
    // The identity route reads the certificate at the moment's cells.
    let chain = chain();
    let mut current = Current::at_rest(&chain);
    let mut identity = SourceMoment::open(&chain, &current);
    identity
        .ingest(&chain, &mut current, &encoded(&chain, &[0, 1, 1, 0, 1]))
        .unwrap();
    assert_eq!(
        SourceCapacity::checked_of(&identity, &chain, &current),
        Ok(SourceCapacity::Identity {
            state_bits: chain.capacity().state_bits(identity.cells()),
            n_star: chain.capacity().n_star(),
        })
    );
}

/// [definition; agent-inferred, October 5] **The moment's text carries its route profile**
/// (`SourceMoment::write`): each marked line, `identity` or `located`, reads back equal; an unmarked
/// line is refused, typed, never read as identity (it cannot be told from a located moment saved
/// before the profile, and an old save is a superseded prototype).
#[test]
fn the_moment_text_carries_its_route_profile() {
    let read = |field: &Field, text: &str| {
        let mut lines = text.lines();
        let head = lines.next().unwrap();
        SourceMoment::read(field, head, &mut |what| {
            lines.next().ok_or(HnnError::ContinuingState { what })
        })
    };
    let unmarked = |text: &str| {
        let (head, rest) = text.split_once('\n').unwrap();
        let (head, _) = head.rsplit_once(' ').unwrap();
        format!("{head}\n{rest}")
    };
    let located_field = helix_field();
    let (passage, key) = partial_span(&located_field);
    let mut current = at_helix(&located_field, key);
    let mut located = SourceMoment::open(&located_field, &current);
    located
        .ingest(&located_field, &mut current, &passage)
        .unwrap();
    let chain = chain();
    let mut current = Current::at_rest(&chain);
    let mut identity = SourceMoment::open(&chain, &current);
    identity
        .ingest(&chain, &mut current, &encoded(&chain, &[1, 0, 1, 1]))
        .unwrap();
    for (field, moment, profile) in [
        (&located_field, &located, "located"),
        (&chain, &identity, "identity"),
    ] {
        let mut text = String::new();
        moment.write(&mut text);
        assert!(
            text.lines()
                .next()
                .unwrap()
                .ends_with(&format!(" {profile}"))
        );
        assert_eq!(read(field, &text).as_ref(), Ok(moment));
        assert_eq!(
            read(field, &unmarked(&text)),
            Err(HnnError::ContinuingState {
                what: "the moment's route profile (identity | located)",
            })
        );
    }
}
