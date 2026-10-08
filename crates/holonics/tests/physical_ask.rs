//! Law controls of the Ask consumer (Refs #73 #62): the native feature read, the admitted waves, the
//! retained phase family's probe and the shared encounter. The fixtures are the declared mechanics
//! fixtures of `physical_action.rs` and `native_action_return.rs`, reused as they stand; every
//! expected value is computed independently of the owner it checks (an independently executed
//! forward Word, the closed work form, a brute-force enumeration, the family API called directly).
//! They are unit controls, not scientific learning evidence, and they claim no World prediction:
//! the probe predicts the NATIVE readout only.

use std::sync::Arc;

use holonics::compression::landmark::context::{BaseMeasure, StopPrior};
use holonics::geometry::{RatVec3, screw::ScrewGenerator};
use holonics::hnn::constitution::CAMPAIGN_ONE_BUDGET;
use holonics::hnn::field::{
    ContactDeclaration, CribDeclaration, FieldMaterial, ReceiverDeclaration,
};
use holonics::hnn::phase_family::PhaseStatistics;
use holonics::hnn::physical::PhysicalReceiver;
use holonics::hnn::physical::action::{
    ActionCommunication, AdmittedWaves, BoundJointWorld, ProbeHold,
};
use holonics::hnn::receiving::ReceivingPhases;
use holonics::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
use holonics::hnn::word::action::PortPreparation;
use holonics::hnn::{
    Absorption, Constitution, Current, Encoded, Field, FieldDeclaration, RingDeclaration,
    SourceMoment, Word, WordOpening,
};
use holonics::holarchy::terrain::KnownTruth;
use holonics::holon::law::{ReferenceHolon, Scheme};
use holonics::holon::parametron::Carrier;
use holonics::holon::{Holon, HolonState, PortHolon};
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::linear::inertia::SymmetricForm;
use holonics::ratio::{Rat, integer, rat};
use holonics::receiver::receipt::{ReceiptLaw, RegionChart};
use holonics::receiver::reception::{JointLaw, ReceiverFace};
use holonics::receiver::release::{ProbeSeparation, ReleaseReturn};
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};

// -------------------------------------------------------------------------------------------
// fixture A: the loaded, pumped exact Word of `physical_action.rs` (no World)

fn open_fixture() -> (Field, Constitution, Current) {
    let ring = |source| RingDeclaration {
        period: 2,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..2)
            .map(|node| FieldDeclaration::quarter_turn(node, 2))
            .collect(),
        lock: if source { vec![0, 1] } else { Vec::new() },
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
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
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
    for g in 0..2 {
        let material = ResonatorMaterial::new(
            ExactRatMatrix::identity(4).unwrap(),
            ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 8)),
            ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 16)),
            Some(
                PumpDeclaration::new(rat(1, 16), Carrier::at(&rat(1, 2)), PumpStep::Half).unwrap(),
            ),
        )
        .unwrap();
        theta = theta.with_ring_resonator(&field, g, material).unwrap();
    }
    let current = Current::at(&field, vec![BigInt::from(0), BigInt::from(1)]).unwrap();
    (field, theta, current)
}

fn moment(field: &Field, current: &Current) -> Arc<SourceMoment> {
    Arc::new(
        SourceMoment::open(field, current)
            .continued(field, current, 0, &[Some(0), Some(1)])
            .unwrap(),
    )
}

fn open<'f>(
    field: &'f Field,
    theta: &Constitution,
    current: &Current,
    opening: &WordOpening,
) -> Word<'f> {
    Word::open_source_exact_received(field, theta, current, moment(field, current), opening)
        .unwrap()
        .0
}

/// The opening after three full ticks: a nonzero loaded interior at an advanced pump clock.
fn loaded_opening(field: &Field, theta: &Constitution, current: &Current) -> WordOpening {
    let mut prior = open(field, theta, current, &WordOpening::Rest);
    prior.run(3).unwrap();
    WordOpening::Received {
        carry: prior.reception_end().unwrap(),
        absorption: Absorption::Nothing,
    }
}

fn reads(
    word: &Word<'_>,
    field: &Field,
    theta: &Constitution,
    current: &Current,
    phases: &ReceivingPhases,
) -> Vec<Vec<Rat>> {
    phases
        .epochs()
        .map(|k| {
            phases
                .read(
                    field,
                    theta,
                    current,
                    word.anchor(k, phases.ring()).unwrap(),
                )
                .unwrap()
                .logits
        })
        .collect()
}

/// An independent actual forward perturbation of the opening by the source wave `added = B u`.
fn perturbed_word<'f>(
    word: &Word<'f>,
    phases: &ReceivingPhases,
    added: &[Rat],
) -> Word<'f> {
    let field = word.field();
    let mut injection: Vec<Vec<Rat>> = field
        .rings()
        .iter()
        .map(|r| vec![Rat::zero(); r.width()])
        .collect();
    injection[0] = added.to_vec();
    let mut actual = Word::continuing(
        field,
        word.operands().clone(),
        &word.change().unwrap(),
        &injection,
        word.opened_at(),
    )
    .unwrap();
    actual.run(phases.junction_steps()).unwrap();
    assert!(actual.field_balances().iter().all(|b| b.closes()));
    actual
}

/// The logits an independently executed forward Word reads at every station.
fn perturbed_target(
    word: &Word<'_>,
    theta: &Constitution,
    current: &Current,
    phases: &ReceivingPhases,
    added: &[Rat],
) -> Vec<Vec<Rat>> {
    let actual = perturbed_word(word, phases, added);
    reads(&actual, word.field(), theta, current, phases)
}

/// The feature `P^lift · anchor` an independently executed forward Word presents at `station`:
/// the vector the receiving read multiplies.
fn perturbed_feature(
    word: &Word<'_>,
    current: &Current,
    phases: &ReceivingPhases,
    station: usize,
    added: &[Rat],
) -> Vec<Rat> {
    let actual = perturbed_word(word, phases, added);
    let epoch = phases.epochs().nth(station).unwrap();
    word.field().ring(phases.ring()).rotate(
        actual.anchor(epoch, phases.ring()).unwrap(),
        &current.lift()[phases.ring()],
    )
}

/// The selection of source coordinates `columns` as the preparation's actuators (rows are the
/// four coordinates of the source wave).
fn selecting(columns: &[usize]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        (0..4)
            .map(|row| {
                columns
                    .iter()
                    .map(|&column| if column == row { Rat::one() } else { Rat::zero() })
                    .collect()
            })
            .collect(),
    )
    .unwrap()
}

// -------------------------------------------------------------------------------------------
// (a) the consumer equations of the native feature read

#[test]
fn the_native_feature_is_what_the_receiving_read_multiplies_and_it_matches_the_request_path_and_a_forward_perturbation()
 {
    let (field, theta, current) = open_fixture();
    let phases =
        ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();
    let preparation =
        PortPreparation::new(&field, 0, ExactRatMatrix::identity(4).unwrap()).unwrap();
    let compared = [false, true];
    let map = theta.receiving_map(1).unwrap().clone();
    for (index, opening) in [
        WordOpening::Rest,
        loaded_opening(&field, &theta, &current),
    ]
    .into_iter()
    .enumerate()
    {
        let baseline = open(&field, &theta, &current, &opening);
        let before = baseline.change().unwrap();
        let feature = baseline
            .prospective_feature(&phases, &preparation, &compared)
            .unwrap();
        // The opening is only read: the Word stays unrun and unchanged.
        assert_eq!(baseline.change().unwrap(), before);
        assert_eq!(baseline.ticks(), 0);
        assert_eq!(feature.station(), 1);
        assert_eq!(feature.crossing(), phases.epochs().nth(1).unwrap());
        assert_eq!(feature.opened_at(), baseline.opened_at());
        assert_eq!(feature.tick(), baseline.opened_at() + feature.crossing());
        assert_eq!(feature.compared(), compared.as_slice());
        assert_eq!(feature.baseline_feature().len(), 4);
        assert_eq!(
            (feature.jacobian().rows(), feature.jacobian().columns()),
            (4, 4)
        );
        assert!(feature.prediction_word().closes());
        assert!(feature.prediction_balances().iter().all(|b| b.closes()));

        // The consumer equations against the request path, row by row: R x0 is its baseline
        // reading at the compared station and R J its response.
        let request = vec![vec![Rat::zero(); 4]; 2];
        let control = baseline
            .prospective_port_preparation(&phases, &preparation, &request, &compared)
            .unwrap();
        assert!(feature.agrees_with(&control).unwrap());
        assert_eq!(
            map.apply(feature.baseline_feature()).unwrap(),
            control.baseline()[1]
        );
        assert_eq!(feature.baseline_logits(), control.baseline()[1].as_slice());
        assert_eq!(map.multiply(feature.jacobian()).unwrap(), *control.response());
        assert_eq!(feature.response(), control.response());
        for (station, logits) in feature.baseline().iter().enumerate() {
            assert_eq!(logits, &control.baseline()[station]);
        }

        // x(u) = x0 + J u against an independently executed forward Word (the exact linear Word
        // is affine in the injected wave), for the identity actuators and for sparse waves.
        for u in [
            vec![Rat::zero(); 4],
            vec![rat(1, 4), rat(-1, 8), rat(1, 16), rat(1, 32)],
            vec![integer(1), integer(-2), integer(0), rat(3, 2)],
        ] {
            let added = preparation.map().apply(&u).unwrap();
            assert_eq!(
                feature.feature_at(&u).unwrap(),
                perturbed_feature(&baseline, &current, &phases, 1, &added)
            );
        }

        // The model preparation work is the owner's: the lattice's work equals the receipt's.
        // The unique preimage of the loaded opening is the existing request path's own control
        // (`physical_action.rs`), so the applied receipt is read there.
        if index == 0 {
            continue;
        }
        let u = vec![rat(1, 4), rat(-1, 8), rat(1, 16), rat(1, 32)];
        let mut target = perturbed_target(&baseline, &theta, &current, &phases, &u);
        // The unused station is an unconstrained receiving face, not a zero target.
        target[0] = vec![Rat::zero(); 4];
        let prospect = baseline
            .prospective_port_preparation(&phases, &preparation, &target, &compared)
            .unwrap();
        assert_eq!(prospect.unique_control(), Some(u.as_slice()));
        assert!(feature.agrees_with(&prospect).unwrap());
        let (_, receipt, applied) = prospect.prepare(baseline).unwrap();
        assert!(receipt.closes());
        assert_eq!(receipt.work, feature.preparation_work(&u).unwrap());
        assert_eq!(applied.control(), u.as_slice());
        // A request carries one requested carrier per station of its aperture.
        assert_eq!(applied.requested().len(), phases.aperture());
    }
}

#[test]
fn a_native_feature_read_compares_exactly_one_declared_station() {
    let (field, theta, current) = open_fixture();
    let phases =
        ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();
    let preparation =
        PortPreparation::new(&field, 0, ExactRatMatrix::identity(4).unwrap()).unwrap();
    let baseline = open(&field, &theta, &current, &WordOpening::Rest);
    for compared in [[true, true], [false, false]] {
        assert!(
            baseline
                .prospective_feature(&phases, &preparation, &compared)
                .is_err()
        );
    }
    // Not the complete receiving partition.
    assert!(
        baseline
            .prospective_feature(&phases, &preparation, &[true])
            .is_err()
    );
    // Either single station is a valid read, and the two read different crossings.
    let first = baseline
        .prospective_feature(&phases, &preparation, &[true, false])
        .unwrap();
    let second = baseline
        .prospective_feature(&phases, &preparation, &[false, true])
        .unwrap();
    assert_eq!((first.station(), second.station()), (0, 1));
    assert_eq!(first.crossing() + 1, second.crossing());
    assert_ne!(first.baseline_feature(), second.baseline_feature());
}

// -------------------------------------------------------------------------------------------
// (b) the admitted waves: a declared finite lattice by exact preparation work

/// The closed work form of this fixture, independent of the owner: h = 1 and Y = 2, so
/// `W(u) = h Y (m . v) / 2 + h Y |v|^2 / 4 = m . v + |v|^2 / 2` with `v = B u`.
fn closed_work(m: &[Rat], v: &[Rat]) -> Rat {
    let cross: Rat = m.iter().zip(v).map(|(a, b)| a * b).sum();
    let quadratic: Rat = v.iter().map(|x| x * x).sum();
    cross + quadratic / integer(2)
}

/// The integers `k` with `low <= k / 2^j <= high`, as `i64`.
fn lattice_range(low: &Rat, high: &Rat, j: u32) -> std::ops::RangeInclusive<i64> {
    let scale = integer(1 << j);
    let first = (low * &scale).ceil().to_integer().to_i64().unwrap();
    let last = (high * &scale).floor().to_integer().to_i64().unwrap();
    first..=last
}

#[test]
fn the_admitted_waves_are_the_exact_work_sublevel_lattice_in_lexicographic_order() {
    let (field, theta, current) = open_fixture();
    let phases =
        ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();
    let compared = [false, true];
    let baseline = open(&field, &theta, &current, &WordOpening::Rest);

    // One actuator on source coordinate 0: W(u) = m0 u + u^2 / 2, so at E = 0 the admitted waves
    // are exactly the lattice points between 0 and -2 m0 (hand-checked closed form).
    let single = PortPreparation::new(&field, 0, selecting(&[0])).unwrap();
    let feature = baseline
        .prospective_feature(&phases, &single, &compared)
        .unwrap();
    let m0 = feature.source_wave()[0].clone();
    for k in -8..=8 {
        let u = rat(k, 4);
        assert_eq!(
            feature.preparation_work(&[u.clone()]).unwrap(),
            &m0 * &u + &u * &u / integer(2)
        );
    }
    let j = 2;
    let waves = AdmittedWaves::declare(&feature, j, Rat::zero(), 1 << 12).unwrap();
    let edge = -integer(2) * &m0;
    let (low, high) = if edge < Rat::zero() {
        (edge.clone(), Rat::zero())
    } else {
        (Rat::zero(), edge.clone())
    };
    let expected: Vec<Vec<Rat>> = lattice_range(&low, &high, j)
        .map(|k| vec![rat(k, 1 << j)])
        .collect();
    assert_eq!(waves.controls(), expected.as_slice());
    assert_eq!(waves.exponent(), j);
    assert_eq!(waves.supply(), &Rat::zero());
    // Exact membership both inside and just outside the bounding interval; the do-nothing wave
    // is admitted at a nonnegative supply.
    assert!(waves.contains(&[Rat::zero()]));
    let window = lattice_range(&(&low - integer(2)), &(&high + integer(2)), j);
    for k in window {
        let u = vec![rat(k, 1 << j)];
        let work = feature.preparation_work(&u).unwrap();
        assert_eq!(waves.contains(&u), work <= Rat::zero(), "u = {u:?}");
        assert_eq!(waves.contains(&u), low <= u[0] && u[0] <= high);
    }

    // Four actuators: the admitted set is the lattice within distance sqrt(2) of the wave -m that
    // cancels the source (E = c (2 - |m|^2) with c = 1/2), against a brute-force enumeration of an
    // independent box that contains that ball.
    let identity = PortPreparation::new(&field, 0, ExactRatMatrix::identity(4).unwrap()).unwrap();
    let feature = baseline
        .prospective_feature(&phases, &identity, &compared)
        .unwrap();
    let m: Vec<Rat> = feature.source_wave().to_vec();
    let norm_sq: Rat = m.iter().map(|x| x * x).sum();
    let supply = (integer(2) - &norm_sq) / integer(2);
    let j = 1;
    let waves = AdmittedWaves::declare(&feature, j, supply.clone(), 1 << 14).unwrap();
    let axes: Vec<Vec<i64>> = m
        .iter()
        .map(|mi| lattice_range(&(-mi - integer(2)), &(-mi + integer(2)), j).collect())
        .collect();
    let mut brute: Vec<Vec<Rat>> = Vec::new();
    for &a in &axes[0] {
        for &b in &axes[1] {
            for &c in &axes[2] {
                for &d in &axes[3] {
                    let u: Vec<Rat> = [a, b, c, d].iter().map(|&k| rat(k, 1 << j)).collect();
                    if closed_work(&m, &u) <= supply {
                        brute.push(u);
                    }
                }
            }
        }
    }
    assert!(!brute.is_empty());
    assert_eq!(waves.controls(), brute.as_slice());
    assert!(waves.controls().windows(2).all(|pair| pair[0] < pair[1]));
    assert!(waves.enumerated() >= waves.len());
    // The owner's work function agrees with the closed form on the admitted waves.
    for u in waves.controls() {
        assert_eq!(feature.preparation_work(u).unwrap(), closed_work(&m, u));
        assert!(feature.preparation_work(u).unwrap() <= supply);
    }

    // A supply below the least work (-c |m|^2) declares the valid empty set.
    let none = AdmittedWaves::declare(&feature, j, -(&norm_sq / integer(2)) - integer(1), 1 << 14)
        .unwrap();
    assert!(none.is_empty());
}

#[test]
fn a_preparation_without_full_column_rank_or_beyond_its_capacity_is_refused() {
    let (field, theta, current) = open_fixture();
    let phases =
        ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();
    let compared = [false, true];
    let baseline = open(&field, &theta, &current, &WordOpening::Rest);
    // Two equal columns: a one-dimensional kernel, a quotient this declaration does not make.
    let duplicate = ExactRatMatrix::new(vec![
        vec![Rat::one(), Rat::one()],
        vec![Rat::zero(), Rat::zero()],
        vec![Rat::zero(), Rat::zero()],
        vec![Rat::zero(), Rat::zero()],
    ])
    .unwrap();
    let rank_deficient = PortPreparation::new(&field, 0, duplicate).unwrap();
    let feature = baseline
        .prospective_feature(&phases, &rank_deficient, &compared)
        .unwrap();
    assert!(AdmittedWaves::declare(&feature, 1, rat(1, 4), 1 << 12).is_err());
    // No actuator at all: a zero column.
    let zero = PortPreparation::new(&field, 0, ExactRatMatrix::zero(4, 1).unwrap()).unwrap();
    let feature = baseline
        .prospective_feature(&phases, &zero, &compared)
        .unwrap();
    assert!(AdmittedWaves::declare(&feature, 1, rat(1, 4), 1 << 12).is_err());

    // A bounding box above the declared capacity is refused, never truncated; the same
    // declaration at a capacity that holds it succeeds.
    let single = PortPreparation::new(&field, 0, selecting(&[0])).unwrap();
    let feature = baseline
        .prospective_feature(&phases, &single, &compared)
        .unwrap();
    assert!(AdmittedWaves::declare(&feature, 6, rat(1, 2), 1).is_err());
    let waves = AdmittedWaves::declare(&feature, 6, rat(1, 2), 1 << 16).unwrap();
    assert!(!waves.is_empty());
    assert!(waves.enumerated() > 1);
}

// -------------------------------------------------------------------------------------------
// fixture B: the physical World fixture of `native_action_return.rs`

fn world_fixture() -> (Field, Constitution, Encoded) {
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
    BoundJointWorld::new(
        law,
        HolonState::at(initial, 0),
        face,
        receipt,
        vec![integer(2); 4],
        chart,
        native_origin,
    )
    .unwrap()
}

/// One retained receiver with the actual World bound, before any encounter.
fn world_receiver<'f>(
    field: &'f Field,
    theta: Constitution,
    source: &Encoded,
) -> PhysicalReceiver<'f> {
    let mut receiver =
        PhysicalReceiver::new(field, theta, Current::at_rest(field), WordOpening::Rest).unwrap();
    receiver
        .bind_world(bound_world(field, source.part(0..0).unwrap(), 0))
        .unwrap();
    receiver
}

/// One actual deposited encounter by the existing request path founds the phase statistics: the
/// request is a declared native carrier condition, never the observed target.
fn found_by_request<'f>(
    field: &'f Field,
    theta: Constitution,
    source: &Encoded,
) -> PhysicalReceiver<'f> {
    let declared = &field.receivers()[0];
    let mut receiver = world_receiver(field, theta, source);
    let identity = PortPreparation::new(field, 0, ExactRatMatrix::identity(4).unwrap()).unwrap();
    let request = vec![
        vec![Rat::zero(); 4],
        vec![rat(1, 4), rat(1, 8), rat(1, 16), rat(-1, 32)],
    ];
    let first = receiver
        .prepare_action(source, declared, &identity, &request, &[false, true])
        .unwrap();
    match first.encounter().unwrap() {
        ActionCommunication::Received(received) => {
            assert!(received.closes());
            assert!(received.comparison.as_ref().unwrap().publication.is_some());
        }
        other => panic!("actual law control: {other:?}"),
    }
    receiver
}

/// The probe's actuators: source coordinates 0 and 1 (a small admitted lattice whatever the
/// fixture's source magnitude is).
fn actuators(field: &Field) -> PortPreparation {
    PortPreparation::new(field, 0, selecting(&[0, 1])).unwrap()
}

const COMPARED: [bool; 2] = [false, true];

fn cells(receiver: &PhysicalReceiver<'_>) -> Rat {
    receiver
        .constitution()
        .receiving_law(1)
        .unwrap()
        .phase_statistics()
        .unwrap()
        .cells()
        .clone()
}

/// The candidates (images that meet two outcome blocks) and the argmax of total leverage with the
/// lexicographic tie-break, computed through the family API alone.
fn candidate_table(
    statistics: &PhaseStatistics,
    prior_scale: u32,
    tolerance: &Rat,
    grain: u64,
    features: &[(Vec<Rat>, Vec<Rat>)],
) -> Vec<(Vec<Rat>, Rat, usize)> {
    let family = statistics.family(prior_scale, tolerance).unwrap();
    features
        .iter()
        .map(|(u, x)| {
            let image = family.image(x).unwrap();
            (
                u.clone(),
                image.total_leverage(),
                image.blocks(grain).unwrap().len(),
            )
        })
        .collect()
}

fn argmax(table: &[(Vec<Rat>, Rat, usize)]) -> (usize, Option<Vec<Rat>>) {
    let mut best: Option<&(Vec<Rat>, Rat, usize)> = None;
    let mut count = 0;
    for row in table.iter().filter(|row| row.2 >= 2) {
        count += 1;
        if best.is_none_or(|held| row.1 > held.1 || (row.1 == held.1 && row.0 < held.0)) {
            best = Some(row);
        }
    }
    (count, best.map(|held| held.0.clone()))
}

// -------------------------------------------------------------------------------------------
// (c) ask: Hold when no admitted wave splits, Ask with a leverage probe when one does

#[test]
fn before_any_reading_the_family_is_one_member_and_the_probe_holds_with_its_reason() {
    let (field, theta, source) = world_fixture();
    let declared = &field.receivers()[0];
    let mut receiver = world_receiver(&field, theta, &source);
    let world_before = receiver.participating_world().unwrap().state().clone();
    let opening_before = receiver.opening();
    let commit_before = receiver.constitution().commit();
    {
        let probe = receiver
            .prepare_probe(&source, declared, &actuators(&field), &COMPARED)
            .unwrap();
        let waves = AdmittedWaves::declare(probe.feature(), 1, rat(1, 4), 1 << 12).unwrap();
        // The do-nothing wave costs no work and is admitted at a nonnegative supply.
        assert!(waves.contains(&[Rat::zero(), Rat::zero()]));
        // No reading has reached the receiving map: its family is the prior alone, a single
        // member, whose image meets one block whatever the wave. Nothing separates.
        let held = probe.ask(&waves).unwrap();
        assert_eq!(held.release, ReleaseReturn::Hold);
        assert_eq!(held.held, Some(ProbeHold::NoSeparatingWave));
        assert_eq!(held.candidates, 0);
        assert!(held.control.is_none() && held.prediction.is_none());
        // The empty lattice holds for its own typed reason: a supply below the least work
        // `−c|m|²` (the storage power of the opening's own source wave) admits no wave.
        let least = probe.feature().storage_power(probe.feature().source_wave());
        let none = AdmittedWaves::declare(probe.feature(), 1, -least - integer(1), 1 << 12).unwrap();
        assert!(none.is_empty());
        let empty = probe.ask(&none).unwrap();
        assert_eq!(empty.release, ReleaseReturn::Hold);
        assert_eq!(empty.held, Some(ProbeHold::NoAdmittedWave));
        // Asking executes nothing: no World step, deposit or carry.
        assert_eq!(probe.opened_at(), 0);
    }
    assert_eq!(receiver.participating_world().unwrap().state(), &world_before);
    assert_eq!(receiver.opening(), opening_before);
    assert_eq!(receiver.constitution().commit(), commit_before);
}

#[test]
fn after_one_deposited_encounter_the_retained_family_separates_waves_and_asks() {
    let (field, theta, source) = world_fixture();
    let declared = &field.receivers()[0];
    let mut receiver = found_by_request(&field, theta, &source);
    assert!(cells(&receiver) > Rat::zero());
    let world_before = receiver.participating_world().unwrap().state().clone();
    let opening_before = receiver.opening();
    let carried_ticks = receiver.resident().carried().unwrap().ticks;
    {
        // A SECOND opening of the same receiver and World is admitted: the Resident's current is
        // the source navigator's lift (never moved by a reception), and the next opening is the
        // carry on the World's actual clock.
        let probe = receiver
            .prepare_probe(&source, declared, &actuators(&field), &COMPARED)
            .unwrap();
        assert_eq!(probe.current(), &Current::at_rest(&field));
        assert!(carried_ticks > 0);
        assert_eq!(probe.opened_at(), carried_ticks);
        let waves = AdmittedWaves::declare(probe.feature(), 1, rat(1, 4), 1 << 12).unwrap();
        assert!(waves.contains(&[Rat::zero(), Rat::zero()]));
        let decision = probe.ask(&waves).unwrap();

        // The candidates and the offered wave, recomputed through the family API alone.
        let phases = probe.receiving_phases();
        let law = probe.constitution().receiving_law(1).unwrap();
        let statistics = law.phase_statistics().unwrap();
        let tolerance = phases.tolerance() * statistics.cells();
        let features: Vec<(Vec<Rat>, Vec<Rat>)> = waves
            .controls()
            .iter()
            .map(|u| (u.clone(), probe.feature().feature_at(u).unwrap()))
            .collect();
        let table = candidate_table(
            statistics,
            law.prior_scale(),
            &tolerance,
            phases.grain(),
            &features,
        );
        let (count, best) = argmax(&table);
        assert_eq!(decision.candidates, count);
        assert_eq!(decision.control, best);
        // The family tells at least two admitted waves' readouts apart at this tolerance and grain.
        assert!(
            count > 0,
            "the retained family separates no admitted wave: {table:?}"
        );

        let ReleaseReturn::Ask { probe: offered } = &decision.release else {
            panic!("the release law asks for the offered probe: {:?}", decision.release);
        };
        let ProbeSeparation::Leverage(separation) = &offered.partition else {
            panic!("a continuum family offers a leverage separation: {offered:?}");
        };
        let prediction = decision.prediction.as_ref().unwrap();
        assert!(separation.classes() >= 2);
        assert_eq!(separation.classes(), prediction.blocks.len());
        assert_eq!(separation.leverage(), &prediction.image.total_leverage());
        assert_eq!(separation.against(), &Rat::zero());
        assert!(separation.leverage() > separation.against());
        assert!(decision.held.is_none());
        // The prediction is of the offered wave's native feature, with two feasible witnesses.
        let u = decision.control.as_ref().unwrap();
        assert_eq!(prediction.station, 1);
        assert_eq!(prediction.feature, probe.feature().feature_at(u).unwrap());
        let [(first_block, first_point), (second_block, second_point)] =
            prediction.witnesses.as_ref().unwrap();
        assert_ne!(first_block, second_block);
        assert!(prediction.blocks.contains(first_block));
        assert!(prediction.blocks.contains(second_block));
        assert!(prediction.image.contains(first_point));
        assert!(prediction.image.contains(second_point));
        // The prediction `encounter` would make for the offered wave is this one.
        assert_eq!(probe.predict(u).unwrap().as_ref(), Some(prediction));
    }
    // Asking executes nothing.
    assert_eq!(receiver.participating_world().unwrap().state(), &world_before);
    assert_eq!(receiver.opening(), opening_before);
}

// -------------------------------------------------------------------------------------------
// (d) the encounter executes the chosen wave, (e) the frozen twin

#[test]
fn the_asked_wave_executes_one_actual_encounter_and_the_receipt_is_absorbed() {
    let (field, theta, source) = world_fixture();
    let declared = &field.receivers()[0];
    let mut receiver = found_by_request(&field, theta, &source);
    let cells_before = cells(&receiver);
    let commit_before = receiver.participating_world().unwrap().state().commit;
    let material_before = receiver.constitution().commit();
    let probe = receiver
        .prepare_probe(&source, declared, &actuators(&field), &COMPARED)
        .unwrap();
    let waves = AdmittedWaves::declare(probe.feature(), 1, rat(1, 4), 1 << 12).unwrap();
    let decision = probe.ask(&waves).unwrap();
    let control = decision.control.clone().expect("an asked wave");
    let work = probe.feature().preparation_work(&control).unwrap();
    let grain = probe.receiving_phases().grain();
    let reception = probe.encounter(&waves, &control).unwrap();
    let ActionCommunication::Received(received) = &reception.reception else {
        panic!("the asked wave is actually received: {:?}", reception.reception);
    };
    assert!(received.closes());
    assert!(received.comparison.as_ref().unwrap().publication.is_some());
    // The World commit advanced, both participants continue on the executed clock.
    let world = receiver.participating_world().unwrap();
    assert!(world.state().commit > commit_before);
    assert_eq!(
        world.native_tick().unwrap(),
        receiver.resident().carried().unwrap().ticks
    );
    assert_eq!(received.carry.ticks, world.native_tick().unwrap());
    // The receipt is absorbed: the receiving law's phase statistics count more cells and the
    // material moved.
    assert!(cells(&receiver) > cells_before);
    assert!(receiver.constitution().commit() > material_before);
    // The applied preparation is the asked wave with the owner's work, and no requested
    // consequence: a probe is not a request.
    assert_eq!(received.applied.control(), control.as_slice());
    assert_eq!(received.preparation.work, work);
    assert!(received.preparation.closes());
    assert!(received.applied.requested().is_empty());
    // The prediction was made before the encounter, at the material the wave met.
    let prediction = reception.prediction.as_ref().unwrap();
    assert_eq!(prediction, decision.prediction.as_ref().unwrap());
    // The executed World face against it: the observed lifted class phases at the compared
    // station, in their block; a miss would falsify the NATIVE prediction, never contradict a
    // containment that was not asserted.
    let discrepancy = reception.discrepancy.as_ref().unwrap();
    let observed = received.encounter.observed()[1].as_ref().unwrap();
    assert_eq!(
        discrepancy.observed_block,
        prediction_block_of(observed.phases(), grain)
    );
    assert_eq!(
        discrepancy.predicted,
        prediction.blocks.contains(&discrepancy.observed_block)
    );
    assert_eq!(discrepancy.contained, prediction.image.contains(observed.phases()));
    assert_eq!(discrepancy.falsified(), !discrepancy.predicted);
    if discrepancy.contained {
        assert!(discrepancy.predicted);
    }
}

fn prediction_block_of(phases: &[Rat], grain: u64) -> Vec<BigInt> {
    let scale = Rat::from_integer(BigInt::from(grain));
    phases
        .iter()
        .map(|phase| (phase * &scale).floor().to_integer())
        .collect()
}

#[test]
fn absorbing_the_receipt_contracts_the_leverage_at_the_probed_feature_while_the_frozen_twin_is_unchanged()
 {
    let (field, theta, source) = world_fixture();
    let declared = &field.receivers()[0];
    let mut receiver = found_by_request(&field, theta, &source);
    // The frozen twin: the statistics as they stand before the probe's receipt, cloned.
    let law = receiver.constitution().receiving_law(1).unwrap();
    let frozen = law.phase_statistics().unwrap().clone();
    let ridge = law.prior_scale();
    let probe = receiver
        .prepare_probe(&source, declared, &actuators(&field), &COMPARED)
        .unwrap();
    let phases = probe.receiving_phases().clone();
    let grain = phases.grain();
    let waves = AdmittedWaves::declare(probe.feature(), 1, rat(1, 4), 1 << 12).unwrap();
    // The SAME candidate features are scored before and after: they are the native features at
    // this opening, fixed once.
    let features: Vec<(Vec<Rat>, Vec<Rat>)> = waves
        .controls()
        .iter()
        .map(|u| (u.clone(), probe.feature().feature_at(u).unwrap()))
        .collect();
    let tolerance_before = phases.tolerance() * frozen.cells();
    let before = candidate_table(&frozen, ridge, &tolerance_before, grain, &features);
    let (count, chosen) = argmax(&before);
    assert!(
        count > 0,
        "the retained family separates no admitted wave: {before:?}"
    );
    let chosen = chosen.unwrap();
    // The probe asks exactly the frozen statistics' argmax, and recomputing is identical.
    let decision = probe.ask(&waves).unwrap();
    assert_eq!(decision.control.as_ref(), Some(&chosen));
    assert_eq!(
        before,
        candidate_table(&frozen, ridge, &tolerance_before, grain, &features)
    );

    // Absorb that receipt by actually executing the chosen wave.
    let reception = probe.encounter(&waves, &chosen).unwrap();
    assert!(matches!(
        reception.reception,
        ActionCommunication::Received(_)
    ));
    let law = receiver.constitution().receiving_law(1).unwrap();
    let absorbed = law.phase_statistics().unwrap();
    assert!(absorbed.cells() > frozen.cells());

    // At the SAME feature and the same ridge the absorbed receipt adds a positive semidefinite
    // term to each class's shape A_c, so the class leverages x^T A_c^-1 x do not increase, and
    // strictly decrease where the receipt's feature is correlated with the probed one in A_c^-1.
    let tolerance_after = phases.tolerance() * absorbed.cells();
    let after = candidate_table(absorbed, ridge, &tolerance_after, grain, &features);
    let probed_before = before.iter().find(|row| row.0 == chosen).unwrap();
    let probed_after = after.iter().find(|row| row.0 == chosen).unwrap();
    assert!(
        probed_after.1 < probed_before.1,
        "the leverage at the probed feature contracts: {} -> {}",
        probed_before.1,
        probed_after.1
    );
    for (row_before, row_after) in before.iter().zip(&after) {
        assert_eq!(row_before.0, row_after.0);
        assert!(row_after.1 <= row_before.1);
    }
    // The frozen twin is untouched by the absorption: recomputed, it is the same table and the
    // same choice. The post-absorption choice may differ; it is read, not asserted equal.
    assert_eq!(
        before,
        candidate_table(&frozen, ridge, &tolerance_before, grain, &features)
    );
    assert_eq!(argmax(&before).1, Some(chosen));
    let (_after_count, _after_choice) = argmax(&after);
}

// -------------------------------------------------------------------------------------------
// (f) two asked probes on ONE receiver and ONE World, and the refusals

#[test]
fn successive_probes_run_on_one_receiver_and_one_world_and_each_is_actually_received() {
    let (field, theta, source) = world_fixture();
    let declared = &field.receivers()[0];
    let mut receiver = world_receiver(&field, theta, &source);
    let mut previous = Rat::zero();
    let mut outcomes: Vec<&str> = Vec::new();
    for round in 0..3 {
        // The opening is the preceding encounter's carry on the World's actual clock.
        let carried = receiver.resident().carried().map(|carry| carry.ticks);
        let world_tick = receiver.participating_world().unwrap().native_tick().unwrap();
        assert_eq!(carried.unwrap_or(0), world_tick);
        let probe = receiver
            .prepare_probe(&source, declared, &actuators(&field), &COMPARED)
            .unwrap();
        assert_eq!(probe.opened_at(), world_tick);
        let waves = AdmittedWaves::declare(probe.feature(), 1, rat(1, 4), 1 << 12).unwrap();
        let decision = probe.ask(&waves).unwrap();
        let control = match (&decision.release, &decision.control) {
            (ReleaseReturn::Ask { .. }, Some(wave)) => {
                outcomes.push("ask");
                wave.clone()
            }
            // Before any reading nothing separates the waves; the do-nothing wave (admitted at a
            // nonnegative supply) founds the statistics. It was not asked. A hold after a reading
            // is recorded below, and the receiver is exercised on every round whatever the
            // family says: the admission of a later opening does not depend on the Ask.
            (ReleaseReturn::Hold, None) => {
                assert_eq!(decision.held, Some(ProbeHold::NoSeparatingWave));
                outcomes.push("hold");
                vec![Rat::zero(); 2]
            }
            other => panic!("round {round}: {other:?}"),
        };
        let reception = probe.encounter(&waves, &control).unwrap();
        let ActionCommunication::Received(received) = &reception.reception else {
            panic!("round {round}: not actually received: {:?}", reception.reception);
        };
        assert!(received.closes(), "round {round}");
        assert!(received.comparison.is_ok(), "round {round}");
        assert!(reception.discrepancy.is_some(), "round {round}");
        // Both participants continue on one clock: the World's native tick is the carried ticks.
        let world = receiver.participating_world().unwrap();
        let carry = receiver.resident().carried().unwrap();
        assert_eq!(world.native_tick().unwrap(), carry.ticks, "round {round}");
        assert_eq!(received.carry.ticks, carry.ticks, "round {round}");
        assert!(carry.ticks > world_tick, "round {round}");
        // The receipt is absorbed after each.
        let now = cells(&receiver);
        assert!(now > previous, "round {round}");
        previous = now;
    }
    // The first reading is the do-nothing wave (a hold: the prior alone is one member); the family
    // founded by it then separates the admitted waves and asks, round after round.
    assert_eq!(outcomes, ["hold", "ask", "ask"]);
}

#[test]
fn a_control_of_the_wrong_shape_is_refused_before_either_participant_moves() {
    let (field, theta, source) = world_fixture();
    let declared = &field.receivers()[0];
    let mut receiver = world_receiver(&field, theta, &source);
    let world_before = receiver.participating_world().unwrap().state().clone();
    let opening_before = receiver.opening();
    let commit_before = receiver.constitution().commit();
    let probe = receiver
        .prepare_probe(&source, declared, &actuators(&field), &COMPARED)
        .unwrap();
    let waves = AdmittedWaves::declare(probe.feature(), 1, rat(1, 4), 1 << 12).unwrap();
    // Two actuators, one control.
    assert!(probe.encounter(&waves, &[Rat::zero()]).is_err());
    assert_eq!(receiver.participating_world().unwrap().state(), &world_before);
    assert_eq!(receiver.opening(), opening_before);
    assert_eq!(receiver.constitution().commit(), commit_before);
    // A probe on a station set other than exactly one compared future is refused at preparation.
    assert!(
        receiver
            .prepare_probe(&source, declared, &actuators(&field), &[false, false])
            .is_err()
    );
    assert_eq!(receiver.participating_world().unwrap().state(), &world_before);
}

/// **An admitted wave is a checked membership** (Epime's review, October 8): a control outside its
/// declaration, though of the right shape, is refused before either participant moves.
#[test]
fn a_control_outside_its_declaration_is_refused_before_either_participant_moves() {
    let (field, theta, source) = world_fixture();
    let declared = &field.receivers()[0];
    let mut receiver = world_receiver(&field, theta, &source);
    let world_before = receiver.participating_world().unwrap().state().clone();
    let opening_before = receiver.opening();
    let commit_before = receiver.constitution().commit();
    let probe = receiver
        .prepare_probe(&source, declared, &actuators(&field), &COMPARED)
        .unwrap();
    let waves = AdmittedWaves::declare(probe.feature(), 1, rat(1, 4), 1 << 12).unwrap();
    assert!(waves.declared_for(probe.feature()));
    let outside = vec![integer(1 << 20), integer(1 << 20)];
    assert!(!waves.contains(&outside));
    assert!(probe.encounter(&waves, &outside).is_err());
    assert_eq!(receiver.participating_world().unwrap().state(), &world_before);
    assert_eq!(receiver.opening(), opening_before);
    assert_eq!(receiver.constitution().commit(), commit_before);
}
