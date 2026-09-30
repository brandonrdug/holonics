//! The parametron re-derived (`hnn::ring`, Lean `HNN/Floquet`, `Objects/ParametronLock`): the
//! Floquet monodromy of a pumped ring and its certificate, the bifurcation, phase-sensitive
//! amplification at the locked sheet, the receiving bank's reading of a relative phase, and its
//! reading of a passage's turn. One test per stated law and per refusal.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use crate::hnn::HnnError;
use crate::hnn::chart::WordLattice;
use crate::hnn::ring::{
    Floquet, FloquetReading, FloquetRefusal, Growth, PumpDeclaration, PumpSchedule, PumpStep,
    ReceivingBank, ResonatorMaterial, ResonatorOperands, ResonatorRemainders, TurnReading, lock,
};
use crate::holon::parametron::Carrier;
use crate::ratio::gaussian::GaussianRat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::dot;
use crate::ratio::{Rat, integer, rat};

fn identity(n: usize) -> ExactRatMatrix {
    ExactRatMatrix::identity(n).unwrap()
}

fn zero(n: usize) -> ExactRatMatrix {
    ExactRatMatrix::zero(n, n).unwrap()
}

/// The quarter turn `i^k` as a carrier.
fn quarter(k: usize) -> Carrier {
    let (cos, sin) = match k % 4 {
        0 => (1, 0),
        1 => (0, 1),
        2 => (-1, 0),
        _ => (0, -1),
    };
    Carrier::new(integer(cos), integer(sin)).unwrap()
}

/// One complex node: `C = I`, `K = kI`, no dissipation but the port, and its pump.
fn node(stiffness: Rat, pump: Option<PumpDeclaration>) -> ResonatorMaterial {
    ResonatorMaterial::new(identity(2), identity(2).scaled(&stiffness), zero(2), pump).unwrap()
}

fn standing(strength: Rat) -> PumpDeclaration {
    PumpDeclaration::new(strength, quarter(0), PumpStep::Stand).unwrap()
}

/// The declared port and hop of these tests: `Y = 16`, `h = 1`.
fn operands(material: &ResonatorMaterial) -> ResonatorOperands {
    ResonatorOperands::at_cut(0, material, &integer(16), &Rat::one(), None).unwrap()
}

fn energy(metric: &ExactRatMatrix, state: &[Rat]) -> Rat {
    dot(state, &metric.apply(state).unwrap())
}

/// The executed, undriven passage of `ticks` ticks from a state, every balance closing.
fn run(operands: &ResonatorOperands, state: &[Rat], ticks: usize) -> Vec<Rat> {
    let n = operands.width();
    let drive = vec![Rat::zero(); n];
    let mut state = [state[..n].to_vec(), state[n..].to_vec()];
    for tick in 0..ticks {
        let step = operands
            .step(
                tick,
                &drive,
                [&state[0], &state[1]],
                &ResonatorRemainders::default(),
                None,
            )
            .unwrap();
        assert!(step.closes());
        state = step.state;
    }
    [state[0].clone(), state[1].clone()].concat()
}

/// Lean `HNN/Floquet.{standing_fixed_point_iff, pumped_inphase_axis, floquet_passive}`: a standing
/// pump's bifurcation is where its in-phase stiffness `k − 2p` vanishes. Below it every multiplier is
/// inside the unit circle and the storage is certified at `ρ = 1`; at it a multiplier sits on the
/// circle (the edge); past it one is outside, and the growth is enclosed and certified.
#[test]
fn a_standing_pump_is_passive_below_its_bifurcation_and_grows_past_it() {
    let below = Floquet::of(&operands(&node(Rat::one(), Some(standing(rat(3, 8)))))).unwrap();
    let edge = Floquet::of(&operands(&node(Rat::one(), Some(standing(rat(1, 2)))))).unwrap();
    let above = Floquet::of(&operands(&node(Rat::one(), Some(standing(rat(5, 8)))))).unwrap();
    let grain = 8;
    let reading = below.decide(grain).unwrap();
    assert!(reading.is_silent());
    assert_eq!(reading.certificate().growth(), &Rat::one());
    match edge.decide(grain).unwrap() {
        FloquetReading::Edge { on_circle, .. } => assert!(on_circle >= 1),
        other => panic!("the bifurcation reads the edge, not {other:?}"),
    }
    match above.decide(grain).unwrap() {
        FloquetReading::Growing { certificate, lower } => {
            assert!(lower > Rat::one());
            assert!(certificate.growth() > &lower);
            assert!(certificate.growth() - &lower <= rat(1, 256));
            let at_lower = above.placement(&lower).unwrap();
            assert!(at_lower.outside + at_lower.on >= 1);
            let at_upper = above.placement(certificate.growth()).unwrap();
            assert_eq!((at_upper.outside, at_upper.on), (0, 0));
        }
        other => panic!("past the bifurcation the ring grows, not {other:?}"),
    }
    // Every placement counts every multiplier.
    for radius in [rat(1, 2), Rat::one(), integer(2)] {
        let placed = above.placement(&radius).unwrap();
        assert_eq!(placed.outside + placed.on + placed.inside, 4);
    }
}

/// Lean `HNN/Ring.ring_tick_port_balance`, `HNN/Floquet.storage_form_certifies_passive`: below the
/// bifurcation the storage form `diag(K_ψ, C)` is itself a Floquet metric at `ρ = 1`, no exterior
/// attainment needed; past it, the form is indefinite and is refused.
#[test]
fn below_the_bifurcation_the_storage_form_is_the_certificate() {
    for (strength, passive) in [(rat(3, 8), true), (rat(5, 8), false)] {
        let material = node(Rat::one(), Some(standing(strength)));
        let floquet = Floquet::of(&operands(&material)).unwrap();
        let stiffness = material.pumped_stiffness(0).unwrap();
        let form = ExactRatMatrix::shaped(
            4,
            4,
            (0..4)
                .map(|i| {
                    (0..4)
                        .map(|j| match (i < 2, j < 2) {
                            (true, true) => stiffness.get(i, j).unwrap().clone(),
                            (false, false) => identity(2).get(i - 2, j - 2).unwrap().clone(),
                            _ => Rat::zero(),
                        })
                        .collect()
                })
                .collect(),
        )
        .unwrap();
        let certified = floquet.certify(&form, &Rat::one());
        if passive {
            assert!(certified.unwrap().is_passive());
        } else {
            assert_eq!(
                certified.unwrap_err(),
                HnnError::UncertifiedFloquet {
                    ring: 0,
                    refusal: FloquetRefusal::MetricNotDefinite
                }
            );
        }
    }
}

/// Lean `HNN/Floquet.{floquet_energy_step, floquet_energy_iterate}`: the certificate bounds the
/// executed passage's energy in its metric by `ρ²` a period, on every seed, exactly.
#[test]
fn the_certificate_bounds_the_executed_energy() {
    let operands = operands(&node(Rat::one(), Some(standing(rat(5, 8)))));
    let floquet = Floquet::of(&operands).unwrap();
    let reading = floquet.decide(6).unwrap();
    let certificate = reading.certificate();
    let seeds = [
        vec![Rat::one(), Rat::zero(), Rat::zero(), Rat::zero()],
        vec![rat(3, 5), rat(-4, 5), rat(1, 2), Rat::zero()],
        vec![Rat::zero(), Rat::one(), Rat::zero(), rat(-1, 3)],
    ];
    for seed in &seeds {
        let start = energy(certificate.metric(), seed);
        for periods in 1..=4usize {
            let state = run(&operands, seed, periods);
            // The executed passage is the monodromy's power.
            let mut expected = seed.clone();
            for _ in 0..periods {
                expected = floquet.monodromy().apply(&expected).unwrap();
            }
            assert_eq!(state, expected);
            assert!(
                energy(certificate.metric(), &state)
                    <= certificate.energy_factor(periods as u64) * &start
            );
        }
    }
}

/// Every refusal of the certificate is typed: a negative growth, a metric of the wrong shape or
/// not positive definite, and a growth the monodromy exceeds; a Stein operator singular at the
/// declared growth is refused by the attainment.
#[test]
fn a_wrong_metric_or_growth_is_refused() {
    let floquet = Floquet::of(&operands(&node(Rat::one(), Some(standing(rat(5, 8)))))).unwrap();
    let refused = |refusal| HnnError::UncertifiedFloquet { ring: 0, refusal };
    assert_eq!(
        floquet.certify(&identity(4), &integer(-1)).unwrap_err(),
        refused(FloquetRefusal::NegativeGrowth)
    );
    assert_eq!(
        floquet.certify(&identity(2), &Rat::one()).unwrap_err(),
        refused(FloquetRefusal::MetricShape)
    );
    let mut indefinite = identity(4).to_rows();
    indefinite[3][3] = integer(-1);
    assert_eq!(
        floquet
            .certify(&ExactRatMatrix::new(indefinite).unwrap(), &Rat::one())
            .unwrap_err(),
        refused(FloquetRefusal::MetricNotDefinite)
    );
    assert_eq!(
        floquet.certify(&identity(4), &Rat::one()).unwrap_err(),
        refused(FloquetRefusal::GrowthExceeded)
    );
    // `ρ = 1` against the lossless identity map: `ρ² = μ_iμ_j = 1`.
    assert_eq!(
        crate::hnn::ring::attain_metric(0, &identity(2), &Rat::one()).unwrap_err(),
        refused(FloquetRefusal::Unattainable)
    );
}

/// The rotating pump (Swing record §4, "The pump"): a quarter-turn pump resonates at a strength the
/// standing pump leaves passive, its growing multiplier negative (a half-turn with a boost, the
/// subharmonic lock); a half-turn pump alternates perpendicular axes and stays passive even past the
/// standing bifurcation.
#[test]
fn a_rotating_pump_resonates_below_the_standing_bifurcation() {
    let rotating = |strength: Rat, step: PumpStep| {
        Floquet::of(&operands(&node(
            Rat::one(),
            Some(PumpDeclaration::new(strength, quarter(0), step).unwrap()),
        )))
        .unwrap()
    };
    let quarter_pump = rotating(rat(1, 4), PumpStep::Quarter);
    match quarter_pump.decide(6).unwrap() {
        FloquetReading::Growing { lower, .. } => {
            // The growing multiplier is negative: the characteristic polynomial changes sign on
            // `(−∞, −lower]`, not on `[lower, ∞)`.
            let at = |x: &Rat| quarter_pump.characteristic().evaluate(x);
            assert!(at(&-&lower).is_negative() != at(&integer(-1024)).is_negative());
        }
        other => panic!("the quarter-turn pump resonates at p = 1/4, not {other:?}"),
    }
    assert!(
        rotating(rat(1, 4), PumpStep::Stand)
            .decide(6)
            .unwrap()
            .is_silent()
    );
    assert!(
        rotating(Rat::one(), PumpStep::Half)
            .decide(6)
            .unwrap()
            .is_silent()
    );
}

/// Lean `HNN/Ring.ring_tick_executed_energy_balance` under a schedule: the executed balance closes
/// at every tick of a modulated pump, on the exact law and on the lattice word's certified charts,
/// and the monodromy of the charted ticks is read from their executed solves.
#[test]
fn the_executed_balance_closes_under_a_modulated_pump() {
    let material = node(Rat::one(), None);
    let schedule = PumpSchedule::modulated(
        &PumpDeclaration::new(rat(5, 8), quarter(0), PumpStep::Quarter).unwrap(),
        &[quarter(1), quarter(3), quarter(2)],
    )
    .unwrap();
    assert_eq!(schedule.period(), 3);
    // tick t: i^t · c_t
    assert_eq!(schedule.carrier(0), &quarter(1).as_gaussian());
    assert_eq!(schedule.carrier(1), &quarter(0).as_gaussian());
    assert_eq!(schedule.carrier(2), &quarter(0).as_gaussian());
    let lattice = WordLattice::by_rule(16, 6, 6, 4);
    for lattice in [None, Some(&lattice)] {
        let operands = ResonatorOperands::scheduled(
            0,
            &material,
            &schedule,
            &integer(16),
            &Rat::one(),
            lattice,
        )
        .unwrap();
        assert_eq!(operands.phase_at(7), 1);
        let drive = vec![rat(1, 3), rat(-1, 5)];
        let mut state = [vec![rat(1, 2), Rat::zero()], vec![Rat::zero(), rat(1, 4)]];
        let mut remainders = ResonatorRemainders::default();
        for tick in 0..9 {
            let step = operands
                .step(
                    tick,
                    &drive,
                    [&state[0], &state[1]],
                    &remainders,
                    lattice.map(WordLattice::transient).as_ref(),
                )
                .unwrap();
            assert!(step.closes(), "tick {tick}");
            remainders = step.remainders().clone();
            state = step.state;
        }
        assert_eq!(Floquet::of(&operands).unwrap().ticks().len(), 3);
    }
    // A scheduled pump replaces the declared one.
    assert!(
        ResonatorOperands::scheduled(
            0,
            &node(Rat::one(), Some(standing(rat(1, 4)))),
            &schedule,
            &integer(16),
            &Rat::one(),
            None,
        )
        .is_err()
    );
}

/// Lean `HNN/Floquet.{inphase_growing, inphase_growing_coordinate, pumped_inphase_axis}`:
/// phase-sensitive amplification at the locked sheet. Past the bifurcation a seed on the
/// displacement locks to the sheet of its in-phase projection, `sign cos(φ_in − φ_a)`; a seed on
/// the quadrature line is held; the half-turn of the seed exchanges the sheets (the lock is linear,
/// then threshold).
#[test]
fn the_linear_lock_reads_its_seed_against_the_pump_axis() {
    let axis = Carrier::at(&rat(1, 3)); // (4/5, 3/5)
    let pump = PumpDeclaration::new(rat(5, 8), axis.clone(), PumpStep::Stand).unwrap();
    let operands = operands(&node(Rat::one(), Some(pump)));
    for parameter in [
        rat(0, 1),
        rat(1, 2),
        rat(2, 1),
        rat(-1, 3),
        rat(5, 1),
        rat(-7, 2),
    ] {
        let input = Carrier::at(&parameter);
        let expected = input.cos_between(&axis);
        for half_turn in [false, true] {
            let seed = if half_turn {
                input.half_turn()
            } else {
                input.clone()
            };
            let locked = lock(
                &operands,
                [
                    &[seed.cos().clone(), seed.sin().clone()],
                    &[Rat::zero(), Rat::zero()],
                ],
                12,
                &axis,
            )
            .unwrap();
            assert!(locked.closed);
            let sign = if half_turn {
                -&expected
            } else {
                expected.clone()
            };
            assert_eq!(
                locked.sheets[0],
                (!sign.is_zero()).then(|| sign.is_negative())
            );
        }
    }
    // A seed on the quadrature line is held.
    let quadrature = Carrier::new(-axis.sin().clone(), axis.cos().clone()).unwrap();
    let held = lock(
        &operands,
        [
            &[quadrature.cos().clone(), quadrature.sin().clone()],
            &[Rat::zero(), Rat::zero()],
        ],
        6,
        &axis,
    )
    .unwrap();
    assert_eq!(held.sheets[0], None);
}

/// Lean `HNN/Floquet.{reflection_mul_reflection, reflection_pair_trace,
/// no_linear_threshold_reads_relative_phase}`: the receiving bank reads the relative phase of the two
/// cells crossing its section. Member `j`'s pump (`a = 1`, step `i^j`) is modulated by the crossing
/// cells `(c_e, c_l)`, so its carriers are `(c_e, i^j c_l)`: it locks exactly when they align,
/// `c_e = i^j c_l`, and is certified silent otherwise. Over all sixteen pairs of quarter-turn cells
/// the bank's class is the relative quarter-turn class `x_e − x_l`.
#[test]
fn the_bank_reads_the_relative_phase_of_two_crossing_cells() {
    let bank = ReceivingBank::new(
        node(Rat::one(), None),
        [
            PumpStep::Stand,
            PumpStep::Quarter,
            PumpStep::Half,
            PumpStep::ThreeQuarters,
        ]
        .into_iter()
        .map(|step| PumpDeclaration::new(rat(5, 8), quarter(0), step).unwrap())
        .collect(),
        integer(16),
        Rat::one(),
        6,
    )
    .unwrap();
    for early in 0..4 {
        for late in 0..4 {
            let reading = bank.read(&[quarter(early), quarter(late)]).unwrap();
            assert_eq!(reading.class(), Some((early + 4 - late) % 4));
            // The half-turn of both cells leaves the reading.
            let turned = bank
                .read(&[quarter(early).half_turn(), quarter(late).half_turn()])
                .unwrap();
            assert_eq!(turned.class(), reading.class());
        }
    }
    // An unpumped material and a positive port are declarations of the bank.
    assert!(
        ReceivingBank::new(
            node(Rat::one(), Some(standing(rat(1, 4)))),
            vec![standing(rat(1, 4))],
            integer(16),
            Rat::one(),
            6,
        )
        .is_err()
    );
}

/// Lean `HNN/Floquet.{floquet_tick_product, floquet_metric_change}`: the consumer's factor
/// `(γ_hi/γ_lo) ρ^(2m) (max σ_t²)^(s − Tm)` bounds the executed passage's Euclidean energy over any
/// span, from any phase.
#[test]
fn the_consumer_bound_covers_every_span_of_the_executed_passage() {
    let material = node(
        Rat::one(),
        Some(PumpDeclaration::new(rat(1, 4), quarter(0), PumpStep::Quarter).unwrap()),
    );
    let operands = operands(&material);
    let floquet = Floquet::of(&operands).unwrap();
    let reading = floquet.decide(6).unwrap();
    let bound = floquet.bound(reading.certificate(), 6).unwrap();
    assert!(bound.low.is_positive() && bound.low <= bound.high);
    let seeds = [
        vec![Rat::one(), Rat::zero(), Rat::zero(), Rat::zero()],
        vec![rat(1, 2), rat(-1, 3), rat(1, 5), rat(2, 7)],
    ];
    for seed in &seeds {
        let n = operands.width();
        let drive = vec![Rat::zero(); n];
        let mut states = vec![seed.clone()];
        let mut state = [seed[..n].to_vec(), seed[n..].to_vec()];
        for tick in 0..11 {
            let step = operands
                .step(
                    tick,
                    &drive,
                    [&state[0], &state[1]],
                    &ResonatorRemainders::default(),
                    None,
                )
                .unwrap();
            state = step.state;
            states.push([state[0].clone(), state[1].clone()].concat());
        }
        for start in 0..states.len() {
            for end in start..states.len() {
                let from = dot(&states[start], &states[start]);
                let to = dot(&states[end], &states[end]);
                assert!(to <= bound.reach((end - start) as u64) * from);
            }
        }
    }
}

// -------------------------------------------------------------------------------------------
// the passage's monodromy: the bank reads a superposed passage

/// The four members of the declared bank: axis `1`, steps `i^j`, at strength `p`.
fn members(strength: Rat) -> Vec<PumpDeclaration> {
    [
        PumpStep::Stand,
        PumpStep::Quarter,
        PumpStep::Half,
        PumpStep::ThreeQuarters,
    ]
    .into_iter()
    .map(|step| PumpDeclaration::new(strength.clone(), quarter(0), step).unwrap())
    .collect()
}

/// A drawn turn of placed amplitudes on the dyadic lattice `2^(−bits − 1)`, within `[−1/2, 1/2]` a
/// coordinate.
fn drawn_turn(seed: u64, ticks: usize, bits: u32) -> Vec<GaussianRat> {
    let mut draw = crate::holarchy::terrain::Draw::new(seed);
    let unit = BigInt::one() << (bits + 1);
    let mut coordinate = || {
        let n = draw.below(1 << bits) as i64 - (1 << (bits - 1));
        Rat::new(BigInt::from(n), unit.clone())
    };
    (0..ticks)
        .map(|_| GaussianRat::new(coordinate(), coordinate()))
        .collect()
}

/// **The placed schedule of unit cells is the modulated schedule**: `PumpSchedule::placed` with
/// unit carriers equals `PumpSchedule::modulated`, and its carrier at tick `t` is `a² s^t z_t`.
#[test]
fn the_placed_schedule_of_unit_cells_is_the_modulated_schedule() {
    let pump = PumpDeclaration::new(rat(5, 8), quarter(0), PumpStep::Quarter).unwrap();
    let cells = [quarter(1), quarter(3), quarter(2), quarter(0)];
    let placed = PumpSchedule::placed(
        &pump,
        &cells.iter().map(Carrier::as_gaussian).collect::<Vec<_>>(),
    )
    .unwrap();
    assert_eq!(placed, PumpSchedule::modulated(&pump, &cells).unwrap());
    let amplitude = GaussianRat::new(rat(3, 8), rat(-1, 4));
    let scaled = PumpSchedule::placed(&pump, &[GaussianRat::zero(), amplitude.clone()]).unwrap();
    assert!(scaled.carrier(0).is_zero());
    // a² s^1 z_1 with a = 1, s = i.
    assert_eq!(scaled.carrier(1), &GaussianRat::i().mul(&amplitude));
}

/// **The turn's reading is the executed monodromy's growth** (`ReceivingBank::read_turn`, the
/// monodromy carried as `N/Δ` on integers and its growth enclosed by the Schur–Cohn test from an
/// attained bracket): every member's enclosure equals the one read from `Floquet::of` on the
/// scheduled operands, and the Cayley placement certifies it (some multiplier outside or on
/// `lower`, none outside or on `upper`); the joint reading is the largest member's, and its
/// certificate holds on every member with every executed tick closed.
#[test]
fn the_turn_reading_is_the_executed_monodromys_growth() {
    let grain = 12;
    for (seed, strength) in [(3, rat(1, 2)), (5, Rat::one())] {
        let bank = ReceivingBank::new(
            node(Rat::one(), None),
            members(strength),
            integer(16),
            Rat::one(),
            6,
        )
        .unwrap();
        let amplitudes = drawn_turn(seed, 8, 6);
        let reading = bank.read_turn(&amplitudes, grain).unwrap();
        for (member, pump) in bank.pumps().iter().enumerate() {
            let operands = ResonatorOperands::scheduled(
                member,
                &node(Rat::one(), None),
                &PumpSchedule::placed(pump, &amplitudes).unwrap(),
                &integer(16),
                &Rat::one(),
                None,
            )
            .unwrap();
            let floquet = Floquet::of(&operands).unwrap();
            let growth = &reading.members[member];
            assert_eq!(growth, &floquet.growth(grain));
            let at_lower = floquet.placement(&growth.lower).unwrap();
            let at_upper = floquet.placement(&growth.upper).unwrap();
            assert!(at_lower.outside + at_lower.on > 0);
            assert_eq!(at_upper.outside + at_upper.on, 0);
            assert!(&growth.upper - &growth.lower <= &growth.upper * rat(1, 1 << grain));
        }
        let largest = reading
            .members
            .iter()
            .map(|growth| growth.upper.clone())
            .max()
            .unwrap();
        assert_eq!(reading.joint.upper, largest);
        let certificate = bank.certify_turn(&amplitudes, &reading, grain).unwrap();
        assert_eq!(certificate.certificates.len(), 4);
        assert_eq!(certificate.closed, certificate.ticks);
        assert_eq!(certificate.ticks, 4 * 8);
    }
}

/// **A member reads a turn only when its pump's period divides it**: a turn of 6 ticks is refused by
/// the quarter-turn members and read by the standing and half-turn ones.
#[test]
fn a_member_reads_a_turn_only_when_its_period_divides_it() {
    let amplitudes = drawn_turn(7, 6, 4);
    let whole = ReceivingBank::new(
        node(Rat::one(), None),
        members(Rat::one()),
        integer(16),
        Rat::one(),
        6,
    )
    .unwrap();
    assert!(matches!(
        whole.read_turn(&amplitudes, 8),
        Err(HnnError::Resonator { ring: 1, .. })
    ));
    let commensurate = ReceivingBank::new(
        node(Rat::one(), None),
        members(Rat::one())
            .into_iter()
            .filter(|pump| pump.phases() <= 2)
            .collect(),
        integer(16),
        Rat::one(),
        6,
    )
    .unwrap();
    assert_eq!(commensurate.read_turn(&amplitudes, 8).unwrap().members.len(), 2);
}

/// **The bank reads a passage's spectral line, and its lock's flip continues it** (known truth of
/// the passage's reading and of generation by the bank): a turn of 8 unit cells
/// `z_t = u·i^(−jt)` steps by one quarter-turn class `j` a crossing (every class `j`, every offset
/// `u`). Member `m`'s carriers `i^(mt) z_t` then turn by `m − j` a tick, so its reading depends only
/// on `m − j (mod 4)`: the line's own member (a standing pump) grows in `[46, 1473/32]`, the two
/// quarter-turn neighbours (the pump nearest the node's parametric resonance `2θ`,
/// `e^(iθ) = (3 + 4i)/5` less its port's loss) in `[1061/16, 531/8]`, and the half-turn partner is
/// certified silent in `[827/1024, 1655/2048]` (its axes cancel): the lock pattern names the line's
/// class. With the last cell left open, the candidate completing the line reads the joint growth
/// `[1061/16, 531/8]`, strictly above every other candidate's, and the bank locks there.
#[test]
fn the_bank_reads_a_passages_spectral_line_and_its_flip_continues_it() {
    let bank = ReceivingBank::new(
        node(Rat::one(), None),
        members(rat(5, 8)),
        integer(16),
        Rat::one(),
        6,
    )
    .unwrap();
    let growth = |lower: Rat, upper: Rat| Growth { lower, upper };
    let by_difference = [
        growth(integer(46), rat(1473, 32)),
        growth(rat(1061, 16), rat(531, 8)),
        growth(rat(827, 1024), rat(1655, 2048)),
        growth(rat(1061, 16), rat(531, 8)),
    ];
    for class in 0..4usize {
        for offset in 0..4usize {
            let cell = |t: usize| quarter(offset + 4 * 8 - (class * t) % 4).as_gaussian();
            let line: Vec<GaussianRat> = (0..8).map(cell).collect();
            let reading = bank.read_turn(&line, 10).unwrap();
            for (member, read) in reading.members.iter().enumerate() {
                assert_eq!(read, &by_difference[(member + 4 - class) % 4]);
            }
            let silent: Vec<usize> = (0..4)
                .filter(|&member| !reading.members[member].is_locked())
                .collect();
            assert_eq!(silent, vec![(class + 2) % 4]);
            let candidates: Vec<TurnReading> = (0..4)
                .map(|candidate| {
                    let mut turn = line.clone();
                    turn[7] = quarter(candidate).as_gaussian();
                    bank.read_turn(&turn, 10).unwrap()
                })
                .collect();
            let completing = (offset + 4 * 8 - (class * 7) % 4) % 4;
            let top = &candidates[completing].joint;
            assert!(top.is_locked());
            for (candidate, read) in candidates.iter().enumerate() {
                if candidate != completing {
                    assert!(top.exceeds(&read.joint));
                }
            }
        }
    }
}

// -------------------------------------------------------------------------------------------
// the bank's second-order face

/// The bank of these tests: one node `C = I`, `K = I`, `Y = 16`, `h = 1`, the four members at
/// `p = 5/8`.
fn declared_bank() -> ReceivingBank {
    ReceivingBank::new(
        node(Rat::one(), None),
        members(rat(5, 8)),
        integer(16),
        Rat::one(),
        6,
    )
    .unwrap()
}

/// **The kicked chart's transport is the node's lossless Cayley multiplier**: `C = I`, `K = I`,
/// `h = 1` give `v = (2 + i)/(2 − i) = (3 + 4i)/5`; a node whose `h√(k/c)` is irrational is
/// refused.
#[test]
fn the_banks_transport_is_the_nodes_lossless_cayley_multiplier() {
    assert_eq!(
        declared_bank().transport().unwrap(),
        GaussianRat::new(rat(3, 5), rat(4, 5))
    );
    let irrational = ReceivingBank::new(
        node(integer(2), None),
        members(rat(5, 8)),
        integer(16),
        Rat::one(),
        6,
    )
    .unwrap();
    assert!(irrational.transport().is_err());
}

/// **The executed turn reads a passage and its conjugate alike** (module header, "The bank's
/// face": the departure from the kicked chart). The executed tick is `A ⊗ I + p B ⊗ R(c)`, the
/// transport on the phase plane and the reflection on the node plane, and the node plane's
/// reflection `F` conjugates `R(c)` to `R(c̄)`: member `m` on `z` and member `−m` on `z̄` have the
/// same characteristic polynomial exactly. The kicked chart `Rot_v(1 + pR_u)` puts its transport
/// on the node plane, where `F Rot_v F = Rot_v̄`, so its trace differs for `u` and `ū`: the executed
/// second order reads the resonance and its mirror, the kicked chart one sideband.
#[test]
fn the_executed_turn_reads_a_passage_and_its_conjugate_alike() {
    let material = node(Rat::one(), None);
    let pumps = members(rat(5, 8));
    let characteristic = |pump: &PumpDeclaration, amplitudes: &[GaussianRat]| {
        let schedule = PumpSchedule::placed(pump, amplitudes).unwrap();
        let operands =
            ResonatorOperands::scheduled(0, &material, &schedule, &integer(16), &Rat::one(), None)
                .unwrap();
        Floquet::of(&operands).unwrap().characteristic().clone()
    };
    for seed in [3u64, 5, 8] {
        let turn = drawn_turn(seed, 8, 5);
        let conjugate: Vec<GaussianRat> = turn.iter().map(GaussianRat::conj).collect();
        for member in 0..4 {
            assert_eq!(
                characteristic(&pumps[member], &turn),
                characteristic(&pumps[(4 - member) % 4], &conjugate)
            );
        }
    }
    // The kicked chart: the product of `Rot_v (1 + p R_u)` over the carriers, its trace.
    let v = GaussianRat::new(rat(3, 5), rat(4, 5));
    let p = rat(5, 8);
    let kicked_trace = |carriers: &[GaussianRat]| -> Rat {
        // 2×2 real matrices as [[a, b], [c, d]].
        let mul = |x: [[Rat; 2]; 2], y: [[Rat; 2]; 2]| -> [[Rat; 2]; 2] {
            std::array::from_fn(|i| {
                std::array::from_fn(|j| &x[i][0] * &y[0][j] + &x[i][1] * &y[1][j])
            })
        };
        let rotation = [[v.re.clone(), -v.im.clone()], [v.im.clone(), v.re.clone()]];
        let mut product = [[Rat::one(), Rat::zero()], [Rat::zero(), Rat::one()]];
        for u in carriers {
            let kick = [
                [Rat::one() + &p * &u.re, &p * &u.im],
                [&p * &u.im, Rat::one() - &p * &u.re],
            ];
            product = mul(mul(rotation.clone(), kick), product);
        }
        &product[0][0] + &product[1][1]
    };
    let turn = drawn_turn(3, 8, 5);
    let conjugate: Vec<GaussianRat> = turn.iter().map(GaussianRat::conj).collect();
    assert_ne!(kicked_trace(&turn), kicked_trace(&conjugate));
}

/// **The face on a spectral line** (module header, "The bank's face"; the known truth of
/// [`ReceivingBank::read_turn`]'s test above). On a line of 8 unit cells stepping one quarter-turn
/// class a crossing, the two quarter-turn neighbours read equal powers (the mirror sideband: the
/// executed law reads them alike, `[1061/16, 531/8]` each) and the largest; and with the last cell
/// open, the candidate completing the line reads the face's reading strictly above every other, as
/// the executed lock's flip does. [measured] The face orders the line's own member below the
/// half-turn partner, where the executed growth orders it above (`[46, 1473/32]` against the silent
/// `[827/1024, 1655/2048]`): the own member's static boost past the standing bifurcation is not a
/// second-order reading (the ordering past the perturbative regime is owed, #62).
#[test]
fn the_banks_face_reads_a_spectral_line_and_its_completion() {
    let bank = declared_bank();
    let chart = bank.chart(8).unwrap();
    for class in 0..4usize {
        for offset in 0..4usize {
            let cell = |t: usize| quarter(offset + 4 * 8 - (class * t) % 4).as_gaussian();
            let line: Vec<GaussianRat> = (0..8).map(cell).collect();
            let powers = chart.resonance(&line).unwrap().powers();
            let by_difference = |d: usize| powers[(class + d) % 4].clone();
            assert_eq!(by_difference(1), by_difference(3));
            assert!(by_difference(1) > by_difference(0));
            assert!(by_difference(1) > by_difference(2));
            assert!(by_difference(0) < by_difference(2));
            let readings: Vec<Rat> = (0..4)
                .map(|candidate| {
                    let mut turn = line.clone();
                    turn[7] = quarter(candidate).as_gaussian();
                    chart.resonance(&turn).unwrap().reading(&chart)
                })
                .collect();
            let completing = (offset + 4 * 8 - (class * 7) % 4) % 4;
            for (candidate, reading) in readings.iter().enumerate() {
                if candidate != completing {
                    assert!(readings[completing] > *reading);
                }
            }
        }
    }
}

/// **The face's covector is the reading's exact differential** (module header, "The bank's face"):
/// along a ray `z + η δ` of the turn, `A(η) = A + η ⟨Ω(K), δ⟩ + η² A(δ)` exactly, with `K` the
/// reading's gradient coefficients at `c = 1` and `A(δ)` the reading of the move (Lean
/// `HNN/BankFace.member_amplitude_ray`); and the reading is within the chart's gain,
/// `A(δ) ≤ κ²|δ|²`.
#[test]
fn the_banks_reading_is_quadratic_along_a_ray_and_its_covector_exact() {
    let bank = declared_bank();
    let chart = bank.chart(8).unwrap();
    let storage = |turn: &[GaussianRat]| -> Vec<Rat> {
        let mut storage = vec![Rat::zero(); 16];
        for (tick, z) in turn.iter().enumerate() {
            storage[2 * (7 - tick)] = z.re.clone();
            storage[2 * (7 - tick) + 1] = z.im.clone();
        }
        storage
    };
    let base = storage(&drawn_turn(11, 8, 5));
    let step = storage(&drawn_turn(12, 8, 5));
    let at = |eta: &Rat| -> Rat {
        let moved: Vec<Rat> = base.iter().zip(&step).map(|(x, y)| x + eta * y).collect();
        chart.of_storage(&moved).unwrap().reading(&chart)
    };
    let resonance = chart.of_storage(&base).unwrap();
    let first = dot(&chart.covector(&resonance.gradient(&chart, &Rat::one())), &step);
    let second = chart.of_storage(&step).unwrap().reading(&chart);
    for eta in [rat(1, 3), rat(-2, 5), integer(3)] {
        assert_eq!(at(&eta), at(&Rat::zero()) + &eta * &first + &eta * &eta * &second);
    }
    assert!(second <= chart.gain() * dot(&step, &step));
}
