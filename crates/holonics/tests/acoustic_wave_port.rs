//! A matched wave drives a loaded ring through its port, the ring continues across the stream, and
//! its own state crosses its own section: the native build of the second rung of the acoustic line
//! (the
//! [record](../../../research/records/2026-10-09_A_MATCHED_WAVE_ENTERS_A_LOADED_RING_AND_ITS_STATE_CROSSES_ITS_OWN_SECTION.md);
//! #148, #73). The numbers asserted are those of an independent exact replica
//! (`research/records/receipts/2026-10-09-acoustic-native/replica_probe_output.txt`, read from the
//! acoustic-locks replica `6d96dfcc…`, which is not a repository owner).
//!
//! The consumer equations, at the declared ring `t = 1, C = 1, D = 0, K = 4(a² + t²), Y = 1/(4a)`,
//! `a = t/8`, `h = 1`, driven from rest by the replica's F1 sawtooth of period 7,
//! `x = (−9, −9, −2, −2, 5, 5, 12)`:
//!
//! ```text
//! E′ − E = (hY/4)(a² − b²) − h ω D ω          at every tick (ReceivedTick::closes, asserted again here)
//! (u, w)_n, b_n                               equal the replica's exact states and reflected waves
//! state after a chunked stream = state after the whole stream          the state is the quotient
//! ℓ_(k+1) = ℓ_k + Δℓ(z_k, z_(k+1)),  z = (w, u)                       symbols (cls, Δℓ) = the replica's
//! section arrivals = aeon::epochs of the lift's micro-steps at ClockLift::ring_section(0, 4)
//! ℓ(−z) = ℓ(z) + 2                            the polarity of the wave is the half-turn
//! ```
//!
//! No float enters. The ring's declared damping `a = t/8` is the replica's (its D4: the least
//! dyadic that lets every ring of the bank forget its rest state by the settle allowance); the
//! settle allowance of 120 samples is the replica's, and nothing here is tuned to the tone.

use std::cmp::Ordering;

use holonics::aeon::{ClockLift, epochs};
use holonics::compression::keys::frames::{FrameFamily, FrameRefusal};
use holonics::hnn::HnnError;
use holonics::hnn::dynamic_section::{RAYS, SectionReader, SectionRefusal, SectionSymbol, chord};
use holonics::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial, ResonatorOperands};
use holonics::hnn::section_lock::{
    Arrival, JointLock, JointRefusal, Lock, LockReader, LockRefusal, LockWindow, SectionRelation,
    SectionWord, Settled,
};
use holonics::hnn::wave::{MatchedWave, ReceivedTick, WavePort};
use holonics::holon::parametron::Carrier;
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::{Rat, integer, rat};
use num_bigint::{BigInt, BigUint};
use num_traits::{ToPrimitive, Zero};

/// The replica's F1 sawtooth, `x = 7 L − ΣL` for `L = 0 0 1 1 2 2 3`: zero mean, period 7.
const F1: [i64; 7] = [-9, -9, -2, -2, 5, 5, 12];
/// The replica's declared samples read, and the settle allowance after which the symbols are read.
const SAMPLES: usize = 240;
const SETTLE: usize = 120;

/// The ring `t` of the replica's declared bank: `C = I`, `D = 0`, `K = 4(a² + t²)`, `Y = 1/(4a)`,
/// `a = t/8`, one complex node (two real coordinates), `h = 1`.
fn declared_ring(t: &Rat) -> ResonatorOperands {
    let a = t / integer(8);
    let stiffness = integer(4) * (&a * &a + t * t);
    let admittance = integer(1) / (integer(4) * &a);
    let identity = ExactRatMatrix::identity(2).unwrap();
    let material = ResonatorMaterial::new(
        identity.clone(),
        identity.scaled(&stiffness),
        ExactRatMatrix::zero(2, 2).unwrap(),
        None,
    )
    .unwrap();
    ResonatorOperands::at_cut(0, &material, &admittance, &integer(1), None).unwrap()
}

fn matched(operands: &ResonatorOperands, stream: &[i64]) -> MatchedWave {
    MatchedWave::new(
        operands.admittance().clone(),
        operands.hop().clone(),
        stream.iter().map(|&x| integer(x)).collect(),
    )
    .unwrap()
}

/// F1 (or its polarity) for `n` samples.
fn stream(sign: i64, n: usize) -> Vec<i64> {
    (0..n).map(|k| sign * F1[k % 7]).collect()
}

/// One run: every tick's receipt and the phase point `(w, u)` after `n` samples, `n = 0..=len`.
struct Run {
    ticks: Vec<ReceivedTick>,
    points: Vec<[Rat; 2]>,
    port: WavePort,
}

fn run(t: &Rat, stream: &[i64]) -> Run {
    let operands = declared_ring(t);
    let wave = matched(&operands, stream);
    let mut port = WavePort::at_rest(operands, 0).unwrap();
    let mut points = vec![port.phase_point()];
    let mut ticks = Vec::new();
    for received in port.receive(&wave).unwrap() {
        ticks.push(received.unwrap());
    }
    for tick in &ticks {
        points.push([tick.step.state[1][0].clone(), tick.step.state[0][0].clone()]);
    }
    Run {
        ticks,
        points,
        port,
    }
}

/// The symbols of ticks `SETTLE..SAMPLES` and the lift after each, started on the settled state.
fn read(run: &Run) -> (Vec<SectionSymbol>, Vec<BigInt>) {
    let mut reader = SectionReader::at(run.points[SETTLE].clone()).unwrap();
    let mut lifts = vec![reader.lift().clone()];
    let mut symbols = Vec::new();
    for n in SETTLE + 1..=SAMPLES {
        symbols.push(reader.advance(run.points[n].clone()).unwrap());
        lifts.push(reader.lift().clone());
    }
    (symbols, lifts)
}

fn parse(text: &str) -> Rat {
    text.parse().unwrap()
}

// -------------------------------------------------------------------------------------------
// the wave port

/// The native step equals the replica's exact states and reflected waves at the declared ticks, and
/// the balance `E′ − E = (hY/4)(a² − b²) − hωDω` closes at every tick, recomputed here from the
/// incident amplitude and the reflected wave alone.
#[test]
fn the_native_ring_steps_the_replicas_exact_states_and_every_tick_closes() {
    let t = integer(1);
    let run = run(&t, &stream(1, SAMPLES));
    assert_eq!(run.ticks.len(), SAMPLES);
    assert_eq!(run.port.ticks(), SAMPLES);

    // the ring of the declaration: Y = 2, M = 145/32, K = 65/16 (the replica's printed constants)
    let operands = run.port.operands();
    assert_eq!(*operands.admittance(), integer(2));
    assert_eq!(*operands.operator(0).get(0, 0).unwrap(), rat(145, 32));
    assert_eq!(
        *operands.material().forms().1.get(0, 0).unwrap(),
        rat(65, 16)
    );

    // the replica's exact states (u, w) after n samples, and b_out at the first four ticks
    let state = |n: usize| {
        (
            run.ticks[n - 1].step.state[0][0].clone(),
            run.ticks[n - 1].step.state[1][0].clone(),
        )
    };
    assert_eq!(state(1), (rat(-288, 145), rat(-576, 145)));
    assert_eq!(state(2), (rat(-82944, 21025), rat(1152, 21025)));
    assert_eq!(state(3), (rat(-2516032, 3048625), rat(18854656, 3048625)));
    assert_eq!(
        state(7),
        (
            rat(3708326026062208, 1347646586640625),
            rat(5976623807860736, 1347646586640625)
        )
    );
    assert_eq!(
        state(14),
        (
            parse("3170913958111974843707898269696/1816151322484127584722900390625"),
            parse("12893354225423276842184025503232/1816151322484127584722900390625")
        )
    );
    let reflected: Vec<Rat> = run.ticks[..4]
        .iter()
        .map(|t| t.driven_reflected().clone())
        .collect();
    assert_eq!(
        reflected,
        vec![
            rat(-1017, 145),
            rat(-148041, 21025),
            rat(-15608098, 3048625),
            rat(-2222771394, 442050625),
        ]
    );

    // the balance at every tick, from a and b alone: h = 1, Y = 2, D = 0
    let (h, y) = (integer(1), integer(2));
    let mut booked = Rat::zero();
    for (n, tick) in run.ticks.iter().enumerate() {
        assert!(tick.closes(), "tick {n} closes");
        assert!(tick.step.closes(), "the owner's step closes at tick {n}");
        assert_eq!(tick.tick, n);
        assert_eq!(tick.incident, integer(F1[n % 7]));
        let (a, b) = (&tick.incident, tick.driven_reflected());
        // the isotropic node's quadrature coordinate reflects nothing either
        assert!(tick.reflected[1].is_zero());
        let work = &h * &y / integer(4) * (a * a - b * b);
        assert_eq!(tick.boundary_work, work, "the wave's work at tick {n}");
        assert_eq!(
            &tick.step.after - &tick.step.before,
            work,
            "E' - E at tick {n}"
        );
        assert!(tick.step.dissipation.is_zero(), "D = 0");
        // the quadrature coordinate of the isotropic node stays exactly at rest
        assert!(tick.step.state.iter().all(|v| v[1].is_zero()));
        assert!(tick.step.remainders().all().all(Zero::is_zero));
        booked += work;
    }
    // the stored energy is the net work booked at the boundary, from rest, with no tape of states
    let (u, w) = (&run.port.state()[0][0], &run.port.state()[1][0]);
    let energy = (rat(65, 16) * u * u + w * w) / integer(2);
    assert_eq!(run.port.stored_energy().unwrap(), energy);
    assert_eq!(energy, booked);
}

/// The state is the quotient: a stream received in chunks, with the state carried, equals the same
/// stream received whole, tick for tick, and the port holds only the state and its clock.
#[test]
fn the_state_carried_across_chunks_is_the_state_of_the_whole_stream() {
    let t = integer(1);
    let whole = run(&t, &stream(1, SAMPLES));
    let operands = declared_ring(&t);
    let all = stream(1, SAMPLES);
    let mut port = WavePort::at_rest(operands.clone(), 0).unwrap();
    let mut ticks = Vec::new();
    let mut at = 0;
    for length in [1, 6, 113, 120] {
        let wave = matched(&operands, &all[at..at + length]);
        for received in port.receive(&wave).unwrap() {
            ticks.push(received.unwrap());
        }
        at += length;
        assert_eq!(port.ticks(), at);
        // at each chunk boundary the carried state is the whole run's state at that tick
        let reached = &whole.ticks[at - 1].step.state;
        assert_eq!(port.state()[0], &reached[0][..]);
        assert_eq!(port.state()[1], &reached[1][..]);
    }
    assert_eq!(at, SAMPLES);
    assert_eq!(ticks, whole.ticks);
    assert_eq!(port.phase_point(), whole.points[SAMPLES]);

    // an empty chunk consumes nothing, and a reception stopped early leaves the clock where it is
    let mut port = WavePort::at_rest(operands.clone(), 0).unwrap();
    let wave = matched(&operands, &all[..10]);
    assert_eq!(port.receive(&wave).unwrap().take(3).count(), 3);
    assert_eq!(port.ticks(), 3);
    assert_eq!(port.receive(&matched(&operands, &[])).unwrap().count(), 0);
    assert_eq!(port.ticks(), 3);
}

/// A wave is admitted at a port by matching it, and a ring by what the equation covers.
#[test]
fn a_wave_must_be_matched_and_the_ring_must_be_the_unpumped_exact_one() {
    let operands = declared_ring(&integer(1));
    let mut port = WavePort::at_rest(operands.clone(), 0).unwrap();
    let samples = vec![integer(1), integer(2)];
    let other_port = MatchedWave::new(integer(3), integer(1), samples.clone()).unwrap();
    let other_clock = MatchedWave::new(integer(2), rat(1, 2), samples.clone()).unwrap();
    for wave in [&other_port, &other_clock] {
        assert!(matches!(port.receive(wave), Err(HnnError::Wave { .. })));
    }
    assert_eq!(port.ticks(), 0);
    assert!(
        MatchedWave::new(Rat::zero(), integer(1), samples.clone()).is_err()
            && MatchedWave::new(integer(2), rat(-1, 1), samples).is_err()
    );
    assert!(matches!(
        WavePort::at_rest(operands.clone(), 2),
        Err(HnnError::Shape { .. })
    ));

    // a pumped ring is refused: its balance carries a pump term the wave port does not book
    let identity = ExactRatMatrix::identity(2).unwrap();
    let pump = PumpDeclaration::new(
        rat(1, 8),
        Carrier::new(integer(1), integer(0)).unwrap(),
        PumpStep::Stand,
    )
    .unwrap();
    let pumped = ResonatorMaterial::new(
        identity.clone(),
        identity.scaled(&integer(2)),
        ExactRatMatrix::zero(2, 2).unwrap(),
        Some(pump),
    )
    .unwrap();
    let pumped = ResonatorOperands::at_cut(0, &pumped, &integer(2), &integer(1), None).unwrap();
    assert!(matches!(
        WavePort::at_rest(pumped, 0),
        Err(HnnError::Resonator { .. })
    ));
}

/// [Codex's review, witness 1] The loaded-solve certificate `2C + hD + (h²/2)K ⪰ 0` does not make the
/// storage positive: `C = I`, `K = −I`, `D = 0`, `h = Y = 1` is certified, both balances close, and the
/// ring is repaid more than it was given. The passive port refuses it; `K = 0` and a coupled positive
/// `K` are admitted.
#[test]
fn a_signed_stiffness_is_not_a_passive_port() {
    let identity = ExactRatMatrix::identity(2).unwrap();
    let zero = ExactRatMatrix::zero(2, 2).unwrap();
    let ring = |stiffness: ExactRatMatrix| {
        let material =
            ResonatorMaterial::new(identity.clone(), stiffness, zero.clone(), None).unwrap();
        ResonatorOperands::at_cut(0, &material, &integer(1), &integer(1), None).unwrap()
    };
    let witness = ring(identity.scaled(&integer(-1)));

    // the witness through the owner's own steps: incident 1 then 0 on one coordinate
    let quiet = vec![Rat::zero(); 2];
    let remainders = holonics::hnn::ring::ResonatorRemainders::default();
    let first = witness
        .step(
            0,
            &[integer(1), Rat::zero()],
            [&quiet, &quiet],
            &remainders,
            None,
        )
        .unwrap();
    assert_eq!(first.state[0], [rat(2, 5), Rat::zero()]);
    assert_eq!(first.state[1], [rat(4, 5), Rat::zero()]);
    assert_eq!(first.output, [rat(1, 5), Rat::zero()]);
    assert_eq!(first.after, rat(6, 25));
    let second = witness
        .step(
            1,
            &[Rat::zero(), Rat::zero()],
            [&first.state[0], &first.state[1]],
            &remainders,
            None,
        )
        .unwrap();
    assert_eq!(second.state[0], [rat(6, 5), Rat::zero()]);
    assert_eq!(second.state[1], [rat(4, 5), Rat::zero()]);
    assert_eq!(second.output, [rat(-8, 5), Rat::zero()]);
    assert_eq!(second.after, rat(-2, 5), "the stored energy is negative");
    assert!(first.closes() && second.closes(), "both balances close");
    // incident (hY/4) a² = 1/4 in all; reflected (hY/4) b² = 1/100 + 64/100 = 13/20
    let (incident, reflected) = (rat(1, 4), rat(1, 100) + rat(64, 100));
    assert_eq!(reflected, rat(13, 20));
    assert!(reflected > incident, "repaid more than it brought");

    assert!(matches!(
        WavePort::at_rest(witness, 0),
        Err(HnnError::Resonator { .. })
    ));
    // a free mass (K = 0, positive semidefinite) and a coupled positive K are passive
    assert!(WavePort::at_rest(ring(zero.clone()), 0).is_ok());
    let coupled = ExactRatMatrix::new(vec![
        vec![integer(2), integer(1)],
        vec![integer(1), integer(2)],
    ])
    .unwrap();
    assert!(WavePort::at_rest(ring(coupled), 0).is_ok());
}

/// [Codex's review, witness 2] The reflected wave is a vector: with a coupled `K` every coordinate of
/// the port reflects. `C = I`, `K = [[2, 1], [1, 2]]`, `h = Y = 1`, input `(1, 0)` reflects
/// `b = (31/63, 4/63)`, and the work booked over the full port vector is `748/3969`, where the driven
/// coordinate alone would give `752/3969`.
#[test]
fn every_coordinate_of_the_port_reflects() {
    let identity = ExactRatMatrix::identity(2).unwrap();
    let coupled = ExactRatMatrix::new(vec![
        vec![integer(2), integer(1)],
        vec![integer(1), integer(2)],
    ])
    .unwrap();
    let material = ResonatorMaterial::new(
        identity.clone(),
        coupled,
        ExactRatMatrix::zero(2, 2).unwrap(),
        None,
    )
    .unwrap();
    let operands = ResonatorOperands::at_cut(0, &material, &integer(1), &integer(1), None).unwrap();
    let wave = matched(&operands, &[1]);
    let mut port = WavePort::at_rest(operands, 0).unwrap();
    let tick = port.receive(&wave).unwrap().next().unwrap().unwrap();

    assert_eq!(tick.reflected, [rat(31, 63), rat(4, 63)]);
    assert_eq!(*tick.driven_reflected(), rat(31, 63));
    assert_eq!(tick.step.drive, [integer(1), Rat::zero()]);
    // the full-vector work, and what the driven coordinate alone would have booked
    assert_eq!(tick.boundary_work, rat(748, 3969));
    let scalar = rat(1, 4) * (integer(1) - tick.driven_reflected() * tick.driven_reflected());
    assert_eq!(scalar, rat(752, 3969));
    assert_ne!(tick.boundary_work, scalar);
    assert_eq!(tick.incident_energy, rat(1, 4));
    assert_eq!(
        tick.reflected_energy,
        rat(1, 4) * (rat(31, 63) * rat(31, 63) + rat(4, 63) * rat(4, 63))
    );
    // from rest D = 0: the stored energy is exactly the work booked over the whole vector
    assert!(tick.closes());
    assert_eq!(port.stored_energy().unwrap(), rat(748, 3969));
}

// -------------------------------------------------------------------------------------------
// the dynamic section

/// The replica's symbol word on F1 at `t = 1`: after the settle allowance the symbols are the
/// 7-cycle `1:+1 2:+1 3:+1 0:+1 1:+1 2:−2 0:+1` (class : advance), net lift `4` (one winding), and
/// the arrivals fall at ticks `122 + 7 j`. The arrivals are then read again by the aeon owner: the
/// lift's micro-steps as an aeon of the ring-of-4 lift, its `epochs` at `ring_section(0, 4)`.
#[test]
fn the_dynamic_section_reads_the_replicas_symbol_word_and_arrival_ticks() {
    const CYCLE: [(u8, i8); 7] = [(1, 1), (2, 1), (3, 1), (0, 1), (1, 1), (2, -2), (0, 1)];
    let run = run(&integer(1), &stream(1, SAMPLES));
    let (symbols, lifts) = read(&run);
    assert_eq!(symbols.len(), SAMPLES - SETTLE);

    // (cls, Δℓ) = the replica's word, every one of the 120 settled symbols
    for (n, symbol) in symbols.iter().enumerate() {
        assert_eq!(
            (symbol.class, symbol.advance),
            CYCLE[n % 7],
            "symbol of tick {}",
            SETTLE + n
        );
    }
    // ℓ_(k+1) = ℓ_k + Δℓ_k, the class is ℓ mod 4, and one cycle turns the lift once round
    for (n, symbol) in symbols.iter().enumerate() {
        assert_eq!(&lifts[n] + BigInt::from(symbol.advance), lifts[n + 1]);
        assert_eq!(BigInt::from(symbol.class), &lifts[n] % BigInt::from(RAYS));
    }
    assert_eq!(&lifts[7] - &lifts[0], BigInt::from(4));
    assert_eq!(lifts[0], BigInt::from(1));
    assert_eq!(*lifts.last().unwrap(), BigInt::from(70));

    // the section arrivals, as the reader read them: tick, signed crossing
    let arrivals: Vec<(usize, i8)> = symbols
        .iter()
        .enumerate()
        .filter(|(_, s)| s.crossing != 0)
        .map(|(n, s)| (SETTLE + n, s.crossing))
        .collect();
    let expected: Vec<(usize, i8)> = (0..17).map(|j| (122 + 7 * j, 1)).collect();
    assert_eq!(arrivals, expected);

    // the lift read as the aeon's reading: ℓ_240 = 70 is 17 + 1/2 turns
    let mut reader = SectionReader::at(run.points[SETTLE].clone()).unwrap();
    for n in SETTLE + 1..=SAMPLES {
        reader.advance(run.points[n].clone()).unwrap();
    }
    let reading = reader.reading();
    assert_eq!(*reading.windings(), BigInt::from(17));
    assert_eq!(*reading.phase(), rat(1, 2));
    assert_eq!(reader.class(), 2);

    // the aeon owner reads the same arrivals: micro-steps of one navigator of period 4
    let lift = ClockLift::new(vec![BigUint::from(4u32)]).unwrap();
    let moves: Vec<(usize, bool)> = symbols
        .iter()
        .flat_map(|s| std::iter::repeat_n((0, s.advance > 0), s.advance.unsigned_abs() as usize))
        .collect();
    let aeon = lift.walk(vec![lifts[0].clone()], &moves).unwrap();
    assert_eq!(aeon.end(), &vec![lifts.last().unwrap().clone()]);
    let section = lift.ring_section(0, BigUint::from(4u32)).unwrap();
    let section_epochs = epochs(&aeon, section);
    assert_eq!(section_epochs.flux(), BigInt::from(17));
    assert!(section_epochs.is_monotone());
    // each aeon tick falls in the sample the reader named, with the sign it named
    let mut starts = vec![0usize];
    for symbol in &symbols {
        starts.push(starts.last().unwrap() + symbol.advance.unsigned_abs() as usize);
    }
    let ticked: Vec<(usize, i8)> = section_epochs
        .ticks()
        .iter()
        .map(|tick| {
            let sample = starts.partition_point(|&start| start <= tick.step) - 1;
            (SETTLE + sample, if tick.forward { 1 } else { -1 })
        })
        .collect();
    assert_eq!(ticked, arrivals);
}

/// The polarity of the wave is the half-turn: the ring driven by `−x` has the exact negative
/// states, every symbol is `(cls + 2, Δℓ)`, and the lifts differ by `2`. The symbols are
/// invariant; the section arrivals are not: the half-turn takes the section ray to the opposite
/// ray, so the arrivals of `−x` at the ray `ℓ ≡ 0` are the crossings of `x` at the ray `ℓ ≡ 2`.
/// (The first run of this test asserted that the arrivals were invariant too, and failed: the
/// law is the one stated here, and the record keeps the failed reading.)
#[test]
fn the_polarity_of_the_wave_is_the_half_turn_of_the_lift() {
    let t = integer(1);
    let positive = run(&t, &stream(1, SAMPLES));
    let negative = run(&t, &stream(-1, SAMPLES));
    // the ring is linear from rest: the states of −x are minus the states of x, exactly
    for (p, n) in positive.points.iter().zip(&negative.points) {
        assert_eq!([-&p[0], -&p[1]], *n);
    }
    let (plus, lifts_plus) = read(&positive);
    let (minus, lifts_minus) = read(&negative);
    for (a, b) in plus.iter().zip(&minus) {
        assert_eq!(b.class, (a.class + 2) % RAYS);
        assert_eq!(b.advance, a.advance);
    }
    // read from their own settled states the two lifts differ by the constant 2
    for (a, b) in lifts_plus.iter().zip(&lifts_minus) {
        assert_eq!(b - a, BigInt::from(2));
    }
    // the arrivals of −x at the ray ℓ ≡ 0 are the crossings of x at the opposite ray ℓ ≡ 2
    for (n, (a, b)) in plus.iter().zip(&minus).enumerate() {
        let lift = lifts_plus[n].to_i64().unwrap();
        let opposite = (lift + i64::from(a.advance) - 2).div_euclid(4) - (lift - 2).div_euclid(4);
        assert_eq!(i64::from(b.crossing), opposite, "tick {}", SETTLE + n);
    }
    // and the replica's arrivals of −x: 120, 124, a departure at 125, 127, 131, a departure at 132, …
    let arrivals: Vec<(usize, i8)> = minus
        .iter()
        .enumerate()
        .filter(|(_, s)| s.crossing != 0)
        .map(|(n, s)| (SETTLE + n, s.crossing))
        .collect();
    assert_eq!(
        arrivals[..8],
        [
            (120, 1),
            (124, 1),
            (125, -1),
            (127, 1),
            (131, 1),
            (132, -1),
            (134, 1),
            (138, 1)
        ]
    );
    assert_eq!(arrivals.len(), 52);
    // the flux is the difference of the whole windings of the endpoints: ⌊70/4⌋ − ⌊1/4⌋ and ⌊72/4⌋ − ⌊3/4⌋
    let flux =
        |symbols: &[SectionSymbol]| symbols.iter().map(|s| i32::from(s.crossing)).sum::<i32>();
    assert_eq!((flux(&plus), flux(&minus)), (17, 18));
    // and the owner's partner, started on −z at ℓ + 2, keeps the lift exactly 2 above
    let mut reader = SectionReader::at(positive.points[SETTLE].clone()).unwrap();
    let mut partner = reader.half_turn();
    for n in SETTLE + 1..=SAMPLES {
        let symbol = reader.advance(positive.points[n].clone()).unwrap();
        let partner_symbol = partner.advance(negative.points[n].clone()).unwrap();
        assert_eq!(partner_symbol.advance, symbol.advance);
        assert_eq!(partner.lift(), &(reader.lift() + BigInt::from(2)));
    }
}

/// The arrival word is the observed placement, not the cycle's mean rate. Ring `t = 2` locks at
/// `W/τ = 2/7` (two windings per seven samples) but its arrivals fall `2, 5, 2, 5` samples apart,
/// where a constant-rate (balanced) word of rate `2/7` has gaps `3` or `4` only; ring `t = 3`
/// closes one winding per cycle through three arrivals, one of them a departure back across the
/// section. A reader that kept only `(W, τ)` would lose both.
#[test]
fn the_arrival_word_is_the_observed_placement_not_the_mean_rate() {
    let cycle_2: [(u8, i8); 7] = [(2, 1), (3, 1), (0, 2), (2, 2), (0, 1), (1, -1), (0, 2)];
    let cycle_3: [(u8, i8); 7] = [(2, 1), (3, 1), (0, 2), (2, 2), (0, 1), (1, -2), (3, -1)];

    // t = 2: W = 2, τ = 7, arrivals 121, 123, 128, 130, … (gaps 2, 5, 2, 5, …)
    let two = run(&integer(2), &stream(1, SAMPLES));
    let (symbols, lifts) = read(&two);
    for (n, symbol) in symbols.iter().enumerate() {
        assert_eq!(
            (symbol.class, symbol.advance),
            cycle_2[n % 7],
            "t = 2, tick {}",
            SETTLE + n
        );
    }
    let winding = (&lifts[7] - &lifts[0]) / BigInt::from(RAYS);
    assert_eq!(winding, BigInt::from(2));
    let arrivals: Vec<usize> = symbols
        .iter()
        .enumerate()
        .filter(|(_, s)| s.crossing == 1)
        .map(|(n, _)| SETTLE + n)
        .collect();
    assert_eq!(arrivals[..6], [121, 123, 128, 130, 135, 137]);
    let gaps: Vec<usize> = arrivals.windows(2).map(|w| w[1] - w[0]).collect();
    assert!(
        gaps.iter()
            .enumerate()
            .all(|(i, &g)| g == if i % 2 == 0 { 2 } else { 5 })
    );
    // a constant-rate word of rate 2/7 has gaps ⌊7/2⌋ = 3 or ⌈7/2⌉ = 4: this word is not one
    let one_cycle: Vec<i8> = (0..7).map(|n| symbols[14 + n].crossing).collect();
    assert_eq!(one_cycle, [0, 1, 0, 1, 0, 0, 0]);
    assert!(!is_balanced(&one_cycle));

    // t = 3: W = 1, τ = 7, yet arrivals 121, 123 and a departure at 125, then 128, 130, 132, …
    let three = run(&integer(3), &stream(1, SAMPLES));
    let (symbols, lifts) = read(&three);
    for (n, symbol) in symbols.iter().enumerate() {
        assert_eq!(
            (symbol.class, symbol.advance),
            cycle_3[n % 7],
            "t = 3, tick {}",
            SETTLE + n
        );
    }
    assert_eq!(
        (&lifts[7] - &lifts[0]) / BigInt::from(RAYS),
        BigInt::from(1)
    );
    let crossings: Vec<(usize, i8)> = symbols
        .iter()
        .enumerate()
        .filter(|(_, s)| s.crossing != 0)
        .map(|(n, s)| (SETTLE + n, s.crossing))
        .collect();
    assert_eq!(
        crossings[..6],
        [(121, 1), (123, 1), (125, -1), (128, 1), (130, 1), (132, -1)]
    );
    // three crossings per cycle, signed sum the winding 1: the series, not the sum
    let one_cycle: Vec<i8> = (0..7).map(|n| symbols[14 + n].crossing).collect();
    assert_eq!(one_cycle, [0, 1, 0, 1, 0, -1, 0]);
    assert_eq!(one_cycle.iter().map(|&c| i32::from(c)).sum::<i32>(), 1);
    assert!(!is_balanced(&one_cycle));

    // t = 1 is the one of the three whose word is the constant-rate word (one arrival per cycle)
    let one = run(&integer(1), &stream(1, SAMPLES));
    let (symbols, _) = read(&one);
    let one_cycle: Vec<i8> = (0..7).map(|n| symbols[14 + n].crossing).collect();
    assert_eq!(one_cycle, [0, 0, 1, 0, 0, 0, 0]);
    assert!(is_balanced(&one_cycle));
}

/// A cyclic 0/±1 word is balanced when any two windows of one length differ in count by at most 1:
/// the necessary shape of a constant-rate word (Lean `Aeon/Clock/CarryWord.carry_balanced`).
fn is_balanced(word: &[i8]) -> bool {
    let n = word.len();
    (1..n).all(|length| {
        let counts: Vec<i32> = (0..n)
            .map(|start| {
                (0..length)
                    .map(|i| i32::from(word[(start + i) % n]))
                    .sum::<i32>()
            })
            .collect();
        counts.iter().max().unwrap() - counts.iter().min().unwrap() <= 1
    })
}

/// The reader starts on a classed state: a ring at rest, the origin, has no symbol, and neither has
/// a chord through it; the first tick from rest is read after the ring has left it.
#[test]
fn the_reader_starts_after_the_ring_has_left_rest() {
    let run = run(&integer(1), &stream(1, 3));
    assert_eq!(
        SectionReader::at(run.points[0].clone()),
        Err(SectionRefusal::AtOrigin)
    );
    assert_eq!(
        chord(&run.points[0], &run.points[1]),
        Err(SectionRefusal::AtOrigin)
    );
    // the classed states of the first ticks read: the chord is the shorter way round
    assert!(chord(&run.points[1], &run.points[2]).is_ok());
    assert_eq!(
        run.points[1][0].cmp(&Rat::zero()),
        Ordering::Less,
        "the first state has w < 0"
    );
}

/// [measured; the prediction is the first rung's replica, `symbol_word_prediction_output.txt`] The
/// strand question of the second-rung record, one cheap reading: is the ring's own symbol word, the
/// `(class, advance)` stream the dynamic section emits, a located route of the first rung's frames?
/// The word is read natively from the ring `t = 1` on F1 (three cycles of the settled word, each
/// distinct symbol an ordinal by first occurrence) and located on the family of rings up to 6. Two
/// things hold whatever the frames say: the advance is not a function of the class alone (class 2
/// advances by `+1` at one place of the cycle and by `−2` at another), so the word is not a located
/// route on the ring's own `ℤ/4` helix, which needs a hidden ring; and every frame is read.
#[test]
fn a_rings_symbol_word_is_read_by_the_first_rungs_frames() {
    let run = run(&integer(1), &stream(1, SAMPLES));
    let (symbols, _) = read(&run);
    let word: Vec<(u8, i8)> = symbols[..21].iter().map(|s| (s.class, s.advance)).collect();
    // the advance is not a function of the class alone
    let class_two: Vec<i8> = word
        .iter()
        .filter(|(c, _)| *c == 2)
        .map(|(_, a)| *a)
        .collect();
    assert!(class_two.contains(&1) && class_two.contains(&-2));

    let mut alphabet: Vec<(u8, i8)> = Vec::new();
    let passage: Vec<usize> = word
        .iter()
        .map(
            |symbol| match alphabet.iter().position(|seen| seen == symbol) {
                Some(ordinal) => ordinal,
                None => {
                    alphabet.push(*symbol);
                    alphabet.len() - 1
                }
            },
        )
        .collect();
    let family = FrameFamily::pairs(6).unwrap();
    let location = family.locate(alphabet.len(), &[passage.clone()]).unwrap();
    let tally = location.tally();
    println!(
        "ring t = 1 symbol word, {} classes {:?}, 21 symbols {:?}: {:?}",
        alphabet.len(),
        alphabet,
        passage,
        tally
    );
    assert_eq!(
        tally.narrow + tally.empty + tally.plural + tally.open + tally.one,
        family.frames().len()
    );
    match location.period() {
        Ok(period) => println!(
            "  located period {} read by frames {:?}",
            period.length, period.frames
        ),
        Err(FrameRefusal::Unlocated { tally }) => {
            println!("  held: no frame carries it ({tally:?})")
        }
        Err(other) => println!("  refused: {other}"),
    }
}

// -------------------------------------------------------------------------------------------
// the lock and the joint period (third task): a consumer of the dynamic section's stream

/// The replica's other tones, as integers (zero mean, its fixtures).
const F3: [i64; 12] = [-15, -15, -3, -3, 9, 9, 21, 9, 9, -3, -3, -15];
const F4: [i64; 12] = [-4, -1, 2, 2, -3, 0, 0, 3, -2, -2, 1, 4];

fn cycle_of(tone: &[i64], n: usize) -> Vec<i64> {
    (0..n).map(|k| tone[k % tone.len()]).collect()
}

/// The declared bank: three rings of the replica's Farey bank, `t = 2/3, 1, 2`. Never searched.
fn bank() -> [Rat; 3] {
    [rat(2, 3), integer(1), integer(2)]
}

/// The declared window: the replica's settle allowance and its settled stretch.
fn lock_window() -> LockWindow {
    LockWindow::new(SETTLE, SAMPLES - SETTLE).unwrap()
}

/// One ring's states fed to the lock reader, tick 0 (rest) to tick 240.
fn settled(run: &Run) -> Result<Settled, LockRefusal> {
    let mut reader = LockReader::new(lock_window());
    for point in &run.points {
        reader.observe(point.clone())?;
    }
    reader.finish()
}

fn bank_settled(stream: &[i64]) -> Vec<Settled> {
    bank()
        .iter()
        .map(|t| settled(&run(t, stream)).unwrap())
        .collect()
}

fn locks(rings: &[Settled]) -> Vec<Result<Lock, LockRefusal>> {
    rings.iter().map(|ring| ring.lock(&lock_window())).collect()
}

/// `(τ, W, address, arrival word, arrival ticks)` of a lock.
type Reading = (usize, i64, Rat, Vec<i8>, Vec<usize>);

fn reading(lock: &Lock) -> Reading {
    (
        lock.period(),
        lock.winding(),
        lock.address().clone(),
        lock.arrival_word(),
        lock.arrivals().iter().map(|a| a.tick).collect(),
    )
}

/// F1 locks at τ = 7 on each ring of the bank with the replica's windings (1, 1, 2), the addresses
/// 1/7, 1/7, 2/7 and its own observed arrival words; the joint period is 7. The mean-rate face is
/// beside the word, and the word of ring `t = 2` (arrivals `0101000`) is not a balanced word.
#[test]
fn f1_locks_at_seven_on_the_declared_bank() {
    let rings = bank_settled(&stream(1, SAMPLES));
    let locks: Vec<Lock> = locks(&rings).into_iter().map(Result::unwrap).collect();
    let readings: Vec<Reading> = locks.iter().map(reading).collect();
    assert_eq!(
        readings,
        [
            (7, 1, rat(1, 7), vec![0, 0, 1, 0, 0, 0, 0], vec![122]),
            (7, 1, rat(1, 7), vec![0, 0, 1, 0, 0, 0, 0], vec![122]),
            (7, 2, rat(2, 7), vec![0, 1, 0, 1, 0, 0, 0], vec![121, 123]),
        ]
    );
    // the observed symbols of ring t = 1: the record's 7-cycle, from tick 120
    let symbols: Vec<(u8, i8)> = locks[1]
        .cycle()
        .iter()
        .map(|s| (s.class, s.advance))
        .collect();
    assert_eq!(
        symbols,
        [(1, 1), (2, 1), (3, 1), (0, 1), (1, 1), (2, -2), (0, 1)]
    );
    assert_eq!(locks[1].start(), SETTLE);
    assert_eq!(
        locks[2].arrivals(),
        [
            Arrival { tick: 121, sign: 1 },
            Arrival { tick: 123, sign: 1 }
        ]
    );
    // the face is beside the word: TwoClocks(W/τ), whose lock address has period 7 on each ring
    for lock in &locks {
        let face = lock.mean_rate_face().unwrap();
        assert_eq!(face.ratio(), lock.address());
        assert_eq!(
            face.lock_address().unwrap().period().unwrap(),
            BigInt::from(7)
        );
        assert_eq!(
            face.convergents().unwrap().last().unwrap().ratio(),
            *lock.address()
        );
    }
    assert!(is_balanced(&locks[0].arrival_word()) && is_balanced(&locks[1].arrival_word()));
    assert!(!is_balanced(&locks[2].arrival_word()));
    // the joint: the lcm of the cycles, dividing the wave's period 7 and every ring's τ dividing it
    let joint = JointLock::read(&lock_window(), &rings).unwrap();
    assert_eq!(joint.period(), 7);
    assert_eq!(7 % joint.period(), 0);
    assert!(
        joint
            .rings()
            .iter()
            .flatten()
            .all(|lock| joint.period() % lock.period() == 0)
    );
}

/// F3 (period 12): rings `t = 2/3` and `t = 1` lock at 12 with one winding; ring `t = 2` rocks without
/// turning, a lock of `W = 0` with an empty arrival word (it is not Silent, and has no mean-rate face).
#[test]
fn f3_has_a_lock_without_rotation() {
    let rings = bank_settled(&cycle_of(&F3, SAMPLES));
    let locks: Vec<Lock> = locks(&rings).into_iter().map(Result::unwrap).collect();
    let readings: Vec<Reading> = locks.iter().map(reading).collect();
    let mut at_three = vec![0i8; 12];
    at_three[3] = 1;
    let mut at_two = vec![0i8; 12];
    at_two[2] = 1;
    assert_eq!(
        readings,
        [
            (12, 1, rat(1, 12), at_three, vec![123]),
            (12, 1, rat(1, 12), at_two, vec![122]),
            (12, 0, integer(0), vec![0i8; 12], vec![]),
        ]
    );
    assert!(locks[2].mean_rate_face().is_none());
    assert!(locks[2].cycle().iter().any(|symbol| symbol.advance != 0));
    assert_eq!(
        JointLock::read(&lock_window(), &rings).unwrap().period(),
        12
    );
}

/// F4 (the 3 + 4 sum, period 12): the rings lock at 4, 12 and 12 with windings 1, 3, 3 and the same
/// address 1/4; the joint period is 12, the lcm. Ring `t = 2/3` reads only the period-4 component, the
/// others read the sum; each ring's τ divides the joint 12, and 12 divides the wave's period. The face
/// of a 12-cycle at address 1/4 has the lock period 4, not 12: the face is not the cycle.
#[test]
fn f4_has_a_joint_period_of_twelve() {
    let rings = bank_settled(&cycle_of(&F4, SAMPLES));
    let locks: Vec<Lock> = locks(&rings).into_iter().map(Result::unwrap).collect();
    let readings: Vec<Reading> = locks.iter().map(reading).collect();
    assert_eq!(
        readings,
        [
            (4, 1, rat(1, 4), vec![0, 0, 0, 1], vec![123]),
            (
                12,
                3,
                rat(1, 4),
                vec![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1],
                vec![122, 126, 131]
            ),
            (
                12,
                3,
                rat(1, 4),
                vec![0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0],
                vec![121, 125, 130]
            ),
        ]
    );
    let joint = JointLock::read(&lock_window(), &rings).unwrap();
    assert_eq!(joint.period(), 12);
    assert_eq!(12 % joint.period(), 0);
    for lock in joint.rings().iter().flatten() {
        assert_eq!(
            joint.period() % lock.period(),
            0,
            "each ring's τ divides the joint"
        );
    }
    // the rate face of ring t = 1 is 1/4: its lock period is 4, on a cycle of 12
    let face = locks[1].mean_rate_face().unwrap();
    assert_eq!(
        face.lock_address().unwrap().period().unwrap(),
        BigInt::from(4)
    );
    assert_ne!(locks[1].period(), 4);
}

/// The concatenation law of section words, at its consumer, on the declared bank (F1, rings
/// `t = 2/3, 1, 2`): for words `u`, `v` whose classes meet (`u` lands on the class `v` starts from),
/// `W(uv) = W(u) + W(v)`, with `W` the owner's signed carry law applied once to the word (start class,
/// net lift) and checked against the signed count of its arrivals; when the classes do not meet the
/// join is refused at `u`'s last tick and has no winding. The ring words are cut at declared ticks and
/// every cut of every ring is joined to every cut of every ring, so both outcomes occur.
#[test]
fn section_words_concatenate_with_the_carry_cocycle_on_the_declared_bank() {
    let words: Vec<SectionWord> = bank_settled(&stream(1, SAMPLES))
        .into_iter()
        .map(|ring| match ring {
            Settled::Word(word) => word,
            Settled::Rest => panic!("the bank rings are not at rest on F1"),
        })
        .collect();
    let length = SAMPLES - SETTLE;
    let part = |word: &SectionWord, cut: std::ops::Range<usize>| {
        SectionWord::new(word.symbols()[cut].to_vec()).unwrap()
    };
    let arrivals = |word: &SectionWord| {
        BigInt::from(
            word.symbols()
                .iter()
                .map(|symbol| i32::from(symbol.crossing))
                .sum::<i32>(),
        )
    };
    let cuts = [1usize, 2, 3, 5, 7, 8, 13, 60, 118, 119];

    // a ring's whole word is the join of its parts at every cut, and the cocycle holds at each
    for word in &words {
        assert_eq!(word.symbols().len(), length);
        assert_eq!(word.winding(), arrivals(word));
        for &cut in &cuts {
            let (u, v) = (part(word, 0..cut), part(word, cut..length));
            assert_eq!(u.concat(&v).as_ref(), Ok(word));
            assert_eq!(word.winding(), u.winding() + v.winding(), "cut {cut}");
        }
        // associativity: the junction carries vanish in either bracketing
        let (u, v, w) = (part(word, 0..7), part(word, 7..60), part(word, 60..length));
        let left = u.concat(&v).unwrap().concat(&w).unwrap();
        let right = u.concat(&v.concat(&w).unwrap()).unwrap();
        assert_eq!((&left, &right), (word, word));
        assert_eq!(
            word.winding(),
            u.winding() + v.winding() + w.winding(),
            "three parts"
        );
    }

    // across rings: the words meet where u's landing class is v's start class, and only there
    let (mut met, mut refused) = (0, 0);
    for a in &words {
        for b in &words {
            for &cut_u in &cuts {
                for &cut_v in &cuts {
                    let (u, v) = (part(a, 0..cut_u), part(b, cut_v..length));
                    let last = u.symbols().last().unwrap();
                    let lands = (i16::from(last.class) + i16::from(last.advance)).rem_euclid(4);
                    if i16::from(v.start_class().unwrap()) == lands {
                        met += 1;
                        let uv = u.concat(&v).unwrap();
                        assert_eq!(uv.symbols().len(), cut_u + length - cut_v);
                        assert_eq!(uv.winding(), u.winding() + v.winding());
                        assert_eq!(uv.winding(), arrivals(&uv));
                    } else {
                        refused += 1;
                        assert_eq!(
                            u.concat(&v),
                            Err(LockRefusal::NotASectionWord {
                                tick: cut_u - 1,
                                relation: SectionRelation::Recursion
                            })
                        );
                    }
                }
            }
        }
    }
    assert!(met > 0 && refused > 0, "met {met}, refused {refused}");
}

/// The three readings of one winding agree on every lock of the declared bank, on F1, F3 and F4: the
/// lock's `W` (the closed-loop owner over the cycle's advances), the word's `W` (the signed carry law
/// over its start class and net lift, on the cycle admitted as a section word) and the signed count of
/// the observed arrivals. The cycle is closed: it lands on the class it starts from.
#[test]
fn a_locks_winding_is_the_closed_loop_owners_the_words_and_the_arrivals() {
    for tone in [
        stream(1, SAMPLES),
        cycle_of(&F3, SAMPLES),
        cycle_of(&F4, SAMPLES),
    ] {
        for ring in bank_settled(&tone) {
            let lock = ring.lock(&lock_window()).unwrap();
            let word = SectionWord::new(lock.cycle().to_vec()).unwrap();
            assert_eq!(word.winding(), BigInt::from(lock.winding()));
            let count: i32 = lock.arrival_word().iter().map(|&c| i32::from(c)).sum();
            assert_eq!(i64::from(count), lock.winding());
            let symbols = lock.cycle();
            let last = symbols.last().unwrap();
            let lands = (i16::from(last.class) + i16::from(last.advance)).rem_euclid(4);
            assert_eq!(Some(u8::try_from(lands).unwrap()), word.start_class());
        }
    }
}

/// Thue–Morse is Unlocked on every ring (no period at most 60 repeats the settled word) and refuses
/// the joint, naming the first ring; the period 61 control, one over half the window, is Unlocked too.
#[test]
fn an_aperiodic_wave_and_a_period_over_half_the_window_are_unlocked() {
    let thue_morse: Vec<i64> = (0..SAMPLES as u32)
        .map(|k| 1 - 2 * i64::from(k.count_ones() % 2))
        .collect();
    let sawtooth_61: Vec<i64> = (0..SAMPLES as i64).map(|k| k % 61 - 30).collect();
    for wave in [thue_morse, sawtooth_61] {
        let rings = bank_settled(&wave);
        for reading in locks(&rings) {
            assert_eq!(
                reading,
                Err(LockRefusal::Unlocked {
                    max_period: 60,
                    length: 120
                })
            );
        }
        assert!(matches!(
            JointLock::read(&lock_window(), &rings),
            Err(JointRefusal::Ring {
                ring: 0,
                refusal: LockRefusal::Unlocked { .. }
            })
        ));
    }
}

/// A ring at rest has no class and is never started: zero input is Silent on every ring and for the
/// joint. A ring at rest at the settle tick that leaves rest inside the window has not settled.
#[test]
fn rest_is_silent_and_a_ring_that_has_not_settled_is_refused() {
    let rings = bank_settled(&vec![0; SAMPLES]);
    assert!(rings.iter().all(|ring| *ring == Settled::Rest));
    for reading in locks(&rings) {
        assert_eq!(reading, Err(LockRefusal::Silent));
    }
    assert_eq!(
        JointLock::read(&lock_window(), &rings),
        Err(JointRefusal::Silent)
    );

    // the wave starts at tick 130: the ring is at rest at tick 120 and moves at 131
    let mut late = vec![0i64; 130];
    late.extend(stream(1, SAMPLES - 130));
    assert_eq!(
        settled(&run(&integer(1), &late)),
        Err(LockRefusal::NotSettled { settle: SETTLE })
    );

    // a reader offered too few states is refused, not guessed
    let mut reader = LockReader::new(lock_window());
    for point in &run(&integer(1), &stream(1, 200)).points {
        reader.observe(point.clone()).unwrap();
    }
    assert!(matches!(
        reader.finish(),
        Err(LockRefusal::Incomplete {
            have: 201,
            need: 241
        })
    ));
}

// -------------------------------------------------------------------------------------------
// the port on a lattice (the bank record, 2026-10-10)

/// **The bounded carry** (bank record A1): the declared ring `t = 1` on the lattice `2^(−32)`, driven
/// by F1 and then left to ring. Every tick closes with its chart and split terms within their
/// bounds, every carried state entry lies on the lattice, every carried remainder is at most half a
/// unit, the whole stream's balance closes exactly, and the emission is `−(2/Y) ω`. On the exact law
/// the same stream's state denominators grow; on the lattice its widest entry does not exceed what
/// the first ticks reach.
#[test]
fn the_port_on_a_lattice_carries_a_bounded_state_and_every_tick_closes() {
    use holonics::hnn::constitution::Lattice;
    use num_traits::Signed;
    let lattice = Lattice::new(32);
    let operands = declared_ring(&integer(1));
    let mut samples: Vec<i64> = stream(1, SAMPLES);
    samples.extend(std::iter::repeat_n(0, SAMPLES));
    let wave = matched(&operands, &samples);
    let mut port = WavePort::on_lattice(operands.clone(), 0, lattice).unwrap();
    let (mut work, mut dissipation, mut defect) = (Rat::zero(), Rat::zero(), Rat::zero());
    let mut widest = Vec::new();
    for received in port.receive(&wave).unwrap() {
        let tick = received.unwrap();
        assert!(tick.closes(), "tick {}", tick.tick);
        assert_eq!(tick.lattice, Some(32));
        let mut bits = 0;
        for x in tick.step.state.iter().flatten() {
            assert!(lattice.contains(x), "tick {}: the state lies on the lattice", tick.tick);
            bits = bits.max(x.denom().bits());
        }
        widest.push(bits);
        for r in tick.step.remainders().all() {
            assert!(r.abs() * integer(2) <= lattice.unit(), "a carried remainder is at most half a unit");
        }
        let emission = tick.emission();
        let expected = -(integer(2) / operands.admittance()) * &tick.step.rate[0];
        assert_eq!(emission[0], expected);
        work += &tick.boundary_work;
        dissipation += &tick.step.dissipation;
        defect += &tick.step.chart + &tick.step.split;
    }
    assert_eq!(port.ticks(), 2 * SAMPLES);
    assert_eq!(port.stored_energy().unwrap(), &work - &dissipation + &defect);
    // The state's denominators never exceed the lattice's.
    assert!(widest.iter().all(|bits| *bits <= 33));
    // The exact law's state on the same stream: its denominators grow with the ticks.
    let exact = run(&integer(1), &stream(1, SAMPLES));
    let first = exact.ticks[9].step.state[0][0].denom().bits();
    let last = exact.ticks[SAMPLES - 1].step.state[0][0].denom().bits();
    assert!(last > first, "the exact law's state grows: {first} then {last} bits");
}

/// **The stream is one on the lattice** (bank record A3): received in chunks, the lattice port
/// carries the same states, remainders and ticks as received whole.
#[test]
fn the_lattice_port_carries_its_remainders_across_chunks() {
    use holonics::hnn::constitution::Lattice;
    let lattice = Lattice::new(32);
    let operands = declared_ring(&integer(1));
    let all = stream(1, SAMPLES);
    let mut whole = WavePort::on_lattice(operands.clone(), 0, lattice).unwrap();
    let whole_ticks: Vec<ReceivedTick> = whole
        .receive(&matched(&operands, &all))
        .unwrap()
        .map(Result::unwrap)
        .collect();
    let mut port = WavePort::on_lattice(operands.clone(), 0, lattice).unwrap();
    let mut ticks = Vec::new();
    let mut at = 0;
    for length in [1, 6, 113, 120] {
        for received in port.receive(&matched(&operands, &all[at..at + length])).unwrap() {
            ticks.push(received.unwrap());
        }
        at += length;
        assert_eq!(port.remainders(), whole_ticks[at - 1].step.remainders());
    }
    assert_eq!(ticks, whole_ticks);
    assert_eq!(port.state(), whole.state());
    assert_eq!(port.remainders(), whole.remainders());
}

/// **A key seated at the port** (bank record §7): the state is replaced, the work booked is the
/// stored energy's change, the remainders are cleared, and a key off the lattice or of another width
/// is refused with the port unchanged.
#[test]
fn a_key_seated_at_a_lattice_port_books_its_work() {
    use holonics::hnn::constitution::Lattice;
    let lattice = Lattice::new(32);
    let operands = declared_ring(&integer(1));
    let mut port = WavePort::on_lattice(operands.clone(), 0, lattice).unwrap();
    for received in port.receive(&matched(&operands, &stream(1, 20))).unwrap() {
        received.unwrap();
    }
    let before = port.stored_energy().unwrap();
    let key = [vec![rat(1, 4), Rat::zero()], vec![rat(-3, 8), rat(1, 2)]];
    let work = port.seat(key.clone()).unwrap();
    assert_eq!(port.state(), [&key[0][..], &key[1][..]]);
    assert_eq!(work, port.stored_energy().unwrap() - before);
    assert!(port.remainders().all().all(Zero::is_zero));
    let off = [vec![Rat::new(1.into(), BigInt::from(3)), Rat::zero()], vec![Rat::zero(), Rat::zero()]];
    assert!(matches!(port.seat(off), Err(HnnError::Wave { .. })));
    assert!(matches!(port.seat([vec![Rat::zero()], vec![Rat::zero()]]), Err(HnnError::Shape { .. })));
    assert_eq!(port.state(), [&key[0][..], &key[1][..]]);
}

// -------------------------------------------------------------------------------------------
// the near-return grain (bank record §11)

/// The Elias gamma length, as the near-return counts it.
fn gamma_length(n: usize) -> u64 {
    2 * u64::from(usize::BITS - 1 - n.leading_zeros()) + 1
}

/// **N1 and N2 on the declared bank** (bank record §11): on every ring of the bank under F1, F3 and F4,
/// the near-return decodes the window's word exactly; wherever the exact lock reads `τ₀`, the
/// near-return is admitted at a description no longer than the exact lock's zero-defect one,
/// `γ(τ₀) + 3τ₀ + 1`, and when it keeps `τ₀` it has no defect and the same winding and address.
#[test]
fn the_near_return_decodes_its_window_and_the_exact_lock_is_its_zero_defect_case() {
    for tone in [cycle_of(&F1, SAMPLES), cycle_of(&F3, SAMPLES), cycle_of(&F4, SAMPLES)] {
        let rings = bank_settled(&tone);
        for (ring, exact) in rings.iter().zip(locks(&rings)) {
            let near = ring.near_return(&lock_window());
            if let Ok(near) = &near {
                let Settled::Word(word) = ring else {
                    panic!("a near-return reads a word")
                };
                assert_eq!(&near.decode().unwrap(), word, "N1: the decode is the window's word");
                let (bits, raw) = near.bits();
                assert!(bits < raw);
            }
            if let Ok(lock) = exact {
                let near = near.expect("N2: an exact lock is admitted as a near-return");
                let tau = lock.period();
                assert!(near.bits().0 <= gamma_length(tau) + 3 * tau as u64 + 1);
                if near.period() == tau {
                    assert!(near.defects().is_empty());
                    assert_eq!(near.winding(), lock.winding());
                    assert_eq!(near.address(), lock.address());
                }
            }
        }
    }
}

/// **A near-periodic word keeps its defects** (bank record §11): the F1 wave with one sample changed
/// after the settle allowance no longer locks exactly on the ring `t = 1`, and the near-return reads
/// the F1 cycle with the departure kept, decoding the window exactly; its defects' lift is read apart
/// from the cycle's winding.
#[test]
fn a_near_periodic_window_keeps_its_departure_as_defects() {
    let mut tone = cycle_of(&F1, SAMPLES);
    tone[SETTLE + 60] += 7;
    let ring = settled(&run(&integer(1), &tone)).unwrap();
    assert!(matches!(ring.lock(&lock_window()), Err(LockRefusal::Unlocked { .. })));
    let near = ring.near_return(&lock_window()).unwrap();
    let Settled::Word(word) = &ring else {
        panic!("the ring reads a word")
    };
    assert_eq!(&near.decode().unwrap(), word);
    assert!(!near.defects().is_empty());
    let exact = settled(&run(&integer(1), &cycle_of(&F1, SAMPLES))).unwrap();
    let clean = exact.lock(&lock_window()).unwrap();
    let (bits, raw) = near.bits();
    println!(
        "near-return: τ {} (clean {}), defects {}, defect lift {}, bits {bits} of {raw}",
        near.period(),
        clean.period(),
        near.defects().len(),
        near.defect_lift()
    );
}
