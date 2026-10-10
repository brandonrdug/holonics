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
    let reflected: Vec<Rat> = run.ticks[..4].iter().map(|t| t.reflected.clone()).collect();
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
        let (a, b) = (&tick.incident, &tick.reflected);
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
