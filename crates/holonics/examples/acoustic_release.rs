//! Run with
//! `cargo run -p holonics --example acoustic_release -- <in.wav> <out.wav> [ticks] [threads]`.
//!
//! **The first acoustic release** (the
//! [bank record](../../../research/records/2026-10-10_A_BANK_OF_RINGS_SOUNDS_ITS_EMISSION_ON_A_BOUNDED_LATTICE.md);
//! #386, #148). A 16-bit mono recording drives a declared bank of rings through their matched ports
//! ([`WavePort::on_lattice`]), each ring's state carried on the lattice `2^(−32)`; the rings'
//! emission `e_b = b_b − a = −(2/Y_b) ω_b` is summed and rendered by one feedback tick at the 16-bit
//! PCM lattice, `g·Σ_b e_b + r = q 2^(−15) + r′`, over the recording and one second of continuation
//! (incident `0`). Every tick's balance is checked, every carried state entry is checked on the
//! lattice, and each ring's whole-stream balance `E_end − E_0 = ΣW − ΣhωDω + Σ(chart + split)` is
//! checked exactly. The WAV codec here is the exterior boundary chart and nothing else.
//!
//! Nothing here is learned, located, generated or graded: the bank is declared (record §2).

use std::time::Instant;

use holonics::hnn::chart::carry;
use holonics::hnn::constitution::Lattice;
use holonics::hnn::dynamic_section::{RAYS, SectionReader};
use holonics::hnn::section_lock::{LockReader, LockRefusal, LockWindow, Settled};
use holonics::hnn::ring::{ResonatorMaterial, ResonatorOperands};
use holonics::hnn::wave::{MatchedWave, WavePort};
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::{Rat, integer, rat};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};

/// The declared bank (record §2): `t_b = (1/50)(6/5)^b`, `b = 0..24`.
const RINGS: usize = 24;
/// One quality for the ladder: `a_b = t_b / QUALITY`.
const QUALITY: i64 = 32;
/// The state lattice `2^(−L)`.
const STATE_LATTICE: u32 = 32;
/// The PCM lattice `2^(−15)`: a 16-bit sample `s` is the amplitude `s 2^(−15)`.
const PCM: u32 = 15;
/// The key grain `2^(−16)` (record §7).
const KEY_GRAIN: u32 = 16;
/// The ticks rendered per progress line and per received chunk.
const CHUNK: usize = 8000;

/// The exterior codec: a RIFF/WAVE file of 16-bit mono PCM, its rate and its samples.
#[allow(
    clippy::disallowed_methods,
    reason = "the exterior boundary reads the recording here (crates/holonics/clippy.toml, guard 7)"
)]
fn read_wav(path: &str) -> (u32, Vec<i16>) {
    let bytes = std::fs::read(path).expect("the recording reads");
    assert!(&bytes[0..4] == b"RIFF" && &bytes[8..12] == b"WAVE", "a RIFF/WAVE file");
    let mut at = 12;
    let (mut rate, mut samples) = (None, None);
    while at + 8 <= bytes.len() {
        let id = &bytes[at..at + 4];
        let size = u32::from_le_bytes(bytes[at + 4..at + 8].try_into().unwrap()) as usize;
        let body = &bytes[at + 8..(at + 8 + size).min(bytes.len())];
        if id == b"fmt " {
            let format = u16::from_le_bytes(body[0..2].try_into().unwrap());
            let channels = u16::from_le_bytes(body[2..4].try_into().unwrap());
            let bits = u16::from_le_bytes(body[14..16].try_into().unwrap());
            assert!(format == 1 && channels == 1 && bits == 16, "16-bit mono PCM");
            rate = Some(u32::from_le_bytes(body[4..8].try_into().unwrap()));
        } else if id == b"data" {
            samples = Some(
                body.chunks_exact(2)
                    .map(|pair| i16::from_le_bytes([pair[0], pair[1]]))
                    .collect(),
            );
        }
        at += 8 + size + (size & 1);
    }
    (rate.expect("a fmt chunk"), samples.expect("a data chunk"))
}

/// The located rates' per-window track, private, beside the render.
#[allow(
    clippy::disallowed_methods,
    reason = "the exterior boundary writes the private located track here (crates/holonics/clippy.toml, guard 7)"
)]
fn write_track(path: &str, track: &str) {
    std::fs::write(path, track).expect("the located track writes");
}

/// The exterior codec's other side: the render as a RIFF/WAVE file of 16-bit mono PCM.
#[allow(
    clippy::disallowed_methods,
    reason = "the exterior boundary writes the render here (crates/holonics/clippy.toml, guard 7)"
)]
fn write_wav(path: &str, rate: u32, samples: &[i16]) {
    let data = (samples.len() * 2) as u32;
    let mut out = Vec::with_capacity(44 + data as usize);
    out.extend_from_slice(b"RIFF");
    out.extend_from_slice(&(36 + data).to_le_bytes());
    out.extend_from_slice(b"WAVEfmt ");
    out.extend_from_slice(&16u32.to_le_bytes());
    out.extend_from_slice(&1u16.to_le_bytes());
    out.extend_from_slice(&1u16.to_le_bytes());
    out.extend_from_slice(&rate.to_le_bytes());
    out.extend_from_slice(&(rate * 2).to_le_bytes());
    out.extend_from_slice(&2u16.to_le_bytes());
    out.extend_from_slice(&16u16.to_le_bytes());
    out.extend_from_slice(b"data");
    out.extend_from_slice(&data.to_le_bytes());
    for sample in samples {
        out.extend_from_slice(&sample.to_le_bytes());
    }
    std::fs::write(path, out).expect("the render writes");
}

/// The declared ring `t` (`tests/acoustic_wave_port.rs`'s `declared_ring` at `a = t/QUALITY`):
/// `C = I`, `D = 0`, `K = 4(a² + t²)`, `Y = 1/(4a)`, one complex node, `h = 1`.
fn declared_ring(t: &Rat) -> ResonatorOperands {
    let a = t / integer(QUALITY);
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

/// `x`'s exact dyadic enclosure `[2^k, 2^(k+1))`, its sign, or `0`.
fn enclosure(x: &Rat) -> String {
    if x.is_zero() {
        return "0".into();
    }
    let y = x.abs();
    let mut k = y.numer().bits() as i64 - y.denom().bits() as i64;
    let at = |k: i64| {
        if k >= 0 {
            Rat::from_integer(BigInt::one() << k as usize)
        } else {
            Rat::new(BigInt::one(), BigInt::one() << (-k) as usize)
        }
    };
    while at(k) > y {
        k -= 1;
    }
    while at(k + 1) <= y {
        k += 1;
    }
    format!("{}[2^{k}, 2^{})", if x.is_negative() { "−" } else { "" }, k + 1)
}

/// One ring's pass over the stream: its emission on the driven coordinate per tick, its decode from
/// its own moment keys (record §7), and its whole-stream readings.
struct Pass {
    emission: Vec<Rat>,
    decoded: Vec<Rat>,
    line: String,
    /// The located rates (record §13): each admitted near-return window's start tick, winding,
    /// period and defect count.
    located: Vec<(usize, i64, usize, usize)>,
}

/// The whole winding `⌊ℓ/4⌋` of a lift.
fn whole(lift: &BigInt) -> BigInt {
    let rays = BigInt::from(RAYS);
    let (quotient, rest) = (lift / &rays, lift % &rays);
    if rest.is_negative() { quotient - 1 } else { quotient }
}

/// The Elias gamma length of `n ≥ 1`, `2⌊log₂ n⌋ + 1`; of a signed integer `z`, that of `|z| + 1`
/// and one sign bit when `z ≠ 0` (record §7, B3: an exterior reading, never a law).
fn gamma(z: &BigInt) -> u64 {
    let n: BigInt = z.abs() + 1;
    2 * (n.bits() - 1) + 1 + u64::from(!z.is_zero())
}

/// The ring's half-memory in whole turns (record §7, repaired on Codex's review): the least `W` such
/// that the free ring, from a unit state on its lattice, holds at most half its starting energy **at
/// its `W`-th complete section return** (a positive arrival of its own reader), together with the
/// tick of its first whole return. The energy is read only at returns, never at a tick inside a turn.
fn half_memory(operands: &ResonatorOperands, lattice: Lattice) -> (u64, usize) {
    let mut port = WavePort::on_lattice(operands.clone(), 0, lattice).unwrap();
    port.seat([vec![Rat::zero(); 2], vec![Rat::one(), Rat::zero()]]).unwrap();
    let start = port.stored_energy().unwrap();
    let mut reader = SectionReader::at(port.phase_point()).unwrap();
    let opened = whole(reader.lift());
    let silence = MatchedWave::new(
        operands.admittance().clone(),
        operands.hop().clone(),
        vec![Rat::zero(); 1],
    )
    .unwrap();
    let mut turn_ticks = None;
    for tick in 1..1_000_000usize {
        for received in port.receive(&silence).unwrap() {
            assert!(received.unwrap().closes());
        }
        let symbol = reader.advance(port.phase_point()).unwrap();
        if symbol.crossing <= 0 {
            continue;
        }
        let turns = whole(reader.lift()) - &opened;
        if turns.is_positive() && turn_ticks.is_none() {
            turn_ticks = Some(tick);
        }
        if turns.is_positive() && port.stored_energy().unwrap() * integer(2) <= start {
            return (turns.to_u64().unwrap(), turn_ticks.unwrap());
        }
    }
    panic!("the free ring does not halve its energy within the declared ticks");
}

fn ring_pass(
    b: usize,
    t: &Rat,
    stream: &[Rat],
    continuation: usize,
    started: Instant,
    census_only: bool,
) -> Pass {
    let operands = declared_ring(t);
    let (admittance, hop) = (operands.admittance().clone(), operands.hop().clone());
    let lattice = Lattice::new(STATE_LATTICE);
    let (memory, turn_ticks) = half_memory(&operands, lattice);
    // The lock census (record §10): consecutive windows of four of the ring's own turns, so that a
    // period of up to two turns shows twice, each read by the existing lock owner.
    let window = LockWindow::new(0, 4 * turn_ticks).unwrap();
    let mut lock_reader = LockReader::new(window);
    let (mut locked, mut unlocked, mut rest, mut refused) = (0u64, 0u64, 0u64, 0u64);
    let mut addresses: std::collections::BTreeMap<String, u64> = std::collections::BTreeMap::new();
    let (mut near_admitted, mut near_refused, mut near_bits, mut near_raw, mut near_defects) =
        (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut located: Vec<(usize, i64, usize, usize)> = Vec::new();
    let mut port = WavePort::on_lattice(operands.clone(), 0, lattice).unwrap();
    let (mut work, mut dissipation, mut defect) = (Rat::zero(), Rat::zero(), Rat::zero());
    let (mut state_bits, mut remainder_bits) = (0u64, 0u64);
    let mut widest_remainder = Rat::zero();
    let total = stream.len() + continuation;
    let mut emission = Vec::with_capacity(total);
    // The ring's own epochs: its reader, the last key's whole winding, and the keys (tick, state).
    let key_grain = Lattice::new(KEY_GRAIN);
    let mut reader: Option<SectionReader> = None;
    let mut last_key: Option<BigInt> = None;
    let mut keys: Vec<(usize, [Vec<Rat>; 2])> = Vec::new();
    let mut restarts = 0u64;
    let mut at = 0;
    while at < total {
        let end = (at + CHUNK).min(total);
        let samples: Vec<Rat> = (at..end)
            .map(|n| stream.get(n).cloned().unwrap_or_else(Rat::zero))
            .collect();
        let wave = MatchedWave::new(admittance.clone(), hop.clone(), samples).unwrap();
        for received in port.receive(&wave).unwrap() {
            let tick = received.expect("every tick admitted");
            assert!(tick.closes(), "ring {b}: the balance closes at tick {}", tick.tick);
            for x in tick.step.state.iter().flatten() {
                assert!(lattice.contains(x), "ring {b}: the state lies on the lattice");
                state_bits = state_bits.max(x.numer().bits() + x.denom().bits());
            }
            for r in tick.step.remainders().all() {
                remainder_bits = remainder_bits.max(r.numer().bits() + r.denom().bits());
                if r.abs() > widest_remainder {
                    widest_remainder = r.abs();
                }
            }
            work += &tick.boundary_work;
            dissipation += &tick.step.dissipation;
            defect += &tick.step.chart + &tick.step.split;
            emission.push(tick.emission()[0].clone());
            let observed = lock_reader.observe([tick.step.state[1][0].clone(), tick.step.state[0][0].clone()]);
            if observed.is_err() {
                refused += 1;
                lock_reader = LockReader::new(window);
            } else if lock_reader.seen() == window.length() + 1 {
                let full = std::mem::replace(&mut lock_reader, LockReader::new(window));
                match full.finish() {
                    Ok(Settled::Rest) => rest += 1,
                    Ok(word @ Settled::Word(_)) => {
                        // N3: the near-return of the same window, with its bits against the raw word.
                        match word.near_return(&window) {
                            Ok(near) => {
                                let (bits, raw) = near.bits();
                                near_admitted += 1;
                                near_bits += bits;
                                near_raw += raw;
                                near_defects += near.defects().len() as u64;
                                located.push((
                                    tick.tick + 1 - window.length(),
                                    near.winding(),
                                    near.period(),
                                    near.defects().len(),
                                ));
                                let Settled::Word(read) = &word else { unreachable!() };
                                assert_eq!(&near.decode().unwrap(), read, "N1 on the recording");
                            }
                            Err(_) => near_refused += 1,
                        }
                        match word.lock(&window) {
                        Ok(lock) => {
                            locked += 1;
                            *addresses
                                .entry(format!("{} over {}", lock.winding(), lock.period()))
                                .or_insert(0) += 1;
                        }
                        Err(LockRefusal::Silent) => rest += 1,
                        Err(LockRefusal::Unlocked { .. }) => unlocked += 1,
                        Err(_) => refused += 1,
                        }
                    }
                    Err(_) => refused += 1,
                }
            }
            // The section reader on the ring's own state; an epoch opens at an arrival `W` whole
            // turns past the last key. A chord through the origin, or the origin itself, restarts it.
            let point = [tick.step.state[1][0].clone(), tick.step.state[0][0].clone()];
            let arrived = match reader.as_mut() {
                None => {
                    reader = SectionReader::at(point).ok();
                    last_key = None;
                    false
                }
                Some(open) => match open.advance(point.clone()) {
                    Ok(symbol) => symbol.crossing != 0,
                    Err(_) => {
                        // A restart opens a new span: the next arrival opens a key, and no winding
                        // is subtracted across the two passages.
                        restarts += 1;
                        reader = SectionReader::at(point).ok();
                        last_key = None;
                        false
                    }
                },
            };
            if arrived {
                let turns = whole(reader.as_ref().unwrap().lift());
                let due = last_key
                    .as_ref()
                    .is_none_or(|last| (&turns - last).abs() >= BigInt::from(memory));
                if due {
                    let key = tick.step.state.clone().map(|part| {
                        let mut dropped = vec![Rat::zero(); part.len()];
                        carry(&key_grain, &part, &mut dropped)
                    });
                    keys.push((tick.tick + 1, key));
                    last_key = Some(turns);
                }
            }
        }
        println!(
            "ring {b}: ticks {end} of {total}, keys {}, elapsed {} ms",
            keys.len(),
            started.elapsed().as_millis()
        );
        at = end;
    }
    let energy = port.stored_energy().unwrap();
    let balanced = energy == &work - &dissipation + &defect;
    assert!(balanced, "ring {b}: the whole stream's balance closes");
    let census = format!(
        "ring {b}: lock census over windows of {} ticks (4 turns of {turn_ticks}): locked {locked}, unlocked {unlocked}, silent or at rest {rest}, refused {refused}; near-returns admitted {near_admitted}, not admitted {near_refused}, bits {near_bits} of {near_raw} raw over the admitted, defects {near_defects}; addresses (winding over period: windows) {:?}",
        window.length(),
        addresses
    );
    println!("{census}");
    if census_only {
        return Pass {
            emission,
            decoded: Vec::new(),
            line: census,
            located,
        };
    }
    // The decoder: the same ring, incident 0, its state seated to each key at the key's tick.
    let mut decoder = WavePort::on_lattice(operands, 0, lattice).unwrap();
    let (mut d_work, mut d_dissipation, mut d_defect, mut seated) =
        (Rat::zero(), Rat::zero(), Rat::zero(), Rat::zero());
    let mut decoded = Vec::with_capacity(total);
    let mut key_bits = 0u64;
    let mut quadrature_bits = 0u64;
    let mut previous = 0usize;
    let mut next = keys.iter().peekable();
    let mut n = 0usize;
    while n < total {
        if let Some((tick, key)) = next.peek()
            && *tick == n
        {
            seated += decoder.seat(key.clone()).unwrap();
            let scale = Rat::from_integer(BigInt::one() << KEY_GRAIN as usize);
            // The key is the ring's state `[u, w]`, one complex node: four integers at the key
            // grain, the driven coordinate's two and the quadrature's two.
            for part in key {
                for (coordinate, x) in part.iter().enumerate() {
                    let bits = gamma(&(x * &scale).to_integer());
                    key_bits += bits;
                    if coordinate != 0 {
                        quadrature_bits += bits;
                    }
                }
            }
            key_bits += gamma(&BigInt::from(n - previous)) - 1;
            previous = n;
            next.next();
        }
        let stop = next.peek().map_or(total, |(tick, _)| (*tick).min(total));
        let silence = MatchedWave::new(admittance.clone(), hop.clone(), vec![Rat::zero(); stop - n])
            .unwrap();
        for received in decoder.receive(&silence).unwrap() {
            let tick = received.expect("every decoder tick admitted");
            assert!(tick.closes(), "ring {b}: the decoder's balance closes");
            d_work += &tick.boundary_work;
            d_dissipation += &tick.step.dissipation;
            d_defect += &tick.step.chart + &tick.step.split;
            decoded.push(tick.emission()[0].clone());
        }
        n = stop;
    }
    let d_energy = decoder.stored_energy().unwrap();
    let d_balanced = d_energy == &d_work - &d_dissipation + &d_defect + &seated;
    assert!(d_balanced, "ring {b}: the decoder's whole stream balance closes");
    let line = format!(
        "ring {b}: t = {t}; half-memory {memory} turns; keys {}; reader restarts {restarts}; key bits (gamma, four integers per key) {key_bits}, of which the quadrature's {quadrature_bits}; E_end {}; ΣW {}; Σ(chart + split) {}; balance closes: {balanced}; decoder balance with seats closes: {d_balanced}, Σ seat {}; widest state entry bits {state_bits}; widest remainder bits {remainder_bits}; widest |remainder| {}",
        keys.len(),
        enclosure(&energy),
        enclosure(&work),
        enclosure(&defect),
        enclosure(&seated),
        enclosure(&widest_remainder),
    );
    Pass {
        emission,
        decoded,
        line,
        located,
    }
}

/// The gain `2^(−k)` and the largest one that keeps `g·peak ≤ 1 − 2^(−14)`, so that one feedback
/// tick at `2^(−15)` stays within 16 bits: a normalization at the exterior boundary, read from the
/// rendered stream's own peak.
fn gain(k: i64) -> Rat {
    if k >= 0 {
        Rat::new(BigInt::one(), BigInt::one() << k as usize)
    } else {
        Rat::from_integer(BigInt::one() << (-k) as usize)
    }
}

fn gain_exponent(peak: &Rat) -> i64 {
    let ceiling = Rat::one() - Rat::new(BigInt::one(), BigInt::from(1u32 << 14));
    let mut k: i64 = 0;
    if !peak.is_zero() {
        while &gain(k) * peak > ceiling {
            k += 1;
        }
        while &gain(k - 1) * peak <= ceiling {
            k -= 1;
        }
    }
    k
}

/// [definition; agent-inferred, October 10; the bank record §16] **The source coded through one
/// ring's cells**: per recorded tick, given the ring's exact carried state, the drive's image is
/// affine in the sample (`ω = ω₀ + x m`, read by two exact-law steps), so the next state's cell (its
/// quadrant, `hnn::dynamic_section::quadrant`) bounds the sample to an interval of PCM values,
/// widened by one value at each end for the lattice's rounding. The code is the section word at
/// `⌈log₂ 5⌉ = 3` bits per tick plus the sample's index in its interval, `⌈log₂ count⌉` bits: it
/// decodes losslessly (`R_source = 0`). Returns the ticks, the word bits, the index bits and the
/// ticks whose interval held one value.
fn interval_pass(b: usize, t: &Rat, stream: &[Rat], started: Instant) -> (u64, u64, u64, u64) {
    use holonics::hnn::dynamic_section::quadrant;
    use holonics::hnn::ring::ResonatorRemainders;
    let operands = declared_ring(t);
    let lattice = Lattice::new(STATE_LATTICE);
    let (admittance, hop) = (operands.admittance().clone(), operands.hop().clone());
    let mut port = WavePort::on_lattice(operands.clone(), 0, lattice).unwrap();
    let pcm = Rat::from_integer(BigInt::one() << PCM as usize);
    let (low, high) = (BigInt::from(-32768), BigInt::from(32767));
    let (mut word_bits, mut index_bits, mut single) = (0u64, 0u64, 0u64);
    let zero = ResonatorRemainders::default();
    for (n, sample) in stream.iter().enumerate() {
        let [u, w] = port.state().map(<[Rat]>::to_vec);
        let rate = |a: Rat| {
            operands
                .step(n, &[a, Rat::zero()], [&u, &w], &zero, None)
                .unwrap()
                .rate
        };
        let (r0, r1) = (rate(Rat::zero()), rate(Rat::one()));
        let m: Vec<Rat> = r1.iter().zip(&r0).map(|(a, b)| a - b).collect();
        // The next phase point of coordinate 0, affine in x: w′ = 2ω − w, u′ = u + hω.
        let (w0, wm) = (integer(2) * &r0[0] - &w[0], integer(2) * &m[0]);
        let (u0, um) = (&u[0] + &hop * &r0[0], &hop * &m[0]);
        let wave = MatchedWave::new(admittance.clone(), hop.clone(), vec![sample.clone()]).unwrap();
        let tick = port.receive(&wave).unwrap().next().unwrap().unwrap();
        let next = [tick.step.state[1][0].clone(), tick.step.state[0][0].clone()];
        let class = quadrant(&next);
        // Each sign condition on a + b·x is a half-line in v = x·2^15; the cell is their meet.
        let (mut lo, mut hi) = (low.clone(), high.clone());
        let mut bound = |a: &Rat, b: &Rat, positive: Option<bool>| {
            // positive: Some(true) a + b x ≥ 0 side, Some(false) ≤ 0 side; widened by one value.
            let Some(up) = positive else { return };
            if b.is_zero() {
                return;
            }
            let root = -(a / b) * &pcm;
            let rises = b.is_positive() == up;
            if rises {
                lo = lo.clone().max(root.floor().to_integer() - 1);
            } else {
                hi = hi.clone().min(root.ceil().to_integer() + 1);
            }
        };
        match class {
            Some(0) => { bound(&w0, &wm, Some(true)); bound(&u0, &um, Some(true)); }
            Some(1) => { bound(&w0, &wm, Some(false)); bound(&u0, &um, Some(true)); }
            Some(2) => { bound(&w0, &wm, Some(false)); bound(&u0, &um, Some(false)); }
            Some(3) => { bound(&w0, &wm, Some(true)); bound(&u0, &um, Some(false)); }
            _ => {}
        }
        let v = (sample * &pcm).to_integer();
        assert!(lo <= v && v <= hi, "ring {b}: the sample lies in its cell's interval at tick {n}");
        let count: BigInt = &hi - &lo + 1;
        let bits = if count <= BigInt::one() { 0 } else { (count - 1u32).bits() };
        if bits == 0 {
            single += 1;
        }
        index_bits += bits;
        word_bits += 3;
        if n % CHUNK == CHUNK - 1 {
            println!("interval ring {b}: ticks {} elapsed {} ms", n + 1, started.elapsed().as_millis());
        }
    }
    (stream.len() as u64, word_bits, index_bits, single)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (input, output) = (&args[1], &args[2]);
    let limit: Option<usize> = args.get(3).map(|x| x.parse().unwrap()).filter(|x| *x > 0);
    let threads: usize = args.get(4).map_or(12, |x| x.parse().unwrap());
    let census_only = args.get(5).is_some_and(|x| x == "census");
    let interval_only = args.get(5).is_some_and(|x| x == "interval");
    let started = Instant::now();
    let (rate, pcm) = read_wav(input);
    let scale = Rat::new(BigInt::one(), BigInt::one() << PCM as usize);
    let mut stream: Vec<Rat> = pcm.iter().map(|&s| Rat::from_integer(s.into()) * &scale).collect();
    let mut continuation = rate as usize;
    if let Some(limit) = limit {
        stream.truncate(limit);
        continuation = continuation.min(limit / 4);
    }
    println!(
        "release: {} recorded ticks + {continuation} continuation ticks at {rate} per second, {RINGS} rings on {threads} threads",
        stream.len()
    );
    let ladder: Vec<Rat> = (0..RINGS)
        .map(|b| rat(1, 50) * (0..b).fold(Rat::one(), |x, _| x * rat(6, 5)))
        .collect();
    if interval_only {
        // Record §16: rings 0, 4, …, 20, the recorded ticks only, one thread each.
        let chosen: Vec<usize> = (0..RINGS).step_by(4).collect();
        let readings: Vec<(usize, (u64, u64, u64, u64))> = std::thread::scope(|scope| {
            let handles: Vec<_> = chosen
                .iter()
                .map(|&b| {
                    let (ladder, stream) = (&ladder, &stream);
                    scope.spawn(move || (b, interval_pass(b, &ladder[b], stream, started)))
                })
                .collect();
            handles.into_iter().map(|h| h.join().expect("a ring's interval pass")).collect()
        });
        for (b, (ticks, word, index, single)) in readings {
            println!(
                "interval ring {b}: ticks {ticks}; word bits {word}; index bits {index}; total {}; raw {}; ticks with one admissible value {single}",
                word + index,
                16 * ticks
            );
        }
        println!("interval: elapsed {} ms", started.elapsed().as_millis());
        return;
    }
    let mut passes: Vec<Option<Pass>> = (0..RINGS).map(|_| None).collect();
    std::thread::scope(|scope| {
        let mut handles = Vec::new();
        for worker in 0..threads {
            let (ladder, stream) = (&ladder, &stream);
            handles.push(scope.spawn(move || {
                (worker..RINGS)
                    .step_by(threads)
                    .map(|b| (b, ring_pass(b, &ladder[b], stream, continuation, started, census_only)))
                    .collect::<Vec<_>>()
            }));
        }
        for handle in handles {
            for (b, pass) in handle.join().expect("a ring's pass") {
                passes[b] = Some(pass);
            }
        }
    });
    let passes: Vec<Pass> = passes.into_iter().map(Option::unwrap).collect();
    for pass in &passes {
        println!("{}", pass.line);
    }
    if census_only {
        // The located rates (record §13): per ring, the distinct addresses `W/τ` in lowest terms with
        // the windows that read them; the per-window track goes to a private local file beside the
        // render, never to the repository.
        let mut track = String::new();
        for (b, pass) in passes.iter().enumerate() {
            let mut rates: std::collections::BTreeMap<(i64, usize), u64> =
                std::collections::BTreeMap::new();
            let mut still: std::collections::BTreeMap<usize, u64> = std::collections::BTreeMap::new();
            for &(start, winding, period, defects) in &pass.located {
                track.push_str(&format!("{b} {start} {winding} {period} {defects}\n"));
                if winding == 0 {
                    // A non-turning near-return: its period is the clock it holds (record §13).
                    *still.entry(period).or_insert(0) += 1;
                    continue;
                }
                let address = Rat::new(BigInt::from(winding), BigInt::from(period as u64));
                let key = (
                    address.numer().to_i64().unwrap(),
                    address.denom().to_usize().unwrap(),
                );
                *rates.entry(key).or_insert(0) += 1;
            }
            let mut ranked: Vec<_> = rates.into_iter().collect();
            ranked.sort_by(|x, y| y.1.cmp(&x.1));
            let top: Vec<String> = ranked
                .iter()
                .take(6)
                .map(|((w, t), n)| format!("{w}/{t}: {n}"))
                .collect();
            let turning: u64 = ranked.iter().map(|(_, n)| n).sum();
            let mut held: Vec<_> = still.into_iter().collect();
            held.sort_by(|x, y| y.1.cmp(&x.1));
            let periods: Vec<String> = held
                .iter()
                .take(8)
                .map(|(period, n)| format!("{period}: {n}"))
                .collect();
            println!(
                "located ring {b}: {turning} windows turning ({} distinct rates; most read: {}); {} windows not turning, periods most read (ticks: windows): {}",
                ranked.len(),
                top.join(", "),
                pass.located.len() as u64 - turning,
                periods.join(", ")
            );
        }
        write_track(&format!("{output}.located.txt"), &track);
        println!("census: elapsed {} ms", started.elapsed().as_millis());
        return;
    }
    // Σ_b e_b per tick, its peak, and the largest gain 2^(−k) with g·peak ≤ 1 − 2^(−14), so that one
    // feedback tick at 2^(−15) stays within 16 bits.
    let total = stream.len() + continuation;
    let sums: Vec<Rat> = (0..total)
        .map(|n| passes.iter().map(|p| &p.emission[n]).sum())
        .collect();
    let decoded: Vec<Rat> = (0..total)
        .map(|n| passes.iter().map(|p| &p.decoded[n]).sum())
        .collect();
    // B2: the exact decomposition Σ e = Σ ê + R at every tick (by construction of R).
    let residual: Vec<Rat> = sums.iter().zip(&decoded).map(|(e, d)| e - d).collect();
    let rate_ticks = rate as usize;
    let render = |name: &str, values: &[Rat], path: &str| {
        let peak = values.iter().map(Signed::abs).max().unwrap_or_else(Rat::zero);
        let k = gain_exponent(&peak);
        let g = gain(k);
        let pcm_lattice = Lattice::new(PCM);
        let mut remainder = [Rat::zero()];
        let mut rendered = Vec::with_capacity(values.len());
        for value in values {
            let carried = carry(&pcm_lattice, &[&g * value], &mut remainder);
            let q = (&carried[0] / &scale).to_integer();
            rendered.push(q.to_i16().expect("the render stays within 16 bits"));
        }
        write_wav(path, rate, &rendered);
        let seconds: Vec<String> = rendered
            .chunks(rate_ticks)
            .map(|second| {
                let sum: i64 = second.iter().map(|&q| i64::from(q) * i64::from(q)).sum();
                let peak = second.iter().map(|&q| i64::from(q).abs()).max().unwrap_or(0);
                format!("({sum}, {peak})")
            })
            .collect();
        println!(
            "render {name}: peak {}; gain 2^{}; final remainder {}; {} samples; per second (sum of squares, peak) {}",
            enclosure(&peak),
            -k,
            enclosure(&remainder[0]),
            rendered.len(),
            seconds.join(" ")
        );
    };
    render("emission", &sums, output);
    render("decode", &decoded, &format!("{output}.decode.wav"));
    render("residual", &residual, &format!("{output}.residual.wav"));
    println!("release: elapsed {} ms", started.elapsed().as_millis());
}
