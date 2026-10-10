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

/// One ring's pass over the stream: its emission on the driven coordinate per tick, and its
/// whole-stream reading.
struct Pass {
    emission: Vec<Rat>,
    line: String,
}

fn ring_pass(b: usize, t: &Rat, stream: &[Rat], continuation: usize, started: Instant) -> Pass {
    let operands = declared_ring(t);
    let (admittance, hop) = (operands.admittance().clone(), operands.hop().clone());
    let lattice = Lattice::new(STATE_LATTICE);
    let mut port = WavePort::on_lattice(operands, 0, lattice).unwrap();
    let (mut work, mut dissipation, mut defect) = (Rat::zero(), Rat::zero(), Rat::zero());
    let (mut state_bits, mut remainder_bits) = (0u64, 0u64);
    let mut widest_remainder = Rat::zero();
    let total = stream.len() + continuation;
    let mut emission = Vec::with_capacity(total);
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
        }
        println!(
            "ring {b}: ticks {end} of {total}, elapsed {} ms",
            started.elapsed().as_millis()
        );
        at = end;
    }
    let energy = port.stored_energy().unwrap();
    let balanced = energy == &work - &dissipation + &defect;
    assert!(balanced, "ring {b}: the whole stream's balance closes");
    let line = format!(
        "ring {b}: t = {t}; E_end {}; ΣW {}; ΣhωDω {}; Σ(chart + split) {}; whole-stream balance closes: {balanced}; widest state entry bits {state_bits}; widest remainder bits {remainder_bits}; widest |remainder| {}",
        enclosure(&energy),
        enclosure(&work),
        enclosure(&dissipation),
        enclosure(&defect),
        enclosure(&widest_remainder),
    );
    Pass { emission, line }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (input, output) = (&args[1], &args[2]);
    let limit: Option<usize> = args.get(3).map(|x| x.parse().unwrap()).filter(|x| *x > 0);
    let threads: usize = args.get(4).map_or(12, |x| x.parse().unwrap());
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
    let mut passes: Vec<Option<Pass>> = (0..RINGS).map(|_| None).collect();
    std::thread::scope(|scope| {
        let mut handles = Vec::new();
        for worker in 0..threads {
            let (ladder, stream) = (&ladder, &stream);
            handles.push(scope.spawn(move || {
                (worker..RINGS)
                    .step_by(threads)
                    .map(|b| (b, ring_pass(b, &ladder[b], stream, continuation, started)))
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
    // Σ_b e_b per tick, its peak, and the largest gain 2^(−k) with g·peak ≤ 1 − 2^(−14), so that one
    // feedback tick at 2^(−15) stays within 16 bits.
    let total = stream.len() + continuation;
    let sums: Vec<Rat> = (0..total)
        .map(|n| passes.iter().map(|p| &p.emission[n]).sum())
        .collect();
    let peak = sums.iter().map(Signed::abs).max().unwrap_or_else(Rat::zero);
    let ceiling = Rat::one() - Rat::new(BigInt::one(), BigInt::from(1u32 << 14));
    let mut k: i64 = 0;
    let gain = |k: i64| {
        if k >= 0 {
            Rat::new(BigInt::one(), BigInt::one() << k as usize)
        } else {
            Rat::from_integer(BigInt::one() << (-k) as usize)
        }
    };
    if !peak.is_zero() {
        while &gain(k) * &peak > ceiling {
            k += 1;
        }
        while &gain(k - 1) * &peak <= ceiling {
            k -= 1;
        }
    }
    let g = gain(k);
    let pcm_lattice = Lattice::new(PCM);
    let mut remainder = [Rat::zero()];
    let mut rendered = Vec::with_capacity(total);
    for sum in &sums {
        let carried = carry(&pcm_lattice, &[&g * sum], &mut remainder);
        let q = (&carried[0] / &scale).to_integer();
        let q = q.to_i16().expect("the render stays within 16 bits");
        rendered.push(q);
    }
    write_wav(output, rate, &rendered);
    println!(
        "render: emission peak {}; gain 2^{}; final remainder {}; {} samples written; elapsed {} ms",
        enclosure(&peak),
        -k,
        enclosure(&remainder[0]),
        rendered.len(),
        started.elapsed().as_millis()
    );
}
