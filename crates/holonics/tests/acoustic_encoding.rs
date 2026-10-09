//! A sampled tone's undeclared period is located by the machine's own location law, and the
//! samples then enter as an `Encoded` source through the located chart (acceptance item 5 of the
//! [encoder record](../../../research/records/2026-10-09_THE_HOLONIC_ENCODER_EXPLODES_A_SOURCE_INTO_CO_PRESENT_FRAMES_AND_AN_AXIS_EXPOSES_WITHOUT_AUTHORING_WHEN_NO_RELABELLING_MOVES_IT.md);
//! the [record](../../../research/records/2026-10-09_A_TONES_PERIOD_IS_LOCATED_NOT_DECLARED.md)).
//!
//! The only modality-specific object here is [`SampleChart`], a **provisional** exterior boundary
//! chart: exact integer samples at a declared sample clock, each distinct value an ordinal of the
//! alphabet it is read with. It is not the chosen audio representation (the Holonic Encoder's
//! audio designs are being recovered) and no library type depends on it. Every other object is
//! the library's, and none is told a period: the frame family is the machine's declared carry
//! helices (`compression::keys::frames`), the location is `TransportLocation`'s loop closure, the
//! period is read from a located navigator's closed cycle, and the samples enter through
//! `PassageChart::located`, `Encoding::found` and `Encoded::through`.
//!
//! The consumer equations asserted for every carrying frame, with `x` the samples read:
//!
//! ```text
//! decode(encode x) = x                                        at the boundary, exactly
//! c(ℓ_k) = the encoded cell of sample k,  ℓ_(k+1) = ℓ_k + A(u_k)          the lift is the address
//! D E = ρ,  E T_c = U_c E                                     at the consuming step (check_step)
//! regenerate(key, n') = x'                                    on samples location never read
//! ```
//!
//! No float enters: samples are `i64`, the clock is an integer rate, and the fundamental is
//! reported as the exact division of the rate by the located period, with its remainder.

use holonics::compression::keys::frames::{
    FrameFamily, FrameLocation, FrameReading, FrameRefusal, FrameTally,
};
use holonics::compression::landmark::context::{BaseMeasure, StopPrior};
use holonics::geometry::{RatVec3, screw::ScrewGenerator};
use holonics::hnn::field::{ContactDeclaration, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::{Encoded, Encoding, Field, FieldDeclaration, PassageChart, RingDeclaration};
use holonics::ratio::{integer, rat};

/// The declared sample clock: samples per second. It is the chart's, never the machine's.
const RATE: u64 = 48_000;

// -------------------------------------------------------------------------------------------
// the provisional exterior boundary chart

/// [provisional; modality boundary only] **Exact integer samples at a declared sample clock.** Each
/// distinct sample value is an ordinal of the alphabet in order of first occurrence, and the
/// decoder maps an ordinal back to its exact value. It declares no period, no bins and no
/// meaning of a value; the machine reads the ordinals' equality only.
struct SampleChart {
    rate: u64,
    alphabet: Vec<i64>,
    ordinals: Vec<usize>,
}

impl SampleChart {
    /// Read exact samples; the alphabet is the values met, in order of first occurrence.
    fn read(rate: u64, samples: &[i64]) -> Self {
        let mut alphabet: Vec<i64> = Vec::new();
        let mut ordinals = Vec::with_capacity(samples.len());
        for &sample in samples {
            let ordinal = match alphabet.iter().position(|&seen| seen == sample) {
                Some(ordinal) => ordinal,
                None => {
                    alphabet.push(sample);
                    alphabet.len() - 1
                }
            };
            ordinals.push(ordinal);
        }
        Self {
            rate,
            alphabet,
            ordinals,
        }
    }

    /// The classes: the distinct values met.
    fn classes(&self) -> usize {
        self.alphabet.len()
    }

    /// The passage the machine reads: the ordinals, in sample order.
    fn passage(&self) -> Vec<usize> {
        self.ordinals.clone()
    }

    /// The ordinal of a value, when the alphabet holds it.
    fn ordinal_of(&self, sample: i64) -> Option<usize> {
        self.alphabet.iter().position(|&seen| seen == sample)
    }

    /// The decoder: the exact value of an ordinal.
    fn decode(&self, ordinal: usize) -> i64 {
        self.alphabet[ordinal]
    }

    /// The same samples under the reversed alphabet: a relabelling of the ordinals.
    fn relabelled(&self) -> Self {
        let last = self.alphabet.len() - 1;
        Self {
            rate: self.rate,
            alphabet: self.alphabet.iter().rev().copied().collect(),
            ordinals: self
                .ordinals
                .iter()
                .map(|&ordinal| last - ordinal)
                .collect(),
        }
    }
}

// -------------------------------------------------------------------------------------------
// the declared exact waveforms (terrain: they generate their truth, the machine locates it)

/// A quantized sawtooth: `⌊(k mod period) / step⌋` levels of 256 about −384, exact integers.
fn sawtooth(period: usize, step: usize, count: usize) -> Vec<i64> {
    (0..count)
        .map(|k| 256 * ((k % period) / step) as i64 - 384)
        .collect()
}

/// The Thue–Morse sequence at the same levels: exact, aperiodic and overlap-free, so no
/// eventually periodic generator reproduces a long prefix of it.
fn thue_morse(count: usize) -> Vec<i64> {
    (0..count)
        .map(|k| 256 * i64::from((k as u32).count_ones() % 2) - 384)
        .collect()
}

/// A triangle tone `0,1,2,3,3,2,1` of period 7.
fn triangle_seven(count: usize) -> Vec<i64> {
    const LEVELS: [i64; 7] = [0, 1, 2, 3, 3, 2, 1];
    (0..count).map(|k| 256 * LEVELS[k % 7] - 384).collect()
}

/// A square tone of period 7: three low samples, four high.
fn square_seven(count: usize) -> Vec<i64> {
    (0..count)
        .map(|k| if k % 7 < 3 { -384 } else { 384 })
        .collect()
}

/// A quantized triangle tone of period 12: `0,0,1,1,2,2,3,2,2,1,1,0`.
fn triangle_twelve(count: usize) -> Vec<i64> {
    const LEVELS: [i64; 12] = [0, 0, 1, 1, 2, 2, 3, 2, 2, 1, 1, 0];
    (0..count).map(|k| 256 * LEVELS[k % 12] - 384).collect()
}

// -------------------------------------------------------------------------------------------
// the field the located chart is read against (copied from the source entrance's declarations)

fn ring(period: u64, lock: Vec<u64>) -> RingDeclaration {
    RingDeclaration {
        period,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..period)
            .map(|node| FieldDeclaration::quarter_turn(node, period))
            .collect(),
        lock,
        reflector: (0..period)
            .map(|p| ((period - p) % period) as usize)
            .collect(),
        admittance: integer(2),
        initial: 0,
    }
}

fn receiver(ring: usize, aperture: usize) -> ReceiverDeclaration {
    ReceiverDeclaration {
        ring,
        aperture,
        tolerance: rat(1, 16),
        depth: 2,
        prior: StopPrior::half(),
        mass: 1,
        base: BaseMeasure::Even,
        receiving_prior: 0,
    }
}

/// One source ring of period 16, wide enough for any frame of the family: `Encoded::through`
/// requires the located chart's cells to inject into every source ring's ports.
fn wide_field() -> Field {
    Field::declare(
        FieldDeclaration {
            rings: vec![ring(16, (0..16).collect())],
            contacts: Vec::new(),
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: 16,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![receiver(0, 1)],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 24,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

/// A field declared on a frame's own rings, in carry order, with the receiving ring the source:
/// the field `Field::admit` accepts a located passage into (its helix is the field's rings).
fn field_on(periods: &[u64]) -> Field {
    let last = periods.len() - 1;
    let rings = periods
        .iter()
        .enumerate()
        .map(|(g, &period)| {
            if g == last {
                ring(period, (0..period).collect())
            } else {
                ring(period, vec![0])
            }
        })
        .collect();
    let contacts = (0..last)
        .map(|g| ContactDeclaration {
            from: g,
            to: g + 1,
            channel: vec![(0, 0), (1, 1)],
            admittance: integer(2),
            exponent: integer(if g == 0 { 2 } else { 0 }),
        })
        .collect();
    Field::declare(
        FieldDeclaration {
            rings,
            contacts,
            loops: Vec::new(),
            sources: vec![last],
            offsets: Vec::new(),
            alphabet: periods[last] as usize,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![receiver(last, 1)],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 24,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

// -------------------------------------------------------------------------------------------
// receipts

fn describe(reading: &FrameReading) -> String {
    match reading {
        FrameReading::Narrow { classes, cells } => {
            format!("narrow ({classes} classes, {cells} receiving cells)")
        }
        FrameReading::Empty => "empty (no survivor)".to_string(),
        FrameReading::Plural { classes } => format!("plural ({classes} gauge classes)"),
        FrameReading::Open(_) => "open (the key's lift is on no closed cycle)".to_string(),
        FrameReading::One(carrying) => format!(
            "one gauge class: key {} of keys {:?}, cycle of {} steps turning the joint clock {} whole time(s)",
            carrying.key(),
            carrying.keys(),
            carrying.cycle().length,
            carrying.cycle().winding
        ),
    }
}

/// Print the location receipt: every frame's typed reading, then the period or the refusal.
fn print_receipt(name: &str, rate: u64, location: &FrameLocation) {
    println!(
        "{name}: {} classes read, readings {:?}",
        location.classes(),
        location.tally()
    );
    for (helix, reading) in location.readings() {
        println!(
            "  frame {:?} (D = {}, {} cells): {}",
            helix.periods(),
            helix.period(),
            helix.cells(),
            describe(reading)
        );
    }
    match location.period() {
        Ok(period) => println!(
            "  located period: {} samples, read by frames {:?}; fundamental {rate}/{} Hz = {} + {}/{}",
            period.length,
            period.frames,
            period.length,
            rate / period.length,
            rate % period.length,
            period.length
        ),
        Err(refusal) => println!("  refused: {refusal}"),
    }
}

// -------------------------------------------------------------------------------------------
// the admission and its consumer equations

/// Admit the samples read through every carrying frame's located chart and check the consumer
/// equations; `held_out` are samples the location never read, with the read ones as their prefix.
/// Returns the number of frames admitted through.
fn admit_through_each_carrying_frame(
    chart: &SampleChart,
    samples: &[i64],
    held_out: &[i64],
    location: &FrameLocation,
) -> usize {
    let passages = vec![chart.passage()];
    let field = wide_field();
    let extended: Vec<usize> = held_out
        .iter()
        .map(|&sample| {
            chart
                .ordinal_of(sample)
                .expect("the held-out value is in the alphabet")
        })
        .collect();
    let mut admitted = 0;
    for (helix, carrying) in location.carrying() {
        let located = PassageChart::located(carrying.location(), &passages).unwrap();
        let encoding = Encoding::found(&located).unwrap();
        let squares = encoding.squares(&located).unwrap();
        let encoded = Encoded::through(&encoding, &located, &field, &passages).unwrap();
        assert_eq!(encoded.len(), 1);
        let encoded = &encoded[0];
        println!(
            "  admitted through frame {:?}: chart dimension {}, reached {}, founded dimension {}, squares {:?}, fibre {} direction(s), {} cells",
            helix.periods(),
            located.chart(),
            encoding.reached(),
            encoding.dimension(),
            squares,
            encoded.fibre().len(),
            encoded.len()
        );

        // decode(encode x) = x, exactly, at the boundary.
        assert_eq!(encoded.len(), samples.len());
        let decoded: Vec<i64> = encoded
            .cells()
            .iter()
            .map(|&cell| chart.decode(encoded.label(cell).expect("a labelled cell")))
            .collect();
        assert_eq!(decoded, samples);

        // The lift is the sample's address: the receiving cell read at ℓ_k is the encoded cell,
        // the located advance is the one the encoded passage carries, and the squares hold at the
        // consuming step.
        let transport = carrying.transport();
        let lifts = transport.lifts(carrying.key(), &chart.passage()).unwrap();
        assert_eq!(lifts.len(), samples.len() + 1);
        for (k, cell) in encoded.cells().iter().enumerate() {
            assert_eq!(helix.cell(lifts[k]) as usize, cell.class(), "sample {k}");
            assert_eq!(
                transport.emit(lifts[k]),
                Some(chart.ordinals[k]),
                "sample {k}"
            );
            let digits = transport.digits(chart.ordinals[k]);
            assert_eq!(encoded.advance(k), Some(digits.as_slice()), "sample {k}");
            encoded
                .check_step(k, lifts[k] % helix.period(), lifts[k + 1] % helix.period())
                .unwrap();
        }

        // The located navigator regenerates samples location never read.
        assert_eq!(
            transport.regenerate(carrying.key(), extended.len()),
            Some(extended.clone()),
            "the located navigator continues the tone"
        );
        admitted += 1;
    }
    admitted
}

/// Locate a tone read from `samples[..read]` on the family of ring bound `bound`, print the
/// receipt, and return the chart and the location.
fn locate_tone(
    name: &str,
    samples: &[i64],
    read: usize,
    bound: u64,
) -> (SampleChart, FrameFamily, FrameLocation) {
    let chart = SampleChart::read(RATE, &samples[..read]);
    let family = FrameFamily::pairs(bound).unwrap();
    let location = family.locate(chart.classes(), &[chart.passage()]).unwrap();
    print_receipt(name, chart.rate, &location);
    (chart, family, location)
}

// -------------------------------------------------------------------------------------------
// the acceptance

/// [fixture (i)] **A tone of undeclared period 7.** The quantized sawtooth `⌊(k mod 7)/2⌋` read
/// over three periods, on a family whose every ring is shorter than 7: the located period is the
/// carrying frame's closed cycle, not a ring's period, and the samples enter as `Encoded`.
#[test]
fn a_sawtooth_of_undeclared_period_seven_is_located_and_admitted() {
    let samples = sawtooth(7, 2, 35);
    let (chart, family, location) = locate_tone("sawtooth, period 7", &samples, 21, 6);
    assert!(
        family
            .frames()
            .iter()
            .all(|helix| helix.periods().iter().all(|&ring| ring < 7)),
        "no ring of the family has the tone's period"
    );
    let period = location.period().expect("the family locates the tone");
    assert_eq!(period.length, 7);
    let admitted = admit_through_each_carrying_frame(&chart, &samples[..21], &samples, &location);
    assert_eq!(admitted, location.tally().one);
    assert!(admitted >= 1);
}

/// [fixture (ii)] **A different, coprime period: 12.** The quantized sawtooth `⌊(k mod 12)/3⌋`
/// at the same four levels (the alphabet is the same, only the period differs), on a family whose
/// every ring is shorter than 12.
#[test]
fn a_sawtooth_of_undeclared_period_twelve_is_located_and_admitted() {
    let samples = sawtooth(12, 3, 60);
    let (chart, family, location) = locate_tone("sawtooth, period 12", &samples, 36, 6);
    assert!(
        family
            .frames()
            .iter()
            .all(|helix| helix.periods().iter().all(|&ring| ring < 12)),
        "no ring of the family has the tone's period"
    );
    let period = location.period().expect("the family locates the tone");
    assert_eq!(period.length, 12);
    let admitted = admit_through_each_carrying_frame(&chart, &samples[..36], &samples, &location);
    assert_eq!(admitted, location.tally().one);
    assert!(admitted >= 1);
}

/// A wider family (rings up to 9) locates period 7 on several frames at once; they must agree on
/// the cycle, and each admits the samples.
#[test]
fn several_frames_read_one_cycle_for_the_same_tone() {
    let samples = sawtooth(7, 2, 35);
    let (chart, _family, location) = locate_tone("sawtooth, period 7, rings to 9", &samples, 21, 9);
    let period = location
        .period()
        .expect("the wider family locates the tone");
    assert_eq!(period.length, 7);
    assert!(
        period.frames.len() >= 2,
        "the tone is carried by more than one frame: {:?}",
        period.frames
    );
    let admitted = admit_through_each_carrying_frame(&chart, &samples[..21], &samples, &location);
    assert_eq!(admitted, period.frames.len());
}

/// [fixture (iii)] **An aperiodic source is refused, typed.** The Thue–Morse sequence is exact and
/// overlap-free, so no deterministic generator on the family's finite lifts (`D ≤ 30` at ring
/// bound 6) reproduces 128 samples of it: every frame is empty and no period is invented.
#[test]
fn an_aperiodic_source_is_refused_not_given_a_period() {
    let samples = thue_morse(128);
    let (_chart, family, location) = locate_tone("Thue-Morse, 128 samples", &samples, 128, 6);
    let frames = family.frames().len();
    assert_eq!(
        location.period(),
        Err(FrameRefusal::Unlocated {
            tally: FrameTally {
                narrow: 0,
                empty: frames,
                plural: 0,
                open: 0,
                one: 0,
            }
        })
    );
}

/// A periodic tone the family does not carry is held, and a tone it does carry is never given a
/// period other than its own. Each outcome is printed: the family's coverage is a finding, not a
/// claim.
#[test]
fn a_periodic_tone_is_held_or_located_never_given_a_wrong_period() {
    let tones: [(&str, Vec<i64>, u64); 5] = [
        ("triangle, period 7", triangle_seven(35), 7),
        ("square, period 7", square_seven(35), 7),
        ("sawtooth step 2, period 8", sawtooth(8, 2, 40), 8),
        ("sawtooth step 3, period 9", sawtooth(9, 3, 45), 9),
        ("quantized triangle, period 12", triangle_twelve(60), 12),
    ];
    for (name, samples, true_period) in tones {
        let read = 3 * true_period as usize;
        let (_chart, _family, location) = locate_tone(name, &samples, read, 6);
        match location.period() {
            Ok(period) => assert_eq!(period.length, true_period, "{name}"),
            Err(refusal) => println!("  {name}: held, {refusal}"),
        }
    }
}

/// **Relabelling moves no reading** (atlas `hnn.encoded-located-relabelling`, on the acoustic
/// route): the reversed alphabet's ordinals locate the same readings, the same cycle and the same
/// windings; only the decoder carries the labels.
#[test]
fn relabelling_the_sample_alphabet_moves_no_reading() {
    let samples = sawtooth(7, 2, 21);
    let (chart, family, location) = locate_tone("sawtooth, period 7", &samples, 21, 6);
    let moved = chart.relabelled();
    let relabelled = family.locate(moved.classes(), &[moved.passage()]).unwrap();
    print_receipt(
        "sawtooth, period 7, reversed alphabet",
        moved.rate,
        &relabelled,
    );
    assert_eq!(relabelled.tally(), location.tally());
    assert_eq!(relabelled.period(), location.period());
    let decoded: Vec<i64> = moved.passage().iter().map(|&o| moved.decode(o)).collect();
    assert_eq!(decoded, samples);
}

/// The located passage enters a field declared on the carrying frame's own rings
/// (`Field::admit`: its helix is the field's rings in carry order, THE_MACHINE guard 9).
#[test]
fn the_located_tone_enters_a_field_declared_on_its_rings() {
    let samples = sawtooth(12, 3, 36);
    let (chart, _family, location) = locate_tone("sawtooth, period 12", &samples, 36, 6);
    let passages = vec![chart.passage()];
    let mut entered = 0;
    for (helix, carrying) in location.carrying() {
        let located = PassageChart::located(carrying.location(), &passages).unwrap();
        let encoding = Encoding::found(&located).unwrap();
        let field = field_on(helix.periods());
        let encoded = Encoded::through(&encoding, &located, &field, &passages).unwrap();
        field
            .admit(&encoded[0])
            .expect("the field declared on the frame's rings admits its located passage");
        println!(
            "  the field on rings {:?} admits the located tone ({} cells)",
            helix.periods(),
            encoded[0].len()
        );
        entered += 1;
    }
    assert!(entered >= 1);
}
