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
    field_on_receiving(periods, periods.len() - 1)
}

/// [`field_on`] with its receiver declared on ring `receiving` (the online-learning record §6: the
/// ring whose clock carries the located cycle); the source ring stays the last.
fn field_on_receiving(periods: &[u64], receiving: usize) -> Field {
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
            receivers: vec![receiver(receiving, 1)],
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

// -------------------------------------------------------------------------------------------
// the located section word (the bank record §23, loop 1)

/// The replica's declared ring `t` (`tests/acoustic_wave_port.rs`'s `declared_ring`): `C = I`,
/// `D = 0`, `K = 4(a² + t²)`, `Y = 1/(4a)`, `a = t/8`, `h = 1`.
fn section_ring(t: i64) -> holonics::hnn::ring::ResonatorOperands {
    use holonics::hnn::ring::{ResonatorMaterial, ResonatorOperands};
    use holonics::ratio::linear::ExactRatMatrix;
    let t = integer(t);
    let a = &t / integer(8);
    let stiffness = integer(4) * (&a * &a + &t * &t);
    let identity = ExactRatMatrix::identity(2).unwrap();
    let material = ResonatorMaterial::new(
        identity.clone(),
        identity.scaled(&stiffness),
        ExactRatMatrix::zero(2, 2).unwrap(),
        None,
    )
    .unwrap();
    ResonatorOperands::at_cut(0, &material, &(integer(1) / (integer(4) * &a)), &integer(1), None).unwrap()
}

/// **A passage ingested whole by the reference port** (§28 F1, §28a R1): each ingest stops after the
/// occurrence whose step carries the joint clock out; the aeon is then closed (`close_aeon`, the
/// port's boundary, over the admitted receiving phases) and the rest of the passage (`Encoded::part`)
/// continues the same moment. Returns the moment and the aeons closed.
fn ingest_whole(
    reference: &holonics::hnn::Reference,
    resident: &mut holonics::hnn::Resident,
    moment: Option<holonics::hnn::MomentId>,
    passage: &Encoded,
) -> (holonics::hnn::MomentId, usize) {
    use holonics::hnn::ExecutionPort;
    let mut moment = moment;
    let mut rest = passage.part(0..passage.len()).unwrap();
    let mut closed = 0;
    loop {
        let (id, ingest) = reference
            .ingest(resident, moment.as_ref(), &rest)
            .unwrap_or_else(|e| panic!("the port refuses a part of {} cells: {e}", rest.len()));
        moment = Some(id);
        let ingested = ingest.forward.into_present().expect("the ingest's forward is present");
        if ingested.carry_out {
            let admitted = resident.admitted().to_vec();
            reference.close_aeon(resident, &admitted).unwrap();
            closed += 1;
        } else {
            assert_eq!(ingested.cells, rest.len(), "without a carry-out the ingest consumes the whole part");
        }
        if ingested.cells == rest.len() {
            return (moment.unwrap(), closed);
        }
        rest = rest.part(ingested.cells..rest.len()).unwrap();
    }
}

/// Bits naming one of `count` values.
fn index_bits(count: usize) -> usize {
    (usize::BITS - count.saturating_sub(1).leading_zeros()) as usize
}

/// The emission's exterior plumbing: `value` in `width` bits, most significant first.
fn push(bits: &mut Vec<bool>, value: usize, width: usize) {
    bits.extend((0..width).rev().map(|k| (value >> k) & 1 == 1));
}

fn pull(bits: &mut impl Iterator<Item = bool>, width: usize) -> usize {
    (0..width).fold(0, |value, _| (value << 1) | usize::from(bits.next().expect("the emission holds the field")))
}

/// Elias gamma of `n ≥ 1`.
fn push_gamma(bits: &mut Vec<bool>, n: usize) {
    let width = (usize::BITS - n.leading_zeros()) as usize;
    bits.extend(std::iter::repeat_n(false, width - 1));
    push(bits, n, width);
}

fn pull_gamma(bits: &mut impl Iterator<Item = bool>) -> usize {
    let mut zeros = 0;
    while !bits.next().expect("the emission holds the gamma code") {
        zeros += 1;
    }
    (0..zeros).fold(1, |value, _| (value << 1) | usize::from(bits.next().expect("the gamma body")))
}

/// What the independent decoder of §28 returns: the placement (settle tick, window length), the clock
/// (the ring's declared `t` and hop), and the whole section word.
#[derive(Debug, PartialEq, Eq)]
struct DecodedSection {
    settle: usize,
    length: usize,
    ring: usize,
    hop: usize,
    word: holonics::hnn::section_lock::SectionWord,
}

/// **The independent decoder** (bank record §28 F3): it reads only the emission and the declared frame
/// family. The header gives the placement and clock; the start class is two bits; the frame index
/// names the helix; the dictionary maps each ordinal to its advance; `read_located` returns the
/// ordinals; the classes and crossings follow from the start class by the owner's carry law
/// (`dynamic_section::land`), and the word is admitted by `SectionWord::new`.
fn decode_section(emission: &[bool], family: &FrameFamily) -> DecodedSection {
    use holonics::compression::keys::transport::read_located;
    use holonics::hnn::dynamic_section::{SectionSymbol, land};
    use holonics::hnn::section_lock::SectionWord;
    let mut bits = emission.iter().copied();
    let settle = pull_gamma(&mut bits) - 1;
    let length = pull_gamma(&mut bits);
    let ring = pull_gamma(&mut bits);
    let hop = pull_gamma(&mut bits);
    let start = u8::try_from(pull(&mut bits, 2)).unwrap();
    let helix = &family.frames()[pull(&mut bits, index_bits(family.frames().len()))];
    let classes = pull_gamma(&mut bits);
    let dictionary: Vec<i8> = (0..classes)
        .map(|_| i8::try_from(pull(&mut bits, 3)).unwrap() - 2)
        .collect();
    let rest: Vec<bool> = bits.collect();
    let ordinals = read_located(helix, classes, &rest, &[length]).unwrap().remove(0);
    let mut class = start;
    let symbols = ordinals
        .iter()
        .map(|&o| {
            let advance = dictionary[o];
            let (crossing, landed) = land(class, advance).unwrap();
            let symbol = SectionSymbol { class, advance, crossing };
            class = landed;
            symbol
        })
        .collect();
    DecodedSection {
        settle,
        length,
        ring,
        hop,
        word: SectionWord::new(symbols).unwrap(),
    }
}

/// **A ring's departed section word enters the field on its located helix, the pair is read at the
/// ring's own distance cap, and the emission decodes the whole word** (bank record §28, which
/// replaces §26's test, narrowed by the review of `f06ff2b0`). The ring `t = 1` under the replica's
/// F1 tone, clean and with one departure after the settle allowance; the dictionary is the actual
/// word's advances in order of first occurrence (a support restriction and relabelling), the
/// passage the actual word's ordinals, the cycle the near-return's.
/// - F1: on every frame of `FrameFamily::pairs(9)` carrying the cycle, the actual passage (its
///   departures included) is founded by the located chart, encoded on `field_on(helix.periods())`,
///   admitted (`Field::admit`) and ingested by the reference port.
/// - F2: on carrying frames whose receiving period `d` exceeds `τ`, the pair located from the
///   admitted passage with its departures erased releases each departure cell to the cycle's class;
///   the repair's residual of the actual word is refused `NotRegenerated` where a departure exists
///   (a substitution is not an erasure) and is empty on the clean tone.
/// - F3: on carrying frames whose receiving cells equal the classes (`located_code`'s bijection), the
///   emission (header, start class, frame index, dictionary, located code with its patches) is read
///   back by [`decode_section`] to the whole window's `SectionWord`, its placement and its clock.
/// - F4: the emission's bits apart from the header beside the near-return's `L_τ + 2` and the spelled
///   `3L + 2`, with the pair's key bits.
#[test]
fn a_rings_departed_section_word_enters_the_field_on_its_located_helix_and_decodes_whole() {
    use holonics::compression::CompressionError;
    use holonics::compression::keys::repair::{CellRelease, DamagedPassage, key_code, residual_code, restrict};
    use holonics::compression::keys::transport::located_code;
    use holonics::hnn::keys::{PairLocation, damaged_station_pairs};
    use holonics::hnn::section_lock::{LockReader, LockWindow, Settled};
    use holonics::hnn::wave::{MatchedWave, WavePort};
    use holonics::hnn::{Current, ExecutionPort, Reference};
    let f1 = [-9i64, -9, -2, -2, 5, 5, 12];
    let (settle, length, ring_t, hop) = (120usize, 120usize, 1usize, 1usize);
    let window = LockWindow::new(settle, length).unwrap();
    let family = FrameFamily::pairs(9).unwrap();
    let frame_width = index_bits(family.frames().len());
    for (name, departure) in [("clean", None), ("departed", Some((180usize, 7i64)))] {
        let mut tone: Vec<i64> = (0..240).map(|k| f1[k % 7]).collect();
        if let Some((k, d)) = departure {
            tone[k] += d;
        }
        let operands = section_ring(ring_t as i64);
        let wave = MatchedWave::new(
            operands.admittance().clone(),
            operands.hop().clone(),
            tone.iter().map(|&x| integer(x)).collect(),
        )
        .unwrap();
        let mut port = WavePort::at_rest(operands, 0).unwrap();
        let mut reader = LockReader::new(window);
        reader.observe(port.phase_point()).unwrap();
        for tick in port.receive(&wave).unwrap() {
            let tick = tick.unwrap();
            reader.observe([tick.step.state[1][0].clone(), tick.step.state[0][0].clone()]).unwrap();
        }
        let settled = reader.finish().unwrap();
        let near = settled.near_return(&window).unwrap();
        let Settled::Word(word) = &settled else {
            panic!("the ring left rest")
        };
        let advances: Vec<i8> = word.symbols().iter().map(|s| s.advance).collect();
        let mut dictionary: Vec<i8> = Vec::new();
        for &a in &advances {
            if !dictionary.contains(&a) {
                dictionary.push(a);
            }
        }
        let classes = dictionary.len();
        let actual: Vec<usize> = advances
            .iter()
            .map(|&a| dictionary.iter().position(|&s| s == a).unwrap())
            .collect();
        let tau = near.period();
        let departures: Vec<usize> = near.defects().iter().map(|&(k, _)| k).collect();
        let cycle: Vec<usize> = (0..tau)
            .map(|j| actual[(j..length).step_by(tau).find(|k| !departures.contains(k)).unwrap()])
            .collect();
        let periodic: Vec<usize> = (0..length).map(|k| cycle[k % tau]).collect();
        let location = family.locate(classes, &[periodic.clone()]).unwrap();
        println!(
            "§28 ({name}): τ {tau}, departures {:?}, dictionary {:?} ({classes} classes), near-return bits {:?}; tally {:?}",
            near.defects(),
            dictionary,
            near.bits(),
            location.tally()
        );
        // A class the cycle never reads has no transport in a located member (its gauge is plural,
        // never guessed): a dictionary wider than the cycle's support carries on no frame (§28, measured).
        let mut support: Vec<usize> = cycle.clone();
        support.sort_unstable();
        support.dedup();
        if location.carrying().next().is_none() {
            assert!(
                classes > support.len(),
                "F1 ({name}): only a dictionary wider than the cycle's support is refused"
            );
            println!(
                "  ({name}) no frame carries: the dictionary's {classes} classes include {} the cycle never reads",
                classes - support.len()
            );
            continue;
        }
        let (mut entered, mut paired, mut emitted) = (0, 0, 0);
        let mut aeons = Vec::new();
        for (helix, carrying) in location.carrying() {
            let frame = family.frames().iter().position(|h| h.periods() == helix.periods()).unwrap();
            // F1: the actual passage enters the field declared on the frame's own rings.
            let located = PassageChart::located(carrying.location(), &[actual.clone()])
                .unwrap_or_else(|e| panic!("F1 ({name}) frame {:?}: the located chart refuses the actual passage: {e}", helix.periods()));
            let encoding = Encoding::found(&located).unwrap();
            let field = field_on(helix.periods());
            let encoded = Encoded::through(&encoding, &located, &field, &[actual.clone()]).unwrap();
            field.admit(&encoded[0]).unwrap();
            let reference = Reference::new(64, u64::MAX);
            let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
            let (_, closed) = ingest_whole(&reference, &mut resident, None, &encoded[0]);
            aeons.push(closed);
            entered += 1;
            // F2: the pair at the receiving ring's own distance cap.
            let d = helix.cells() as usize;
            let receiving = helix.periods().len() - 1;
            if d > tau {
                // The admitted passage's own classes are the chart's indices (`classes_read`), over
                // the chart's class count: the pair is read in them, not in the dictionary's ordinals.
                let cells: Vec<usize> = encoded[0].classes_read().collect();
                let chart_classes = encoded[0].classes();
                let cycle_cells: Vec<usize> = (0..tau)
                    .map(|j| cells[(j..length).step_by(tau).find(|k| !departures.contains(k)).unwrap()])
                    .collect();
                let damaged = DamagedPassage::encoded(&encoded[0], &departures, 1).unwrap();
                let mut pair = PairLocation::open(&field, receiving);
                for (_, readings) in damaged_station_pairs(&field, receiving, &damaged).unwrap() {
                    pair.observe(&readings);
                }
                let survivors = pair.survivors();
                match survivors.located() {
                    Some(located_pair) => {
                        let relation = located_pair.relation(&field, receiving, chart_classes).unwrap();
                        let key = key_code(&relation, d).unwrap();
                        let releases = restrict(&damaged, &relation).unwrap().release().unwrap();
                        for &k in &departures {
                            assert_eq!(
                                releases[k],
                                CellRelease::Released(cycle_cells[k % tau]),
                                "F2 ({name}) frame {:?}: the departure cell {k} is released to the cycle's class",
                                helix.periods()
                            );
                        }
                        let residual = residual_code(&cells, &damaged, &relation);
                        if departures.is_empty() {
                            assert_eq!(residual.unwrap(), Vec::<bool>::new(), "F2 ({name}): nothing is held");
                        } else {
                            assert!(
                                matches!(residual, Err(CompressionError::NotRegenerated { .. })),
                                "F2 ({name}): a substitution is not an erasure; got {residual:?}"
                            );
                        }
                        println!(
                            "  F2 frame {:?} (index {frame}, {chart_classes} chart classes): pair (δ {}, map {:?}), key {} bits, surviving distances {:?}",
                            helix.periods(),
                            located_pair.offset,
                            located_pair.map,
                            key.len(),
                            survivors.distances()
                        );
                        paired += 1;
                    }
                    None => println!(
                        "  F2 frame {:?} (index {frame}): no pair located; surviving distances {:?} of {} read",
                        helix.periods(),
                        survivors.distances(),
                        survivors.read
                    ),
                }
            }
            // F3: the emission, read back by the independent decoder.
            if d == classes {
                let code = located_code(carrying.transport(), &[actual.clone()]).unwrap();
                let mut emission = Vec::new();
                push_gamma(&mut emission, settle + 1);
                push_gamma(&mut emission, length);
                push_gamma(&mut emission, ring_t);
                push_gamma(&mut emission, hop);
                let header = emission.len();
                push(&mut emission, usize::from(word.start_class().unwrap()), 2);
                push(&mut emission, frame, frame_width);
                push_gamma(&mut emission, classes);
                for &a in &dictionary {
                    push(&mut emission, usize::try_from(a + 2).unwrap(), 3);
                }
                emission.extend(&code);
                let decoded = decode_section(&emission, &family);
                assert_eq!(
                    decoded,
                    DecodedSection { settle, length, ring: ring_t, hop, word: word.clone() },
                    "F3 ({name}) frame {:?}: the emission decodes the whole word, its placement and clock",
                    helix.periods()
                );
                assert_eq!(decoded.word.winding(), word.winding());
                let (near_bits, raw_bits) = near.bits();
                println!(
                    "  F3 frame {:?} (index {frame}): emission {} bits after a {header}-bit header (located code {}), against near-return {} and spelled {}",
                    helix.periods(),
                    emission.len() - header,
                    code.len(),
                    near_bits + 2,
                    raw_bits + 2
                );
                emitted += 1;
            }
        }
        println!("  ({name}) frames entered {entered} (aeons closed per frame {aeons:?}), paired {paired}, emitted {emitted}");
        assert!(entered > 0, "F1 ({name}): some declared frame carries the cycle");
    }
}

/// The maximal runs of `[0, length)` between the departures, nonempty, in clock order.
fn runs_between(length: usize, departures: &[usize]) -> Vec<std::ops::Range<usize>> {
    let mut runs = Vec::new();
    let mut start = 0;
    for &k in departures.iter().chain(std::iter::once(&length)) {
        if k > start {
            runs.push(start..k);
        }
        start = k + 1;
    }
    runs
}

/// **The independent decoder of §28a** (R3): the header, start class, frame and dictionary as in
/// [`decode_section`]; then the departures (count, each gap and advance); the run lengths follow from
/// them and the window length; `read_located` returns the runs; the departures are interleaved and the
/// classes and crossings follow by `land` from the start class.
fn decode_runs(emission: &[bool], family: &FrameFamily) -> DecodedSection {
    use holonics::compression::keys::transport::read_located;
    use holonics::hnn::dynamic_section::{SectionSymbol, land};
    use holonics::hnn::section_lock::SectionWord;
    let mut bits = emission.iter().copied();
    let settle = pull_gamma(&mut bits) - 1;
    let length = pull_gamma(&mut bits);
    let ring = pull_gamma(&mut bits);
    let hop = pull_gamma(&mut bits);
    let start = u8::try_from(pull(&mut bits, 2)).unwrap();
    let helix = &family.frames()[pull(&mut bits, index_bits(family.frames().len()))];
    let classes = pull_gamma(&mut bits);
    let dictionary: Vec<i8> = (0..classes)
        .map(|_| i8::try_from(pull(&mut bits, 3)).unwrap() - 2)
        .collect();
    let count = pull_gamma(&mut bits) - 1;
    let mut at: isize = -1;
    let departures: Vec<(usize, i8)> = (0..count)
        .map(|_| {
            at += pull_gamma(&mut bits) as isize;
            (at as usize, i8::try_from(pull(&mut bits, 3)).unwrap() - 2)
        })
        .collect();
    let positions: Vec<usize> = departures.iter().map(|&(k, _)| k).collect();
    let runs = runs_between(length, &positions);
    let rest: Vec<bool> = bits.collect();
    let lengths: Vec<usize> = runs.iter().map(|r| r.len()).collect();
    let read = read_located(helix, classes, &rest, &lengths).unwrap();
    let mut advances = vec![0i8; length];
    for (run, ordinals) in runs.iter().zip(&read) {
        for (k, &o) in run.clone().zip(ordinals) {
            advances[k] = dictionary[o];
        }
    }
    for &(k, advance) in &departures {
        advances[k] = advance;
    }
    let mut class = start;
    let symbols = advances
        .iter()
        .map(|&advance| {
            let (crossing, landed) = land(class, advance).unwrap();
            let symbol = SectionSymbol { class, advance, crossing };
            class = landed;
            symbol
        })
        .collect();
    DecodedSection {
        settle,
        length,
        ring,
        hop,
        word: SectionWord::new(symbols).unwrap(),
    }
}

/// **The departed section word enters as its runs in the cycle's chart, its departures the residual**
/// (bank record §28a). §28 measured that a departure outside the cycle's support `S` has no class of
/// the cycle's located chart (the chart's cokernel). The window's maximal runs inside `S` are the
/// passages: founded together by the located chart, each at its own key, encoded on
/// `field_on(helix.periods())`, admitted, and ingested in clock order into one moment (R1); the pair
/// is located from all the runs' stations, each run's repair residual empty (R2); the emission
/// (header, start class, frame, dictionary `S`, the departures by gap and advance, the runs' located
/// code) decodes to the whole word (R3), charged beside the near-return and the spelled word (R4).
#[test]
fn a_departed_section_word_enters_as_its_runs_in_the_cycles_chart_with_its_departures_the_residual() {
    use holonics::compression::keys::repair::{DamagedPassage, residual_code};
    use holonics::compression::keys::transport::located_code;
    use holonics::hnn::keys::{PairLocation, damaged_station_pairs};
    use holonics::hnn::section_lock::{LockReader, LockWindow, Settled};
    use holonics::hnn::wave::{MatchedWave, WavePort};
    use holonics::hnn::{Current, ExecutionPort, Reference};
    let f1 = [-9i64, -9, -2, -2, 5, 5, 12];
    let (settle, length, ring_t, hop) = (120usize, 120usize, 1usize, 1usize);
    let window = LockWindow::new(settle, length).unwrap();
    let family = FrameFamily::pairs(9).unwrap();
    let frame_width = index_bits(family.frames().len());
    let mut tone: Vec<i64> = (0..240).map(|k| f1[k % 7]).collect();
    tone[180] += 7;
    let operands = section_ring(ring_t as i64);
    let wave = MatchedWave::new(
        operands.admittance().clone(),
        operands.hop().clone(),
        tone.iter().map(|&x| integer(x)).collect(),
    )
    .unwrap();
    let mut port = WavePort::at_rest(operands, 0).unwrap();
    let mut reader = LockReader::new(window);
    reader.observe(port.phase_point()).unwrap();
    for tick in port.receive(&wave).unwrap() {
        let tick = tick.unwrap();
        reader.observe([tick.step.state[1][0].clone(), tick.step.state[0][0].clone()]).unwrap();
    }
    let settled = reader.finish().unwrap();
    let near = settled.near_return(&window).unwrap();
    let Settled::Word(word) = &settled else {
        panic!("the ring left rest")
    };
    let advances: Vec<i8> = word.symbols().iter().map(|s| s.advance).collect();
    let tau = near.period();
    let defects: Vec<usize> = near.defects().iter().map(|&(k, _)| k).collect();
    // The cycle's advances and its support `S`, in order of first occurrence.
    let cycle: Vec<i8> = (0..tau)
        .map(|j| advances[(j..length).step_by(tau).find(|k| !defects.contains(k)).unwrap()])
        .collect();
    let mut support: Vec<i8> = Vec::new();
    for &a in &cycle {
        if !support.contains(&a) {
            support.push(a);
        }
    }
    let classes = support.len();
    let ordinal = |a: i8| support.iter().position(|&s| s == a);
    let periodic: Vec<usize> = (0..length).map(|k| ordinal(cycle[k % tau]).unwrap()).collect();
    // The departures: the cells outside the chart's support.
    let departures: Vec<usize> = (0..length).filter(|&k| ordinal(advances[k]).is_none()).collect();
    let runs = runs_between(length, &departures);
    let passages: Vec<Vec<usize>> = runs
        .iter()
        .map(|run| run.clone().map(|k| ordinal(advances[k]).unwrap()).collect())
        .collect();
    let location = family.locate(classes, &[periodic.clone()]).unwrap();
    println!(
        "§28a: τ {tau}, support {support:?}, departures {departures:?}, runs {:?}; tally {:?}",
        runs,
        location.tally()
    );
    assert_eq!(location.carrying().count(), 18, "R1: the cycle in S carries on the clean tone's 18 frames");
    let (mut paired, mut emitted) = (0, 0);
    let mut aeons = Vec::new();
    for (helix, carrying) in location.carrying() {
        let frame = family.frames().iter().position(|h| h.periods() == helix.periods()).unwrap();
        // R1: the runs enter, in clock order, into one moment.
        let located = PassageChart::located(carrying.location(), &passages).unwrap();
        let encoding = Encoding::found(&located).unwrap();
        let field = field_on(helix.periods());
        let encoded = Encoded::through(&encoding, &located, &field, &passages).unwrap();
        let reference = Reference::new(64, u64::MAX);
        let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
        let mut moment = None;
        let mut closed = 0;
        for passage in &encoded {
            field.admit(passage).unwrap();
            let (id, aeons) = ingest_whole(&reference, &mut resident, moment, passage);
            moment = Some(id);
            closed += aeons;
        }
        aeons.push(closed);
        // R2: the pair from every run's stations.
        let d = helix.cells() as usize;
        let receiving = helix.periods().len() - 1;
        if d > tau {
            let mut pair = PairLocation::open(&field, receiving);
            let damaged: Vec<DamagedPassage> =
                encoded.iter().map(|passage| DamagedPassage::encoded(passage, &[], 1).unwrap()).collect();
            for passage in &damaged {
                for (_, readings) in damaged_station_pairs(&field, receiving, passage).unwrap() {
                    pair.observe(&readings);
                }
            }
            let survivors = pair.survivors();
            let located_pair = survivors.located().unwrap_or_else(|| {
                panic!("R2 frame {:?}: no pair located; surviving {:?}", helix.periods(), survivors.distances())
            });
            let relation = located_pair.relation(&field, receiving, encoded[0].classes()).unwrap();
            for (passage, run_cells) in damaged.iter().zip(&encoded) {
                let cells: Vec<usize> = run_cells.classes_read().collect();
                assert_eq!(residual_code(&cells, passage, &relation).unwrap(), Vec::<bool>::new(), "R2: a run holds no departure");
            }
            println!(
                "  R2 frame {:?} (index {frame}): pair (δ {}, map {:?}), surviving {:?}",
                helix.periods(),
                located_pair.offset,
                located_pair.map,
                survivors.distances()
            );
            paired += 1;
        }
        // R3: the emission and the independent decoder.
        if d == classes {
            let code = located_code(carrying.transport(), &passages).unwrap();
            let mut emission = Vec::new();
            push_gamma(&mut emission, settle + 1);
            push_gamma(&mut emission, length);
            push_gamma(&mut emission, ring_t);
            push_gamma(&mut emission, hop);
            let header = emission.len();
            push(&mut emission, usize::from(word.start_class().unwrap()), 2);
            push(&mut emission, frame, frame_width);
            push_gamma(&mut emission, classes);
            for &a in &support {
                push(&mut emission, usize::try_from(a + 2).unwrap(), 3);
            }
            push_gamma(&mut emission, departures.len() + 1);
            let mut at: isize = -1;
            for &k in &departures {
                push_gamma(&mut emission, (k as isize - at) as usize);
                push(&mut emission, usize::try_from(advances[k] + 2).unwrap(), 3);
                at = k as isize;
            }
            let residual = emission.len() - header;
            emission.extend(&code);
            let decoded = decode_runs(&emission, &family);
            assert_eq!(
                decoded,
                DecodedSection { settle, length, ring: ring_t, hop, word: word.clone() },
                "R3 frame {:?}: the emission decodes the whole departed word, its placement and clock",
                helix.periods()
            );
            let (near_bits, raw_bits) = near.bits();
            println!(
                "  R3 frame {:?} (index {frame}): emission {} bits after a {header}-bit header (start, frame, dictionary and departures {residual}; the runs' located code {}), against near-return {} and spelled {}",
                helix.periods(),
                emission.len() - header,
                code.len(),
                near_bits + 2,
                raw_bits + 2
            );
            emitted += 1;
        }
    }
    println!("  §28a: frames entered 18 (aeons closed per frame {aeons:?}), paired {paired}, emitted {emitted}");
    assert!(emitted > 0, "R3: some carrying frame's code ranks the support");
}

// -------------------------------------------------------------------------------------------
// the field learns the section word online (the online-learning record §1)

/// The clean F1 section word of the ring `t = 1` over the window opening at `settle` and running
/// `length` ticks: its advances read as their own ordinals (the dictionary in order of first
/// occurrence), and the near-return's period of the word's first `prefix` ticks alone (the
/// development prefix; the online-learning record §10).
fn clean_section_word(settle: usize, length: usize, prefix: usize) -> (Vec<usize>, Vec<i8>, usize) {
    use holonics::hnn::section_lock::{LockReader, LockWindow, Settled};
    use holonics::hnn::wave::{MatchedWave, WavePort};
    let f1 = [-9i64, -9, -2, -2, 5, 5, 12];
    let tone: Vec<i64> = (0..settle + length).map(|k| f1[k % 7]).collect();
    let read = |window: LockWindow| -> Settled {
        let operands = section_ring(1);
        let wave = MatchedWave::new(
            operands.admittance().clone(),
            operands.hop().clone(),
            tone.iter().map(|&x| integer(x)).collect(),
        )
        .unwrap();
        let mut port = WavePort::at_rest(operands, 0).unwrap();
        let mut reader = LockReader::new(window);
        reader.observe(port.phase_point()).unwrap();
        for tick in port.receive(&wave).unwrap() {
            let tick = tick.unwrap();
            reader.observe([tick.step.state[1][0].clone(), tick.step.state[0][0].clone()]).unwrap();
        }
        reader.finish().unwrap()
    };
    let development = LockWindow::new(settle, prefix).unwrap();
    let tau = read(development).near_return(&development).unwrap().period();
    let Settled::Word(word) = read(LockWindow::new(settle, length).unwrap()) else {
        panic!("the ring left rest")
    };
    let mut dictionary: Vec<i8> = Vec::new();
    for symbol in word.symbols() {
        if !dictionary.contains(&symbol.advance) {
            dictionary.push(symbol.advance);
        }
    }
    let ordinals = word
        .symbols()
        .iter()
        .map(|symbol| dictionary.iter().position(|&a| a == symbol.advance).unwrap())
        .collect();
    (ordinals, dictionary, tau)
}

/// **The field learns a ring's section word online, its chart pinned from a development prefix**
/// (the online-learning record §1–§10). For two openings of the clean F1 window (`settle` 120 and
/// 123, a shifted phase of the same cycle), the cycle's period and the located chart are read from
/// the word's first 28 cells only and frozen; the field declared on each carrying frame whose
/// receiving cells equal the support ingests the prefix, then each later cell is coded at the
/// receiver's population (the compare's receipt) before it is read: the learner deposits, the twin
/// discards its staged deposit. The receiver addresses by cells alone, or by cells and the hidden
/// ring's phase class (`Phase(0, d_0)`, the located navigator's clock, read after each received
/// cell). Asserts, on cells `60 … 119`: C1, the learner below its twin; with the clock letter, C2″
/// (every cell of the last two cycles below one bit) and C3″ (the clocked learner's code below the
/// cell-only learner's); and reports the letters' description charge (`Field::describe`) and the
/// frozen chart's located code beside them.
#[test]
fn the_field_learns_a_rings_section_word_online() {
    use holonics::compression::keys::transport::located_code;
    use holonics::hnn::port::ReceiptDetail;
    use holonics::hnn::receiving::{Feature, FeatureFamily};
    use holonics::hnn::{Current, ExecutionPort, Handle, Reference};
    use std::time::Instant;
    let (length, prefix) = (120usize, 28usize);
    let started = Instant::now();
    let mut read = 0;
    for settle in [120usize, 123] {
        let (actual, dictionary, tau) = clean_section_word(settle, length, prefix);
        // The development prefix alone founds the chart: its cycle, located and frozen.
        let periodic: Vec<usize> = (0..prefix).map(|k| actual[k % tau]).collect();
        let family = FrameFamily::pairs(9).unwrap();
        let location = family.locate(dictionary.len(), &[periodic.clone()]).unwrap();
        for (helix, carrying) in location.carrying() {
            if helix.cells() as usize != dictionary.len() {
                continue;
            }
            read += 1;
            let located = PassageChart::located(carrying.location(), &[actual[..prefix].to_vec()]).unwrap();
            let encoding = Encoding::found(&located).unwrap();
            let chart_bits = located_code(carrying.transport(), &[actual[..prefix].to_vec()]).unwrap().len();
            let mut learner_sums = Vec::new();
            for clocked in [false, true] {
                let plain = field_on(helix.periods());
                let field = if clocked {
                    let letter = Feature::Phase { ring: 0, grain: helix.periods()[0] };
                    plain.clone().with_letter_family(FeatureFamily::new(vec![letter]).unwrap()).unwrap()
                } else {
                    plain.clone()
                };
                let letters_charge = field.describe(u64::MAX, 64).len() as i64 - plain.describe(u64::MAX, 64).len() as i64;
                let encoded = Encoded::through(&encoding, &located, &field, &[actual.clone()]).unwrap().remove(0);
                let mut sums = Vec::new();
                let mut continued = 0;
                let mut minus = Vec::new();
                for learner in [true, false] {
                    let reference = Reference::new(64, u64::MAX);
                    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
                    let (moment, _) = ingest_whole(&reference, &mut resident, None, &encoded.part(0..prefix).unwrap());
                    let phases = resident.admitted()[0].clone();
                    let (mut lower, mut upper) = (rat(0, 1), rat(0, 1));
                    for n in prefix..length {
                        let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
                        let (staged, compared) = reference
                            .compare(&mut resident, pending, &encoded.part(n..n + 1).unwrap())
                            .unwrap();
                        let code = match &compared.receipt.detail {
                            ReceiptDetail::Compare { code_length, .. } => code_length.clone(),
                            _ => panic!("a compare's receipt"),
                        };
                        if n >= length / 2 {
                            lower = lower + &code.lower;
                            upper = upper + &code.upper;
                        }
                        if learner {
                            reference.deposit(&mut resident, staged).unwrap();
                            if n >= length - 2 * tau {
                                if code.upper < rat(1, 1) {
                                    continued += 1;
                                }
                                if dictionary[actual[n]] == -2 {
                                    minus.push((n, code.clone()));
                                }
                            }
                        } else {
                            reference.discard(&mut resident, Handle::Staged(staged)).unwrap();
                        }
                        ingest_whole(&reference, &mut resident, Some(moment), &encoded.part(n..n + 1).unwrap());
                    }
                    sums.push((lower, upper));
                }
                println!(
                    "§10 settle {settle} frame {:?} clocked {clocked}: τ {tau} from the {prefix}-cell prefix; cells {}..{} population, learner [{}, {}] against twin [{}, {}]; continued {continued} of {}; the -2 cells {:?}; letters charge {letters_charge} bits; frozen chart {chart_bits} bits ({} ms)",
                    helix.periods(),
                    length / 2,
                    length,
                    sums[0].0,
                    sums[0].1,
                    sums[1].0,
                    sums[1].1,
                    2 * tau,
                    minus.iter().map(|(n, c)| (*n, c.upper.clone())).collect::<Vec<_>>(),
                    started.elapsed().as_millis()
                );
                assert!(sums[0].1 < sums[1].0, "C1: the learner codes the second half below its twin");
                if clocked {
                    assert_eq!(continued, 2 * tau, "C2'': the clocked learner codes the last two cycles below one bit");
                    assert!(letters_charge > 0, "the declared letters are charged in the field's code");
                } else {
                    assert!(continued < 2 * tau, "cell letters alone: the majority read (§3, §4)");
                }
                learner_sums.push(sums[0].clone());
            }
            println!(
                "§10 settle {settle} frame {:?}: C3'' the clocked learner's upper {} against the cell-only learner's lower {}",
                helix.periods(),
                learner_sums[1].1,
                learner_sums[0].0
            );
            assert!(learner_sums[1].1 < learner_sums[0].0, "C3'': the clock letter lowers the learner's code");
        }
    }
    assert!(read > 0);
}
