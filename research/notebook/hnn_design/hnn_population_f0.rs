//! **`f0`: F0's acceptance run, the predictor on unseen families** (`docs/plans/THE_REBUILD.md`, F0
//! and U6; the pins are
//! `research/records/2026-09-28_F0_THE_PREDICTOR_ON_UNSEEN_FAMILIES_PINNED_BEFORE_ITS_SPLIT_IS_READ.md`,
//! §1, committed before the split was generated; #63, #73, #148). Included by `hnn_population.rs`
//! as its `f0-acceptance` mode; a committed command run once in release, never a test. It prints
//! counts, codes, bytes and times only; the releases' text goes to an owner-only file (`none` skips
//! the releases).
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_population -- f0-acceptance .local/cuts/curated-f0-passage-cut.bin .local/cuts/curated-f0-passage-flat-cut.bin .local/cuts/f0-acceptance-releases.json
//! ```
//!
//! [definition; agent-inferred, the record's pins] **What it executes.**
//! - **The egg**: F0's admitted egg (`f0-egg`'s constructor, its byte tree at
//!   [`F0_BYTE_DEPTH`] = 12 ticks, U2's adopted cut), the hazard partition learned on the choosing
//!   cells alone, read directly through its `Family` law (exact faces), as U2's harness read it.
//! - **The receiver**: U2's conditional byte-and-stop code at `L_R = 16`: every byte cell's face,
//!   and at each response's stop (a section letter whose open part is on the agent channel) the
//!   face's mass on the section letters; the letter given the stop, the human closes, the request's
//!   pointer and the letter at the families' join are observed and charged to neither side. At each
//!   stop the face read is checked equal to the face the egg charges when the letter arrives.
//! - **The comparison**: the egg's validation bytes and stops, charged its declaration (the
//!   development sweep's 17 bits, F0's adoption decisions' 5 and the learned partition's
//!   description), against the flat tree's (`D = 48`) validation bytes, charged its depth sweep's 3;
//!   the flat tree codes no stop and is charged none. The code clause holds when the charged
//!   difference's upper end lies strictly below `−m`. The bytes alone and the whole curated stream
//!   (every cell, the request's pointer and the charges, against the flat stream) are read beside.
//! - **The standing**: the egg's canonical checkpoint after the passage, whole, against the budget
//!   of 1,298 bytes a cell; the readings kept beside the state (44 bytes a byte-tree node) and the
//!   standing without them beside it.
//! - **The passage budget**: the egg's reading of the validation families within 600,000 ms (the
//!   releases' time apart), and the run's resident set within 20,000,000,000 bytes.
//! - **The releases**, deciding nothing: at each of the selected validation responses (the lowest
//!   32 order keys among the eligible, module constants), the egg's future is branched at the
//!   response's opening and released under the scored law (`Population::release_response`, the egg
//!   alone named by 0 bits) with a cap of [`RELEASE_CAP`] bytes; the flat tree's future is branched
//!   at the same byte and, having no stop to draw, draws the same cap's bytes from the same keys. It
//!   is given no length: the logged reply is observed conduct, never a target, and the length it lent
//!   the flat control is retired (the audit of September 29, finding 7; THE_REBUILD U6). The logged
//!   reply is shown beside the releases, and the text of each goes to the owner-only file.
//! - **The aeons** (the audit's §4 item 1; THE_REBUILD U6): a passage whose cut carries its aeons
//!   (`<cut>.aeons.bin`, `curated_source.py`) is read with each conversation's context its own. The
//!   egg enters a part's aeon at its letter (`AdmittedEgg::enter_aeon`), and the flat tree enters it
//!   before the part's first byte (`TreeFamily::enter_aeon`), so the comparison stays symmetric.
//! - **The reserve**: every cut read must name the development reserve as excluded
//!   (`exterior::RESERVE_SHA256`) unless `--read-reserve` is passed; F0's own passage predates the
//!   reserve and holds it, so its receipts reproduce at `adc2cfbc`.
//! - **The guards**: a passage past 600,000 ms or a resident set past 20,000,000,000 bytes stops the
//!   run; its partial evidence is printed as incomplete.

use std::collections::BTreeMap;
use std::time::Instant;

use holonics::compression::landmark::context::{LetterFamily, PassageCode, SectionChart};
use holonics::holarchy::terrain::Draw;
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use holonics::receiver::population::{
    AdmittedEgg, AdmittedReadout, Family, HazardPartition, Population, Readout, Relation,
    RelationKind, ResponseLaw, ResponseRefusal, TreeFamily, learn_hazard_partition,
};
use holonics::receiver::release::{ReleaseReturn, draw_exact};
use num_bigint::BigInt;

use super::curated::{
    F0_BYTE_DEPTH, FLAT_DEPTH, FLAT_SWEEP, PROBED, admitted_egg_at, bits, ceil_log2, declaration,
    joined, point, sum,
};
use super::exterior::{
    RESERVE_SHA256, against, enclosure, per, read_aeons, read_curated, read_cut, read_incidence,
    reading_of, reserve_read, resident_set,
};

/// **The margin `m` in bits** (the record's pin 6): the range of the uncharged conditional
/// difference `V_egg − V_flat` over the spent family draws read at F0's aperture by this harness
/// (F1's, F4's, F5's and U2's passages), rounded up to whole bits: from F1's upper end (the draw
/// `−279 + 10/16 + ε`) to U2's lower end (`−812 + 9/16 + ε`), `533 + 1/16 + ε`, so `m = 534`
/// (the record's §2), committed before the fresh split is generated.
const MARGIN: Option<u64> = Some(534);

/// The standing budget in bytes a cell (pin 7: the flat control's standing on F4's passage, U2's).
const BUDGET: u64 = 1298;

/// F0's adoption decisions made on choosing families before this run (pin 5): candidates 1, 2 and
/// 3 each adopted or not, candidate 5 one of three; charged `⌈log₂ (2·2·2·3)⌉ = 5` bits.
pub(super) const DECISIONS: [u64; 4] = [2, 2, 2, 3];

/// The readings a byte-tree node's chart keeps beside the state (the census's E0, U2's pin 5).
const READING_BYTES: u64 = 44;

/// The guards and the passage budget: a passage's milliseconds, and the resident set's bytes.
const PASSAGE_MS: u128 = 600_000;
const RESIDENT: u128 = 20_000_000_000;
const GUARD_EVERY: usize = 1 << 14;

/// The releases (pin 9): how many, the declared seed of their order keys, and the cap in bytes:
/// the largest power of two `P` with `P·c + b ≤ 60,000` ms (F4's warm response), `c = 89/4` ms a
/// released cell and `b = 677` ms the longest branch on the F4 dry run, so `2048·c + b = 46,245`
/// and `4096·c + b = 91,813` (the record's §2).
const RELEASES: usize = 32;
const RELEASE_SEED: u64 = 20_260_928;
const RELEASE_CAP: usize = 2048;

/// The agent channel (the curated chart's channels: human, agent, tool).
const AGENT: usize = 1;
const CHANNELS: [&str; 3] = ["human", "agent", "tool"];

/// **One role's conditional byte-and-stop code**: each channel's bytes and the response stops, and
/// the whole curated stream (every cell's face, letters included).
struct Code {
    bytes: [PassageCode; 3],
    stops: PassageCode,
    whole: PassageCode,
    byte_cells: [u64; 3],
    stop_cells: u64,
    letters: u64,
}

impl Code {
    fn new() -> Self {
        Self {
            bytes: [PassageCode::new(), PassageCode::new(), PassageCode::new()],
            stops: PassageCode::new(),
            whole: PassageCode::new(),
            byte_cells: [0; 3],
            stop_cells: 0,
            letters: 0,
        }
    }

    fn total(&self) -> ExactInterval {
        joined(self.bytes.iter().chain([&self.stops]))
    }

    fn bytes_only(&self) -> ExactInterval {
        joined(&self.bytes)
    }

    fn byte_count(&self) -> u64 {
        self.byte_cells.iter().sum()
    }
}

/// The standing: the egg's canonical checkpoint bytes and its byte tree's nodes (U2's reading).
struct Standing {
    whole: u64,
    nodes: u64,
}

impl Standing {
    fn of(egg: &AdmittedEgg) -> Self {
        let whole = egg
            .admitted_checkpoint()
            .expect("the admitted egg's checkpoint")
            .expect("an encodable standing")
            .len() as u64;
        Self {
            whole,
            nodes: egg.inner().byte_tree().tree().nodes() as u64,
        }
    }

    fn readings(&self) -> u64 {
        READING_BYTES * self.nodes
    }

    fn bare(&self) -> u64 {
        self.whole - self.readings()
    }
}

/// Why a passage stopped: a guard passed.
pub(super) enum Stopped {
    Time(u128),
    Memory(u128),
}

pub(super) fn guard(reading_ms: u128) -> Result<(), Stopped> {
    if reading_ms > PASSAGE_MS {
        return Err(Stopped::Time(reading_ms));
    }
    if let Some((now, _)) = resident_set()
        && now > RESIDENT
    {
        return Err(Stopped::Memory(now));
    }
    Ok(())
}

pub(super) fn stopped(what: &str, why: Stopped) -> ! {
    let why = match why {
        Stopped::Time(ms) => format!("the passage reached {ms} ms, past {PASSAGE_MS}"),
        Stopped::Memory(bytes) => {
            format!("the resident set reached {bytes} bytes, past {RESIDENT}")
        }
    };
    panic!(
        "STOPPED at {what}: {why}; resident set (now, peak) {:?} bytes; the partial evidence above is incomplete",
        resident_set()
    );
}

/// `a − b`, enclosed: `[a.lower − b.upper, a.upper − b.lower]`.
pub(super) fn minus(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower - &b.upper,
        upper: &a.upper - &b.lower,
    }
}

fn difference_line(label: &str, a: &ExactInterval, b: &ExactInterval, cells: u64) {
    let delta = minus(a, b);
    println!(
        "    {label}: {}; difference {}, a byte {}",
        against(a, b),
        enclosure(&delta, super::GRAIN),
        per(&delta, cells, super::GRAIN)
    );
}

/// A validation response selected for release: its letter, its request's letter, its order key.
pub(super) struct Selected {
    pub(super) letter: usize,
    pub(super) target: usize,
    pub(super) key: u64,
}

/// The bytes of the part a section letter opens, up to the next section letter.
pub(super) fn part_bytes(codes: &[usize], letter: usize, chart: SectionChart) -> Vec<u8> {
    codes[letter + 1..]
        .iter()
        .take_while(|&&code| chart.section(code).is_none())
        .map(|&code| u8::try_from(code).expect("a byte cell"))
        .collect()
}

/// **The selection** (pin 9): the validation role's declared request→response relations whose
/// request lies in the validation role, whose response opens on the agent channel, and whose two
/// parts are nonempty, with room in the aperture; ordered by `Draw::new(seed + v).next()`, `v` the
/// response letter's tick in the validation role, the lowest `count` kept (F0: [`RELEASE_SEED`]
/// and [`RELEASES`]).
pub(super) fn select(
    codes: &[usize],
    relations: &[Relation],
    development: usize,
    population: usize,
    chart: SectionChart,
    seed: u64,
    count: usize,
) -> (usize, Vec<Selected>) {
    let mut eligible: Vec<Selected> = relations
        .iter()
        .filter(|relation| relation.kind == RelationKind::Request)
        .filter_map(|relation| {
            let letter = usize::try_from(relation.letter).ok()?;
            let target = usize::try_from(relation.target).ok()?;
            let opens_agent = chart
                .section(*codes.get(letter)?)
                .is_some_and(|section| section.channel == AGENT);
            let nonempty = |at: usize| {
                codes
                    .get(at + 1)
                    .is_some_and(|&code| chart.section(code).is_none())
            };
            (letter >= development
                && target >= development
                && target < letter
                && opens_agent
                && nonempty(letter)
                && nonempty(target)
                && population > letter + 2)
                .then(|| Selected {
                    letter,
                    target,
                    key: Draw::new(seed.wrapping_add((letter - development) as u64)).next(),
                })
        })
        .collect();
    let eligible_count = eligible.len();
    eligible.sort_by_key(|selected| selected.key);
    eligible.truncate(count);
    (eligible_count, eligible)
}

/// One key of `[0, 1)` from the draw.
pub(super) fn key_of(draw: &mut Draw) -> Rat {
    Rat::new(BigInt::from(draw.next()), BigInt::from(1u8) << 64)
}

/// The egg's release at one response: its status, bytes and times.
struct EggRelease {
    status: String,
    bytes: Vec<u8>,
    released: bool,
    cells: usize,
    branch_ms: u128,
    warm_ms: u128,
}

pub(super) fn refusal_name(refusal: &ResponseRefusal) -> &'static str {
    match refusal {
        ResponseRefusal::Chart { .. } => "chart",
        ResponseRefusal::NoRoomForStop { .. } => "no-room-for-stop",
        ResponseRefusal::FamilyMissing { .. } => "family-missing",
        ResponseRefusal::Face { .. } => "face",
        ResponseRefusal::Draw { .. } => "unresolved-face-fibre",
        ResponseRefusal::Provenance { .. } => "provenance",
        ResponseRefusal::Receive { .. } => "receive",
    }
}

/// **The egg's release** from its standing after the response's opening letter (`received` cells):
/// a branch at the present incidence (`AdmittedEgg::branch_at_present`: the passage's declared
/// future relations withheld, amended pin 9), alone in a population named by 0 bits, under the
/// scored law, the cap the least of [`RELEASE_CAP`] and the aperture's room.
fn release_egg(
    egg: &AdmittedEgg,
    chart: SectionChart,
    population: usize,
    received: usize,
    key: u64,
) -> EggRelease {
    let clock = Instant::now();
    let branch: Box<dyn Family> = Box::new(egg.branch_at_present());
    let branch_ms = clock.elapsed().as_millis();
    let mut alone = Population::new(vec![branch]).expect("the egg alone, named by 0 bits");
    let room = RELEASE_CAP.min(population - received - 1);
    let mut draw = Draw::new(key);
    let mut keys = || key_of(&mut draw);
    let release = alone.release_response(chart, room + 1, ResponseLaw::Scored, &mut keys);
    let status = match (&release.refusal, release.last()) {
        (None, Some(ReleaseReturn::Unresolved(_))) => "unresolved-face-fibre".to_string(),
        (Some(refusal), _) => format!("refused ({})", refusal_name(refusal)),
        (None, Some(ReleaseReturn::NoContinuationBridges { .. })) => {
            "no-stop-within-the-cap".to_string()
        }
        (None, _) => match release.text(chart) {
            Some(Ok(_)) => "released".to_string(),
            Some(Err(_)) => "text-codec-separator".to_string(),
            None => "no-stop".to_string(),
        },
    };
    EggRelease {
        released: status == "released",
        status,
        cells: release.emitted(),
        bytes: release.bytes,
        branch_ms,
        warm_ms: clock.elapsed().as_millis(),
    }
}

/// **The flat tree's release** at the response's first byte: a branch of its future drawing
/// `length` bytes from its exact face, from the same keys; the caller passes the egg's cap, never a
/// logged reply's length.
fn release_flat(tree: &TreeFamily, length: usize, key: u64) -> (Vec<u8>, u128) {
    let clock = Instant::now();
    let mut branch = Family::branch_future(tree).expect("the flat tree branches its future");
    let mut draw = Draw::new(key);
    let mut bytes = Vec::with_capacity(length);
    for _ in 0..length {
        let face = branch.face().expect("the flat tree's face");
        let class = draw_exact(&face, &key_of(&mut draw))
            .expect("a normalized exact face")
            .drawn_class()
            .expect("an exact face certifies one class");
        branch.receive(class).expect("a byte of the flat chart");
        bytes.push(u8::try_from(class).expect("a byte class"));
    }
    (bytes, clock.elapsed().as_millis())
}

/// A JSON string literal of `bytes` (lossy where they are not UTF-8; the flag says which).
pub(super) fn json_text(bytes: &[u8]) -> String {
    let text = String::from_utf8_lossy(bytes);
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if u32::from(c) < 0x20 => out.push_str(&format!("\\u{:04x}", u32::from(c))),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Write the owner-only release file (mode 0600, its directory owner-only).
pub(super) fn write_private(path: &str, contents: &str) {
    use std::io::Write;
    use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
    let path = std::path::Path::new(path);
    let parent = path.parent().expect("a private output directory");
    assert_eq!(
        std::fs::metadata(parent)
            .expect("the output directory")
            .permissions()
            .mode()
            & 0o077,
        0,
        "the output directory is owner-only"
    );
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .mode(0o600)
        .open(path)
        .expect("the owner-only release file");
    file.set_permissions(std::fs::Permissions::from_mode(0o600))
        .expect("an owner-only release file");
    file.write_all(contents.as_bytes())
        .expect("write the release file");
    file.sync_all().expect("a durable release file");
}

/// The request's pointer code in the admitted egg's readout.
pub(super) fn pointer(readout: &AdmittedReadout) -> ExactInterval {
    bits(&readout.pointers[RelationKind::Request.index()].code)
}

pub(super) fn admitted(egg: &AdmittedEgg) -> Box<AdmittedReadout> {
    match Family::readout(egg) {
        Readout::Admitted(readout) => readout,
        _ => panic!("the admitted egg's readout"),
    }
}

/// **F0's acceptance run** (module header).
#[allow(clippy::too_many_lines)]
pub fn acceptance(curated_path: &str, flat_path: &str, releases_path: &str) {
    let clock = Instant::now();
    let grain = super::GRAIN;
    let chart = SectionChart::curated();
    let cut = read_curated(curated_path, &chart);
    let (flat_bytes, flat_count, flat_held) = read_cut(flat_path);
    let bytes_of: Vec<usize> = cut
        .codes
        .iter()
        .copied()
        .filter(|&code| chart.section(code).is_none())
        .collect();
    assert!(
        bytes_of.len() == flat_count
            && bytes_of
                .iter()
                .zip(&flat_bytes)
                .all(|(&a, &b)| a == usize::from(b)),
        "the flat cut is the curated cut's bytes"
    );
    let development = cut.held.start;
    let cells = cut.codes.len();
    let population = usize::try_from(cut.population).expect("the aperture fits a machine word");
    assert_eq!(
        flat_held.start,
        bytes_of.len()
            - cut.codes[development..]
                .iter()
                .filter(|&&code| chart.section(code).is_none())
                .count(),
        "identical held-out cells"
    );
    let relations = read_incidence(curated_path);
    // The aeons (module header): each conversation change's letter tick and the aeon it enters,
    // and for the flat twin the position of the part's first byte (a later mark at one position
    // is the one entered). A cut written without its aeons reads as one aeon.
    let aeons_file = curated_path.strip_suffix(".bin").map_or_else(
        || format!("{curated_path}.aeons.bin"),
        |stem| format!("{stem}.aeons.bin"),
    );
    let aeons: BTreeMap<usize, u64> = if std::path::Path::new(&aeons_file).exists() {
        read_aeons(curated_path, &cut.codes, &chart)
            .into_iter()
            .collect()
    } else {
        BTreeMap::new()
    };
    let mut flat_aeons: BTreeMap<usize, u64> = BTreeMap::new();
    let mut bytes_before = 0usize;
    for (t, &code) in cut.codes.iter().enumerate() {
        if let Some(&aeon) = aeons.get(&t) {
            flat_aeons.insert(bytes_before, aeon);
        }
        if chart.section(code).is_none() {
            bytes_before += 1;
        }
    }
    let mut open = None;
    let open_before: Vec<Option<usize>> = cut
        .codes
        .iter()
        .map(|&code| {
            let before = open;
            if let Some(section) = chart.section(code) {
                open = Some(section.channel);
            }
            before
        })
        .collect();
    let with_releases = releases_path != "none";
    println!(
        "hnn_population f0-acceptance: F0's acceptance run, the predictor on unseen families (the record's pins; #63, #73, #148)"
    );
    println!(
        "  the aeons: {} conversation changes entered{}",
        aeons.len(),
        if aeons.is_empty() {
            " (the cut carries no aeons: one aeon)"
        } else {
            ""
        }
    );
    println!(
        "0. the passage: {cells} curated cells (|A| = {}), the first {development} the choosing families; {flat_count} flat cells; n* = {population}, L_R = {grain}",
        chart.alphabet(),
    );
    println!(
        "  the margin m = {}; the standing budget {BUDGET} bytes a cell; the passage budget {PASSAGE_MS} ms and {RESIDENT} bytes resident",
        MARGIN.map_or(
            "not yet pinned (the dry runs read it)".to_string(),
            |m| format!("{m} bits")
        )
    );

    // 1. The partition on the choosing cells alone; the egg at F0's byte depth; the charges.
    let (partition, receipt) =
        learn_hazard_partition(chart, &cut.codes[..development]).expect("the learned partition");
    let classes_only = HazardPartition::learned(
        partition.classes().to_vec(),
        std::collections::BTreeMap::new(),
    )
    .expect("the learned classes");
    let other = if receipt.shares_adopted {
        ("learned classes without shares", classes_only)
    } else {
        (
            "learned classes with the refused shares",
            receipt.shared.clone(),
        )
    };
    let comparisons = vec![
        ("declared".to_string(), HazardPartition::declared()),
        (other.0.to_string(), other.1),
    ];
    let mut egg = admitted_egg_at(
        chart,
        cut.population,
        grain,
        partition,
        relations.clone(),
        &comparisons,
        0,
        F0_BYTE_DEPTH,
    )
    .expect("the admitted egg");
    let swept: u64 = PROBED.iter().map(|&count| ceil_log2(count)).sum();
    let decided = ceil_log2(DECISIONS.iter().product());
    let egg_charge = sum(&point(swept + decided), &receipt.description);
    let flat_charge = ceil_log2(FLAT_SWEEP);
    println!(
        "1. the egg: the admitted receivers over the boundary egg on the typed tree at D = {F0_BYTE_DEPTH} ticks, the learned hazard partition (its description {}); charged the sweep's {swept} bits, F0's decisions' {decided} and the description: {}; the flat tree (D = {FLAT_DEPTH}) charged {flat_charge} bits",
        reading_of(&receipt.description, grain),
        reading_of(&egg_charge, grain)
    );
    let (eligible, selected) = select(
        &cut.codes,
        &relations,
        development,
        population,
        chart,
        RELEASE_SEED,
        RELEASES,
    );
    println!(
        "  the declared relations: {} in all; requests with both parts in the validation role and room in the aperture {eligible}; releases {} (cap {RELEASE_CAP} bytes){}; setup {} ms",
        relations.len(),
        selected.len(),
        if with_releases {
            ""
        } else {
            ", not released (none)"
        },
        clock.elapsed().as_millis()
    );
    println!();

    // 2. The choosing families, then 3. the validation families, once each.
    let at_letter: BTreeMap<usize, usize> = selected
        .iter()
        .enumerate()
        .map(|(order, chosen)| (chosen.letter, order))
        .collect();
    let mut egg_releases: Vec<Option<EggRelease>> = (0..selected.len()).map(|_| None).collect();
    let mut codes: Vec<Code> = Vec::new();
    let mut reading_ms = [0u128; 2];
    let mut at_join = None;
    for (role, range) in [(0usize, 0..development), (1, development..cells)] {
        let name = ["the choosing families", "the validation families"][role];
        let passage = Instant::now();
        let mut releasing = 0u128;
        let mut code = Code::new();
        for t in range {
            let cell = cut.codes[t];
            if let Some(&aeon) = aeons.get(&t) {
                egg.enter_aeon(aeon).expect("an aeon at its letter");
            }
            if chart.section(cell).is_some() {
                code.letters += 1;
                let charged = if t != development && open_before[t] == Some(AGENT) {
                    let face = Family::face(&egg).expect("the egg's face");
                    let mass: Rat = face[chart.bytes()..].iter().sum();
                    let charged = Family::receive(&mut egg, cell).expect("a letter");
                    assert_eq!(
                        face[cell], charged,
                        "the stop's face is the face the egg charges"
                    );
                    code.stops.face(&mass).expect("a positive stop mass");
                    code.stop_cells += 1;
                    charged
                } else {
                    Family::receive(&mut egg, cell).expect("a letter")
                };
                code.whole.face(&charged).expect("a positive face");
            } else {
                let face = Family::receive(&mut egg, cell).expect("a byte");
                let channel = open_before[t].expect("a byte lies in an open part");
                code.bytes[channel].face(&face).expect("a positive face");
                code.whole.face(&face).expect("a positive face");
                code.byte_cells[channel] += 1;
            }
            if with_releases && let Some(&order) = at_letter.get(&t) {
                let release = release_egg(&egg, chart, population, t + 1, selected[order].key);
                releasing += release.warm_ms;
                egg_releases[order] = Some(release);
            }
            if (t + 1) % GUARD_EVERY == 0
                && let Err(why) = guard(passage.elapsed().as_millis() - releasing)
            {
                stopped(name, why);
            }
        }
        reading_ms[role] = passage.elapsed().as_millis() - releasing;
        if let Err(why) = guard(reading_ms[role]) {
            stopped(name, why);
        }
        println!(
            "{}. {name} ({} cells): the egg's reading {} ms{}; resident set (now, peak) {:?} bytes",
            role + 2,
            code.byte_count() + code.letters,
            reading_ms[role],
            if role == 1 && with_releases {
                format!(", the releases {releasing} ms apart")
            } else {
                String::new()
            },
            resident_set()
        );
        for (c, channel) in CHANNELS.iter().enumerate() {
            println!(
                "    {channel} bytes ({}): {}",
                code.byte_cells[c],
                reading_of(&joined([&code.bytes[c]]), grain)
            );
        }
        println!(
            "    response stops ({}): {}",
            code.stop_cells,
            reading_of(&joined([&code.stops]), grain)
        );
        println!(
            "    bytes {}; bytes and stops {}",
            reading_of(&code.bytes_only(), grain),
            enclosure(&code.total(), grain)
        );
        if role == 0 {
            at_join = Some(admitted(&egg));
        }
        codes.push(code);
    }
    let pointer_code = minus(
        &pointer(&admitted(&egg)),
        &pointer(at_join.as_ref().expect("the readout at the join")),
    );
    let standing = Standing::of(&egg);
    println!(
        "  the standing after the passage ({cells} cells): whole {} bytes ({} a cell, remainder {}); the readings beside the state {} bytes ({} byte-tree nodes; {} a cell, remainder {}); without them {} bytes ({} a cell, remainder {}); resident set (now, peak) {:?} bytes",
        standing.whole,
        standing.whole / cells as u64,
        standing.whole % cells as u64,
        standing.readings(),
        standing.nodes,
        standing.readings() / cells as u64,
        standing.readings() % cells as u64,
        standing.bare(),
        standing.bare() / cells as u64,
        standing.bare() % cells as u64,
        resident_set()
    );
    drop(egg);
    println!();

    // 4. The flat tree over the flat twin, once, with its releases at the same bytes.
    let flat_clock = Instant::now();
    let mut flat_tree = TreeFamily::new(
        declaration(
            256,
            FLAT_DEPTH,
            cut.population,
            grain,
            LetterFamily::cells(),
        ),
        0,
    )
    .expect("the flat tree");
    let logged: Vec<Vec<u8>> = selected
        .iter()
        .map(|chosen| part_bytes(&cut.codes, chosen.letter, chart))
        .collect();
    let at_byte: BTreeMap<usize, usize> = selected
        .iter()
        .enumerate()
        .map(|(order, chosen)| {
            (
                cut.codes[..chosen.letter]
                    .iter()
                    .filter(|&&code| chart.section(code).is_none())
                    .count(),
                order,
            )
        })
        .collect();
    let mut flat_releases: Vec<Option<(Vec<u8>, u128)>> =
        (0..selected.len()).map(|_| None).collect();
    let mut flat = [PassageCode::new(), PassageCode::new()];
    let mut flat_releasing = 0u128;
    for (position, &byte) in flat_bytes.iter().enumerate() {
        if let Some(&aeon) = flat_aeons.get(&position) {
            flat_tree
                .enter_aeon(aeon)
                .expect("a cell-only tree enters at once");
        }
        if with_releases && let Some(&order) = at_byte.get(&position) {
            // The egg's cap at this response (its aperture's room), never the logged reply's length.
            let cap = RELEASE_CAP.min(population - selected[order].letter - 2);
            let released = release_flat(&flat_tree, cap, selected[order].key);
            flat_releasing += released.1;
            flat_releases[order] = Some(released);
        }
        let face = flat_tree
            .receive(usize::from(byte))
            .expect("a byte of the flat chart");
        flat[usize::from(position >= flat_held.start)]
            .face(&face)
            .expect("a positive face");
        if (position + 1) % GUARD_EVERY == 0
            && let Err(why) = guard(flat_clock.elapsed().as_millis() - flat_releasing)
        {
            stopped("the flat tree", why);
        }
    }
    let flat_standing = flat_tree.encode_checkpoint().len() as u64;
    drop(flat_tree);
    println!(
        "4. the flat tree at D = {FLAT_DEPTH} over the flat twin: {} ms{}; its standing {flat_standing} bytes after {flat_count} cells ({} a cell, remainder {}); resident set (now, peak) {:?} bytes",
        flat_clock.elapsed().as_millis() - flat_releasing,
        if with_releases {
            format!(", its releases {flat_releasing} ms apart")
        } else {
            String::new()
        },
        flat_standing / flat_count as u64,
        flat_standing % flat_count as u64,
        resident_set()
    );
    let flat_choosing = joined([&flat[0]]);
    let flat_validation = joined([&flat[1]]);
    println!(
        "  the flat tree's choosing bytes ({}): {}",
        flat_held.start,
        reading_of(&flat_choosing, grain)
    );
    println!(
        "  the flat tree's validation bytes ({}): {}",
        flat_count - flat_held.start,
        enclosure(&flat_validation, grain)
    );
    println!();

    // 5. The receipt.
    let (choosing, validation) = (&codes[0], &codes[1]);
    let bytes = validation.byte_count();
    assert_eq!(
        bytes,
        (flat_count - flat_held.start) as u64,
        "the egg and the flat tree read the same validation bytes"
    );
    println!("5. the receipt (the validation families):");
    let uncharged = minus(&validation.total(), &flat_validation);
    println!(
        "  the uncharged conditional difference V_egg − V_flat (bytes and stops against the flat tree's bytes; the margin's reading): {}",
        enclosure(&uncharged, grain)
    );
    let egg_charged = sum(&validation.total(), &egg_charge);
    let flat_charged = sum(&flat_validation, &point(flat_charge));
    difference_line(
        "the acceptance's comparison: the egg's bytes and stops, charged, against the flat tree's bytes, charged",
        &egg_charged,
        &flat_charged,
        bytes,
    );
    let charged = minus(&egg_charged, &flat_charged);
    let code_clause = MARGIN.map(|m| {
        let bound = -Rat::from_integer(BigInt::from(m));
        (charged.upper < bound, charged.lower >= bound)
    });
    println!(
        "      against the margin: {}",
        match (MARGIN, code_clause) {
            (Some(m), Some((true, _))) => format!(
                "strictly below the flat tree's by more than m = {m} bits: the code clause HOLDS"
            ),
            (Some(m), Some((false, true))) => format!(
                "not below the flat tree's by more than m = {m} bits: the code clause FAILS"
            ),
            (Some(m), _) => format!(
                "undecided against m = {m} bits (the enclosure straddles −m): the code clause is not decided, so it FAILS"
            ),
            (None, _) => "the margin is not yet pinned".to_string(),
        }
    );
    for (c, channel) in CHANNELS.iter().enumerate() {
        if validation.byte_cells[c] > 0 {
            println!(
                "    {channel} bytes ({}), uncharged: {}",
                validation.byte_cells[c],
                reading_of(&joined([&validation.bytes[c]]), grain)
            );
        }
    }
    println!(
        "    the response stops ({}), coded by the egg alone: {}",
        validation.stop_cells,
        reading_of(&joined([&validation.stops]), grain)
    );
    difference_line(
        "beside: the egg's bytes alone, charged, against the flat tree's, charged",
        &sum(&validation.bytes_only(), &egg_charge),
        &flat_charged,
        bytes,
    );
    let whole = sum(
        &sum(&joined([&validation.whole]), &pointer_code),
        &egg_charge,
    );
    println!(
        "    beside: the whole curated stream on the validation families ({} cells: bytes, {} section letters, the request's pointer {}), charged: {}",
        bytes + validation.letters,
        validation.letters,
        reading_of(&pointer_code, grain),
        reading_of(&whole, grain)
    );
    difference_line(
        "beside: the whole curated stream against the flat stream, charged",
        &whole,
        &flat_charged,
        bytes,
    );
    difference_line(
        "beside: the choosing families' bytes and stops against the flat tree's bytes, uncharged",
        &choosing.total(),
        &flat_choosing,
        choosing.byte_count(),
    );
    let within_standing = standing.whole <= BUDGET * cells as u64;
    println!(
        "  the standing against the budget of {BUDGET} bytes a cell: whole {} ({} a cell); without the readings {} ({} a cell); the flat tree's {} a cell",
        if within_standing { "within" } else { "past" },
        standing.whole / cells as u64,
        if standing.bare() <= BUDGET * cells as u64 {
            "within"
        } else {
            "past"
        },
        standing.bare() / cells as u64,
        flat_standing / flat_count as u64
    );
    let peak = resident_set().map_or(0, |(_, peak)| peak);
    let within_passage = reading_ms[1] <= PASSAGE_MS && peak <= RESIDENT;
    println!(
        "  the passage budget: the validation reading {} ms against {PASSAGE_MS}, the peak resident set {peak} bytes against {RESIDENT}: {}",
        reading_ms[1],
        if within_passage { "within" } else { "past" }
    );
    match code_clause {
        Some((holds, _)) => println!(
            "  acceptance (the code strictly below the flat tree's by more than m, within the standing and passage budgets): the code {}; the standing {}; the passage {}; {}",
            if holds { "holds" } else { "fails" },
            if within_standing { "within" } else { "past" },
            if within_passage { "within" } else { "past" },
            if holds && within_standing && within_passage {
                "PASSES"
            } else {
                "FAILS: the byte population stays a compression result"
            }
        ),
        None => println!("  acceptance: not read (the margin is not yet pinned)"),
    }

    // 6. The releases, deciding nothing: counts and times here, the text owner-only.
    if with_releases {
        println!();
        println!("6. the releases (deciding nothing; the text owner-only in the release file):");
        let mut statuses: BTreeMap<String, usize> = BTreeMap::new();
        let mut cases = Vec::with_capacity(selected.len());
        for (order, chosen) in selected.iter().enumerate() {
            let egg_release = egg_releases[order].as_ref().expect("the egg released here");
            let (flat_release, flat_ms) = flat_releases[order]
                .as_ref()
                .expect("the flat tree released here");
            let reply = &logged[order];
            *statuses.entry(egg_release.status.clone()).or_default() += 1;
            println!(
                "  release {order}: {}; {} bytes over {} cells; branch {} ms, warm {} ms; the logged reply {} bytes (UTF-8 {}); the flat tree {} bytes (UTF-8 {}) in {flat_ms} ms",
                egg_release.status,
                egg_release.bytes.len(),
                egg_release.cells,
                egg_release.branch_ms,
                egg_release.warm_ms,
                reply.len(),
                std::str::from_utf8(reply).is_ok(),
                flat_release.len(),
                std::str::from_utf8(flat_release).is_ok()
            );
            let athena = if egg_release.released {
                json_text(&egg_release.bytes)
            } else {
                json_text(format!("[typed refusal: {}]", egg_release.status).as_bytes())
            };
            let request = part_bytes(&cut.codes, chosen.target, chart);
            cases.push(format!(
                "{{\"order\":{order},\"validation_tick\":{},\"request\":{},\"responses\":{{\"athena\":{{\"text\":{athena},\"valid_utf8\":{},\"bytes\":{},\"emitted\":{}}},\"logged\":{{\"text\":{},\"valid_utf8\":{},\"bytes\":{}}},\"flat\":{{\"text\":{},\"valid_utf8\":{},\"bytes\":{}}}}}}}",
                chosen.letter - development,
                json_text(&request),
                std::str::from_utf8(&egg_release.bytes).is_ok(),
                egg_release.bytes.len(),
                json_text(&egg_release.bytes),
                json_text(reply),
                std::str::from_utf8(reply).is_ok(),
                reply.len(),
                json_text(flat_release),
                std::str::from_utf8(flat_release).is_ok(),
                flat_release.len()
            ));
        }
        let warm: Vec<u128> = egg_releases
            .iter()
            .flatten()
            .map(|release| release.warm_ms)
            .collect();
        println!(
            "  the egg's statuses {statuses:?}; warm ms: the longest {}, in all {}",
            warm.iter().max().copied().unwrap_or(0),
            warm.iter().sum::<u128>()
        );
        let excluded = if reserve_read() {
            "null".to_string()
        } else {
            format!("\"{RESERVE_SHA256}\"")
        };
        write_private(
            releases_path,
            &format!(
                "{{\"schema\":\"holonics.f0-acceptance-releases.v1\",\"cap\":{RELEASE_CAP},\"reserve_excluded\":{excluded},\"cases\":[{}]}}\n",
                cases.join(",")
            ),
        );
        println!(
            "  written: the owner-only release file ({} cases)",
            cases.len()
        );
    }
    println!(
        "wall time in all: {} ms; resident set (now, peak) {:?} bytes",
        clock.elapsed().as_millis(),
        resident_set()
    );
}
