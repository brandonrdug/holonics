//! **The curated conversation source read as typed letters, against the flat stream of the same
//! bytes** (campaign 5's input under HNN_FORMULA's source contract; #73, #148): the notebook's
//! development receipt of `holonics::compression::landmark::context` on the curated source, a
//! committed command run once in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_curated -- curated .local/cuts/curated-cut.bin .local/cuts/curated-flat-cut.bin
//! ```
//!
//! [definition; agent-inferred] **The source** (`curated_source.py`, an exterior codec step): the
//! exposure's development partition, each visible part's UTF-8 bytes on its channel's port (human,
//! agent, tool; the harness holds references only), and before each part one **section letter**, a
//! coded cell of the declared chart `|A| = 256 + 12`: `open` (the occurrence opens its
//! conversation's aeon), `switch` (it lies in another conversation than the previous emitted
//! occurrence), `part` (it lies in the previous emitted occurrence's declared turn, the provider's
//! `turn_id`, or is a further part of the same record) or `turn` (a new declared turn, or the
//! record boundary where no `turn_id` is declared: the next epoch of the same aeon), each typed by
//! the channel the part opens on. So the channel is never supplied: it is read from the coded
//! past, and every section costs the bits of its letter. The flat cut is the same bytes with every
//! letter removed, its held-out cells the curated held-out cells' bytes: the two are measured on
//! identical cells.
//!
//! [definition; agent-inferred] **The reader** (`curated`): each tick's bundle is its cell with two
//! declared slots, its **channel** (3 letters) and its **section** letter (the kind of the letter
//! that opened its part, 4 letters), `LetterFamily::new([3, 4])`, so each cell's address carries
//! its channel and section letters (`letter_address` over `Letter::Bundle`). Three trees, each the
//! `½` stop prior, the KT node (`Capacity::Unbounded`, the HNN's declared receiving tree), stored
//! where paths part, at the declared population `n*` of the curated manifest (`2^20`) and campaign
//! 1's receiver grain `L_R`:
//! - the **flat** tree: the cell-only tree over the flat bytes (`|A| = 256`);
//! - the **curated cell** tree: the cell-only tree over the curated cells, letters included;
//! - the **curated typed** tree: the enlarged tree over the typed bundles.
//!
//! - **0. The cut and its counts**: the cells per channel and the section letters per kind, on each
//!   population; the check that the curated cut without its letters is the flat cut, cell for cell.
//! - **1. The families**, stated before any passage: each tree's depths doubling from 6 to the
//!   deepest its carriers admit at `n*` (`Landmarks::new`), charged `⌈log₂⌉` of its length; the
//!   curated family (cells or typed) charged `⌈log₂ 2⌉ = 1` bit; the a-priori memory (each
//!   branch at most `2 n B` stored nodes and `n D` label letters) of the three sweeps run together,
//!   checked against Brandon's 20 GB cap and the memory the kernel reports available.
//! - **2. The sweeps** on the development cells, the three trees run together on the host (each
//!   reads its own immutable stream and writes its own sweep), each until its code does not fall
//!   strictly (`DepthSweep::{decreasing, of}`) or a passage passes four minutes: every depth's code in
//!   all and per slot (human, agent, tool, section letters).
//! - **3. The choices**: each tree's depth; the curated family, typed only when its charged code lies
//!   below the cell tree's by disjoint exact enclosures.
//! - **4. The development readings**: per slot, the flat tree against the chosen curated tree on
//!   identical cells (uncharged), the section letters' price, the whole codes charged (the curated
//!   stream carries its sections, the flat one does not), and each tree against online order-0 and
//!   PPM-2 on its own stream (`context::baseline`).
//! - **5. One held-out passage** of the flat tree and of the chosen curated tree at their chosen
//!   depths over the whole cut, every cell scored at the standing before its own deposit, beside the
//!   baselines re-read: the same readings, choosing nothing.
//!
//! [definition] **Privacy**: the cut is private (`.local/cuts/`); this reads codes and prints counts,
//! bits and hashes' scope only, never any cell's content. Every reading is exact (`exterior`): bits
//! as enclosures with exact endpoints read at the grain, `n + k/L_R + ε`, orderings by disjoint
//! exact enclosures, wall times in integer milliseconds.

#[path = "exterior.rs"]
mod exterior;

use std::time::Instant;

use holonics::compression::cost::ceil_log2;
use holonics::compression::landmark::context::baseline::{Baselines, PPM_ORDER};
use holonics::compression::landmark::context::{
    Capacity, LandmarkDeclaration, Landmarks, Letter, LetterFamily, PassageCode, SectionChart,
    SectionSlots, Sections, StopPrior, Widths, cell_letters, letter_address, odometer_digits,
};
use holonics::hnn::reference::DepthSweep;
use holonics::hnn::{Field, FieldDeclaration};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::{ExactInterval, interval_sum};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

use exterior::{
    against, difference, enclosure, exact, manifest_number, per, read_curated, read_cut, reading_of,
};

/// The exterior chart's bytes; the section letters are coded after them.
const BYTES: usize = 256;

/// The ports that carry cells, in the letters' order (the harness carries references only).
const CHANNELS: [&str; 3] = ["human", "agent", "tool"];

/// The section letters' kinds, in the letters' order.
const KINDS: [&str; 4] = ["open", "switch", "turn", "part"];

/// The readings' slots: a cell's channel, or a section letter.
const SLOTS: [&str; 4] = ["human", "agent", "tool", "section letters"];
const SECTION: usize = 3;
const BYTE_SLOTS: [usize; 3] = [0, 1, 2];
const ALL_SLOTS: [usize; 4] = [0, 1, 2, 3];

/// **The declared doubling family** (Decision 37's, stated before any passage): `D = 6, 12, 24, 48`,
/// then the deepest depth the carriers admit at the population.
const DOUBLING: [usize; 4] = [6, 12, 24, 48];

/// **A passage's budget**, stated in advance: a passage past four minutes stops its sweep there.
const PASSAGE_STOP_MS: u128 = 240_000;

/// Brandon's cap on resident memory: 20 GB (`20 · 10^9` bytes).
const CAP: u128 = 20_000_000_000;

/// The bytes a stored node occupies with its child-table entry, and a label letter
/// (`compression::landmark::context`, "The arena": 96 in the flat vectors, 16 an entry, 4 a letter).
const NODE_BYTES: u128 = 96 + 16;
const LETTER_BYTES: u128 = 4;

// -------------------------------------------------------------------------------------------
// the exterior boundary: the curated cut

/// **The ticks' channels and typed letters, read from the coded past** (the library's typed
/// address, `compression::landmark::context::sections`): each letter opens its part on its channel;
/// each byte lies on the channel and section of the last letter before it. The cut opens at a
/// letter (the codec's pin), so no cell precedes its port.
fn ticks(codes: &[usize], chart: SectionChart) -> (Vec<usize>, Vec<Letter>) {
    let mut sections =
        Sections::new(chart, SectionSlots::ChannelKind).expect("the channel and section slots");
    let mut channels = Vec::with_capacity(codes.len());
    let mut typed = Vec::with_capacity(codes.len());
    for &code in codes {
        typed.push(
            sections
                .read(code)
                .expect("the cut opens at a section letter"),
        );
        channels.push(sections.open().expect("an open section").channel);
    }
    (channels, typed)
}

// -------------------------------------------------------------------------------------------
// the streams and their passages

/// **A stream the trees read**: its cells, each tick's letter, each cell's reading slot, the
/// exterior chart and the development cells' count (the held-out cells close it).
struct Stream {
    cells: Vec<usize>,
    letters: Vec<Letter>,
    slots: Vec<usize>,
    alphabet: usize,
    development: usize,
}

/// **One passage of a tree over a stream's first `end` cells**: the faces' products per population
/// (before and from `development`) and slot, the certified residuals summed, the stored nodes and
/// label letters, the widths, the rule and the chart, and wall time.
struct Pass {
    depth: usize,
    codes: [[PassageCode; 4]; 2],
    residuals: [Rat; 2],
    largest: Rat,
    nodes: usize,
    held: usize,
    widths: Widths,
    rule: Rat,
    rebases: u64,
    drift: Rat,
    wall: u128,
}

fn pass(stream: &Stream, end: usize, declaration: &LandmarkDeclaration) -> Pass {
    let clock = Instant::now();
    let mut tree = Landmarks::new(declaration.clone()).expect("a declared tree");
    let mut codes = [[PassageCode::new(); 4]; 2];
    let mut residuals = [Rat::zero(), Rat::zero()];
    let mut largest = Rat::zero();
    for position in 0..end {
        let reading = tree
            .receive(
                &letter_address(&stream.letters, position, declaration.depth),
                stream.cells[position],
            )
            .expect("a cell within the declaration");
        let part = usize::from(position >= stream.development);
        codes[part][stream.slots[position]]
            .face(&reading.executed)
            .expect("a positive face");
        residuals[part] += &reading.residual;
        if reading.residual > largest {
            largest = reading.residual;
        }
    }
    let chart = tree.chart();
    Pass {
        depth: declaration.depth,
        codes,
        residuals,
        largest,
        nodes: tree.nodes(),
        held: tree.held(),
        widths: tree.widths(),
        rule: tree.face_rule(),
        rebases: chart.rebases,
        drift: chart.drift,
        wall: clock.elapsed().as_millis(),
    }
}

/// The product of a population's faces over the named slots.
fn joined(codes: &[PassageCode; 4], slots: &[usize]) -> PassageCode {
    let mut all = PassageCode::new();
    for &slot in slots {
        all.join(&codes[slot]);
    }
    all
}

fn bits(code: &PassageCode) -> ExactInterval {
    code.bits().expect("an enclosure")
}

/// **The deepest depth the carriers admit** at a declaration's population (`Landmarks::new`
/// refuses past it).
fn deepest_admitted(declared: &LandmarkDeclaration) -> usize {
    let mut depth = 1;
    while Landmarks::new(LandmarkDeclaration {
        depth: depth + 1,
        ..declared.clone()
    })
    .is_ok()
    {
        depth += 1;
    }
    depth
}

/// **A passage's a-priori memory** over `cells` cells at `depth`: each branch at most `2 n B`
/// stored nodes and `n D_b` label letters, at the bytes each occupies, doubled for the vectors'
/// and the table's growth.
fn projected(cells: usize, declared: &LandmarkDeclaration, depth: usize) -> u128 {
    let at = LandmarkDeclaration {
        depth,
        ..declared.clone()
    };
    let n = cells as u128;
    let digits = u128::from(odometer_digits(at.alphabet));
    let branches = at.branch_depths();
    let nodes = branches.len() as u128 * 2 * n * digits;
    let letters: u128 = branches.iter().map(|&d| n * d as u128).sum();
    2 * (nodes * NODE_BYTES + letters * LETTER_BYTES)
}

/// **A tree's declared doubling family**: `D = 6, 12, 24, 48` below its carriers' deepest, then
/// the deepest.
fn family_of(declared: &LandmarkDeclaration) -> Vec<usize> {
    let deepest = deepest_admitted(declared);
    DOUBLING
        .iter()
        .copied()
        .filter(|&depth| depth < deepest)
        .chain([deepest])
        .collect()
}

/// **One tree's depth sweep on the development cells**: the family's depths in order while the
/// code falls strictly (`DepthSweep`'s rule) and no passage passed the budget.
struct Sweep {
    family: Vec<usize>,
    passes: Vec<Pass>,
    choice: DepthSweep,
    stopped: Option<String>,
}

fn sweep(stream: &Stream, declared: &LandmarkDeclaration) -> Sweep {
    let family = family_of(declared);
    let mut passes: Vec<Pass> = Vec::new();
    let mut tried: Vec<(usize, ExactInterval)> = Vec::new();
    let mut stopped = None;
    for &depth in &family {
        if let Some(last) = passes.last() {
            if !DepthSweep::decreasing(&tried) {
                break;
            }
            if last.wall > PASSAGE_STOP_MS {
                stopped = Some(format!(
                    "the passage at D = {} took {} ms, past {PASSAGE_STOP_MS}",
                    last.depth, last.wall
                ));
                break;
            }
        }
        let run = pass(
            stream,
            stream.development,
            &LandmarkDeclaration {
                depth,
                ..declared.clone()
            },
        );
        tried.push((depth, bits(&joined(&run.codes[0], &ALL_SLOTS))));
        passes.push(run);
    }
    Sweep {
        family,
        passes,
        choice: DepthSweep::of(tried).expect("at least one depth"),
        stopped,
    }
}

impl Sweep {
    fn chosen(&self) -> &Pass {
        self.passes
            .iter()
            .find(|pass| pass.depth == self.choice.chosen)
            .expect("the chosen depth was run")
    }

    fn charge(&self) -> u64 {
        ceil_log2(&BigUint::from(self.family.len()))
    }
}

/// **The online baselines over a stream** (order-0 and order-1 KT, PPM-2 escape C), each cell's
/// face per population and slot: `[coder][population][slot]`.
fn baselines(stream: &Stream) -> ([[[PassageCode; 4]; 2]; 3], u128) {
    let clock = Instant::now();
    let mut coders = Baselines::new(stream.alphabet).expect("the baselines");
    let mut codes = [[[PassageCode::new(); 4]; 2]; 3];
    for (position, &class) in stream.cells.iter().enumerate() {
        let faces = coders.face_cell(class).expect("a cell in the chart");
        let part = usize::from(position >= stream.development);
        let slot = stream.slots[position];
        for (coder, face) in [&faces.order_zero, &faces.order_one, &faces.ppm]
            .into_iter()
            .enumerate()
        {
            codes[coder][part][slot]
                .face(face)
                .expect("a positive face");
        }
    }
    (codes, clock.elapsed().as_millis())
}

// -------------------------------------------------------------------------------------------
// presentation

fn charged(bits: &ExactInterval, description: u64) -> ExactInterval {
    interval_sum(
        bits,
        &ExactInterval::point(Rat::from_integer(BigInt::from(description))),
    )
    .expect("an enclosure")
}

/// **A strict ordering**, `a` against `b`: decided by disjoint exact enclosures, with the exact
/// difference in bits and a cell; or undecided, with the overlap.
fn ordering(label: &str, a: &ExactInterval, b: &ExactInterval, cells: u64, grain: u64) {
    println!("  {label}: {}", against(a, b));
    if a.upper < b.lower || a.lower > b.upper {
        let delta = ExactInterval {
            lower: &a.lower - &b.upper,
            upper: &a.upper - &b.lower,
        };
        println!("    difference {}", difference(a, b, grain));
        println!("    a cell: {}", per(&delta, cells, grain));
    } else {
        let lower = if a.lower > b.lower {
            &a.lower
        } else {
            &b.lower
        };
        let upper = if a.upper < b.upper {
            &a.upper
        } else {
            &b.upper
        };
        println!("    overlap [{}, {}] bits", exact(lower), exact(upper));
    }
}

fn widths(widths: &Widths) -> String {
    format!(
        "B = {}, M_p = {}, W = {}, C = {}",
        widths.digits, widths.face, widths.carrier, widths.certificate
    )
}

/// The dyadic ceiling of a printed upper bound on `2^(−48)`.
fn dyadic_ceiling(value: &Rat) -> Rat {
    let scale: BigInt = BigInt::from(1) << 48usize;
    let scaled = value * Rat::from_integer(scale.clone());
    Rat::new(scaled.ceil().to_integer(), scale)
}

/// A passage's line on a population: its code in all (exact, at the grain) and a cell, per slot
/// at the grain and a cell, its certified residual, and its stored parts and wall time.
fn pass_lines(pass: &Pass, part: usize, counts: &[u64; 4], grain: u64) {
    let all = bits(&joined(&pass.codes[part], &ALL_SLOTS));
    let cells: u64 = counts.iter().sum();
    println!(
        "  D = {} ({}): {}; a cell {}",
        pass.depth,
        widths(&pass.widths),
        enclosure(&all, grain),
        per(&all, cells, grain)
    );
    for (slot, name) in SLOTS.iter().enumerate() {
        if counts[slot] == 0 {
            println!("    {name}: no cells");
            continue;
        }
        let code = bits(&pass.codes[part][slot]);
        println!(
            "    {name} ({} cells): {}; a cell {}",
            counts[slot],
            reading_of(&code, grain),
            per(&code, counts[slot], grain)
        );
    }
    println!(
        "    certified residuals summed ≤ {} bits; the largest a cell ≤ {} bits, {} the rule ≤ {}; {} rebases, the largest drift ≤ {} bits; {} nodes stored, {} label letters; {} ms",
        exact(&dyadic_ceiling(&pass.residuals[part])),
        exact(&dyadic_ceiling(&pass.largest)),
        if pass.largest <= pass.rule {
            "within"
        } else {
            "ABOVE"
        },
        exact(&dyadic_ceiling(&pass.rule)),
        pass.rebases,
        exact(&dyadic_ceiling(&pass.drift)),
        pass.nodes,
        pass.held,
        pass.wall
    );
}

/// Each slot's cells on each population.
fn slot_counts(stream: &Stream) -> [[u64; 4]; 2] {
    let mut counts = [[0u64; 4]; 2];
    for (position, &slot) in stream.slots.iter().enumerate() {
        counts[usize::from(position >= stream.development)][slot] += 1;
    }
    counts
}

const BASELINE_NAMES: [&str; 3] = [
    "online order-0 KT",
    "online order-1 KT",
    "PPM order 2, escape C",
];

/// **The readings on one population**: the flat tree against the curated tree on identical cells
/// per channel and in all (uncharged), the section letters' price, the whole codes charged, and each
/// tree against order-0 and PPM-2 on its own stream, per slot and in all.
#[allow(clippy::too_many_arguments)]
fn readings(
    part: usize,
    flat: &Pass,
    flat_charge: u64,
    curated: &Pass,
    curated_charge: u64,
    flat_baselines: &[[[PassageCode; 4]; 2]; 3],
    curated_baselines: &[[[PassageCode; 4]; 2]; 3],
    counts: &[u64; 4],
    grain: u64,
) {
    let bytes: u64 = BYTE_SLOTS.iter().map(|&slot| counts[slot]).sum();
    println!(
        "  a. identical cells, the curated tree (D = {}) against the flat tree (D = {}), uncharged:",
        curated.depth, flat.depth
    );
    for &slot in &BYTE_SLOTS {
        if counts[slot] == 0 {
            println!("    {}: no cells", SLOTS[slot]);
            continue;
        }
        let (a, b) = (
            bits(&curated.codes[part][slot]),
            bits(&flat.codes[part][slot]),
        );
        println!(
            "    {} ({} cells): curated {} a cell {}; flat {} a cell {}",
            SLOTS[slot],
            counts[slot],
            reading_of(&a, grain),
            per(&a, counts[slot], grain),
            reading_of(&b, grain),
            per(&b, counts[slot], grain)
        );
        ordering(
            &format!("    {} cells, curated against flat", SLOTS[slot]),
            &a,
            &b,
            counts[slot],
            grain,
        );
    }
    let curated_bytes = bits(&joined(&curated.codes[part], &BYTE_SLOTS));
    let flat_bytes = bits(&joined(&flat.codes[part], &BYTE_SLOTS));
    ordering(
        &format!("    every byte ({bytes} cells), curated against flat"),
        &curated_bytes,
        &flat_bytes,
        bytes,
        grain,
    );
    let letters = bits(&curated.codes[part][SECTION]);
    println!(
        "  b. the section letters' price in the curated tree ({} letters): {}; a letter {}",
        counts[SECTION],
        reading_of(&letters, grain),
        per(&letters, counts[SECTION], grain)
    );
    let curated_all = bits(&joined(&curated.codes[part], &ALL_SLOTS));
    let flat_all = bits(&joined(&flat.codes[part], &ALL_SLOTS));
    println!(
        "  c. the whole codes: the curated stream (its bytes and its sections) charged {curated_charge} bits, against the flat stream (its bytes alone) charged {flat_charge}:"
    );
    println!(
        "    curated {}",
        enclosure(&charged(&curated_all, curated_charge), grain)
    );
    println!(
        "    flat    {}",
        enclosure(&charged(&flat_all, flat_charge), grain)
    );
    ordering(
        "    curated with its sections against flat, charged, a byte",
        &charged(&curated_all, curated_charge),
        &charged(&flat_all, flat_charge),
        bytes,
        grain,
    );
    println!("  d. each tree against the online baselines on its own stream:");
    for (name, pass, charge, coders) in [
        ("flat", flat, flat_charge, flat_baselines),
        ("curated", curated, curated_charge, curated_baselines),
    ] {
        let tree = charged(&bits(&joined(&pass.codes[part], &ALL_SLOTS)), charge);
        for coder in [0usize, 2] {
            let base = bits(&joined(&coders[coder][part], &ALL_SLOTS));
            println!(
                "    {name} stream, {}: {}",
                BASELINE_NAMES[coder],
                reading_of(&base, grain)
            );
            for (slot, slot_name) in SLOTS.iter().enumerate() {
                if counts[slot] == 0 || (name == "flat" && slot == SECTION) {
                    continue;
                }
                let code = bits(&coders[coder][part][slot]);
                println!(
                    "      {slot_name}: {}; a cell {}",
                    reading_of(&code, grain),
                    per(&code, counts[slot], grain)
                );
            }
            ordering(
                &format!(
                    "    the {name} tree charged {charge} against {}",
                    BASELINE_NAMES[coder]
                ),
                &tree,
                &base,
                if name == "flat" {
                    bytes
                } else {
                    bytes + counts[SECTION]
                },
                grain,
            );
        }
    }
}

// -------------------------------------------------------------------------------------------
// the harness

#[allow(clippy::too_many_lines)]
fn curated_harness(curated_path: &str, flat_path: &str) {
    let setup = Instant::now();
    let chart = SectionChart::curated();
    assert_eq!(
        (chart.bytes(), chart.channels(), chart.kinds()),
        (BYTES, CHANNELS.len(), KINDS.len()),
        "the declared chart"
    );
    let cut = read_curated(curated_path, &chart);
    let (flat_bytes, flat_count, flat_held) = read_cut(flat_path);
    let declared_population = manifest_number(flat_path, "\"declared_population\":") as u64;
    assert_eq!(
        declared_population, cut.population,
        "one declared population"
    );
    let (channels, typed) = ticks(&cut.codes, chart);

    // 0. The identical cells: the curated cut without its letters is the flat cut.
    let bytes_of: Vec<usize> = cut.codes.iter().copied().filter(|&c| c < BYTES).collect();
    let identical = bytes_of.len() == flat_count
        && bytes_of
            .iter()
            .zip(&flat_bytes)
            .all(|(&a, &b)| a == usize::from(b));
    assert!(identical, "the flat cut is the curated cut's bytes");
    let flat_held_start = cut.codes[..cut.held.start]
        .iter()
        .filter(|&&c| c < BYTES)
        .count();
    assert_eq!(flat_held.start, flat_held_start, "identical held-out cells");

    let field = Field::declare(FieldDeclaration::campaign_one(cut.population))
        .expect("campaign 1's declared field at the population");
    let grain = exterior::receiver_grain(&field);
    assert_eq!(field.alphabet(), BYTES, "the flat chart is campaign 1's");

    let family = SectionSlots::ChannelKind
        .family(&chart)
        .expect("the channel and section slots");
    let slots: Vec<usize> = cut
        .codes
        .iter()
        .zip(&channels)
        .map(|(&code, &channel)| if code >= BYTES { SECTION } else { channel })
        .collect();
    let flat = Stream {
        cells: bytes_of.clone(),
        letters: cell_letters(&bytes_of),
        slots: slots.iter().copied().filter(|&s| s != SECTION).collect(),
        alphabet: BYTES,
        development: flat_held.start,
    };
    let curated_cells = Stream {
        cells: cut.codes.clone(),
        letters: cell_letters(&cut.codes),
        slots: slots.clone(),
        alphabet: cut.alphabet,
        development: cut.held.start,
    };
    let curated_typed = Stream {
        cells: cut.codes.clone(),
        letters: typed,
        slots,
        alphabet: cut.alphabet,
        development: cut.held.start,
    };
    let counts = slot_counts(&curated_typed);
    assert_eq!(
        slot_counts(&flat)
            .iter()
            .map(|c| c[..SECTION].to_vec())
            .collect::<Vec<_>>(),
        counts
            .iter()
            .map(|c| c[..SECTION].to_vec())
            .collect::<Vec<_>>(),
        "identical cells on each port"
    );
    let mut letters = [[[0u64; 3]; 4]; 2];
    for (position, &code) in cut.codes.iter().enumerate() {
        if let Some(section) = chart.section(code) {
            letters[usize::from(position >= cut.held.start)][section.kind][section.channel] += 1;
        }
    }

    println!(
        "hnn_curated curated: the curated conversation source as typed letters against the flat stream of the same bytes (campaign 5's input; #73, #148)"
    );
    println!(
        "0. the cut: {} curated cells (|A| = {} = 256 bytes + 12 section letters), {} flat cells (|A| = 256), identical bytes: {identical}; n* = {}, L_R = {grain}",
        cut.codes.len(),
        cut.alphabet,
        flat_count,
        cut.population
    );
    for (part, name) in ["development", "held out"].iter().enumerate() {
        let range = if part == 0 {
            0..cut.held.start
        } else {
            cut.held.clone()
        };
        let flat_range = if part == 0 {
            0..flat_held.start
        } else {
            flat_held.clone()
        };
        println!(
            "  {name}: curated cells {}..{}, flat cells {}..{}; human {}, agent {}, tool {}, section letters {}",
            range.start,
            range.end,
            flat_range.start,
            flat_range.end,
            counts[part][0],
            counts[part][1],
            counts[part][2],
            counts[part][SECTION]
        );
        for (kind, kind_name) in KINDS.iter().enumerate() {
            println!(
                "    {kind_name} letters: human {}, agent {}, tool {}",
                letters[part][kind][0], letters[part][kind][1], letters[part][kind][2]
            );
        }
    }
    println!();

    // 1. The declarations, their families and the memory.
    let declare = |alphabet: usize, family: LetterFamily| LandmarkDeclaration {
        alphabet,
        depth: DOUBLING[0],
        forced: 0,
        population: cut.population,
        grain,
        family,
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    };
    let trees: [(&str, &Stream, LandmarkDeclaration); 3] = [
        (
            "the flat tree",
            &flat,
            declare(BYTES, LetterFamily::cells()),
        ),
        (
            "the curated cell tree",
            &curated_cells,
            declare(cut.alphabet, LetterFamily::cells()),
        ),
        (
            "the curated typed tree",
            &curated_typed,
            declare(cut.alphabet, family.clone()),
        ),
    ];
    let family_choice = ceil_log2(&BigUint::from(2u32));
    println!(
        "1. the declarations: the ½ stop prior, the KT node (c = ∞), stored where paths part; each family doubling from 6 to its carriers' deepest at n* = {}; the curated family (cells or typed, slots [channel 3, section 4]) charged ⌈log₂ 2⌉ = {family_choice} bit",
        cut.population
    );
    let mut total_projection = 0u128;
    for (name, stream, declared) in &trees {
        let depths = family_of(declared);
        let deepest = *depths.last().expect("a family");
        let projection = projected(stream.development, declared, deepest);
        total_projection += projection;
        println!(
            "  {name}: D = {depths:?}, charged ⌈log₂ {}⌉ = {} bits; P at D = 6: {}; the a-priori memory at D = {deepest}: {projection} bytes",
            depths.len(),
            ceil_log2(&BigUint::from(depths.len())),
            LandmarkDeclaration {
                depth: 6,
                ..declared.clone()
            }
            .path_depth(),
        );
    }
    let available = exterior::available_memory();
    let together = total_projection <= CAP && available.is_none_or(|free| total_projection <= free);
    println!(
        "  the three sweeps together: {total_projection} bytes a priori, the cap {CAP}, {} bytes available: {}",
        available.map_or_else(|| "unread".to_string(), |free| free.to_string()),
        if together {
            "run together"
        } else {
            "run one after another"
        }
    );
    println!("  setup: {} ms", setup.elapsed().as_millis());
    println!();

    // 2. The sweeps on the development cells.
    let clock = Instant::now();
    let sweeps: Vec<Sweep> = if together {
        std::thread::scope(|scope| {
            let handles: Vec<_> = trees
                .iter()
                .map(|(_, stream, declared)| scope.spawn(move || sweep(stream, declared)))
                .collect();
            handles
                .into_iter()
                .map(|handle| handle.join().expect("a sweep"))
                .collect()
        })
    } else {
        trees
            .iter()
            .map(|(_, stream, declared)| sweep(stream, declared))
            .collect()
    };
    println!(
        "2. the sweeps on the development cells ({} ms in all):",
        clock.elapsed().as_millis()
    );
    for ((name, _, _), result) in trees.iter().zip(&sweeps) {
        println!("  {name}:");
        let dev = if *name == "the flat tree" {
            [counts[0][0], counts[0][1], counts[0][2], 0]
        } else {
            counts[0]
        };
        for run in &result.passes {
            pass_lines(run, 0, &dev, grain);
        }
        if let Some(reason) = &result.stopped {
            println!("    the sweep stopped: {reason}");
        }
    }
    println!();

    // 3. The choices.
    let [flat_sweep, cell_sweep, typed_sweep] = &sweeps[..] else {
        unreachable!("three sweeps")
    };
    println!("3. the choices on the development cells:");
    for ((name, _, _), result) in trees.iter().zip(&sweeps) {
        println!(
            "  {name}: D = {} of {:?} tried ({}), charged {} bits",
            result.choice.chosen,
            result
                .choice
                .tried
                .iter()
                .map(|(d, _)| *d)
                .collect::<Vec<_>>(),
            if DepthSweep::decreasing(&result.choice.tried) {
                "the code fell at every depth tried"
            } else {
                "the last depth's code did not fall below the one before"
            },
            result.charge()
        );
    }
    let cell_charged = charged(
        &bits(&joined(&cell_sweep.chosen().codes[0], &ALL_SLOTS)),
        cell_sweep.charge() + family_choice,
    );
    let typed_charged = charged(
        &bits(&joined(&typed_sweep.chosen().codes[0], &ALL_SLOTS)),
        typed_sweep.charge() + family_choice,
    );
    ordering(
        "the typed tree against the cell tree on the curated development cells, each charged its depths and the family bit",
        &typed_charged,
        &cell_charged,
        counts[0].iter().sum(),
        grain,
    );
    let typed_chosen = typed_charged.upper < cell_charged.lower;
    let (chosen_name, chosen_sweep, chosen_stream, chosen_declared) = if typed_chosen {
        (
            "the curated typed tree",
            typed_sweep,
            &curated_typed,
            &trees[2].2,
        )
    } else {
        (
            "the curated cell tree",
            cell_sweep,
            &curated_cells,
            &trees[1].2,
        )
    };
    let curated_charge = chosen_sweep.charge() + family_choice;
    let flat_charge = flat_sweep.charge();
    println!("  the curated source's tree: {chosen_name}, charged {curated_charge} bits");
    println!();

    // Baselines on each stream (development and held out; they choose nothing).
    let ((flat_base, flat_base_ms), (curated_base, curated_base_ms)) =
        rayon::join(|| baselines(&flat), || baselines(chosen_stream));
    println!(
        "  the baselines ({}, {}, {}; PPM order {PPM_ORDER}): flat {flat_base_ms} ms, curated {curated_base_ms} ms",
        BASELINE_NAMES[0], BASELINE_NAMES[1], BASELINE_NAMES[2]
    );
    println!();

    // 4. The development readings.
    println!(
        "4. the development readings ({} bytes and {} section letters), bits at L_R = {grain}:",
        counts[0][..SECTION].iter().sum::<u64>(),
        counts[0][SECTION]
    );
    readings(
        0,
        flat_sweep.chosen(),
        flat_charge,
        chosen_sweep.chosen(),
        curated_charge,
        &flat_base,
        &curated_base,
        &counts[0],
        grain,
    );
    println!();

    // 5. One held-out passage of each at its chosen depth.
    let clock = Instant::now();
    let flat_at = LandmarkDeclaration {
        depth: flat_sweep.choice.chosen,
        ..trees[0].2.clone()
    };
    let curated_at = LandmarkDeclaration {
        depth: chosen_sweep.choice.chosen,
        ..chosen_declared.clone()
    };
    let held_projection = projected(flat.cells.len(), &flat_at, flat_at.depth)
        + projected(chosen_stream.cells.len(), &curated_at, curated_at.depth);
    let available = exterior::available_memory();
    if held_projection > CAP || available.is_some_and(|free| held_projection > free) {
        println!(
            "5. the held-out passages REFUSED: {held_projection} bytes a priori against the cap {CAP} and {} available",
            available.map_or_else(|| "unread".to_string(), |free| free.to_string())
        );
        return;
    }
    let (flat_whole, curated_whole) = rayon::join(
        || pass(&flat, flat.cells.len(), &flat_at),
        || pass(chosen_stream, chosen_stream.cells.len(), &curated_at),
    );
    println!(
        "5. one held-out passage of each at its chosen depth over the whole cut, every cell scored at the standing before its own deposit ({} ms; {held_projection} bytes a priori):",
        clock.elapsed().as_millis()
    );
    println!(
        "  checks: the flat passage's development code is its sweep's: {}; the curated passage's: {}",
        bits(&joined(&flat_whole.codes[0], &ALL_SLOTS))
            == bits(&joined(&flat_sweep.chosen().codes[0], &ALL_SLOTS)),
        bits(&joined(&curated_whole.codes[0], &ALL_SLOTS))
            == bits(&joined(&chosen_sweep.chosen().codes[0], &ALL_SLOTS))
    );
    println!("  the flat tree, held out:");
    pass_lines(
        &flat_whole,
        1,
        &[counts[1][0], counts[1][1], counts[1][2], 0],
        grain,
    );
    println!("  {chosen_name}, held out:");
    pass_lines(&curated_whole, 1, &counts[1], grain);
    println!(
        "  held out ({} bytes and {} section letters), bits at L_R = {grain}:",
        counts[1][..SECTION].iter().sum::<u64>(),
        counts[1][SECTION]
    );
    readings(
        1,
        &flat_whole,
        flat_charge,
        &curated_whole,
        curated_charge,
        &flat_base,
        &curated_base,
        &counts[1],
        grain,
    );
    println!();
    println!("wall time in all: {} ms", setup.elapsed().as_millis());
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    match arguments.as_slice() {
        [mode, curated, flat] if mode == "curated" => curated_harness(curated, flat),
        _ => println!(
            "usage: hnn_curated -- curated <curated-cut.bin> <curated-flat-cut.bin> (module header)"
        ),
    }
}
