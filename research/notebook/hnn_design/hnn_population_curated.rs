//! **`curated`: the curated conversation source through the egg population** (campaign 5 on the
//! population; `holonics::receiver::population::{families, boundary}`,
//! `holonics::compression::landmark::context::sections`; Lean
//! `Compression/Landmark/Context/Composition.{stagedFace_*, staged_chain_rule, staged_code}`;
//! #73, #148). Included by `hnn_population.rs` as its `curated` mode; count-only **development
//! receipts**, a committed command run once in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_population -- curated .local/cuts/curated-cut.bin .local/cuts/curated-flat-cut.bin
//! ```
//!
//! [definition; agent-inferred] **The cut** is `curated_source.py`'s pinned cut (`hnn_curated`'s):
//! the section chart `256 + 12` (`SectionChart::curated`), `n* = 2^20`, the final eighth held out,
//! and its flat twin, the same bytes with every letter removed.
//!
//! [definition; agent-inferred] **The population**, declared before any passage, every family named
//! by `⌈log₂ 8⌉ = 3` bits (`M = 1`), each tree the `½` stop prior and
//! the KT node (`c = ∞`), stored where paths part, at `n* = 2^20` and `L_R = 16`:
//! - **the curated cell tree** (bytes and letters as cells) at `D = 6, 12, 24, 48` and the deepest its
//!   carriers admit;
//! - **the typed tree** (`TreeFamily::sectioned`: each tick's cell bundled with its part's channel,
//!   read once at the section; the joint address across ports) at `D = 6, 12`;
//! - **the boundary egg** (`BoundaryEgg`): the part clock composed with the typed tree at the deepest
//!   its carriers admit and the letter tree at `D_L = 12`, through the hazard law. Its byte tree read
//!   alone (the part clock's port unheld) is the typed tree at that depth, reported from the egg's own
//!   receipt: the same tree on the same cells, so the population does not hold it twice.
//!
//! [definition; agent-inferred] **The development sweep, charged.** On the development cells alone
//! (`boundary_probe`, a scratch command, never committed) the egg's constituents were chosen among
//! the laws probed: the byte tree among 3 (the typed reader's `[channel, kind]` tree at `D = 16`, the
//! cell tree at `D = 48`, the channel-slot tree at `D = 21`, one below its deepest), the hazard among
//! 45 partitions and
//! mixtures, the letter tree among 11 (plain and typed, `D_L ≤ 12`): `⌈log₂ 3⌉ + ⌈log₂ 45⌉ +
//! ⌈log₂ 11⌉ = 2 + 6 + 4 = 12` bits, charged to the curated stream. The flat tree is charged its
//! recorded depth sweep, `⌈log₂ 5⌉ = 3` bits.
//!
//! [definition] **One passage**: the population reads the whole cut once, development cells then
//! held-out cells, every cell scored at the standing before its own deposit
//! (`Population::receive_partitioned`, parts by population and slot: human, agent and tool bytes,
//! section letters); then the flat tree at `D = 48` reads the flat twin once. The held-out cells are
//! read by nothing else. **Printed, exactly**: the population's code against the flat stream's, in
//! all, per channel and on the section letters; the boundary egg's stages (the hazard on each
//! channel's bytes and at each channel's closes, against the retired per-port reader's closes,
//! `849 + 1/16` over 84 human and `3139 + 4/16` over 1392 agent ends; the byte tree within the bytes;
//! the letter tree against the retired section navigator's `1839 + 12/16`); the part clock's value
//! (the egg's unheld byte tree against the egg); each family's code, posterior and selection; wall
//! times and the resident set. Bits are enclosures read at `L_R = 16` as `n + k/16 + ε`; no decimal
//! and no content is printed.

use std::time::Instant;

use holonics::compression::landmark::context::{
    Capacity, LandmarkDeclaration, Landmarks, LetterFamily, PassageCode, SectionChart,
    SectionSlots, Sections, StopPrior,
};
use holonics::hnn::field::{Field, FieldDeclaration};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::{ExactInterval, interval_difference, interval_sum};
use holonics::receiver::population::{
    BoundaryEgg, BoundaryReadout, Family, PartReading, Population, PopulationReceipt, Posterior,
    Readout, TreeFamily,
};
use num_bigint::BigInt;

use super::exterior::{
    against, enclosure, per, read_curated, read_cut, reading_of, receiver_grain, resident_set,
};

/// The cell tree's doubling ladder below its deepest admitted depth.
const CELL_DEPTHS: [usize; 4] = [6, 12, 24, 48];

/// The typed tree's ladder below the egg's byte tree (its deepest admitted depth).
const TYPED_DEPTHS: [usize; 2] = [6, 12];

/// The letter tree's depth (chosen on development among the probed, charged below).
const LETTER_DEPTH: usize = 12;

/// The flat tree's recorded depth (the typed reader's development sweep, `hnn_curated`).
const FLAT_DEPTH: usize = 48;

/// The development sweep's charges (module header): the byte tree among 3, the hazard among 45,
/// the letter tree among 11; the flat tree's recorded depth sweep among 5.
const PROBED: [u64; 3] = [3, 45, 11];
const FLAT_SWEEP: u64 = 5;

/// The readings' slots.
const SLOTS: [&str; 4] = [
    "human bytes",
    "agent bytes",
    "tool bytes",
    "section letters",
];
const LETTERS: usize = 3;
const PARTS: [&str; 2] = ["development", "held out"];

/// The retired per-port reader's receipts (commit `38b0b81c`): the closes per port and the section
/// navigator's letters, on the development cells.
const RETIRED_CLOSES: [&str; 2] = [
    "849 + 1/16 (84 human ends)",
    "3139 + 4/16 (1392 agent ends)",
];
const RETIRED_LETTERS: &str = "1839 + 12/16";

fn ceil_log2(count: u64) -> u64 {
    u64::from(count.next_power_of_two().trailing_zeros())
}

fn point(bits: u64) -> ExactInterval {
    ExactInterval::point(Rat::from_integer(BigInt::from(bits)))
}

fn sum(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    interval_sum(a, b).expect("an enclosure")
}

fn bits(code: &PassageCode) -> ExactInterval {
    code.bits().expect("an enclosure")
}

/// The product of several passages' faces, read once.
fn joined<'a>(codes: impl IntoIterator<Item = &'a PassageCode>) -> ExactInterval {
    let mut all = PassageCode::new();
    for code in codes {
        all.join(code);
    }
    bits(&all)
}

/// `a − b`, enclosed.
fn minus(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    interval_difference(a, b).expect("a difference")
}

/// A strict ordering with its exact difference, and the difference a cell.
fn ordering(label: &str, a: &ExactInterval, b: &ExactInterval, cells: u64) {
    let delta = ExactInterval {
        lower: &a.lower - &b.upper,
        upper: &a.upper - &b.lower,
    };
    println!(
        "    {label}: {}; difference {}, a cell {}",
        against(a, b),
        enclosure(&delta, super::GRAIN),
        per(&delta, cells, super::GRAIN)
    );
}

fn declaration(
    alphabet: usize,
    depth: usize,
    population: u64,
    grain: u64,
    family: LetterFamily,
) -> LandmarkDeclaration {
    LandmarkDeclaration {
        alphabet,
        depth,
        forced: 0,
        population,
        grain,
        family,
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    }
}

/// **The deepest depth a declaration's carriers admit** (`Landmarks::new` refuses past it).
fn deepest(declared: &LandmarkDeclaration) -> usize {
    let mut depth = declared.depth;
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

fn posterior(posterior: &Posterior) -> String {
    match posterior {
        Posterior::Dead => "dead".to_string(),
        Posterior::Bits(bits) => reading_of(bits, super::GRAIN),
    }
}

/// The population's receipt: each family's posterior, and the selected family.
fn selection(receipt: &PopulationReceipt) {
    for (index, family) in receipt.families.iter().enumerate() {
        println!(
            "    [{index}] {}: −log₂ w = {}",
            family.label,
            posterior(&family.posterior)
        );
    }
    match receipt.selected {
        Some(index) => println!(
            "    selected (posterior decided above ½): [{index}] {}",
            receipt.families[index].label
        ),
        None => println!("    selected: none decided above ½"),
    }
}

/// The egg's readout on one population: the later readout less the earlier (held out), or the
/// development readout alone.
struct Stages {
    hazard_bytes: Vec<ExactInterval>,
    hazard_closes: Vec<ExactInterval>,
    within_bytes: Vec<ExactInterval>,
    letters: ExactInterval,
    root_bytes: Vec<ExactInterval>,
    root_closes: Vec<ExactInterval>,
    tree_letters: ExactInterval,
    bytes: Vec<u64>,
    closes: Vec<u64>,
}

impl Stages {
    fn of(readout: &BoundaryReadout, before: Option<&BoundaryReadout>) -> Self {
        let read = |now: &PassageCode, then: Option<&PassageCode>| match then {
            Some(then) => minus(&bits(now), &bits(then)),
            None => bits(now),
        };
        let each = |now: &[PassageCode], then: Option<&[PassageCode]>| -> Vec<ExactInterval> {
            now.iter()
                .enumerate()
                .map(|(c, code)| read(code, then.map(|t| &t[c])))
                .collect()
        };
        let counts = |now: &[u64], then: Option<&[u64]>| -> Vec<u64> {
            now.iter()
                .enumerate()
                .map(|(c, &n)| n - then.map_or(0, |t| t[c]))
                .collect()
        };
        Self {
            hazard_bytes: each(&readout.hazard_bytes, before.map(|b| &b.hazard_bytes[..])),
            hazard_closes: each(&readout.hazard_closes, before.map(|b| &b.hazard_closes[..])),
            within_bytes: each(&readout.within_bytes, before.map(|b| &b.within_bytes[..])),
            letters: read(&readout.letters, before.map(|b| &b.letters)),
            root_bytes: each(&readout.root_bytes, before.map(|b| &b.root_bytes[..])),
            root_closes: each(&readout.root_closes, before.map(|b| &b.root_closes[..])),
            tree_letters: read(&readout.tree_letters, before.map(|b| &b.tree_letters)),
            bytes: counts(&readout.bytes, before.map(|b| &b.bytes[..])),
            closes: counts(&readout.closes, before.map(|b| &b.closes[..])),
        }
    }

    fn total(parts: &[&ExactInterval]) -> ExactInterval {
        parts.iter().fold(point(0), |all, part| sum(&all, part))
    }
}

/// The boundary egg's stages on one population.
fn stages(stages: &Stages, channels: &[&str], letters: u64) {
    let grain = super::GRAIN;
    println!("  the boundary egg by stage:");
    for (c, name) in channels.iter().enumerate() {
        if stages.bytes[c] == 0 && stages.closes[c] == 0 {
            println!("    {name}: no cells");
            continue;
        }
        println!(
            "    {name}: {} bytes, {} closes",
            stages.bytes[c], stages.closes[c]
        );
        println!(
            "      the hazard: on the bytes {}; at the closes {}, a close {}; together {}",
            reading_of(&stages.hazard_bytes[c], grain),
            reading_of(&stages.hazard_closes[c], grain),
            per(&stages.hazard_closes[c], stages.closes[c], grain),
            reading_of(
                &sum(&stages.hazard_bytes[c], &stages.hazard_closes[c]),
                grain
            )
        );
        println!(
            "      the byte tree's root digit (the port unheld): on the bytes {}; at the closes {}; together {}",
            reading_of(&stages.root_bytes[c], grain),
            reading_of(&stages.root_closes[c], grain),
            reading_of(&sum(&stages.root_bytes[c], &stages.root_closes[c]), grain)
        );
        println!(
            "      the byte tree within the bytes: {}; a byte {}",
            reading_of(&stages.within_bytes[c], grain),
            per(&stages.within_bytes[c], stages.bytes[c], grain)
        );
    }
    println!(
        "    the letters: the letter tree {} (a letter {}); the byte tree's own letters within the letters {}",
        reading_of(&stages.letters, grain),
        per(&stages.letters, letters, grain),
        reading_of(&stages.tree_letters, grain)
    );
    let hazard: Vec<&ExactInterval> = stages
        .hazard_bytes
        .iter()
        .chain(&stages.hazard_closes)
        .collect();
    let root: Vec<&ExactInterval> = stages
        .root_bytes
        .iter()
        .chain(&stages.root_closes)
        .collect();
    let (hazard, root) = (Stages::total(&hazard), Stages::total(&root));
    let within = Stages::total(&stages.within_bytes.iter().collect::<Vec<_>>());
    println!(
        "    the egg in all {}; the byte tree alone (the typed tree, the part clock's port unheld) {}",
        reading_of(&sum(&sum(&hazard, &within), &stages.letters), grain),
        reading_of(&sum(&sum(&root, &within), &stages.tree_letters), grain)
    );
    let section = sum(&hazard, &stages.letters);
    let unheld_section = sum(&root, &stages.tree_letters);
    println!(
        "    the section's cost (the boundary and the letters): the egg {}, the byte tree alone {}",
        reading_of(&section, grain),
        reading_of(&unheld_section, grain)
    );
    ordering(
        "the part clock's value, the byte tree alone against the egg (its boundary share, then its letters' share)",
        &unheld_section,
        &section,
        letters,
    );
    println!(
        "      boundary {}; letters {}",
        reading_of(&minus(&root, &hazard), grain),
        reading_of(&minus(&stages.tree_letters, &stages.letters), grain)
    );
}

/// The population's readings on one population against the flat tree's.
#[allow(clippy::too_many_arguments)]
fn readings(
    part: usize,
    readings: &[PartReading],
    flat: &[[PassageCode; 3]; 2],
    counts: &[[u64; 4]; 2],
    charge: u64,
    flat_charge: u64,
    egg: usize,
) {
    let grain = super::GRAIN;
    let at = |slot: usize| &readings[part * SLOTS.len() + slot];
    println!(
        "  the population against the flat tree (D = {FLAT_DEPTH}) on identical bytes, uncharged:"
    );
    let mut population_bytes = point(0);
    for (slot, name) in SLOTS.iter().enumerate().take(LETTERS) {
        if counts[part][slot] == 0 {
            println!("    {name}: no cells");
            continue;
        }
        let (population, tree) = (&at(slot).population, bits(&flat[part][slot]));
        population_bytes = sum(&population_bytes, population);
        println!(
            "    {name} ({} cells): population {} (a cell {}), flat {} (a cell {}); the boundary egg alone {}",
            counts[part][slot],
            reading_of(population, grain),
            per(population, counts[part][slot], grain),
            reading_of(&tree, grain),
            per(&tree, counts[part][slot], grain),
            at(slot).families[egg]
                .as_ref()
                .map_or("-".to_string(), |code| reading_of(code, grain))
        );
        ordering(
            &format!("{name}, population against flat"),
            population,
            &tree,
            counts[part][slot],
        );
    }
    let bytes: u64 = counts[part][..LETTERS].iter().sum();
    let flat_bytes = joined(&flat[part]);
    ordering(
        &format!("every byte ({bytes}), population against flat"),
        &population_bytes,
        &flat_bytes,
        bytes,
    );
    let letters = &at(LETTERS).population;
    println!(
        "    the section letters ({}): population {} (a letter {})",
        counts[part][LETTERS],
        reading_of(letters, grain),
        per(letters, counts[part][LETTERS], grain)
    );
    let whole = sum(&sum(&population_bytes, letters), &point(charge));
    let flat_whole = sum(&flat_bytes, &point(flat_charge));
    println!(
        "  the whole curated stream (bytes and sections) charged {charge} bits: {}",
        enclosure(&whole, grain)
    );
    println!(
        "  the flat stream (bytes alone) charged {flat_charge} bits: {}",
        enclosure(&flat_whole, grain)
    );
    ordering(
        "the whole curated stream against the flat stream, a byte",
        &whole,
        &flat_whole,
        bytes,
    );
}

#[allow(clippy::too_many_lines)]
pub fn harness(curated_path: &str, flat_path: &str, development_only: bool) {
    let clock = Instant::now();
    let chart = SectionChart::curated();
    let cut = read_curated(curated_path, &chart);
    let (flat_bytes, flat_count, flat_held) = read_cut(flat_path);
    let bytes_of: Vec<usize> = cut
        .codes
        .iter()
        .copied()
        .filter(|&code| chart.section(code).is_none())
        .collect();
    let identical = bytes_of.len() == flat_count
        && bytes_of
            .iter()
            .zip(&flat_bytes)
            .all(|(&a, &b)| a == usize::from(b));
    assert!(identical, "the flat cut is the curated cut's bytes");
    let development = cut.held.start;
    let flat_development = cut.codes[..development]
        .iter()
        .filter(|&&code| chart.section(code).is_none())
        .count();
    assert_eq!(
        flat_held.start, flat_development,
        "identical held-out cells"
    );
    let field = Field::declare(FieldDeclaration::campaign_one(cut.population))
        .expect("campaign 1's declared field at the population");
    let grain = receiver_grain(&field);
    assert_eq!(grain, super::GRAIN, "the receiver's grain");

    // Each cell's part: its population and its slot (the channel of its part, or a letter).
    let mut open = None;
    let mut counts = [[0u64; 4]; 2];
    let parts: Vec<usize> = cut
        .codes
        .iter()
        .enumerate()
        .map(|(position, &code)| {
            let slot = match chart.section(code) {
                Some(section) => {
                    open = Some(section.channel);
                    LETTERS
                }
                None => open.expect("the cut opens at a section letter"),
            };
            let population = usize::from(position >= development);
            counts[population][slot] += 1;
            population * SLOTS.len() + slot
        })
        .collect();
    println!(
        "hnn_population curated: the curated source through the egg population against the flat stream of the same bytes (campaign 5; #73, #148)"
    );
    println!(
        "0. the cut: {} curated cells (|A| = {}), {flat_count} flat cells, identical bytes: {identical}; n* = {}, L_R = {grain}",
        cut.codes.len(),
        chart.alphabet(),
        cut.population
    );
    for (part, name) in PARTS.iter().enumerate() {
        println!(
            "  {name}: human {}, agent {}, tool {}, section letters {}",
            counts[part][0], counts[part][1], counts[part][2], counts[part][LETTERS]
        );
    }

    // 1. The declarations.
    let cells = |depth| {
        declaration(
            chart.alphabet(),
            depth,
            cut.population,
            grain,
            LetterFamily::cells(),
        )
    };
    let slots = || Sections::new(chart, SectionSlots::Channel).expect("the channel slot");
    let typed = |depth| {
        declaration(
            chart.alphabet(),
            depth,
            cut.population,
            grain,
            slots().family().clone(),
        )
    };
    let cell_deepest = deepest(&cells(CELL_DEPTHS[CELL_DEPTHS.len() - 1]));
    let typed_deepest = deepest(&typed(TYPED_DEPTHS[TYPED_DEPTHS.len() - 1]));
    let letter_declaration = declaration(
        chart.letters(),
        LETTER_DEPTH,
        cut.population,
        grain,
        BoundaryEgg::letter_family(cut.population).expect("the letter family"),
    );
    let families = CELL_DEPTHS.len() + 1 + TYPED_DEPTHS.len() + 1;
    let naming = ceil_log2(families as u64);
    let mut declared: Vec<Box<dyn Family>> = Vec::new();
    for depth in CELL_DEPTHS.iter().copied().chain([cell_deepest]) {
        declared.push(Box::new(
            TreeFamily::new(cells(depth), naming).expect("a cell tree"),
        ));
    }
    for &depth in &TYPED_DEPTHS {
        declared.push(Box::new(
            TreeFamily::sectioned(typed(depth), naming, slots()).expect("a typed tree"),
        ));
    }
    let egg_index = declared.len();
    declared.push(Box::new(
        BoundaryEgg::new(
            format!(
                "boundary egg (part clock ⊳ typed tree D = {typed_deepest}, letter tree D_L = {LETTER_DEPTH})"
            ),
            naming,
            TreeFamily::sectioned(typed(typed_deepest), naming, slots()).expect("the byte tree"),
            chart,
            letter_declaration,
        )
        .expect("the boundary egg"),
    ));
    let charge: u64 = PROBED.iter().map(|&count| ceil_log2(count)).sum();
    let flat_charge = ceil_log2(FLAT_SWEEP);
    println!(
        "1. the population: {families} families, each named by ⌈log₂ {families}⌉ = {naming} bits (M = {families}/{}): the cell tree at D = {:?}, the typed tree (channel slot) at D = {TYPED_DEPTHS:?}, the boundary egg on the typed tree at D = {typed_deepest}; the development sweep charged {charge} bits, the flat tree's {flat_charge}",
        1u64 << naming,
        CELL_DEPTHS
            .iter()
            .copied()
            .chain([cell_deepest])
            .collect::<Vec<_>>(),
    );
    let mut population = Population::new(declared).expect("the population");
    println!("  setup: {} ms", clock.elapsed().as_millis());
    println!();

    // 2. One passage: the development cells, then the held-out cells.
    let passage = Instant::now();
    let (_, mut reading) = population
        .receive_partitioned(
            &cut.codes[..development],
            &parts[..development],
            2 * SLOTS.len(),
        )
        .expect("the development cells");
    let development_ms = passage.elapsed().as_millis();
    let development_receipt = population.receipt().expect("a receipt");
    let Some(Readout::Boundary(development_stages)) = population.readout(egg_index) else {
        panic!("the boundary egg's readout")
    };
    if development_only {
        println!(
            "2. the development cells only (the held-out cells are not read): {development_ms} ms; resident set (now, peak) {:?} bytes",
            resident_set()
        );
        println!();
        println!(
            "3. development, the population alone (the flat tree's recorded development code 1800742 + 1/16 + ε):"
        );
        let letters = &reading[LETTERS].population;
        let bytes: Vec<&ExactInterval> =
            (0..LETTERS).map(|slot| &reading[slot].population).collect();
        let bytes = Stages::total(&bytes);
        println!(
            "  bytes {}, section letters {}, the whole charged {charge} bits {}",
            reading_of(&bytes, grain),
            reading_of(letters, grain),
            reading_of(&sum(&sum(&bytes, letters), &point(charge)), grain)
        );
        selection(&development_receipt);
        stages(
            &Stages::of(&development_stages, None),
            &["human", "agent", "tool"],
            counts[0][LETTERS],
        );
        println!("wall time in all: {} ms", clock.elapsed().as_millis());
        return;
    }
    let (_, held) = population
        .receive_partitioned(
            &cut.codes[development..],
            &parts[development..],
            2 * SLOTS.len(),
        )
        .expect("the held-out cells");
    for (index, part) in held.into_iter().enumerate() {
        if index >= SLOTS.len() {
            reading[index] = part;
        }
    }
    let receipt = population.receipt().expect("a receipt");
    let Some(Readout::Boundary(whole_stages)) = population.readout(egg_index) else {
        panic!("the boundary egg's readout")
    };
    let resident = resident_set();
    println!(
        "2. one passage of the population over the whole cut: development {development_ms} ms, in all {} ms; resident set (now, peak) {resident:?} bytes",
        passage.elapsed().as_millis()
    );
    drop(population);

    // The flat tree over the flat twin, once.
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
    let mut flat = [[PassageCode::new(); 3]; 2];
    let byte_slots: Vec<usize> = parts
        .iter()
        .filter(|&&part| part % SLOTS.len() != LETTERS)
        .map(|&part| part % SLOTS.len())
        .collect();
    for (position, &byte) in flat_bytes.iter().enumerate() {
        let face = flat_tree
            .receive(usize::from(byte))
            .expect("a byte of the flat chart");
        flat[usize::from(position >= flat_held.start)][byte_slots[position]]
            .face(&face)
            .expect("a positive face");
    }
    println!(
        "  the flat tree at D = {FLAT_DEPTH}, one passage over the flat twin: {} ms",
        flat_clock.elapsed().as_millis()
    );
    println!();

    // 3. The readings.
    let channels = ["human", "agent", "tool"];
    for (part, name) in PARTS.iter().enumerate() {
        println!(
            "{}. {name} ({} bytes, {} section letters), bits at L_R = {grain}:",
            3 + part,
            counts[part][..LETTERS].iter().sum::<u64>(),
            counts[part][LETTERS]
        );
        readings(
            part,
            &reading,
            &flat,
            &counts,
            charge,
            flat_charge,
            egg_index,
        );
        println!("  each family's code on this population:");
        let family_receipt = if part == 0 {
            &development_receipt
        } else {
            &receipt
        };
        for (index, family) in family_receipt.families.iter().enumerate() {
            let code = (0..SLOTS.len())
                .map(|slot| reading[part * SLOTS.len() + slot].families[index].clone())
                .collect::<Option<Vec<ExactInterval>>>()
                .map(|codes| Stages::total(&codes.iter().collect::<Vec<_>>()));
            println!(
                "    [{index}] {}: {}",
                family.label,
                code.map_or("dead".to_string(), |code| reading_of(&code, grain))
            );
        }
        println!("  the posterior after the {name} cells:",);
        selection(family_receipt);
        let egg_stages = if part == 0 {
            Stages::of(&development_stages, None)
        } else {
            Stages::of(&whole_stages, Some(&development_stages))
        };
        stages(&egg_stages, &channels, counts[part][LETTERS]);
        if part == 0 {
            println!(
                "    the retired per-port reader's closes on the development cells: human {}, agent {}; its section navigator's letters {RETIRED_LETTERS}",
                RETIRED_CLOSES[0], RETIRED_CLOSES[1]
            );
        }
        println!();
    }
    println!(
        "the population's code over the whole cut: {}",
        enclosure(&receipt.code, grain)
    );
    println!("wall time in all: {} ms", clock.elapsed().as_millis());
}
