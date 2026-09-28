//! **`f0-local`: F0's second candidate, a family wins where it is closest** (THE_REBUILD F0,
//! candidate 2; `holonics::receiver::population::LocalMixture`; Lean
//! `Compression/Landmark/Context/Population.{local_telescope, local_mixture_code,
//! local_of_constant}`; #73, #148). Included by `hnn_population.rs`; count-only **development
//! receipts**, a committed command run once in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_population -- f0-local-probe .local/cuts/curated-f4-passage-cut.bin .local/cuts/curated-f4-passage-flat-cut.bin [cells]
//! cargo run --release -p holonics --example hnn_population -- f0-local .local/cuts/curated-f4-passage-cut.bin .local/cuts/curated-f4-passage-flat-cut.bin
//! ```
//!
//! [definition; agent-inferred] **The mixture.** The eight families of F4's population
//! (`Members::Declared`: the cell tree at `D = 6, 12, 24, 48` and its deepest, the typed tree at
//! `D = 6, 12`, the admitted egg), each named by `⌈log₂ 8⌉ = 3` bits (`π_f = 1/8` at every context,
//! so each context met pays at most `log₂ 8 = 3` bits for its mixing), are wrapped in one
//! `LocalMixture` over the declared ladder `d ∈ {0, 1, 2}` (the last `d` curated cells, bytes and
//! section letters). The choosing role chooses `d` by its own code on the choosing cells, the rung
//! choice charged `⌈log₂ 3⌉ = 2` bits; ties go to the shallower rung (`agent-inferred`: fewer
//! contexts to pay). `d = 0` makes the face while the choosing cells are read (whole-passage Bayes
//! with the executed chart's floor); the chosen rung makes it on the validation cells. Every rung
//! is read on every cell as a comparison, so the unchosen rungs' validation readings are disclosed
//! and choose nothing. The members' faces are the same whatever the rung, so the admitted egg's own
//! code on the same cells is the egg alone (F0's first candidate) read like with like.
//!
//! [definition; agent-inferred] **Adoption** (THE_REBUILD F0): the mixture is adopted only if its
//! validation bytes, with the rung choice's 2 bits, lie strictly below the egg alone's on the same
//! bytes (the egg alone is named by 0 bits). Validation is read once, after the choice.
//!
//! **The probe** (`f0-local-probe`) reads the first `N` choosing cells (default `2^16`) twice: the
//! eight members alone, then the mixture over them, and projects the full passage from the recorded
//! eight-family passage (272,849 ms at a 10,843,217,920-byte peak) plus the mixture's measured cost
//! a cell, against ten minutes and 20 GB. Bits are enclosures read at `L_R = 16` as `n + k/16 + ε`;
//! no decimal and no content is printed.

use std::time::Instant;

use holonics::compression::landmark::context::{LetterFamily, PassageCode, SectionChart};
use holonics::hnn::field::{Field, FieldDeclaration};
use holonics::ratio::algebraic::ExactInterval;
use holonics::receiver::population::{
    Family, HazardPartition, LocalMixture, TreeFamily, learn_hazard_partition,
};
use rayon::prelude::*;

use super::curated::{
    FLAT_DEPTH, FLAT_SWEEP, LETTERS, Members, PROBED, bits, ceil_log2, curated_families,
    declaration, joined, ordering, point, sum,
};
use super::exterior::{
    against, available_memory, enclosure, per, read_curated, read_cut, read_incidence, reading_of,
    receiver_grain, resident_set,
};

/// The declared gating ladder.
const LADDER: [usize; 3] = [0, 1, 2];

/// The recorded eight-family passage on F4's development passage (THE_REBUILD F0, the diagnosis):
/// its milliseconds and its peak resident set in bytes.
const RECORDED_PASSAGE: (u128, u128) = (272_849, 10_843_217_920);

/// The budgets every full passage is projected against: ten minutes and 20 GB.
const BUDGET: (u128, u128) = (600_000, 20_000_000_000);

/// The recorded flat tree passage and the population census's standing stream on this cut, the
/// rest of a full run: milliseconds.
const RECORDED_REST: u128 = 22_922 + 13_266;

/// The probe's default cells.
pub const PROBE: usize = 1 << 16;

/// The declared parts: the choosing and the validation families.
const PARTS: [&str; 2] = ["choosing", "validation"];

/// Counts the bytes a standing encodes to, holding none of them.
struct StandingBytes(u64);

impl std::io::Write for StandingBytes {
    fn write(&mut self, buffer: &[u8]) -> std::io::Result<usize> {
        self.0 += u64::try_from(buffer.len()).expect("a write length fits u64");
        Ok(buffer.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// The cut, its parts and the members, prepared from choosing cells alone.
struct Prepared {
    codes: Vec<usize>,
    choosing: usize,
    slots: Vec<usize>,
    counts: [[u64; 4]; 2],
    flat_bytes: Vec<u8>,
    flat_held: usize,
    population: u64,
    grain: u64,
    charge: ExactInterval,
    flat_charge: u64,
    members: Vec<Box<dyn Family>>,
    egg: usize,
    labels: Vec<String>,
}

fn prepare(curated_path: &str, flat_path: &str) -> Prepared {
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
    let choosing = cut.held.start;
    let flat_choosing = cut.codes[..choosing]
        .iter()
        .filter(|&&code| chart.section(code).is_none())
        .count();
    assert_eq!(flat_held.start, flat_choosing, "identical validation cells");
    let field = Field::declare(FieldDeclaration::campaign_one(cut.population))
        .expect("campaign 1's declared field at the population");
    let grain = receiver_grain(&field);
    assert_eq!(grain, super::GRAIN, "the receiver's grain");
    let mut open = None;
    let mut counts = [[0u64; 4]; 2];
    let slots: Vec<usize> = cut
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
            counts[usize::from(position >= choosing)][slot] += 1;
            slot
        })
        .collect();
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
    let learning = Instant::now();
    let (partition, receipt) =
        learn_hazard_partition(chart, &cut.codes[..choosing]).expect("the learned partition");
    println!(
        "1. the merges, learned on the choosing cells only: {} ms",
        learning.elapsed().as_millis()
    );
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
    let (members, egg, _) = curated_families(
        chart,
        cut.population,
        grain,
        partition,
        read_incidence(curated_path),
        &comparisons,
        Members::Declared,
    )
    .expect("the eight declared families");
    let labels = members.iter().map(|member| member.label()).collect();
    let swept: u64 = PROBED.iter().map(|&count| ceil_log2(count)).sum();
    Prepared {
        codes: cut.codes,
        choosing,
        slots,
        counts,
        flat_bytes,
        flat_held: flat_held.start,
        population: cut.population,
        grain,
        charge: sum(&point(swept), &receipt.description),
        flat_charge: ceil_log2(FLAT_SWEEP),
        members,
        egg,
        labels,
    }
}

fn ladder_charge() -> u64 {
    ceil_log2(LADDER.len() as u64)
}

/// **The bounded choosing probe**: the first `cells` choosing cells through the eight members
/// alone, then through the mixture over fresh members, and the full passage projected.
pub fn probe(curated_path: &str, flat_path: &str, cells: usize) {
    let clock = Instant::now();
    println!(
        "hnn_population f0-local-probe: the first {cells} choosing cells, the eight members alone and then mixed node-locally (THE_REBUILD F0 candidate 2; #73, #148)"
    );
    let prepared = prepare(curated_path, flat_path);
    let cells = cells.min(prepared.choosing);
    let passage = &prepared.codes[..cells];
    let mut members = prepared.members;
    let alone = Instant::now();
    for &cell in passage {
        members
            .par_iter_mut()
            .try_for_each(|member| member.receive(cell).map(|_| ()))
            .expect("a member's face");
    }
    let alone_ms = alone.elapsed().as_millis();
    drop(members);
    let fresh = prepare_members_again(curated_path, flat_path);
    let mut mixture = LocalMixture::new(fresh, &LADDER, 0, ladder_charge()).expect("the mixture");
    let mixed = Instant::now();
    for &cell in passage {
        mixture.receive(cell).expect("the mixture's face");
    }
    let mixed_ms = mixed.elapsed().as_millis();
    let resident = resident_set();
    println!(
        "2. {cells} choosing cells: the members alone {alone_ms} ms, the mixture over them {mixed_ms} ms; resident set (now, peak) {resident:?} bytes"
    );
    for rung in 0..LADDER.len() {
        let receipt = mixture.receipt(rung).expect("a rung's receipt");
        println!(
            "  d = {}: {} contexts met, code {} (a cell {}); floors bound at {} cells, roundings at {}",
            receipt.depth,
            receipt.contexts,
            reading_of(&receipt.code, prepared.grain),
            per(&receipt.code, receipt.cells, prepared.grain),
            receipt.floors,
            receipt.roundings
        );
    }
    let total = prepared.codes.len() as u128;
    let overhead = mixed_ms.saturating_sub(alone_ms);
    let projected = RECORDED_PASSAGE.0 + overhead * total / cells as u128 + RECORDED_REST;
    println!(
        "3. the projection: the recorded eight-family passage {} ms, plus the mixture's {overhead} ms over {cells} cells scaled to {total} cells ({} ms), plus the flat tree and the standing stream {RECORDED_REST} ms: {projected} ms against {} ms: {}",
        RECORDED_PASSAGE.0,
        overhead * total / cells as u128,
        BUDGET.0,
        if projected < BUDGET.0 {
            "within"
        } else {
            "past it: refused"
        }
    );
    println!(
        "  memory: the recorded peak {} bytes plus the contexts (at most 269² = 72,361 at d = 2, each eight weights and eight codes) against {} bytes; available now {:?} bytes",
        RECORDED_PASSAGE.1,
        BUDGET.1,
        available_memory()
    );
    println!("wall time in all: {} ms", clock.elapsed().as_millis());
}

/// Fresh members for the probe's second reading (the merges relearned on the same choosing cells,
/// deterministically).
fn prepare_members_again(curated_path: &str, flat_path: &str) -> Vec<Box<dyn Family>> {
    prepare(curated_path, flat_path).members
}

/// Each part's and slot's codes: every rung's, and every member's.
struct Readings {
    rungs: Vec<[[PassageCode; 4]; 2]>,
    members: Vec<[[PassageCode; 4]; 2]>,
}

impl Readings {
    fn new(rungs: usize, members: usize) -> Self {
        Self {
            rungs: vec![[[PassageCode::new(); 4]; 2]; rungs],
            members: vec![[[PassageCode::new(); 4]; 2]; members],
        }
    }

    fn read(&mut self, mixture: &LocalMixture, part: usize, slot: usize) {
        for (rung, codes) in self.rungs.iter_mut().enumerate() {
            let face = mixture.rung_face(rung).expect("a declared rung");
            codes[part][slot].face(face).expect("a positive face");
        }
        for (member, face) in mixture.member_faces().iter().enumerate() {
            if let Some(face) = face {
                self.members[member][part][slot]
                    .face(face)
                    .expect("a positive face");
            }
        }
    }

    fn bytes(codes: &[[PassageCode; 4]; 2], part: usize) -> ExactInterval {
        joined(codes[part][..LETTERS].iter())
    }

    fn whole(codes: &[[PassageCode; 4]; 2], part: usize) -> ExactInterval {
        joined(codes[part].iter())
    }
}

/// **The full passage**: the choosing cells, the choice of `d`, the validation cells read once, the
/// readings, the bound, the standing and the flat tree.
#[allow(clippy::too_many_lines)]
pub fn harness(curated_path: &str, flat_path: &str) {
    let clock = Instant::now();
    println!(
        "hnn_population f0-local: F0's second candidate, the eight declared families mixed node-locally over the gating ladder d ∈ {LADDER:?} (receiver::population::LocalMixture; THE_REBUILD F0; #73, #148)"
    );
    println!("  available memory {:?} bytes", available_memory());
    let prepared = prepare(curated_path, flat_path);
    let grain = prepared.grain;
    let charge = ladder_charge();
    println!(
        "2. the members: {} families, each named by ⌈log₂ 8⌉ = 3 bits (π_f = 1/8 at every context): {:?}; the admitted egg is member [{}]; the ladder d ∈ {LADDER:?} charged ⌈log₂ {}⌉ = {charge} bits, the floor K = {}; the curated stream's development sweep and learned partition charged {} beside, the flat tree's {}",
        prepared.members.len(),
        prepared.labels,
        prepared.egg,
        LADDER.len(),
        holonics::receiver::population::local::FLOOR,
        reading_of(&prepared.charge, grain),
        prepared.flat_charge
    );
    println!("  setup: {} ms", clock.elapsed().as_millis());
    let Prepared {
        codes,
        choosing,
        slots,
        counts,
        flat_bytes,
        flat_held,
        population,
        flat_charge,
        members,
        egg,
        labels,
        ..
    } = prepared;
    let count = members.len();
    let mut mixture = LocalMixture::new(members, &LADDER, 0, charge).expect("the mixture");
    let mut readings = Readings::new(LADDER.len(), count);

    // 3. The choosing cells, d = 0 making the face.
    let passage = Instant::now();
    for (&cell, &slot) in codes[..choosing].iter().zip(&slots[..choosing]) {
        mixture.receive(cell).expect("the mixture's face");
        readings.read(&mixture, 0, slot);
    }
    let choosing_ms = passage.elapsed().as_millis();
    println!();
    println!(
        "3. the choosing cells ({choosing}): {choosing_ms} ms; resident set (now, peak) {:?} bytes",
        resident_set()
    );
    let choosing_whole: Vec<ExactInterval> = readings
        .rungs
        .iter()
        .map(|codes| Readings::whole(codes, 0))
        .collect();
    for (rung, whole) in choosing_whole.iter().enumerate() {
        println!(
            "  d = {}: the choosing stream (bytes and letters) {}, charged {charge} bits",
            LADDER[rung],
            enclosure(&sum(whole, &point(charge)), grain)
        );
    }
    let egg_choosing = Readings::whole(&readings.members[egg], 0);
    println!(
        "  the admitted egg alone (named by 0 bits): {}",
        enclosure(&egg_choosing, grain)
    );
    // The choice: the rung whose enclosure lies below every other's; ties to the shallower.
    let mut chosen = 0;
    for rung in 1..LADDER.len() {
        if choosing_whole[rung].upper < choosing_whole[chosen].lower {
            chosen = rung;
        }
    }
    let decided = (0..LADDER.len())
        .filter(|&rung| rung != chosen)
        .all(|rung| choosing_whole[chosen].upper < choosing_whole[rung].lower);
    println!(
        "  chosen on the choosing cells alone: d = {} ({}); against the egg alone the chosen rung's charged stream lies {}",
        LADDER[chosen],
        if decided {
            "decided below every other rung"
        } else {
            "not decided below every other rung: the shallower kept"
        },
        against(&sum(&choosing_whole[chosen], &point(charge)), &egg_choosing)
    );
    for rung in 0..LADDER.len() {
        if rung != chosen {
            ordering(
                &format!(
                    "the choosing stream, d = {} against d = {}",
                    LADDER[chosen], LADDER[rung]
                ),
                &choosing_whole[chosen],
                &choosing_whole[rung],
                choosing as u64,
            );
        }
    }
    mixture.choose(chosen).expect("a declared rung");

    // 4. The validation cells, read once, the chosen rung making the face.
    let validation = Instant::now();
    for (&cell, &slot) in codes[choosing..].iter().zip(&slots[choosing..]) {
        mixture.receive(cell).expect("the mixture's face");
        readings.read(&mixture, 1, slot);
    }
    let validation_ms = validation.elapsed().as_millis();
    let passage_ms = passage.elapsed().as_millis();
    let resident = resident_set();
    println!();
    println!(
        "4. the validation cells ({}), read once: {validation_ms} ms; the passage in all {passage_ms} ms; resident set (now, peak) {resident:?} bytes",
        codes.len() - choosing
    );

    // 5. The standing: the members' own checkpoints and the chosen rung's weights.
    let standing_clock = Instant::now();
    let mut standing = StandingBytes(0);
    let members_only = mixture
        .write_standing(&mut standing)
        .expect("every member has a native codec");
    let read = codes.len() as u64;
    println!(
        "5. standing: {} bytes after {read} cells, {} bytes a cell (remainder {}); the members' checkpoints {members_only} bytes, the chosen rung's table and frame {} bytes; {} ms; resident set (now, peak) {:?} bytes",
        standing.0,
        standing.0 / read,
        standing.0 % read,
        standing.0 - members_only,
        standing_clock.elapsed().as_millis(),
        resident_set()
    );

    // 6. The declared bound, rung by rung, over every cell.
    let bound_clock = Instant::now();
    println!("6. the declared bound over every cell (code ≤ Σ_c min_f (code_f(c) + 3) + drift):");
    for rung in 0..LADDER.len() {
        let receipt = mixture.receipt(rung).expect("a rung's receipt");
        let slack = ExactInterval {
            lower: &receipt.bound.lower + &receipt.drift - &receipt.code.upper,
            upper: &receipt.bound.upper + &receipt.drift - &receipt.code.lower,
        };
        println!(
            "  d = {}: {} contexts met over {} cells; code {}; bound {}; drift {} bits (floors at {} cells, roundings at {}); bound + drift − code {}",
            receipt.depth,
            receipt.contexts,
            receipt.cells,
            reading_of(&receipt.code, grain),
            reading_of(&receipt.bound, grain),
            super::exterior::exact(&receipt.drift),
            receipt.floors,
            receipt.roundings,
            enclosure(&slack, grain)
        );
    }
    println!("  {} ms", bound_clock.elapsed().as_millis());
    let egg_label = labels[egg].clone();
    drop(mixture);

    // 7. The flat tree over the flat twin, once.
    let flat_clock = Instant::now();
    let mut flat_tree = TreeFamily::new(
        declaration(256, FLAT_DEPTH, population, grain, LetterFamily::cells()),
        0,
    )
    .expect("the flat tree");
    let mut flat = [[PassageCode::new(); 3]; 2];
    let byte_slots: Vec<usize> = slots
        .iter()
        .copied()
        .filter(|&slot| slot != LETTERS)
        .collect();
    for (position, &byte) in flat_bytes.iter().enumerate() {
        let face = flat_tree
            .receive(usize::from(byte))
            .expect("a byte of the flat chart");
        flat[usize::from(position >= flat_held)][byte_slots[position]]
            .face(&face)
            .expect("a positive face");
    }
    println!(
        "7. the flat tree at D = {FLAT_DEPTH}, one passage over the flat twin: {} ms",
        flat_clock.elapsed().as_millis()
    );
    drop(flat_tree);
    println!();

    // 8. The readings.
    let names = ["human", "agent", "tool"];
    for (part, name) in PARTS.iter().enumerate() {
        let bytes: u64 = counts[part][..LETTERS].iter().sum();
        println!(
            "{}. {name} ({bytes} bytes, {} section letters), bits at L_R = {grain}; the face made by d = {}:",
            8 + part,
            counts[part][LETTERS],
            if part == 0 { LADDER[0] } else { LADDER[chosen] }
        );
        for (slot, slot_name) in names.iter().enumerate() {
            if counts[part][slot] == 0 {
                continue;
            }
            let rungs: Vec<String> = readings
                .rungs
                .iter()
                .enumerate()
                .map(|(rung, codes)| {
                    format!(
                        "d = {} {}",
                        LADDER[rung],
                        reading_of(&bits(&codes[part][slot]), grain)
                    )
                })
                .collect();
            println!(
                "  {slot_name} bytes ({}): {}; the egg alone {}; flat {}",
                counts[part][slot],
                rungs.join(", "),
                reading_of(&bits(&readings.members[egg][part][slot]), grain),
                reading_of(&bits(&flat[part][slot]), grain)
            );
        }
        let flat_bytes_code = joined(flat[part].iter());
        let egg_bytes = Readings::bytes(&readings.members[egg], part);
        ordering(
            "every byte, the egg alone against flat",
            &egg_bytes,
            &flat_bytes_code,
            bytes,
        );
        for (rung, codes) in readings.rungs.iter().enumerate() {
            let rung_bytes = Readings::bytes(codes, part);
            let mark = if rung == chosen { " (chosen)" } else { "" };
            ordering(
                &format!("every byte, d = {}{mark} against flat", LADDER[rung]),
                &rung_bytes,
                &flat_bytes_code,
                bytes,
            );
            ordering(
                &format!(
                    "every byte, d = {}{mark} against the egg alone",
                    LADDER[rung]
                ),
                &rung_bytes,
                &egg_bytes,
                bytes,
            );
        }
        let letters: Vec<String> = readings
            .rungs
            .iter()
            .enumerate()
            .map(|(rung, codes)| {
                format!(
                    "d = {} {}",
                    LADDER[rung],
                    reading_of(&bits(&codes[part][LETTERS]), grain)
                )
            })
            .collect();
        println!(
            "  the section letters ({}): {}; the egg alone {}",
            counts[part][LETTERS],
            letters.join(", "),
            reading_of(&bits(&readings.members[egg][part][LETTERS]), grain)
        );
        println!("  each member's code on this part (its bytes and letters):");
        for (member, label) in labels.iter().enumerate() {
            println!(
                "    [{member}] {label}: {}",
                reading_of(&Readings::whole(&readings.members[member], part), grain)
            );
        }
        println!();
    }

    // 10. Like with like on validation, charged, and the verdict.
    let bytes: u64 = counts[1][..LETTERS].iter().sum();
    let flat_validation = sum(&joined(flat[1].iter()), &point(0));
    let mixture_bytes = Readings::bytes(&readings.rungs[chosen], 1);
    let egg_bytes = Readings::bytes(&readings.members[egg], 1);
    let charged = sum(&mixture_bytes, &point(charge));
    println!(
        "10. validation, like with like: the bytes given the observed sections ({bytes}); the mixture at d = {} charged its {charge} rung bits, the egg alone ({egg_label}) 0 bits:",
        LADDER[chosen]
    );
    ordering(
        "the mixture's bytes against flat, uncharged",
        &mixture_bytes,
        &flat_validation,
        bytes,
    );
    ordering(
        "the egg alone's bytes against flat, uncharged",
        &egg_bytes,
        &flat_validation,
        bytes,
    );
    ordering(
        "the mixture's bytes, charged, against the egg alone's",
        &charged,
        &egg_bytes,
        bytes,
    );
    ordering(
        "the mixture's bytes charged against flat charged its depth sweep",
        &charged,
        &sum(&flat_validation, &point(flat_charge)),
        bytes,
    );
    let adopted = charged.upper < egg_bytes.lower;
    println!(
        "  verdict: {}",
        if adopted {
            "adopted: the mixture's validation bytes with its charges lie strictly below the egg alone's"
        } else {
            "not adopted: the mixture's validation bytes with its charges do not lie strictly below the egg alone's"
        }
    );
    println!("wall time in all: {} ms", clock.elapsed().as_millis());
}
