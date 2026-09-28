//! **`u2`: U2's acceptance run of F0's memory** (`docs/plans/THE_REBUILD.md`, U2; the pins are
//! `research/records/2026-09-28_U2_F0S_MEMORY_ACCEPTANCE_RUN_PINNED_BEFORE_ITS_SPLIT_IS_READ.md`, §1,
//! committed before the split was generated; #63, #73, #148). Included by `hnn_population.rs` as its
//! `u2-acceptance` mode; a committed command run once in release, never a test. It prints counts,
//! codes and bytes only; no text of the cut.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_population -- u2-acceptance .local/cuts/curated-u2-passage-cut.bin .local/cuts/curated-u2-passage-flat-cut.bin
//! ```
//!
//! [definition; agent-inferred, the record's pins] **What it executes.**
//! - **The receiver**: the conditional byte-and-stop code at `L_R = 16`: every byte cell's face, and
//!   at each response's stop (a section letter whose open part is on the agent channel) the face's
//!   mass on the section letters; the letter given the stop, the human closes, the request's pointer
//!   and the letter at the families' join are observed and charged to neither side. At each stop the
//!   face read is checked equal to the face the egg charges when the letter arrives.
//! - **The candidates**, F0's admitted egg (`f0-egg`'s constructor before U2, the hazard partition
//!   learned on the choosing cells) with its byte tree (0) at the deepest depth its carriers admit,
//!   (1) the same with the once-reached leaf chains released at each aeon boundary (each `open`
//!   letter before it is read, the families' join, the passage's close), (2) declared at `D = 12`
//!   ticks. [historical] (1) was not admissible on the choosing families and is retired: its release
//!   (`Landmarks::release_once_reached`, `compression::landmark::context::once_reached`, delegated
//!   through the eggs) and this mode's path for it are at commit `d31c8b37`, where the run was made.
//!   The mode now reads (0) and (2), which is the same choice.
//! - **The choice** on the choosing families alone: admissible when `C_k + 2 − C_0 ≤ m` (the
//!   difference's upper end), the least standing among the admissible, ties to the lower index; the
//!   chosen candidate charged `⌈log₂ 3⌉ = 2` bits, (0) nothing.
//! - **The validation reading, once**: the chosen candidate and (0) (or (0) alone), then the flat
//!   tree (`D = 48`) over the flat twin.
//! - **The standing**: the egg's canonical checkpoint (`Family::admitted_checkpoint`, as the census),
//!   whole; the readings kept beside the state, 44 bytes a byte-tree node (its certificates, cached
//!   stop weight and rebase count); and the standing without them.
//! - **The acceptance**: the chosen candidate's standing after the passage strictly below (0)'s, and
//!   `V_chosen + 2 − V_0 ≤ m` decided on the enclosures. The standing budget (1,298 bytes a cell) is
//!   read beside it for F0's gate.
//! - **The guards**: a passage past 600,000 ms or a resident set past 20,000,000,000 bytes stops the
//!   run; its partial evidence is printed as incomplete.

use std::ops::Range;
use std::time::Instant;

use holonics::compression::landmark::context::{LetterFamily, PassageCode, SectionChart};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use holonics::receiver::population::{
    AdmittedEgg, Family, HazardPartition, TreeFamily, learn_hazard_partition,
};
use num_bigint::BigInt;

use super::curated::{
    FLAT_DEPTH, TYPED_DEPTHS, admitted_egg_at, declaration, deepest, joined, point, sum,
    typed_declaration,
};
use super::exterior::{
    against, enclosure, per, read_curated, read_cut, read_incidence, reading_of, resident_set,
};

/// The margin `m` in bits (the record's pin 6: `⌊G/2⌋` of F0's gain over flat on unseen bytes).
const MARGIN: u64 = 1214;

/// The standing budget in bytes a cell (pin 7: the flat control's standing on F4's passage).
const BUDGET: u64 = 1298;

/// The candidates, and the choice's charge `⌈log₂ 3⌉`. (1) is retired (module header); the mode
/// reads (0) and (2).
const CANDIDATES: [&str; 3] = [
    "(0) the unmerged tree",
    "(1) once-reached leaf chains released at the aeon boundary",
    "(2) the depth cut at 12 ticks",
];
const CHOICE: u64 = 2;

/// The depth cut's depth in ticks: candidate (2), adopted for F0's egg (`curated::F0_BYTE_DEPTH`).
pub(super) const CUT: usize = 12;

/// The readings a byte-tree node's chart keeps beside the state (the census's E0).
const READING_BYTES: u64 = 44;

/// The guards: a passage's milliseconds, and the resident set's bytes.
const PASSAGE_MS: u128 = 600_000;
const RESIDENT: u128 = 20_000_000_000;
const GUARD_EVERY: usize = 1 << 14;

/// The agent channel (the curated chart's channels: human, agent, tool).
const AGENT: usize = 1;
const CHANNELS: [&str; 3] = ["human", "agent", "tool"];

/// **One role's conditional byte-and-stop code** on one candidate: each channel's bytes and the
/// response stops, each a product of faces enclosed once.
struct Code {
    bytes: [PassageCode; 3],
    stops: PassageCode,
    byte_cells: [u64; 3],
    stop_cells: u64,
}

impl Code {
    fn new() -> Self {
        Self {
            bytes: [PassageCode::new(), PassageCode::new(), PassageCode::new()],
            stops: PassageCode::new(),
            byte_cells: [0; 3],
            stop_cells: 0,
        }
    }

    /// The bytes and the stops together.
    fn total(&self) -> ExactInterval {
        joined(self.bytes.iter().chain([&self.stops]))
    }

    fn bytes_only(&self) -> ExactInterval {
        joined(&self.bytes)
    }

    fn channel(&self, c: usize) -> ExactInterval {
        joined([&self.bytes[c]])
    }

    fn stops(&self) -> ExactInterval {
        joined([&self.stops])
    }
}

/// A candidate: its index among [`CANDIDATES`] and its egg.
struct Candidate {
    index: usize,
    egg: AdmittedEgg,
}

/// The standing: the egg's canonical checkpoint bytes and its byte tree's nodes.
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

    fn print(&self, label: &str, cells: u64) {
        let bare = self.whole - self.readings();
        println!(
            "    {label}: whole {} bytes ({} a cell, remainder {}); the readings beside the state {} bytes ({} byte-tree nodes, {} a cell, remainder {}); without them {} bytes ({} a cell, remainder {})",
            self.whole,
            self.whole / cells,
            self.whole % cells,
            self.readings(),
            self.nodes,
            self.readings() / cells,
            self.readings() % cells,
            bare,
            bare / cells,
            bare % cells
        );
        println!(
            "      against the standing budget of {BUDGET} bytes a cell: whole {}, without the readings {}",
            if self.whole <= BUDGET * cells {
                "within"
            } else {
                "past"
            },
            if bare <= BUDGET * cells {
                "within"
            } else {
                "past"
            }
        );
    }
}

/// Why a passage stopped: a guard passed.
enum Stopped {
    Time(u128),
    Memory(u128),
}

fn guard(clock: &Instant) -> Result<(), Stopped> {
    let elapsed = clock.elapsed().as_millis();
    if elapsed > PASSAGE_MS {
        return Err(Stopped::Time(elapsed));
    }
    if let Some((now, _)) = resident_set()
        && now > RESIDENT
    {
        return Err(Stopped::Memory(now));
    }
    Ok(())
}

/// **One candidate reads one role's cells** (module header), charging each byte and each response's
/// stop; the letter at the join closes a choosing part and is charged to neither role.
fn read_role(
    candidate: &mut Candidate,
    codes: &[usize],
    open_before: &[Option<usize>],
    range: Range<usize>,
    join: usize,
    chart: SectionChart,
) -> Result<(Code, u128), Stopped> {
    let clock = Instant::now();
    let mut code = Code::new();
    for t in range {
        let cell = codes[t];
        if chart.section(cell).is_some() {
            if t != join && open_before[t] == Some(AGENT) {
                let face = Family::face(&candidate.egg).expect("the egg's face");
                let mass: Rat = face[chart.bytes()..].iter().sum();
                let charged = Family::receive(&mut candidate.egg, cell).expect("a letter");
                assert_eq!(
                    face[cell], charged,
                    "the stop's face is the face the egg charges"
                );
                code.stops.face(&mass).expect("a positive stop mass");
                code.stop_cells += 1;
            } else {
                Family::receive(&mut candidate.egg, cell).expect("a letter");
            }
        } else {
            let face = Family::receive(&mut candidate.egg, cell).expect("a byte");
            let channel = open_before[t].expect("a byte lies in an open part");
            code.bytes[channel]
                .face(&face)
                .expect("a positive face");
            code.byte_cells[channel] += 1;
        }
        if (t + 1) % GUARD_EVERY == 0 {
            guard(&clock)?;
        }
    }
    guard(&clock)?;
    Ok((code, clock.elapsed().as_millis()))
}

/// `a − b`, enclosed: `[a.lower − b.upper, a.upper − b.lower]`.
fn minus(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower - &b.upper,
        upper: &a.upper - &b.lower,
    }
}

/// The difference against the margin: within (its upper end at most `m`), past (its lower end
/// above), or undecided.
fn within_margin(delta: &ExactInterval) -> &'static str {
    let m = Rat::from_integer(BigInt::from(MARGIN));
    if delta.upper <= m {
        "within m"
    } else if delta.lower > m {
        "past m"
    } else {
        "undecided against m"
    }
}

fn difference_line(label: &str, a: &ExactInterval, b: &ExactInterval, cells: u64) {
    let delta = minus(a, b);
    println!(
        "    {label}: {}; difference {}, a cell {}",
        against(a, b),
        enclosure(&delta, super::GRAIN),
        per(&delta, cells, super::GRAIN)
    );
}

fn stopped(what: &str, why: Stopped) -> ! {
    let why = match why {
        Stopped::Time(ms) => format!("the passage reached {ms} ms, past {PASSAGE_MS}"),
        Stopped::Memory(bytes) => format!("the resident set reached {bytes} bytes, past {RESIDENT}"),
    };
    panic!(
        "STOPPED at {what}: {why}; resident set (now, peak) {:?} bytes; the partial evidence above is incomplete",
        resident_set()
    );
}

fn print_code(code: &Code, grain: u64) {
    for (c, name) in CHANNELS.iter().enumerate() {
        println!(
            "      {name} bytes ({}): {}",
            code.byte_cells[c],
            reading_of(&code.channel(c), grain)
        );
    }
    println!(
        "      response stops ({}): {}",
        code.stop_cells,
        reading_of(&code.stops(), grain)
    );
    println!(
        "      bytes {}; bytes and stops {}",
        reading_of(&code.bytes_only(), grain),
        enclosure(&code.total(), grain)
    );
}

/// **U2's acceptance run** (module header).
#[allow(clippy::too_many_lines)]
pub fn acceptance(curated_path: &str, flat_path: &str) {
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
    println!(
        "hnn_population u2-acceptance: U2's acceptance run of F0's memory (the record's pins; #63, #73, #148)"
    );
    println!(
        "0. the passage: {cells} curated cells (|A| = {}), the first {development} the choosing families; {flat_count} flat cells; n* = {}, L_R = {grain}",
        chart.alphabet(),
        cut.population,
    );
    println!(
        "  m = {MARGIN} bits; the choice charged {CHOICE} bits; the standing budget {BUDGET} bytes a cell; guards {PASSAGE_MS} ms a passage, {RESIDENT} bytes resident"
    );

    // 1. The partition, learned on the choosing cells alone (the census's and f0-egg's).
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
    let deepest_depth = deepest(&typed_declaration(
        chart,
        TYPED_DEPTHS[TYPED_DEPTHS.len() - 1],
        cut.population,
        grain,
    ));
    let egg = |depth: usize| {
        admitted_egg_at(
            chart,
            cut.population,
            grain,
            partition.clone(),
            relations.clone(),
            &comparisons,
            0,
            depth,
        )
        .expect("the admitted egg")
    };
    let mut candidates: Vec<Candidate> = [(0, deepest_depth), (2, CUT)]
        .into_iter()
        .map(|(index, depth)| Candidate {
            index,
            egg: egg(depth),
        })
        .collect();
    println!(
        "1. the candidates (the byte tree: (0) at D = {deepest_depth} ticks, (2) at D = {CUT}; (1) retired, its run at commit d31c8b37); setup {} ms",
        clock.elapsed().as_millis()
    );
    println!();

    // 2. The choosing families, each candidate once.
    println!("2. the choosing families ({development} cells), each candidate:");
    let mut choosing: Vec<(Code, Standing)> = Vec::new();
    for candidate in &mut candidates {
        let (code, ms) = match read_role(
            candidate,
            &cut.codes,
            &open_before,
            0..development,
            development,
            chart,
        ) {
            Ok(read) => read,
            Err(why) => stopped(CANDIDATES[candidate.index], why),
        };
        let standing = Standing::of(&candidate.egg);
        println!(
            "  {}: {ms} ms; resident set (now, peak) {:?} bytes",
            CANDIDATES[candidate.index],
            resident_set()
        );
        print_code(&code, grain);
        standing.print(
            "the standing after the choosing families",
            development as u64,
        );
        choosing.push((code, standing));
    }
    let totals: Vec<ExactInterval> = choosing.iter().map(|(code, _)| code.total()).collect();
    println!("  the choice (admissible when C_k + {CHOICE} − C_0 ≤ m; the least standing among them):");
    let (mut chosen, mut chosen_at) = (0, 0);
    for (at, candidate) in candidates.iter().enumerate() {
        let k = candidate.index;
        let charged = if k == 0 {
            totals[at].clone()
        } else {
            sum(&totals[at], &point(CHOICE))
        };
        let delta = minus(&charged, &totals[0]);
        let admissible = k == 0
            || delta.upper <= Rat::from_integer(BigInt::from(MARGIN));
        println!(
            "    {}: C_k{} − C_0 {}; {}; standing {} bytes",
            CANDIDATES[k],
            if k == 0 { "" } else { " + 2" },
            enclosure(&delta, grain),
            if admissible {
                "admissible"
            } else {
                "not admissible"
            },
            choosing[at].1.whole
        );
        if admissible && choosing[at].1.whole < choosing[chosen_at].1.whole {
            (chosen, chosen_at) = (k, at);
        }
    }
    println!("  chosen: {}", CANDIDATES[chosen]);
    drop(choosing);
    candidates.retain(|candidate| candidate.index == 0 || candidate.index == chosen);
    println!();

    // 3. The validation families, once: (0) and the chosen candidate.
    println!(
        "3. the validation families ({} cells), read once:",
        cells - development
    );
    let mut validation: Vec<(Code, Standing)> = Vec::new();
    for candidate in &mut candidates {
        let (code, ms) = match read_role(
            candidate,
            &cut.codes,
            &open_before,
            development..cells,
            development,
            chart,
        ) {
            Ok(read) => read,
            Err(why) => stopped(CANDIDATES[candidate.index], why),
        };
        let standing = Standing::of(&candidate.egg);
        println!(
            "  {}: {ms} ms; resident set (now, peak) {:?} bytes",
            CANDIDATES[candidate.index],
            resident_set()
        );
        print_code(&code, grain);
        standing.print("the standing after the passage", cells as u64);
        validation.push((code, standing));
    }
    drop(candidates);

    // 4. The flat tree over the flat twin, once.
    let flat_clock = Instant::now();
    let mut flat_tree = TreeFamily::new(
        declaration(256, FLAT_DEPTH, cut.population, grain, LetterFamily::cells()),
        0,
    )
    .expect("the flat tree");
    let mut flat = [PassageCode::new(), PassageCode::new()];
    for (position, &byte) in flat_bytes.iter().enumerate() {
        let face = flat_tree
            .receive(usize::from(byte))
            .expect("a byte of the flat chart");
        flat[usize::from(position >= flat_held.start)]
            .face(&face)
            .expect("a positive face");
        if (position + 1) % GUARD_EVERY == 0
            && let Err(why) = guard(&flat_clock)
        {
            stopped("the flat tree", why);
        }
    }
    let flat_standing = flat_tree.encode_checkpoint().len() as u64;
    println!(
        "4. the flat tree at D = {FLAT_DEPTH} over the flat twin: {} ms; its standing {flat_standing} bytes after {flat_count} cells ({} a cell, remainder {}); resident set (now, peak) {:?} bytes",
        flat_clock.elapsed().as_millis(),
        flat_standing / flat_count as u64,
        flat_standing % flat_count as u64,
        resident_set()
    );
    let flat_validation = joined([&flat[1]]);
    println!(
        "  the flat tree's validation bytes ({}): {}",
        flat_count - flat_held.start,
        enclosure(&flat_validation, grain)
    );
    println!();

    // 5. The receipt.
    let unmerged = &validation[0];
    let (chosen_code, chosen_standing) = {
        let last = &validation[validation.len() - 1];
        (&last.0, &last.1)
    };
    let validation_bytes: u64 = unmerged.0.byte_cells.iter().sum();
    println!("5. the receipt (validation):");
    println!("  the chosen candidate: {}", CANDIDATES[chosen]);
    let charge = if chosen == 0 { 0 } else { CHOICE };
    let chosen_total = sum(&chosen_code.total(), &point(charge));
    let chosen_bytes = sum(&chosen_code.bytes_only(), &point(charge));
    difference_line(
        &format!("its bytes and stops, charged {charge} bits, against the unmerged tree's"),
        &chosen_total,
        &unmerged.0.total(),
        validation_bytes + unmerged.0.stop_cells,
    );
    println!(
        "      against the margin m = {MARGIN} bits: {}",
        within_margin(&minus(&chosen_total, &unmerged.0.total()))
    );
    for (c, name) in CHANNELS.iter().enumerate() {
        if unmerged.0.byte_cells[c] > 0 {
            difference_line(
                &format!("  {name} bytes against the unmerged tree's"),
                &chosen_code.channel(c),
                &unmerged.0.channel(c),
                unmerged.0.byte_cells[c],
            );
        }
    }
    difference_line(
        "  response stops against the unmerged tree's",
        &chosen_code.stops(),
        &unmerged.0.stops(),
        unmerged.0.stop_cells.max(1),
    );
    difference_line(
        &format!("its bytes, charged {charge} bits, against the flat tree's"),
        &chosen_bytes,
        &flat_validation,
        validation_bytes,
    );
    difference_line(
        &format!("its bytes and stops, charged {charge} bits, against the flat tree's bytes"),
        &chosen_total,
        &flat_validation,
        validation_bytes,
    );
    if chosen != 0 {
        difference_line(
            "the unmerged tree's bytes against the flat tree's",
            &unmerged.0.bytes_only(),
            &flat_validation,
            validation_bytes,
        );
        difference_line(
            "the unmerged tree's bytes and stops against the flat tree's bytes",
            &unmerged.0.total(),
            &flat_validation,
            validation_bytes,
        );
    }
    println!("  the standing a cell after the passage ({cells} cells):");
    unmerged.1.print("the unmerged tree", cells as u64);
    if chosen != 0 {
        chosen_standing.print(CANDIDATES[chosen], cells as u64);
    }
    let falls = chosen != 0 && chosen_standing.whole < unmerged.1.whole;
    let delta = minus(&chosen_total, &unmerged.0.total());
    let within = delta.upper <= Rat::from_integer(BigInt::from(MARGIN));
    println!(
        "  acceptance (the standing a cell falls strictly while the code stays within m = {MARGIN} bits): the standing {}; the code {}; {}",
        if falls {
            "falls strictly"
        } else {
            "does not fall"
        },
        within_margin(&delta),
        if falls && within {
            "PASSES"
        } else {
            "FAILS: the unmerged tree stays"
        }
    );
    println!(
        "wall time in all: {} ms; resident set (now, peak) {:?} bytes",
        clock.elapsed().as_millis(),
        resident_set()
    );
}
