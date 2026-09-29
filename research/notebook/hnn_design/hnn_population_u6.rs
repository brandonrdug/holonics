//! **`u6`: U6 item 2, the symmetric comparison, read once on the conversation split**
//! (`docs/plans/THE_REBUILD.md` U6; the audit of September 29, §4 item 2; the pins are
//! `research/records/2026-09-29_U6_THE_SYMMETRIC_COMPARISON_PINNED_BEFORE_ITS_VALIDATION_ROLE_IS_READ.md`,
//! §1, committed before the validation role's stream was generated; #63, #73, #148). Included by
//! `hnn_population.rs` as its `u6-symmetric` mode; a committed command run once in release, never a
//! test. It prints counts, codes, bytes and times only; the releases' text goes to an owner-only file
//! (`none` skips the releases).
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_population -- u6-symmetric .local/cuts/curated-u6-passage-cut.bin .local/cuts/u6-symmetric-releases.json
//! ```
//!
//! [definition; agent-inferred, the record's pins] **What it executes.**
//! - **Same context, same events.** Both sides read every cell of the joined passage, the choosing
//!   role and then the validation role, over the one 268-symbol chart (`SectionChart::curated`):
//!   every byte, every section letter and so every end. Each cell is scored by the side's face
//!   before its own deposit, and each side enters every conversation's aeon at the letter that opens
//!   its part, reading that letter in the leaving aeon's address (the passage's `aeons.bin`; the
//!   aeon's ordinal is exterior codec information given to both, and it cancels).
//! - **The candidate**: F0's admitted egg (`admitted_egg_at` at [`F0_BYTE_DEPTH`] = 12 ticks: the
//!   channel-typed byte tree, the letter tree, the part clock and hazard on the partition learned on
//!   the choosing cells alone, the request's copy stage and pointer), read through its `Family` law.
//! - **The control**: the context tree over the same stream, its address the cells alone (no slots,
//!   `SectionSlots::Cells`), at the flat tree's recorded depth [`FLAT_DEPTH`] = 48, the `½` stop
//!   prior, entering the same aeons at the same letters (`TreeFamily::sectioned`).
//! - **Symmetric charges.** Every letter is coded by both, so the letters' identity, the human parts'
//!   closes and the channel every typed context reads are paid for in the stream. The candidate is
//!   further charged the request's pointer on the validation role (the incidence it reads: the
//!   information the cells do not carry, coded at each reading part's letter), the development
//!   sweep's 17 bits (its byte tree among 3, which is the choice of channel-typed contexts; the
//!   hazard among 47; the letter tree among 11; the copy law among 8; the pointer's code among 3),
//!   F0's adoption decisions' 5 bits and the learned partition's description. The control is charged
//!   its recorded depth sweep, `⌈log₂ 5⌉ = 3` bits. The later human return's pointer enters no face
//!   (a receipt only), so it is reported beside and charged to neither.
//! - **The event kinds.** A byte by its channel, and a section letter by its kind: *a response's end*
//!   (a `turn` or `part` letter opening a human part after an agent part), *a record boundary within
//!   a turn* (any other `part` letter), *a turn* (any other `turn` letter), *a switch* and *an
//!   opening*. Each letter's code splits exactly into the end (the face's mass on the letters at that
//!   tick) and the letter given the end.
//! - **The acceptance**: the charged difference (candidate − control) on the validation role, its
//!   upper end strictly below `−m`, [`MARGIN`] `= 534` bits. An enclosure that straddles `−m` fails.
//! - **Beside it, deciding nothing**: the whole state of each side after the passage against 1,298
//!   bytes a cell (no reading subtracted); each validation reading against 600,000 ms and the peak
//!   resident set against 20,000,000,000 bytes (the guards stop the run past them); each release's
//!   complete warm response (its branch and its draws) against 60,000 ms; each validation
//!   conversation's own difference; the letters that close an agent part (F0's stops) by kind.
//! - **The releases**: at the [`RELEASES`] validation responses lowest by `Draw::new(RELEASE_SEED +
//!   v).next()` among the eligible (F0's rule), each side is branched at its standing after the
//!   response's opening letter (the candidate at the present incidence) and released alone under the
//!   scored law with the same keys and the same cap, [`RELEASE_CAP`] bytes and the aperture's room,
//!   each stopping at its own drawn section letter. Neither is given the logged reply's length. The
//!   logged reply (observed conduct, never a target) is written beside them to the owner-only file.

use std::collections::BTreeMap;
use std::time::Instant;

use holonics::compression::landmark::context::{
    LetterFamily, PassageCode, SectionChart, SectionSlots, Sections, sections::Section,
};
use holonics::holarchy::terrain::Draw;
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use holonics::receiver::population::{
    AdmittedEgg, Family, HazardPartition, Population, RelationKind, ResponseLaw, TreeFamily,
    learn_hazard_partition,
};
use holonics::receiver::release::ReleaseReturn;

use super::curated::{
    F0_BYTE_DEPTH, FLAT_DEPTH, FLAT_SWEEP, PROBED, admitted_egg_at, bits, ceil_log2, declaration,
    joined, point, sum,
};
use super::exterior::{
    RESERVE_SHA256, against, enclosure, per, read_aeons, read_curated, read_incidence, reading_of,
    reserve_read, resident_set,
};
use super::f0::{
    DECISIONS, Selected, admitted, guard, json_text, key_of, minus, part_bytes, pointer,
    refusal_name, select, stopped, write_private,
};

/// **The margin `m` in bits** (pin 5): F0's range of the spent family draws (its pin 6 and §2:
/// from F1's `−279 + 10/16 + ε` to U2's `−812 + 9/16 + ε`, `533 + 1/16 + ε`, rounded up), unchanged.
pub(super) const MARGIN: u64 = 534;

/// The standing budget in bytes a cell (F0's pin 7).
const BUDGET: u64 = 1298;

/// The passage budget (F0's pin 8) and the warm response budget (F4's).
const PASSAGE_MS: u128 = 600_000;
const RESIDENT: u128 = 20_000_000_000;
const WARM_MS: u128 = 60_000;
const GUARD_EVERY: usize = 1 << 14;

/// The releases (pin 8): how many, the seed of their order keys, the cap in bytes (F0's).
const RELEASES: usize = 8;
const RELEASE_SEED: u64 = 20_260_929;
const RELEASE_CAP: usize = 2048;

/// The curated chart's channels and section kinds (`SectionChart::curated`).
const HUMAN: usize = 0;
const AGENT: usize = 1;
const CHANNELS: [&str; 3] = ["human", "agent", "tool"];
const OPEN: usize = 0;
const SWITCH: usize = 1;
const PART: usize = 3;

/// **The event kinds of a section letter** (module header), in the order printed.
const KINDS: [&str; 5] = [
    "a response's end (a human part follows an agent part)",
    "a record boundary within a turn",
    "a turn",
    "a switch",
    "an opening",
];
const RESPONSE_END: usize = 0;
const RECORD: usize = 1;
const TURN: usize = 2;
const SWITCHED: usize = 3;
const OPENING: usize = 4;

/// A letter's event kind: its section and the channel of the part it closes.
fn event_kind(section: Section, closed: Option<usize>) -> usize {
    match section.kind {
        OPEN => OPENING,
        SWITCH => SWITCHED,
        _ if section.channel == HUMAN && closed == Some(AGENT) => RESPONSE_END,
        PART => RECORD,
        _ => TURN,
    }
}

/// **One side's code of the validation role, by event**: each channel's bytes; each kind's letters,
/// their ends and the letters given the ends, and the letters closing an agent part (F0's stops);
/// each conversation's cells.
struct Side {
    bytes: [PassageCode; 3],
    byte_cells: [u64; 3],
    letters: [PassageCode; 5],
    ends: [PassageCode; 5],
    given: [PassageCode; 5],
    letter_cells: [u64; 5],
    agent_closes: [PassageCode; 5],
    agent_close_cells: [u64; 5],
    aeons: BTreeMap<u64, PassageCode>,
}

impl Side {
    fn new() -> Self {
        Self {
            bytes: [PassageCode::new(); 3],
            byte_cells: [0; 3],
            letters: [PassageCode::new(); 5],
            ends: [PassageCode::new(); 5],
            given: [PassageCode::new(); 5],
            letter_cells: [0; 5],
            agent_closes: [PassageCode::new(); 5],
            agent_close_cells: [0; 5],
            aeons: BTreeMap::new(),
        }
    }

    /// Score one validation cell before its deposit, then deposit it.
    fn read<F: Family + ?Sized>(
        &mut self,
        family: &mut F,
        chart: SectionChart,
        cell: usize,
        open: Option<usize>,
        aeon: u64,
    ) {
        let face = match chart.section(cell) {
            Some(section) => {
                let kind = event_kind(section, open);
                let face = family.face().expect("the face before the letter");
                let mass: Rat = face[chart.bytes()..].iter().sum();
                let charged = family.receive(cell).expect("a letter");
                assert_eq!(
                    face[cell], charged,
                    "the letter's face is the face the side charges"
                );
                self.letters[kind].face(&charged).expect("a positive face");
                self.ends[kind].face(&mass).expect("a positive end");
                self.given[kind]
                    .face(&(&charged / &mass))
                    .expect("a positive letter given the end");
                self.letter_cells[kind] += 1;
                if open == Some(AGENT) {
                    self.agent_closes[kind]
                        .face(&charged)
                        .expect("a positive face");
                    self.agent_close_cells[kind] += 1;
                }
                charged
            }
            None => {
                let channel = open.expect("a byte lies in an open part");
                let face = family.receive(cell).expect("a byte");
                self.bytes[channel].face(&face).expect("a positive face");
                self.byte_cells[channel] += 1;
                face
            }
        };
        self.aeons
            .entry(aeon)
            .or_default()
            .face(&face)
            .expect("a positive face");
    }

    fn all_bytes(&self) -> ExactInterval {
        joined(&self.bytes)
    }

    fn all_letters(&self) -> ExactInterval {
        joined(&self.letters)
    }

    fn cells(&self) -> ExactInterval {
        joined(self.bytes.iter().chain(&self.letters))
    }
}

/// One side's release at a response: its status, bytes and times.
struct Released {
    status: String,
    bytes: Vec<u8>,
    released: bool,
    cells: usize,
    branch_ms: u128,
    warm_ms: u128,
}

/// **Release one side alone** from `branch` (already its standing after the response's opening
/// letter, branched at the present), in a population named by 0 bits, under the scored law, the cap
/// `room` bytes and its stop; `clock` started before the branch, so the warm time is complete.
fn release_alone(
    branch: Box<dyn Family>,
    chart: SectionChart,
    room: usize,
    key: u64,
    clock: Instant,
) -> Released {
    let branch_ms = clock.elapsed().as_millis();
    let mut alone = Population::new(vec![branch]).expect("one family alone, named by 0 bits");
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
    Released {
        released: status == "released",
        status,
        cells: release.emitted(),
        bytes: release.bytes,
        branch_ms,
        warm_ms: clock.elapsed().as_millis(),
    }
}

/// The passage's reading of one side: each role's milliseconds (releases apart), the releases, and
/// the state after the passage.
struct Pass {
    reading_ms: [u128; 2],
    releasing_ms: u128,
    releases: Vec<Option<Released>>,
    standing: u64,
    resident: Option<(u128, u128)>,
}

/// The passage's shape, read once from the cut: each cell's aeon (a letter's: the aeon whose part it
/// opens), the channel open before it, and the aeon marks.
struct Shape {
    codes: Vec<usize>,
    development: usize,
    population: usize,
    aeon_of: Vec<u64>,
    open_before: Vec<Option<usize>>,
    marks: BTreeMap<usize, u64>,
}

/// **Read one side over the whole passage** (module header): the choosing role, then the validation
/// role scored by events; at each selected response's letter the side is released from its standing.
#[allow(clippy::too_many_arguments)]
fn pass<F: Family>(
    name: &str,
    family: &mut F,
    enter: impl Fn(&mut F, u64),
    branch: impl Fn(&F) -> Box<dyn Family>,
    standing: impl Fn(&F) -> u64,
    at_join: &mut dyn FnMut(&F),
    shape: &Shape,
    chart: SectionChart,
    selected: &[Selected],
    side: &mut Side,
) -> Pass {
    let at_letter: BTreeMap<usize, usize> = selected
        .iter()
        .enumerate()
        .map(|(order, chosen)| (chosen.letter, order))
        .collect();
    let mut releases: Vec<Option<Released>> = (0..selected.len()).map(|_| None).collect();
    let mut reading_ms = [0u128; 2];
    let mut releasing_ms = 0u128;
    let cells = shape.codes.len();
    for (role, range) in [
        (0usize, 0..shape.development),
        (1, shape.development..cells),
    ] {
        if role == 1 {
            at_join(family);
        }
        let passage = Instant::now();
        let mut releasing = 0u128;
        for t in range {
            let cell = shape.codes[t];
            if let Some(&aeon) = shape.marks.get(&t) {
                enter(family, aeon);
            }
            if role == 1 {
                side.read(family, chart, cell, shape.open_before[t], shape.aeon_of[t]);
            } else {
                family.receive(cell).expect("a choosing cell");
            }
            if let Some(&order) = at_letter.get(&t) {
                let clock = Instant::now();
                let room = RELEASE_CAP.min(shape.population - (t + 1) - 1);
                let released =
                    release_alone(branch(family), chart, room, selected[order].key, clock);
                releasing += released.warm_ms;
                releases[order] = Some(released);
            }
            if (t + 1) % GUARD_EVERY == 0
                && let Err(why) = guard(passage.elapsed().as_millis() - releasing)
            {
                stopped(name, why);
            }
        }
        reading_ms[role] = passage.elapsed().as_millis() - releasing;
        releasing_ms += releasing;
        if let Err(why) = guard(reading_ms[role]) {
            stopped(name, why);
        }
    }
    Pass {
        reading_ms,
        releasing_ms,
        releases,
        standing: standing(family),
        resident: resident_set(),
    }
}

/// A row of the table: the count, each side's code, the difference, and each side a count.
fn row(label: &str, count: u64, candidate: &ExactInterval, control: &ExactInterval) {
    let grain = super::GRAIN;
    println!(
        "  {label} ({count}): candidate {}; control {}; candidate − control {} ({}); a count, candidate {}, control {}",
        reading_of(candidate, grain),
        reading_of(control, grain),
        reading_of(&minus(candidate, control), grain),
        against(candidate, control),
        per(candidate, count, grain),
        per(control, count, grain)
    );
}

/// **U6 item 2's run** (module header).
#[allow(clippy::too_many_lines)]
pub fn symmetric(curated_path: &str, releases_path: &str) {
    let clock = Instant::now();
    let grain = super::GRAIN;
    let chart = SectionChart::curated();
    let cut = read_curated(curated_path, &chart);
    let relations = read_incidence(curated_path);
    let marks: BTreeMap<usize, u64> = read_aeons(curated_path, &cut.codes, &chart)
        .into_iter()
        .collect();
    assert!(
        !marks.is_empty(),
        "the passage carries its aeons (U6: each conversation's context its own)"
    );
    let development = cut.held.start;
    let cells = cut.codes.len();
    let population = usize::try_from(cut.population).expect("the aperture fits a machine word");
    let mut aeon_of = Vec::with_capacity(cells);
    let mut open_before = Vec::with_capacity(cells);
    let (mut aeon, mut open) = (0u64, None);
    for (t, &code) in cut.codes.iter().enumerate() {
        if let Some(&entered) = marks.get(&t) {
            aeon = entered;
        }
        aeon_of.push(aeon);
        open_before.push(open);
        if let Some(section) = chart.section(code) {
            open = Some(section.channel);
        }
    }
    let shape = Shape {
        codes: cut.codes.clone(),
        development,
        population,
        aeon_of,
        open_before,
        marks,
    };
    let with_releases = releases_path != "none";
    let choosing_aeons: std::collections::BTreeSet<u64> =
        shape.aeon_of[..development].iter().copied().collect();
    let validation_aeons: std::collections::BTreeSet<u64> =
        shape.aeon_of[development..].iter().copied().collect();
    assert!(
        choosing_aeons.is_disjoint(&validation_aeons),
        "no conversation lies in both roles"
    );
    println!(
        "hnn_population u6-symmetric: U6 item 2, the symmetric comparison on the conversation split (the record's pins; #63, #73, #148)"
    );
    println!(
        "0. the passage: {cells} cells (|A| = {}), the first {development} the choosing role's ({} conversations), the rest the validation role's ({} conversations); n* = {population}, L_R = {grain}; {} aeon changes",
        chart.alphabet(),
        choosing_aeons.len(),
        validation_aeons.len(),
        shape.marks.len()
    );
    println!(
        "  the margin m = {MARGIN} bits; beside: the standing budget {BUDGET} bytes a cell, the passage budget {PASSAGE_MS} ms and {RESIDENT} bytes resident, the warm response {WARM_MS} ms"
    );
    let mut counted = [0u64; 5];
    let mut bytes_counted = [0u64; 3];
    for t in development..cells {
        match chart.section(shape.codes[t]) {
            Some(section) => counted[event_kind(section, shape.open_before[t])] += 1,
            None => bytes_counted[shape.open_before[t].expect("an open part")] += 1,
        }
    }
    println!(
        "  the validation role's events: bytes {} (human {}, agent {}, tool {}); letters {} ({})",
        bytes_counted.iter().sum::<u64>(),
        bytes_counted[0],
        bytes_counted[1],
        bytes_counted[2],
        counted.iter().sum::<u64>(),
        KINDS
            .iter()
            .zip(counted)
            .map(|(kind, count)| format!("{kind} {count}"))
            .collect::<Vec<_>>()
            .join(", ")
    );

    // 1. The partition on the choosing cells alone; the candidate; the charges; the selection.
    let (partition, receipt) =
        learn_hazard_partition(chart, &cut.codes[..development]).expect("the learned partition");
    let classes_only = HazardPartition::learned(partition.classes().to_vec(), BTreeMap::new())
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
    let swept: u64 = PROBED.iter().map(|&count| ceil_log2(count)).sum();
    let decided = ceil_log2(DECISIONS.iter().product());
    let candidate_charge = sum(&point(swept + decided), &receipt.description);
    let control_charge = point(ceil_log2(FLAT_SWEEP));
    let (eligible, selected) = select(
        &shape.codes,
        &relations,
        development,
        population,
        chart,
        RELEASE_SEED,
        RELEASES,
    );
    println!(
        "1. the candidate: the admitted egg (typed byte tree D = {F0_BYTE_DEPTH}, letter tree, part clock and hazard on the partition learned on the choosing cells, copy stage and pointer); charged the sweep's {swept} bits, F0's decisions' {decided} and the partition's description {}: {}",
        reading_of(&receipt.description, grain),
        reading_of(&candidate_charge, grain)
    );
    println!(
        "  the control: the context tree over every byte and letter (no slots) at D = {FLAT_DEPTH}, the ½ stop prior; charged {}",
        reading_of(&control_charge, grain)
    );
    println!(
        "  the declared relations: {} in all; eligible responses in the validation role {eligible}; releases {} (cap {RELEASE_CAP} bytes){}; setup {} ms",
        relations.len(),
        selected.len(),
        if with_releases {
            ""
        } else {
            ", not released (none)"
        },
        clock.elapsed().as_millis()
    );
    let selected = if with_releases { selected } else { Vec::new() };
    println!();

    // 2. The candidate over the passage, once.
    let mut egg: AdmittedEgg = admitted_egg_at(
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
    let mut candidate = Side::new();
    let mut join_readout = None;
    let candidate_pass = pass(
        "the candidate",
        &mut egg,
        |egg, aeon| egg.enter_aeon(aeon).expect("an aeon at its letter"),
        |egg| Box::new(egg.branch_at_present()),
        |egg| {
            egg.admitted_checkpoint()
                .expect("the admitted egg's checkpoint")
                .expect("an encodable standing")
                .len() as u64
        },
        &mut |egg: &AdmittedEgg| join_readout = Some(admitted(egg)),
        &shape,
        chart,
        &selected,
        &mut candidate,
    );
    let end_readout = admitted(&egg);
    let at_join = join_readout.expect("the readout at the join");
    let request_pointer = minus(&pointer(&end_readout), &pointer(&at_join));
    let later_pointer = minus(
        &bits(&end_readout.pointers[RelationKind::LaterHuman.index()].code),
        &bits(&at_join.pointers[RelationKind::LaterHuman.index()].code),
    );
    println!(
        "2. the candidate: choosing {} ms, validation {} ms, its releases {} ms apart; its whole state after the passage {} bytes; resident set (now, peak) {:?} bytes",
        candidate_pass.reading_ms[0],
        candidate_pass.reading_ms[1],
        candidate_pass.releasing_ms,
        candidate_pass.standing,
        candidate_pass.resident
    );
    drop(egg);

    // 3. The control over the passage, once.
    let control_sections = Sections::new(chart, SectionSlots::Cells).expect("no slots");
    let mut tree = TreeFamily::sectioned(
        declaration(
            chart.alphabet(),
            FLAT_DEPTH,
            cut.population,
            grain,
            LetterFamily::cells(),
        ),
        0,
        control_sections,
    )
    .expect("the control");
    let mut control = Side::new();
    let control_pass = pass(
        "the control",
        &mut tree,
        |tree, aeon| tree.enter_aeon(aeon).expect("an aeon at its letter"),
        |tree| Box::new(tree.clone()),
        |tree| tree.encode_checkpoint().len() as u64,
        &mut |_: &TreeFamily| {},
        &shape,
        chart,
        &selected,
        &mut control,
    );
    println!(
        "3. the control: choosing {} ms, validation {} ms, its releases {} ms apart; its whole state after the passage {} bytes; resident set (now, peak) {:?} bytes",
        control_pass.reading_ms[0],
        control_pass.reading_ms[1],
        control_pass.releasing_ms,
        control_pass.standing,
        control_pass.resident
    );
    drop(tree);
    println!();

    // 4. The receipt.
    let validation_cells = (cells - development) as u64;
    println!(
        "4. the receipt: the validation role ({validation_cells} cells, {} conversations), candidate against control",
        validation_aeons.len()
    );
    for (c, channel) in CHANNELS.iter().enumerate() {
        row(
            &format!("{channel} bytes"),
            candidate.byte_cells[c],
            &joined([&candidate.bytes[c]]),
            &joined([&control.bytes[c]]),
        );
    }
    row(
        "every byte",
        candidate.byte_cells.iter().sum(),
        &candidate.all_bytes(),
        &control.all_bytes(),
    );
    for (k, kind) in KINDS.iter().enumerate() {
        row(
            &format!("letters, {kind}"),
            candidate.letter_cells[k],
            &joined([&candidate.letters[k]]),
            &joined([&control.letters[k]]),
        );
        row(
            &format!("    its end (the mass on the letters), {kind}"),
            candidate.letter_cells[k],
            &joined([&candidate.ends[k]]),
            &joined([&control.ends[k]]),
        );
        row(
            &format!("    the letter given the end, {kind}"),
            candidate.letter_cells[k],
            &joined([&candidate.given[k]]),
            &joined([&control.given[k]]),
        );
    }
    row(
        "every letter",
        candidate.letter_cells.iter().sum(),
        &candidate.all_letters(),
        &control.all_letters(),
    );
    row(
        "every cell, uncharged",
        validation_cells,
        &candidate.cells(),
        &control.cells(),
    );
    let zero = point(0);
    row(
        "the request's pointer (the incidence the candidate reads)",
        end_readout.pointers[RelationKind::Request.index()].parts
            - at_join.pointers[RelationKind::Request.index()].parts,
        &request_pointer,
        &zero,
    );
    row(
        "the declared charges",
        1,
        &candidate_charge,
        &control_charge,
    );
    let candidate_total = sum(
        &sum(&candidate.cells(), &request_pointer),
        &candidate_charge,
    );
    let control_total = sum(&control.cells(), &control_charge);
    let charged = minus(&candidate_total, &control_total);
    println!(
        "  THE CHARGED TOTAL: candidate {}; control {}; the charged difference candidate − control {}",
        reading_of(&candidate_total, grain),
        reading_of(&control_total, grain),
        enclosure(&charged, grain)
    );
    let bound = -Rat::from_integer(num_bigint::BigInt::from(MARGIN));
    let (holds, fails) = (charged.upper < bound, charged.lower >= bound);
    println!(
        "  against the margin m = {MARGIN} bits: {}",
        if holds {
            "the upper end lies strictly below −m: the acceptance HOLDS"
        } else if fails {
            "the upper end is not below −m: the acceptance FAILS"
        } else {
            "the enclosure straddles −m: undecided, so the acceptance FAILS"
        }
    );
    println!(
        "  beside: the later human return's pointer, entering no face, charged to neither: {}",
        reading_of(&later_pointer, grain)
    );
    println!("  beside: the letters closing an agent part (F0's stops), by kind:");
    for (k, kind) in KINDS.iter().enumerate() {
        if candidate.agent_close_cells[k] > 0 {
            row(
                &format!("    {kind}"),
                candidate.agent_close_cells[k],
                &joined([&candidate.agent_closes[k]]),
                &joined([&control.agent_closes[k]]),
            );
        }
    }
    println!("  beside: each validation conversation's cells, uncharged, candidate − control:");
    let mut shorter = 0usize;
    for (aeon, code) in &candidate.aeons {
        let theirs = &control.aeons[aeon];
        let (mine, theirs) = (joined([code]), joined([theirs]));
        if mine.upper < theirs.lower {
            shorter += 1;
        }
        println!(
            "    aeon {aeon} ({} cells): {} ({})",
            code.factors(),
            reading_of(&minus(&mine, &theirs), grain),
            against(&mine, &theirs)
        );
    }
    println!(
        "    the candidate is shorter on {shorter} of {} conversations",
        candidate.aeons.len()
    );
    for (name, whole) in [
        ("the candidate", candidate_pass.standing),
        ("the control", control_pass.standing),
    ] {
        println!(
            "  beside: {name}'s whole state {whole} bytes after {cells} cells: {} a cell, remainder {}, {} the budget of {BUDGET}",
            whole / cells as u64,
            whole % cells as u64,
            if whole <= BUDGET * cells as u64 {
                "within"
            } else {
                "past"
            }
        );
    }
    let peak = resident_set().map_or(0, |(_, peak)| peak);
    println!(
        "  beside: the validation readings {} ms (candidate) and {} ms (control) against {PASSAGE_MS}; the peak resident set {peak} bytes against {RESIDENT}: {}",
        candidate_pass.reading_ms[1],
        control_pass.reading_ms[1],
        if candidate_pass.reading_ms[1] <= PASSAGE_MS
            && control_pass.reading_ms[1] <= PASSAGE_MS
            && peak <= RESIDENT
        {
            "within"
        } else {
            "past"
        }
    );

    // 5. The releases, deciding nothing: counts and times here, the text owner-only.
    if with_releases {
        println!();
        println!("5. the releases (deciding nothing; the text owner-only in the release file):");
        let mut cases = Vec::with_capacity(selected.len());
        let mut statuses: [BTreeMap<String, usize>; 2] = [BTreeMap::new(), BTreeMap::new()];
        let mut warm = [Vec::new(), Vec::new()];
        for (order, chosen) in selected.iter().enumerate() {
            let sides = [
                candidate_pass.releases[order]
                    .as_ref()
                    .expect("the candidate released here"),
                control_pass.releases[order]
                    .as_ref()
                    .expect("the control released here"),
            ];
            let reply = part_bytes(&shape.codes, chosen.letter, chart);
            for (s, released) in sides.iter().enumerate() {
                *statuses[s].entry(released.status.clone()).or_default() += 1;
                warm[s].push(released.warm_ms);
            }
            println!(
                "  release {order} (validation tick {}): the candidate {}, {} bytes over {} cells, branch {} ms, warm {} ms; the control {}, {} bytes over {} cells, branch {} ms, warm {} ms; the logged reply {} bytes (UTF-8 {})",
                chosen.letter - development,
                sides[0].status,
                sides[0].bytes.len(),
                sides[0].cells,
                sides[0].branch_ms,
                sides[0].warm_ms,
                sides[1].status,
                sides[1].bytes.len(),
                sides[1].cells,
                sides[1].branch_ms,
                sides[1].warm_ms,
                reply.len(),
                std::str::from_utf8(&reply).is_ok()
            );
            let side_json = |released: &Released| {
                let text = if released.released {
                    json_text(&released.bytes)
                } else {
                    json_text(format!("[typed refusal: {}]", released.status).as_bytes())
                };
                format!(
                    "{{\"text\":{text},\"status\":{},\"valid_utf8\":{},\"bytes\":{},\"emitted\":{},\"warm_ms\":{}}}",
                    json_text(released.status.as_bytes()),
                    std::str::from_utf8(&released.bytes).is_ok(),
                    released.bytes.len(),
                    json_text(&released.bytes),
                    released.warm_ms
                )
            };
            let request = part_bytes(&shape.codes, chosen.target, chart);
            cases.push(format!(
                "{{\"order\":{order},\"validation_tick\":{},\"request\":{},\"responses\":{{\"athena\":{},\"tree\":{},\"logged\":{{\"text\":{},\"valid_utf8\":{},\"bytes\":{}}}}}}}",
                chosen.letter - development,
                json_text(&request),
                side_json(sides[0]),
                side_json(sides[1]),
                json_text(&reply),
                std::str::from_utf8(&reply).is_ok(),
                reply.len()
            ));
        }
        for (s, name) in ["the candidate", "the control"].iter().enumerate() {
            println!(
                "  {name}'s statuses {:?}; complete warm responses: the longest {} ms against {WARM_MS}, in all {} ms",
                statuses[s],
                warm[s].iter().max().copied().unwrap_or(0),
                warm[s].iter().sum::<u128>()
            );
        }
        let excluded = if reserve_read() {
            "null".to_string()
        } else {
            format!("\"{RESERVE_SHA256}\"")
        };
        write_private(
            releases_path,
            &format!(
                "{{\"schema\":\"holonics.u6-symmetric-releases.v1\",\"cap\":{RELEASE_CAP},\"reserve_excluded\":{excluded},\"cases\":[{}]}}\n",
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
