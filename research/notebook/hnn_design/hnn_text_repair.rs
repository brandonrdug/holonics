//! **Text repair by local keys glued on overlaps** (THE_REBUILD U6, "The task is repair, not
//! continuation", its **Text** item; the
//! [record](../../records/2026-10-05_TEXT_REPAIR_BY_LOCAL_KEYS_GLUED_ON_OVERLAPS.md), whose §0 pins
//! every declaration below; #73, #148, #63).
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- executed text-repair <cut> <out dir> <dev|run>
//! ```
//!
//! [definition; agent-inferred, the record's §0] Each passage of 48 bytes of the cut's development
//! range is damaged at the declared cells; from there only the damaged cells are read: the local keys
//! over the cover (regions of 16 at stride 8, distances `[1, 4]`, the byte chart's `2⁸` ports),
//! their gluing, and the restriction per glued region (`compression::keys::local`, the located law
//! of the record's §0 amendment). Beside it, the pinned §0 step 3 ([`pinned_arm`]), read once as the
//! measurement of its certificate failure. Only then is the truth read, to score. Stdout carries counts only; every byte (damaged, repaired and true passages,
//! the released spans, the training text) is written to `<out dir>`, which must be private
//! (`.local/`).

use super::*;
use holonics::compression::keys::local::{
    Cover, GluedRegion, Join, LocalKey, LocalRepair, fibre, locate, relation,
};
use holonics::compression::keys::repair::{CellRelease, DamagedPassage, key_code};
use std::fmt::Write as _;

/// The record's §0 pins.
const LENGTH: usize = 48;
const REGION: usize = 16;
const STRIDE: usize = 8;
const REACH: usize = 4;
const PORTS: usize = 256;
const ERASED: [usize; 12] = [5, 11, 12, 20, 26, 27, 28, 35, 39, 40, 41, 42];
const READ_FIRST: usize = 8192;
const READ_STRIDE: usize = 7024;
const READ_COUNT: usize = 64;
const DEV_FIRST: usize = 6192;
const DEV_COUNT: usize = 4;
const TRAINING: usize = 6144;
const SHOWN: usize = 8;

/// A cell for the eye: printable ASCII as itself, every other byte escaped.
fn shown(byte: usize) -> String {
    match byte {
        0x5c => "\\\\".to_string(),
        0x0a => "\\n".to_string(),
        0x09 => "\\t".to_string(),
        0x20..=0x7e => char::from(u8::try_from(byte).expect("a byte")).to_string(),
        _ => format!("\\x{byte:02x}"),
    }
}

/// Whether a run of known bytes reads as UTF-8, an incomplete sequence at either end excused.
fn utf8_run(run: &[u8]) -> bool {
    let mut start = 0;
    while start < run.len().min(3) && run[start] & 0xc0 == 0x80 {
        start += 1;
    }
    let mut end = run.len();
    for back in 1..=3.min(run.len() - start) {
        let p = run.len() - back;
        let lead = run[p];
        let width = match lead {
            0xc0..=0xdf => 2,
            0xe0..=0xef => 3,
            0xf0..=0xf7 => 4,
            _ => continue,
        };
        if p + width > run.len() {
            end = p;
        }
        break;
    }
    start >= end || std::str::from_utf8(&run[start..end]).is_ok()
}

/// The maximal runs of known cells, and whether each holds a released cell.
fn known_runs(cells: &[Option<usize>], released: &[bool]) -> Vec<(Vec<u8>, bool)> {
    let mut runs = Vec::new();
    let mut current: (Vec<u8>, bool) = (Vec::new(), false);
    for (t, cell) in cells.iter().enumerate() {
        match cell {
            Some(byte) => {
                current.0.push(u8::try_from(*byte).expect("a byte"));
                current.1 |= released[t];
            }
            None => {
                if !current.0.is_empty() {
                    runs.push(std::mem::take(&mut current));
                }
                current.1 = false;
            }
        }
    }
    if !current.0.is_empty() {
        runs.push(current);
    }
    runs
}

/// The longest common substring of two byte strings (the copy length's law, `tools/copy_length.py`).
fn common(a: &[u8], b: &[u8]) -> usize {
    let mut best = 0;
    for i in 0..a.len() {
        for j in 0..b.len() {
            let mut k = 0;
            while i + k < a.len() && j + k < b.len() && a[i + k] == b[j + k] {
                k += 1;
            }
            best = best.max(k);
        }
    }
    best
}

/// [definition; the record's §0, step 3 as pinned, refused by its amendment] **The pinned arm**: a
/// region extends the glued region before it while both are keyed and the joint menus keep a
/// survivor, and a plural glued region restricts through every joint survivor's read relation (the
/// skip-relation index the amendment refuses). It is read once beside the located law to measure the
/// certificate failure the development read found; nothing of it enters the library.
fn pinned_arm(passage: &DamagedPassage, cover: &Cover, joins: &[Join]) -> LocalRepair {
    let cells = passage.cells();
    let regions = cover.regions();
    let keys: Vec<LocalKey> = regions.iter().map(|region| fibre(cells, region, REACH, PORTS).1).collect();
    let mut glued = Vec::new();
    let mut first = 0;
    while first < regions.len() {
        let mut last = first;
        while last + 1 < regions.len()
            && keys[first].keyed()
            && keys[last + 1].keyed()
            && fibre(cells, &(regions[first].start..regions[last + 1].end), REACH, PORTS).1.keyed()
        {
            last += 1;
        }
        let span = regions[first].start..regions[last].end;
        let (menus, key) = fibre(cells, &span, REACH, PORTS);
        let offsets = match &key {
            LocalKey::One(offset) => vec![*offset],
            LocalKey::Plural(offsets) => offsets.clone(),
            LocalKey::Unread | LocalKey::Empty => Vec::new(),
        };
        let members = offsets
            .into_iter()
            .map(|offset| relation(&menus[offset - 1], offset, PORTS).expect("a relation"))
            .collect();
        glued.push(GluedRegion { regions: first..last + 1, span, key, members });
        first = last + 1;
    }
    LocalRepair { keys, joins: joins.to_vec(), glued }
}

#[derive(Default)]
struct Tally {
    keys: [u64; 4],
    joins: [u64; 4],
    glued: u64,
    members: u64,
    refused: u64,
    released: u64,
    right: u64,
    held: u64,
    held_whole: u64,
    held_holds_truth: u64,
    held_sizes: BTreeMap<usize, u64>,
    in_alphabet: u64,
    word_cells: [u64; 2],
    released_word: [u64; 2],
    utf8_damaged: u64,
    utf8_repaired: u64,
    released_runs_valid: u64,
    released_runs: u64,
    residual_bits: u64,
    key_bits: u64,
    codec_refused: u64,
    reopened: u64,
    literal_bits: u64,
    spans: u64,
    span_own_copy: BTreeMap<usize, u64>,
}

/// One arm's reading of one passage: its releases, scored against the truth into its tally; the
/// released spans written to `<out>/spans`. Returns the releases and the passage's line of counts.
#[allow(clippy::disallowed_methods, clippy::too_many_arguments)]
fn score(
    label: &str,
    local: &LocalRepair,
    passage: &DamagedPassage,
    truth: &[usize],
    tally: &mut Tally,
    out: &str,
    i: usize,
) -> (Vec<CellRelease>, String) {
    let cells = passage.cells();
    let read = local.families(passage).expect("the families");
    let releases = local.release(passage).expect("the release");
    let residual = local.residual_code(truth, passage);
    let key_bits: usize = local
        .glued
        .iter()
        .flat_map(|glued| glued.members.iter())
        .map(|member| key_code(member, PORTS).expect("a key's code").len())
        .sum();
    // The score: the truth is read from here.
    for key in &local.keys {
        tally.keys[match key {
            LocalKey::Unread => 0,
            LocalKey::Empty => 1,
            LocalKey::One(_) => 2,
            LocalKey::Plural(_) => 3,
        }] += 1;
    }
    for join in &local.joins {
        tally.joins[*join as usize] += 1;
    }
    tally.glued += local.glued.len() as u64;
    tally.members += local.glued.iter().map(|g| g.members.len() as u64).sum::<u64>();
    tally.refused += read.refused.iter().map(|&r| r as u64).sum::<u64>();
    let alphabet: Vec<usize> = cells.iter().flatten().copied().collect();
    let mut released_mask = vec![false; LENGTH];
    let (mut released, mut right, mut held_count) = (0u64, 0u64, 0u64);
    for &t in &ERASED {
        let word = usize::from(
            truth[t] < 0x80 && char::from(u8::try_from(truth[t]).expect("a byte")).is_ascii_alphanumeric(),
        );
        tally.word_cells[word] += 1;
        match &releases[t] {
            CellRelease::Released(class) => {
                released += 1;
                released_mask[t] = true;
                tally.released_word[word] += 1;
                right += u64::from(*class == truth[t]);
                tally.in_alphabet += u64::from(alphabet.contains(class));
            }
            CellRelease::Held(family) => {
                held_count += 1;
                *tally.held_sizes.entry(family.len()).or_default() += 1;
                tally.held_whole += u64::from(family.len() == PORTS);
                tally.held_holds_truth += u64::from(family.contains(&truth[t]));
            }
            CellRelease::Intact(_) => unreachable!("an erased cell"),
        }
    }
    tally.released += released;
    tally.right += right;
    tally.held += held_count;
    let repaired: Vec<Option<usize>> = releases.iter().map(CellRelease::class).collect();
    let damaged_valid = known_runs(cells, &[false; LENGTH]).iter().all(|(run, _)| utf8_run(run));
    let repaired_runs = known_runs(&repaired, &released_mask);
    tally.utf8_damaged += u64::from(damaged_valid);
    tally.utf8_repaired += u64::from(repaired_runs.iter().all(|(run, _)| utf8_run(run)));
    for (run, has) in &repaired_runs {
        if *has {
            tally.released_runs += 1;
            tally.released_runs_valid += u64::from(utf8_run(run));
        }
    }
    // The released spans: each maximal run of released cells.
    let mut t = 0;
    while t < LENGTH {
        if released_mask[t] {
            let mut end = t;
            while end < LENGTH && released_mask[end] {
                end += 1;
            }
            let span: Vec<u8> = (t..end)
                .map(|k| u8::try_from(repaired[k].expect("released")).expect("a byte"))
                .collect();
            std::fs::write(format!("{out}/spans/{label}_p{i}_c{t}.bin"), &span).expect("write");
            let own = known_runs(cells, &[false; LENGTH])
                .iter()
                .map(|(run, _)| common(&span, run))
                .max()
                .unwrap_or(0);
            *tally.span_own_copy.entry(own).or_default() += 1;
            tally.spans += 1;
            t = end;
        } else {
            t += 1;
        }
    }
    tally.literal_bits += 8 * ERASED.len() as u64;
    tally.key_bits += key_bits as u64;
    let residual_line = match &residual {
        Ok(code) => {
            let mut bits = code.iter().copied();
            let reopened = local.reopen(passage, &mut bits).expect("the reopening");
            assert!(bits.next().is_none(), "the residual is read whole");
            tally.reopened += u64::from(reopened == truth);
            tally.residual_bits += code.len() as u64;
            format!("{}", code.len())
        }
        Err(error) => {
            tally.codec_refused += 1;
            format!("refused ({error})")
        }
    };
    let line = format!(
        "{label}: keys {:?}; joins {:?}; glued {} (members {:?}, refused {:?}); released {released} (equal to truth {right}), held {held_count}; residual bits {residual_line}, key bits {key_bits}",
        local.keys,
        local.joins,
        local.glued.len(),
        local.glued.iter().map(|g| g.members.len()).collect::<Vec<_>>(),
        read.refused,
    );
    (releases, line)
}

fn report(label: &str, tally: &Tally, passages: usize, out: &str) {
    let erased = (passages * ERASED.len()) as u64;
    println!(
        "[{label}] regions: unread {}, empty {}, one {}, plural {} (of {})",
        tally.keys[0], tally.keys[1], tally.keys[2], tally.keys[3], tally.keys.iter().sum::<u64>()
    );
    println!(
        "[{label}] joins: unique {}, plural {}, obstructed {}, open {} (of {}); glued regions {}, members {}, members refused by their passage {}",
        tally.joins[Join::Unique as usize],
        tally.joins[Join::Plural as usize],
        tally.joins[Join::Obstructed as usize],
        tally.joins[Join::Open as usize],
        tally.joins.iter().sum::<u64>(),
        tally.glued,
        tally.members,
        tally.refused
    );
    println!(
        "[{label}] erased {erased} (truth alphanumeric {}, other {}): released {} (alphanumeric {}, other {}), equal to truth {}; held {} (whole alphabet {}, family holding the truth {}); held family sizes {:?}",
        tally.word_cells[1],
        tally.word_cells[0],
        tally.released,
        tally.released_word[1],
        tally.released_word[0],
        tally.right,
        tally.held,
        tally.held_whole,
        tally.held_holds_truth,
        tally.held_sizes
    );
    println!(
        "[{label}] valid decode: released bytes in their passage's alphabet {} of {}; passages reading as UTF-8 damaged {}, repaired {} (of {passages}); known runs holding a released byte {} of which valid {}",
        tally.in_alphabet,
        tally.released,
        tally.utf8_damaged,
        tally.utf8_repaired,
        tally.released_runs,
        tally.released_runs_valid
    );
    println!(
        "[{label}] codec: residual {} bits, keys by key_code {} bits, literal {} bits; passages reopened exactly {}, codec refused {}",
        tally.residual_bits, tally.key_bits, tally.literal_bits, tally.reopened, tally.codec_refused
    );
    println!(
        "[{label}] released spans {} (written to {out}/spans); copy length against own intact cells {:?}",
        tally.spans, tally.span_own_copy
    );
}

/// **`executed text-repair <cut> <out dir> <dev|run>`** (module header).
#[allow(clippy::disallowed_methods)]
pub(super) fn run(cut: &str, out: &str, which: &str) {
    let clock = Instant::now();
    let (bytes, population, held) = exterior::read_cut(cut);
    let starts: Vec<usize> = match which {
        "dev" => (0..DEV_COUNT).map(|j| DEV_FIRST + LENGTH * j).collect(),
        "run" => (0..READ_COUNT).map(|i| READ_FIRST + READ_STRIDE * i).collect(),
        _ => panic!("executed text-repair <cut> <out dir> <dev|run>"),
    };
    assert!(starts.iter().all(|&s| s + LENGTH <= held.start), "the development range only");
    assert!(READ_FIRST >= DEV_FIRST + LENGTH * DEV_COUNT, "the read set apart from development");
    std::fs::create_dir_all(format!("{out}/spans")).expect("the private directory");
    std::fs::write(format!("{out}/training.bin"), &bytes[..TRAINING]).expect("write");
    let cover = Cover::declare(LENGTH, REGION, STRIDE, REACH).expect("the pinned cover");
    println!(
        "executed text-repair ({which}): the cut {population} bytes, development range 0..{}; {} passages of {LENGTH} bytes from {} ; erased {:?}; cover regions {REGION} stride {STRIDE} reach {REACH} on {PORTS} ports",
        held.start,
        starts.len(),
        starts[0],
        ERASED
    );
    let (mut located, mut pinned) = (Tally::default(), Tally::default());
    let mut triples = String::new();
    let mut slowest = 0u128;
    for (i, &start) in starts.iter().enumerate() {
        let unit = Instant::now();
        let truth: Vec<usize> = bytes[start..start + LENGTH].iter().map(|&b| usize::from(b)).collect();
        let cells: Vec<Option<usize>> = (0..LENGTH)
            .map(|t| (!ERASED.contains(&t)).then_some(truth[t]))
            .collect();
        let passage = DamagedPassage::new(cells.clone(), PORTS, 0).expect("a passage");
        // Only the damaged cells are read until `score` reads the truth.
        let local = locate(&passage, &cover, PORTS).expect("the local keys");
        let refused_arm = pinned_arm(&passage, &cover, &local.joins);
        let (releases, located_line) = score("located", &local, &passage, &truth, &mut located, out, i);
        let (pinned_releases, pinned_line) =
            score("pinned", &refused_arm, &passage, &truth, &mut pinned, out, i);
        let ms = unit.elapsed().as_millis();
        slowest = slowest.max(ms);
        println!("passage {i}: {ms} ms (elapsed {} ms); {located_line} | {pinned_line}", clock.elapsed().as_millis());
        // The private show.
        let line = |cell: &dyn Fn(usize) -> String| (0..LENGTH).map(|t| cell(t)).collect::<String>();
        let repaired_of = |releases: &[CellRelease]| {
            line(&|t| match &releases[t] {
                CellRelease::Intact(c) | CellRelease::Released(c) => shown(*c),
                CellRelease::Held(family) => format!("▯{{{}}}", family.len()),
            })
        };
        let count = |releases: &[CellRelease]| {
            ERASED
                .iter()
                .filter(|&&t| matches!(releases[t], CellRelease::Released(_)))
                .count()
        };
        let right = |releases: &[CellRelease]| {
            ERASED
                .iter()
                .filter(|&&t| releases[t] == CellRelease::Released(truth[t]))
                .count()
        };
        write!(
            triples,
            "passage {i} (cut bytes {start}..{}): released {} of {}, equal to truth {}\n  damaged  {}\n  repaired {}\n",
            start + LENGTH,
            count(&releases),
            ERASED.len(),
            right(&releases),
            line(&|t| cells[t].map_or("▯".to_string(), shown)),
            repaired_of(&releases),
        )
        .unwrap();
        if count(&pinned_releases) > 0 {
            write!(
                triples,
                "  pinned   {} (the refused arm: released {}, equal to truth {})\n",
                repaired_of(&pinned_releases),
                count(&pinned_releases),
                right(&pinned_releases)
            )
            .unwrap();
        }
        writeln!(triples, "  truth    {}\n", line(&|t| shown(truth[t]))).unwrap();
        if i + 1 == SHOWN {
            std::fs::write(format!("{out}/shown.txt"), &triples).expect("write");
        }
    }
    std::fs::write(format!("{out}/triples.txt"), &triples).expect("write");
    report("located", &located, starts.len(), out);
    report("pinned", &pinned, starts.len(), out);
    println!(
        "done: {} passages in {} ms, slowest {slowest} ms; {}",
        starts.len(),
        clock.elapsed().as_millis(),
        resident()
    );
}
