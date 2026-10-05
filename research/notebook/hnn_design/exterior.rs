//! **The notebook's exterior boundary**, shared by the `hnn_design` examples (each includes it by
//! `#[path = "exterior.rs"] mod exterior;`): the cut file read as its two parts, the seen and the
//! held; a run's pin; the one way a release is shown; and the exact presentation of readings for a
//! person.
//!
//! [definition] **Every reading is exact; no decimal is printed** (a decimal is a collapse, CLAUDE.md's
//! exact-arithmetic law). Integers print as integers and rationals as `n/d` (`n/2^e` or
//! `n/(2^e·m)` on a wide denominator with a power-of-two factor); bits are enclosures with exact
//! endpoints, each also read at the receiver's grain `L_R` through `GrainCell::of`:
//! `n + k/L_R + ε`, the carry `n`, the phase class `k` and the exact fibre `0 ≤ ε < 1/L_R`; a
//! comparison is the exact ordering of two enclosures with their exact difference.
//!
//! [definition; agent-inferred, October 5] **Three guards live here** (THE_MACHINE, "Guards that
//! make the rejected forms impossible", 19, 21 and 22), each a construction of this boundary, proved
//! by the `compile_fail` and runnable doctests of `crates/holonics/src/exterior_guards.rs`, which
//! include this file:
//! - **guard 21**, seen material is never graded as unseen: [`read_cut`] returns a [`Cut`] of a
//!   [`Seen`] development range and a [`Held`] held-out range, never bytes with a range to slice;
//! - **guard 19**, one release shown whole with its copy length: [`show_release`];
//! - **guard 22**, no limit is raised: a run's deadline, unit bound and thread budget are a
//!   committed [`Pin`]'s, never a command line's.

// Each example reads only the part of the boundary it needs.
#![allow(dead_code)]

use std::fmt;
use std::ops::Range;
use std::time::{Duration, Instant};

use holonics::hnn::Field;
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use holonics::receiver::face::GrainCell;
use num_bigint::BigInt;
use num_traits::One;

// -------------------------------------------------------------------------------------------
// the cut, read as its two parts (guard 21)

/// **The development reserve's name** (`development_families.py`, `RESERVE_SHA256`; THE_REBUILD U6):
/// the SHA-256 of the reserve's sorted membership, committed before any run reads a role. Every cut
/// this boundary reads must name it as excluded (`"reserve_excluded"` in its manifest); a cut
/// written before the reserve was named holds it (every earlier split read every conversation).
pub const RESERVE_SHA256: &str = "09d7ae5b86d1b34cd1f57a100fb0ec412f59902f6ec3b90924a7c80b136f8a24";

/// **Refuse a manifest that does not name the reserve as excluded.** [agent-inferred, October 5;
/// guard 21] There is no bypass: the logged `--read-reserve` this boundary admitted until October 5
/// was passed by no run (THE_REBUILD U6, item 1), and a cut read past it would have offered the
/// reserve's material as a held-out range. The Python scripts keep their own logged flag for
/// regenerating spent receipts; no Rust harness reads such a cut.
fn require_reserve_excluded(manifest_path: &str, manifest: &str) {
    let named = manifest
        .find("\"reserve_excluded\":")
        .map(|at| &manifest[at + "\"reserve_excluded\":".len()..])
        .is_some_and(|rest| {
            rest.trim_start()
                .strip_prefix('"')
                .is_some_and(|value| value.starts_with(RESERVE_SHA256))
        });
    assert!(
        named,
        "refused: {manifest_path} does not name the development reserve as excluded, so it may hold \
         the reserve's material"
    );
}

/// [definition; agent-inferred, October 5] **A cut, read as its two parts** (THE_MACHINE guard 21;
/// lesson 8 of the [repeated failures](../../records/2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md),
/// "unseen means unread by any run", against its failure 6, seen material graded as unseen). The
/// cut is partitioned once, at its manifest's held-out start `s`: the development range `[0, s)` is
/// [`Seen`] and the held-out range `[s, population)` is [`Held`]. Both have private fields and only
/// [`read_cut`] makes them, so no caller holds the cut's bytes beside a range it slices freely: a
/// training passage, a development read or a repair reads the `Seen` by reference, and a grading of
/// held-out material takes the `Held` by value. Structural (`exterior_guards`): a `Seen` is refused
/// where a `Held` is required (`E0308`), a `Held` is never forged from bytes (`E0451`), its bytes
/// are never read by reference (`E0599`), and once read it is gone (`E0382`).
pub struct Cut {
    /// The manifest's population: the cut's length.
    pub population: usize,
    /// The development range `[0, s)`.
    pub seen: Seen,
    /// The held-out range `[s, population)`.
    pub held: Held,
}

impl Cut {
    /// **The prequential exposure's read** (`hnn::Reference::expose`, whose `Cut` compares every
    /// held cell before it deposits it and lets no crib read one): the cut whole with its held-out
    /// range. It consumes the cut, its `Held` with it: the one path by which held bytes enter a
    /// passage whole, and only for a reading that grades each before any deposit reads it.
    pub fn prequential(self) -> (Vec<u8>, Range<usize>) {
        let range = self.held.range();
        let mut bytes = self.seen.bytes;
        bytes.extend(self.held.bytes);
        (bytes, range)
    }
}

/// [definition] **Seen material** (guard 21): the cut's development range `[0, s)`, which runs
/// read (a training passage, a development read, a repair's passages). It is read by reference, and
/// nothing converts it into [`Held`].
pub struct Seen {
    bytes: Vec<u8>,
}

impl Seen {
    /// The development range's bytes, from the cut's position `0`.
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// The development range `[0, s)` in the cut's positions.
    pub fn range(&self) -> Range<usize> {
        0..self.bytes.len()
    }
}

/// [definition] **Held material** (guard 21): the cut's held-out range `[s, population)`, read by no
/// run. Its positions are read by reference ([`Held::range`]); its bytes are read once, by value, at
/// declared windows ([`Held::windows`]), so no development read reaches them before the grading
/// that takes them.
pub struct Held {
    start: usize,
    bytes: Vec<u8>,
}

impl Held {
    /// The held-out range in the cut's positions.
    pub fn range(&self) -> Range<usize> {
        self.start..self.start + self.bytes.len()
    }

    /// **The held range read once, at declared windows**: `length` cells from each start (the cut's
    /// positions), each window inside the range, in order and pairwise disjoint. It consumes the
    /// range; a window outside it, or overlapping the one before, is refused.
    pub fn windows(self, starts: &[usize], length: usize) -> Vec<Vec<u8>> {
        let range = self.range();
        let mut end = range.start;
        starts
            .iter()
            .map(|&start| {
                assert!(
                    start >= end && start + length <= range.end,
                    "refused: the held window {start}..{} lies outside the held-out range {range:?} \
                     or overlaps the window before it",
                    start + length
                );
                end = start + length;
                self.bytes[start - range.start..end - range.start].to_vec()
            })
            .collect()
    }
}

/// **A cut file and its manifest** (the standing real cut in `.local/cuts/`, written by
/// `standing_cut.py`), read whole at the notebook's exterior boundary and returned as its two parts
/// ([`Cut`]): the manifest's population and its held-out range are read by the numbers after their
/// keys (the manifest is exterior JSON; no parser enters the crate). The file's length must be the
/// manifest's population, the held-out range must close the cut, and the manifest must name the
/// development reserve as excluded. Only its scope and counts are printed.
#[allow(clippy::disallowed_types, clippy::disallowed_methods)]
pub fn read_cut(path: &str) -> Cut {
    let mut bytes =
        std::fs::read(path).unwrap_or_else(|error| panic!("read the cut file {path}: {error}"));
    let manifest_path = path
        .strip_suffix(".bin")
        .map_or_else(|| format!("{path}.json"), |stem| format!("{stem}.json"));
    let manifest = std::fs::read_to_string(&manifest_path)
        .unwrap_or_else(|error| panic!("read the cut manifest {manifest_path}: {error}"));
    require_reserve_excluded(&manifest_path, &manifest);
    let numbers_after = |key: &str| -> Vec<usize> {
        let start = manifest
            .find(key)
            .unwrap_or_else(|| panic!("the manifest names {key}"))
            + key.len();
        let rest = manifest[start..].trim_start();
        let value = if rest.starts_with('[') {
            &rest[..rest.find(']').expect("a closed list")]
        } else {
            &rest[..rest.find([',', '\n', '}']).unwrap_or(rest.len())]
        };
        value
            .split(|c: char| !c.is_ascii_digit())
            .filter(|piece| !piece.is_empty())
            .map(|piece| piece.parse().expect("a count"))
            .collect()
    };
    let population = numbers_after("\"population\":")[0];
    let range = numbers_after("\"held_out_range\":");
    assert_eq!(
        bytes.len(),
        population,
        "the cut file's length is the manifest's population"
    );
    assert_eq!(range[1], population, "the held-out range closes the cut");
    assert!(range[0] <= population, "the held-out range lies in the cut");
    let held = bytes.split_off(range[0]);
    Cut {
        population,
        seen: Seen { bytes },
        held: Held {
            start: range[0],
            bytes: held,
        },
    }
}

/// **A count from a cut's manifest** (exterior JSON, read by the number after its key), e.g. the
/// development stream's length `"development_stream_bytes":`.
#[allow(clippy::disallowed_types, clippy::disallowed_methods)]
pub fn manifest_number(path: &str, key: &str) -> usize {
    let manifest_path = path
        .strip_suffix(".bin")
        .map_or_else(|| format!("{path}.json"), |stem| format!("{stem}.json"));
    let manifest = std::fs::read_to_string(&manifest_path)
        .unwrap_or_else(|error| panic!("read the cut manifest {manifest_path}: {error}"));
    let start = manifest
        .find(key)
        .unwrap_or_else(|| panic!("the manifest names {key}"))
        + key.len();
    manifest[start..]
        .trim_start()
        .split(|c: char| !c.is_ascii_digit())
        .find(|piece| !piece.is_empty())
        .and_then(|piece| piece.parse().ok())
        .expect("a count")
}

/// **The process's resident set, now and at its peak**, in bytes (exterior: the kernel's
/// `/proc/self/status`, `VmRSS` and `VmHWM`, read in kB), when the status reads.
#[allow(clippy::disallowed_types, clippy::disallowed_methods)]
pub fn resident_set() -> Option<(u128, u128)> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let field = |key: &str| -> Option<u128> {
        let line = status.lines().find(|line| line.starts_with(key))?;
        let kilobytes: u128 = line.split_whitespace().nth(1)?.parse().ok()?;
        Some(kilobytes * 1024)
    };
    Some((field("VmRSS:")?, field("VmHWM:")?))
}

/// **The memory the kernel reports available**, in bytes (exterior: `/proc/meminfo`'s
/// `MemAvailable`, read in kB), when it reads; a passage whose projected memory passes it is refused.
#[allow(clippy::disallowed_types, clippy::disallowed_methods)]
pub fn available_memory() -> Option<u128> {
    let info = std::fs::read_to_string("/proc/meminfo").ok()?;
    let line = info
        .lines()
        .find(|line| line.starts_with("MemAvailable:"))?;
    let kilobytes: u128 = line.split_whitespace().nth(1)?.parse().ok()?;
    Some(kilobytes * 1024)
}

// -------------------------------------------------------------------------------------------
// presentation (for a person; every reading exact, never a decimal)

/// **The receiver's grain** `L_R = ⌈1/ε_bits⌉` of the field's first receiver (campaign 1: 16), the
/// declared grain every bit count is read at.
pub fn receiver_grain(field: &Field) -> u64 {
    field.receivers()[0]
        .tolerance
        .recip()
        .ceil()
        .to_integer()
        .try_into()
        .expect("a grain fits a machine word")
}

/// An exact rational: an integer, `n/2^e` on a wide dyadic denominator, `n/(2^e·m)` on a wide
/// denominator with a power-of-two factor, or `n/d`.
pub fn exact(value: &Rat) -> String {
    let denominator = value.denom().magnitude();
    if denominator.is_one() {
        return value.numer().to_string();
    }
    let twos = denominator.trailing_zeros().unwrap_or(0);
    let odd = denominator >> twos;
    if denominator.bits() <= 16 {
        format!("{}/{}", value.numer(), denominator)
    } else if odd.is_one() {
        format!("{}/2^{twos}", value.numer())
    } else if twos > 0 {
        format!("{}/(2^{twos}·{odd})", value.numer())
    } else {
        format!("{}/{}", value.numer(), denominator)
    }
}

/// **A reading at the grain** `L` (`GrainCell::of`): `value = n + k/L + ε`, the carry `n`, the
/// phase class `k ∈ ℤ/L` and the unresolved fibre `0 ≤ ε < 1/L`, each exact.
pub fn reading(value: &Rat, grain: u64) -> String {
    let cell = GrainCell::of(value, grain);
    format!(
        "{} + {}/{grain} + ε, ε = {} < 1/{grain}",
        cell.carry,
        cell.phase,
        exact(&cell.fibre)
    )
}

/// **An enclosure read at the grain**: both endpoints' cells; when they share their carry and
/// phase class, that cell once with the enclosure of its fibre.
pub fn reading_of(interval: &ExactInterval, grain: u64) -> String {
    let (lower, upper) = (
        GrainCell::of(&interval.lower, grain),
        GrainCell::of(&interval.upper, grain),
    );
    if lower.carry == upper.carry && lower.phase == upper.phase {
        format!(
            "{} + {}/{grain} + ε, ε ∈ [{}, {}] ⊂ [0, 1/{grain})",
            lower.carry,
            lower.phase,
            exact(&lower.fibre),
            exact(&upper.fibre)
        )
    } else {
        format!(
            "[{} + {}/{grain} + {}, {} + {}/{grain} + {}] (each fibre < 1/{grain})",
            lower.carry,
            lower.phase,
            exact(&lower.fibre),
            upper.carry,
            upper.phase,
            exact(&upper.fibre)
        )
    }
}

/// An exact ratio, reduced, with its integer quotient and remainder: `n/d (q rem r over d)`.
pub fn ratio(value: &Rat) -> String {
    if value.is_integer() {
        return value.numer().to_string();
    }
    let (numerator, denominator) = (value.numer(), value.denom());
    let quotient = value.floor().to_integer();
    let remainder = numerator - &quotient * denominator;
    format!(
        "{} ({quotient} rem {remainder} over {denominator})",
        exact(value)
    )
}

/// An enclosure of bits: its exact endpoints, then its reading at the grain.
pub fn enclosure(interval: &ExactInterval, grain: u64) -> String {
    format!(
        "exact [{}, {}] bits; at L_R = {grain}: {}",
        exact(&interval.lower),
        exact(&interval.upper),
        reading_of(interval, grain)
    )
}

/// An enclosure divided by a count (bits a cell): the exact ratios read at the grain.
pub fn per(interval: &ExactInterval, count: u64, grain: u64) -> String {
    if count == 0 {
        return "-".to_string();
    }
    let count = Rat::from_integer(BigInt::from(count));
    reading_of(
        &ExactInterval {
            lower: &interval.lower / &count,
            upper: &interval.upper / &count,
        },
        grain,
    )
}

/// Where enclosure `a` lies against `b`, exactly.
pub fn against(a: &ExactInterval, b: &ExactInterval) -> &'static str {
    if a.upper < b.lower {
        "below"
    } else if a.lower > b.upper {
        "above"
    } else {
        "undecided (the enclosures overlap)"
    }
}

/// **The exact difference** of two enclosures, `a − b ∈ [a.lower − b.upper, a.upper − b.lower]`,
/// with its exact endpoints and its reading at the grain.
pub fn difference(a: &ExactInterval, b: &ExactInterval, grain: u64) -> String {
    enclosure(
        &ExactInterval {
            lower: &a.lower - &b.upper,
            upper: &a.upper - &b.lower,
        },
        grain,
    )
}

// -------------------------------------------------------------------------------------------
// the release shown whole, with its copy length (guard 19)

/// The copy length's declared threshold `K` for its covered count (`tools/copy_length.py`'s
/// default `--min-run`).
pub const MIN_RUN: usize = 8;

/// [definition] **The copy length** (THE_MACHINE guard 19; `tools/copy_length.py`'s law, ported
/// exactly, with its output): the longest run of release bytes occurring verbatim in one admitted
/// passage, `L = max_f max { |w| : w ⊑ R, w ⊑ P_f }`, over bytes, a run never spanning two
/// passages; its first start in the release, the first passage holding it and its first offset
/// there (none when `L = 0`); and the release bytes covered by runs of at least `K` bytes. An
/// exterior receipt that makes recitation visible: never a control, a grade or a loss, and nothing
/// in the machine reads it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CopyLength {
    pub copy_length: usize,
    pub release_start: Option<usize>,
    pub passage_file: Option<usize>,
    pub passage_offset: Option<usize>,
    pub covered_bytes: usize,
    pub min_run: usize,
    pub release_bytes: usize,
    pub passage_bytes: usize,
}

impl fmt::Display for CopyLength {
    /// The tool's plain output: one `key value` line a field, `-1` where there is no run.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let at = |value: Option<usize>| value.map_or_else(|| "-1".to_string(), |v| v.to_string());
        writeln!(f, "copy_length {}", self.copy_length)?;
        writeln!(f, "release_start {}", at(self.release_start))?;
        writeln!(f, "passage_file {}", at(self.passage_file))?;
        writeln!(f, "passage_offset {}", at(self.passage_offset))?;
        writeln!(f, "covered_bytes {}", self.covered_bytes)?;
        writeln!(f, "min_run {}", self.min_run)?;
        writeln!(f, "release_bytes {}", self.release_bytes)?;
        write!(f, "passage_bytes {}", self.passage_bytes)
    }
}

/// **The suffix automaton of the release** (the tool's `ReleaseAutomaton`): built once over the
/// release, `O(|R|)` states; each passage streams through it.
struct ReleaseAutomaton {
    next: Vec<std::collections::BTreeMap<u8, usize>>,
    link: Vec<Option<usize>>,
    length: Vec<usize>,
    prefix_state: Vec<usize>,
    /// The states by increasing length: a topological order of the suffix-link tree.
    order: Vec<usize>,
}

impl ReleaseAutomaton {
    fn new(data: &[u8]) -> Self {
        let mut next = vec![std::collections::BTreeMap::new()];
        let mut link: Vec<Option<usize>> = vec![None];
        let mut length = vec![0usize];
        let mut prefix_state = Vec::with_capacity(data.len());
        let mut last = 0;
        for &c in data {
            let cur = next.len();
            next.push(std::collections::BTreeMap::new());
            length.push(length[last] + 1);
            link.push(Some(0));
            let mut p = Some(last);
            while let Some(state) = p {
                if next[state].contains_key(&c) {
                    break;
                }
                next[state].insert(c, cur);
                p = link[state];
            }
            if let Some(from) = p {
                let q = next[from][&c];
                if length[from] + 1 == length[q] {
                    link[cur] = Some(q);
                } else {
                    let clone = next.len();
                    next.push(next[q].clone());
                    length.push(length[from] + 1);
                    link.push(link[q]);
                    let mut p = Some(from);
                    while let Some(state) = p {
                        if next[state].get(&c) != Some(&q) {
                            break;
                        }
                        next[state].insert(c, clone);
                        p = link[state];
                    }
                    link[q] = Some(clone);
                    link[cur] = Some(clone);
                }
            }
            last = cur;
            prefix_state.push(cur);
        }
        let mut order: Vec<usize> = (0..next.len()).collect();
        order.sort_by_key(|&state| length[state]);
        Self {
            next,
            link,
            length,
            prefix_state,
            order,
        }
    }

    /// `best[v]`: the longest suffix of the passage read so far that state `v` held at some step.
    fn mark(&self, passage: &[u8]) -> Vec<usize> {
        let mut best = vec![0; self.next.len()];
        let (mut v, mut n) = (0usize, 0usize);
        for &c in passage {
            loop {
                if let Some(&to) = self.next[v].get(&c) {
                    v = to;
                    n += 1;
                    best[v] = best[v].max(n);
                    break;
                }
                if v == 0 {
                    n = 0;
                    break;
                }
                v = self.link[v].expect("a state past the root has a suffix link");
                n = self.length[v];
            }
        }
        best
    }

    /// `ms[i]`: the longest suffix of `R[..=i]` occurring in the streamed passage.
    fn matching_statistics(&self, mut best: Vec<usize>) -> Vec<usize> {
        for &v in self.order.iter().rev() {
            if v != 0 && best[v] != 0 {
                let p = self.link[v].expect("a suffix link");
                if p > 0 {
                    best[p] = self.length[p];
                }
            }
        }
        let mut top = vec![0; best.len()];
        for &v in &self.order {
            if v != 0 {
                let parent = self.link[v].expect("a suffix link");
                top[v] = if best[v] != 0 { best[v] } else { top[parent] };
            }
        }
        self.prefix_state.iter().map(|&v| top[v]).collect()
    }
}

/// **The copy-length receipt** of `release` against the admitted `passages`, each a separate
/// passage (a run never spans two), with the covered count at `min_run` (module header; the tool's
/// `copy_length`, linear in `|R| + Σ|P_f|`).
pub fn copy_length(release: &[u8], passages: &[&[u8]], min_run: usize) -> CopyLength {
    assert!(min_run >= 1, "min_run must be at least 1");
    let mut covered = vec![false; release.len()];
    // (length, release start, passage): the longest, then the earliest start, then the first passage.
    let mut best: Option<(usize, usize, usize)> = None;
    let mut passage_bytes = 0;
    let automaton = (!release.is_empty()).then(|| ReleaseAutomaton::new(release));
    for (index, passage) in passages.iter().enumerate() {
        passage_bytes += passage.len();
        let Some(automaton) = &automaton else {
            continue;
        };
        let ms = automaton.matching_statistics(automaton.mark(passage));
        let (mut longest, mut end) = (0usize, 0usize);
        let mut hi: Option<usize> = None;
        for (i, &m) in ms.iter().enumerate() {
            if m > longest {
                longest = m;
                end = i;
            }
            if m >= min_run {
                let start = (i + 1 - m).max(hi.map_or(0, |h| h + 1));
                for cell in covered.iter_mut().take(i + 1).skip(start) {
                    *cell = true;
                }
                hi = Some(i);
            }
        }
        if longest > 0 {
            let key = (longest, end + 1 - longest, index);
            if best.is_none_or(|b| key.0 > b.0 || (key.0 == b.0 && (key.1, key.2) < (b.1, b.2))) {
                best = Some(key);
            }
        }
    }
    let Some((longest, start, index)) = best else {
        return CopyLength {
            copy_length: 0,
            release_start: None,
            passage_file: None,
            passage_offset: None,
            covered_bytes: 0,
            min_run,
            release_bytes: release.len(),
            passage_bytes,
        };
    };
    let run = &release[start..start + longest];
    CopyLength {
        copy_length: longest,
        release_start: Some(start),
        passage_file: Some(index),
        passage_offset: passages[index].windows(longest).position(|w| w == run),
        covered_bytes: covered.iter().filter(|&&c| c).count(),
        min_run,
        release_bytes: release.len(),
        passage_bytes,
    }
}

/// **A byte for the eye**: printable ASCII as itself, the backslash, newline and tab escaped, every
/// other byte `\xNN`.
pub fn eye(byte: u8) -> String {
    match byte {
        0x5c => "\\\\".to_string(),
        0x0a => "\\n".to_string(),
        0x09 => "\\t".to_string(),
        0x20..=0x7e => char::from(byte).to_string(),
        _ => format!("\\x{byte:02x}"),
    }
}

/// [definition; agent-inferred, October 5] **The one way a release is shown** (THE_MACHINE guard
/// 19; the [contamination cycles](../../records/2026-10-05_THE_CONTAMINATION_CYCLES_EVERY_COPY_PIPELINE_FOLLOWED_A_DEMAND_FOR_OUTPUT_BEFORE_THE_FIELD_COULD_RELEASE.md)).
/// It writes the release whole to `<out>/<name>`, appends it whole (each byte for the eye) with its
/// copy length against the passages the machine admitted to the private show `<out>/releases.show`,
/// and prints the copy length's integers on stdout, so recitation is visible at once and no release
/// is shown without its receipt. Nothing is selected, cut or compared with a reference here: the
/// release arrives whole and leaves whole. `<out>` is a private directory (`.local/`): the release
/// may derive from private data, so stdout carries counts only.
#[allow(clippy::disallowed_methods, clippy::disallowed_types)]
pub fn show_release(out: &str, name: &str, release: &[u8], admitted: &[&[u8]]) -> CopyLength {
    use std::io::Write as _;
    let receipt = copy_length(release, admitted, MIN_RUN);
    std::fs::write(format!("{out}/{name}"), release).expect("write the release whole");
    let mut show = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(format!("{out}/releases.show"))
        .expect("the private show");
    let whole: String = release.iter().map(|&b| eye(b)).collect();
    writeln!(show, "{name} ({} bytes): {whole}\n{receipt}\n", release.len()).expect("write the show");
    let at = |value: Option<usize>| value.map_or_else(|| "none".to_string(), |v| v.to_string());
    println!(
        "    shown {name}: {} bytes whole; copy length {} against {} admitted passages (release start {}, passage {}, offset {}); bytes covered by runs of at least {} {}",
        receipt.release_bytes,
        receipt.copy_length,
        admitted.len(),
        at(receipt.release_start),
        at(receipt.passage_file),
        at(receipt.passage_offset),
        receipt.min_run,
        receipt.covered_bytes
    );
    receipt
}

// -------------------------------------------------------------------------------------------
// a run's pin (guard 22)

/// The exit status of a run stopped at its pinned deadline (loop 1c's `INCOMPLETE`): never a
/// result, and never truncated into one.
pub const INCOMPLETE: i32 = 3;

/// [definition; agent-inferred, October 5] **A run's pin** (THE_MACHINE guard 22; lesson 9 of the
/// [repeated failures](../../records/2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md),
/// "a refusal changes the law or the partition, never the limit", against 29 raised limits; CLAUDE.md,
/// "Waiting, deadlines and concurrency"). A run's deadline, its per-unit bound and its thread budget
/// are read from a committed file, never from the command line: the command names the pin, and
/// the pin holds the numbers with the projection they come from.
///
/// ```text
/// # what the run reads, and why these numbers
/// command = executed text
/// projection = 16 · 54,240 ms = 867,840 ms (the development read's founded request)
/// deadline_ms = 1084800
/// unit_bound_ms = 94445
/// threads = 8
/// ```
///
/// [`Pin::read`] refuses (the run does not start) a missing pin, one not tracked by git, one that
/// differs from its commit, and one whose history holds more than one commit: a pin is fixed once,
/// so a limit is never raised by editing it. A run past its pin is reported incomplete, and the
/// next loop commits a new pin for a changed law, partition or read, saying why. Its fields are
/// private and it has no setter (`exterior_guards`: `E0451`, `E0616`).
#[derive(Debug)]
pub struct Pin {
    path: String,
    command: String,
    projection: String,
    deadline_ms: u128,
    unit_bound_ms: Option<u128>,
    threads: usize,
    commit: String,
}

/// `git -C <dir> <args>`: whether it succeeded, and its standard output.
#[allow(clippy::disallowed_types, clippy::disallowed_methods)]
fn git(dir: &std::path::Path, args: &[&str]) -> (bool, String) {
    let output = std::process::Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("refused: git reads a pin's commit ({error})"));
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stdout).into_owned(),
    )
}

impl Pin {
    /// **Read the committed pin** of `command` at `path` (module header): refused when it is
    /// missing, untracked, changed since its commit, committed more than once, of another command,
    /// or missing its projection, deadline or threads.
    #[allow(clippy::disallowed_methods)]
    pub fn read(path: &str, command: &str) -> Pin {
        let text = std::fs::read_to_string(path).unwrap_or_else(|error| {
            panic!(
                "refused: no pin at {path} ({error}); a run's deadline, unit bound and threads are \
                 a committed pin's, never the command line's"
            )
        });
        let file = std::path::Path::new(path);
        let dir = file
            .parent()
            .filter(|dir| !dir.as_os_str().is_empty())
            .unwrap_or(std::path::Path::new("."));
        let name = file
            .file_name()
            .and_then(|name| name.to_str())
            .expect("a pin's file name");
        assert!(
            git(dir, &["ls-files", "--error-unmatch", "--", name]).0,
            "refused: the pin {path} is not committed"
        );
        assert!(
            git(dir, &["diff", "--quiet", "HEAD", "--", name]).0,
            "refused: the pin {path} differs from its commit"
        );
        let (_, log) = git(dir, &["log", "--format=%H", "--", name]);
        let commits: Vec<&str> = log.lines().collect();
        assert!(
            commits.len() == 1,
            "refused: the pin {path} was committed {} times; a pin is fixed once (a limit is never \
             raised): a run past it is incomplete, and the next loop pins its changed read anew",
            commits.len()
        );
        let mut fields: std::collections::BTreeMap<&str, &str> = std::collections::BTreeMap::new();
        for line in text.lines().map(str::trim) {
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let (key, value) = line
                .split_once('=')
                .unwrap_or_else(|| panic!("refused: the pin {path}'s line `{line}` is not `key = value`"));
            let key = key.trim();
            assert!(
                matches!(key, "command" | "projection" | "deadline_ms" | "unit_bound_ms" | "threads"),
                "refused: the pin {path} declares an unknown key `{key}`"
            );
            assert!(
                fields.insert(key, value.trim()).is_none(),
                "refused: the pin {path} declares `{key}` twice"
            );
        }
        let field = |key: &str| -> &str {
            fields
                .get(key)
                .copied()
                .filter(|value| !value.is_empty())
                .unwrap_or_else(|| panic!("refused: the pin {path} declares no `{key}`"))
        };
        let count = |key: &str, value: &str| -> u128 {
            value
                .parse()
                .unwrap_or_else(|_| panic!("refused: the pin {path}'s `{key}` is not a whole count"))
        };
        assert_eq!(
            field("command"),
            command,
            "refused: the pin {path} pins another command"
        );
        let threads = usize::try_from(count("threads", field("threads"))).expect("a thread count");
        assert!(threads > 0, "refused: the pin {path} declares no thread");
        Pin {
            path: path.to_string(),
            command: command.to_string(),
            projection: field("projection").to_string(),
            deadline_ms: count("deadline_ms", field("deadline_ms")),
            unit_bound_ms: fields
                .get("unit_bound_ms")
                .map(|value| count("unit_bound_ms", value)),
            threads,
            commit: commits[0].chars().take(8).collect(),
        }
    }

    /// The run's deadline in milliseconds.
    pub fn deadline_ms(&self) -> u128 {
        self.deadline_ms
    }

    /// The per-unit bound in milliseconds, when the run declares a unit.
    pub fn unit_bound_ms(&self) -> Option<u128> {
        self.unit_bound_ms
    }

    /// The thread budget.
    pub fn threads(&self) -> usize {
        self.threads
    }

    /// **Launch under the pin**: its line printed and its deadline armed from `clock`: past it the
    /// process stops [`INCOMPLETE`], whatever it is reading. `arm` is false for a run that checks
    /// its own deadline before each unit and reports itself incomplete there. The harness installs
    /// [`Pin::threads`] as the host's pool before any parallel read (this boundary is also built
    /// where the host's pool is not a dependency).
    pub fn launch(&self, clock: Instant, arm: bool) {
        println!(
            "pin {} (commit {}): {}, deadline {} ms, unit bound {}, {} threads; {}",
            self.path,
            self.commit,
            self.command,
            self.deadline_ms,
            self.unit_bound_ms
                .map_or_else(|| "none".to_string(), |bound| format!("{bound} ms")),
            self.threads,
            self.projection
        );
        if !arm {
            return;
        }
        let (deadline, path) = (self.deadline_ms, self.path.clone());
        std::thread::spawn(move || {
            let whole = Duration::from_millis(u64::try_from(deadline).unwrap_or(u64::MAX));
            std::thread::sleep(whole.saturating_sub(clock.elapsed()));
            let reason = format!("stopped: past the pinned deadline {deadline} ms ({path}): INCOMPLETE");
            println!("{reason}");
            eprintln!("{reason}");
            #[allow(clippy::disallowed_methods)] // exterior notebook: an incomplete run exits so
            std::process::exit(INCOMPLETE)
        });
    }
}
