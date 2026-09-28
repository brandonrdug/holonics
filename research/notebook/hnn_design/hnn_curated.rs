//! **The curated conversation source read by its own navigators: a tree per port and a navigator
//! for its sections, against the flat stream of the same bytes** (campaign 5's input under
//! HNN_FORMULA's source contract; #73, #148): the notebook's development receipt of
//! `holonics::compression::landmark::context` on the curated source, a committed command run once
//! in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_curated -- curated .local/cuts/curated-cut.bin .local/cuts/curated-flat-cut.bin
//! ```
//!
//! [definition; agent-inferred] **The source** (`curated_source.py`, an exterior codec step): the
//! exposure's development partition, each visible part's UTF-8 bytes on its channel's port (human,
//! agent, tool; the harness holds references only), and before each part one **section letter**,
//! a coded cell of the declared chart `|A| = 256 + 12`: `open` (the occurrence opens its
//! conversation's aeon), `switch` (another aeon than the previous emitted occurrence's), `part`
//! (the previous emitted occurrence's declared turn, or a further part of its record) or `turn`
//! (the next epoch of the same aeon), each typed by the channel the part opens on. Beside the cut,
//! `curated-cut.aeons.bin` gives each letter's aeon ordinal (a coordinate); the reader codes it
//! through the letters and checks it against them. The flat cut is the same bytes with every
//! letter removed, its held-out cells the curated held-out cells' bytes: the two are measured on
//! identical bytes.
//!
//! [definition; agent-inferred, the typed reader's receipt at `a76413d3`] **The readers.** The
//! typed tree read the channel as a slot of every bundle, which capped it at `D = 16` (path depth
//! `D + 3D + 2`). Here the source is read by its own navigators, each a cell-only tree (the `½`
//! stop prior, the KT node `c = ∞`, stored where paths part, at the declared population `n*` of the
//! curated manifest and campaign 1's receiver grain `L_R`):
//! - **the flat tree** over the flat bytes (`|A| = 256`), unchanged;
//! - **a tree per port** (the winding guide's faces and placement, and the tube): channel `c`'s tree
//!   reads its **port spans**, one per aeon (the conversation's own span, not the joint clock of
//!   interleaved conversations): the span `σ(a, c)` is channel `c`'s ticks in aeon `a` within the
//!   cut, each part's opening kind (the section, read once) and then its bytes. Its chart is the
//!   bytes, the four kinds (address letters only: the section navigator codes them) and `END`
//!   (`|A| = 256 + 4 + 1`, `END` last, alone in its dyadic cell beside the kinds). It emits each
//!   byte, and at a part's close (a section letter follows in the cut) it emits `END`: **the
//!   boundary predicted from the bytes**, the probability that a section letter comes next read
//!   from the port's own context. `END`'s tick in the span is the next part's kind, when the span
//!   reopens. The span's address is its last `D` ticks, `Boundary` before its first in the cut.
//! - **the section navigator** (the tower thread: sections as restrictions of the passage), with
//!   its own clock, the section epochs (one tick a letter): its address is the last `D` section
//!   letters of every port (the joint alternation), its **letter tree** codes the twelve letters,
//!   and at a `switch` its **target tree** codes the target aeon's recency rank among the aeons met
//!   in the cut (`0`: not yet met), since `switch` says only that the aeon changes. `open` founds a
//!   new aeon, and `turn` and `part` stay, so every part's span is decoded from the code.
//! - **the shared port tree**, a development diagnostic that locates the trees per port's cost: one
//!   tree for every port (the ports share their landmarks, as the flat tree's bytes do), each
//!   emission still addressed on its own port span in its own aeon, the span's opening tick the
//!   whole section letter (the channel read once, at the section), `|A| = 256 + 12 + 1`. It is swept
//!   on the development cells beside the rest and read against the trees per port there; its
//!   held-out passage is not taken, since the held-out cells are read once, by the declared reader
//!   (the trees per port and the section navigator).
//!
//! [definition; agent-inferred] **The composition** (the chain rule; each face the executed face
//! at its tree's standing before its own deposit). For the cut `x_0 … x_(N−1)`, its letters
//! `ℓ_k = (kind_k, c_k)` at `p_0 = 0 < p_1 < … < p_(K−1)`, part `k` in aeon `a_k` on port `c_k`, and
//! `α_(a,c)(t)` the last `D_c` ticks of `σ(a, c)` before its tick `t`:
//!
//! ```text
//! L(x) = Σ_(k<K)  [ −log₂ q̂_S(ℓ_k | ℓ_(k−1), …, ℓ_(k−D_S)) − [kind_k = switch] log₂ q̂_T(r_k | ℓ_(k−1), …, ℓ_(k−D_S)) ]
//!      + Σ_(bytes j) −log₂ q̂_(c(j))(x_j | α_(a(j), c(j))(j))
//!      + Σ_(1≤k<K)   −log₂ q̂_(c_(k−1))(END | α_(a_(k−1), c_(k−1))(p_k))
//! ```
//!
//! A decoder reads `ℓ_0` (and `r_0` at a switch), then port `c_0`'s tree until `END`, then `ℓ_1`,
//! and so on: a prefix code of the curated stream given its length `N`, as the flat code is given
//! its length. The byte terms carry `P(no section yet)` in their top digit, as the joint tree's
//! bytes carried `P(no letter)`; the section terms are `END`, the letter and the target.
//!
//! - **0. The cut and its counts**: the bytes per port, the letters per kind, the port spans, the
//!   closes per port and the switch targets' ranks, on each population; the checks (the curated cut
//!   without its letters is the flat cut; each letter's aeon agrees with its kind).
//! - **1. The families**, stated before any passage: each navigator's depths doubling from 6 to the
//!   deepest its carriers admit at `n*` (`Landmarks::new`; a navigator of two trees, the deepest
//!   both admit), charged `⌈log₂⌉` of its length; the a-priori memory, checked against Brandon's
//!   20 GB cap and the memory the kernel reports available.
//! - **2. The sweeps** on the development cells, the navigators run together on the host (each
//!   reads its own immutable spans and writes its own sweep), each until its code does not fall
//!   strictly (`DepthSweep::{decreasing, of}`) or a passage passes four minutes.
//! - **3. The choices**: each navigator's depth and charge.
//! - **4. The development readings**: per port, the port tree against the flat tree on identical
//!   bytes (uncharged); the section cost (the closes, the letters, the targets); the whole codes
//!   charged (the curated stream carries its sections, the flat one does not).
//! - **5. One held-out passage** of each navigator at its chosen depth over the whole cut, every
//!   emission scored at the standing before its own deposit: the same readings, choosing nothing.
//!
//! [definition] **Privacy**: the cut is private (`.local/cuts/`); this reads codes and prints counts,
//! bits and hashes' scope only, never any cell's content. Every reading is exact (`exterior`): bits
//! as enclosures with exact endpoints read at the grain, `n + k/L_R + ε`, orderings by disjoint
//! exact enclosures, wall times in integer milliseconds.

#[path = "exterior.rs"]
mod exterior;

use std::collections::BTreeMap;
use std::ops::Range;
use std::time::Instant;

use holonics::compression::cost::ceil_log2;
use holonics::compression::landmark::context::{
    Capacity, LandmarkDeclaration, Landmarks, Letter, LetterFamily, PassageCode, StopPrior, Widths,
    odometer_digits,
};
use holonics::hnn::reference::DepthSweep;
use holonics::hnn::{Field, FieldDeclaration};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::{ExactInterval, interval_sum};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

use exterior::{against, difference, enclosure, exact, manifest_number, per, read_cut, reading_of};

/// The exterior chart's bytes; the section letters are coded after them.
const BYTES: usize = 256;

/// The ports that carry cells, in the letters' order (the harness carries references only).
const CHANNELS: [&str; 3] = ["human", "agent", "tool"];

/// The section letters' kinds, in the letters' order.
const KINDS: [&str; 4] = ["open", "switch", "turn", "part"];
const OPEN: usize = 0;
const SWITCH: usize = 1;

/// The section letters: `kind × channel`.
const LETTERS: usize = KINDS.len() * CHANNELS.len();

/// **A port's chart**: the bytes, the four kinds at `BYTES + kind` (address letters only), and
/// `END` last (the part's close, alone in its dyadic cell beside the kinds).
const END: usize = BYTES + KINDS.len();
const PORT_ALPHABET: usize = END + 1;

/// The readings' slots: each port's bytes, each port's closes, the letters, the switch targets.
const SLOTS: [&str; 8] = [
    "human bytes",
    "agent bytes",
    "tool bytes",
    "human closes (END)",
    "agent closes (END)",
    "tool closes (END)",
    "section letters",
    "switch targets",
];
const SLOT_COUNT: usize = SLOTS.len();
const BYTE_SLOTS: [usize; 3] = [0, 1, 2];
const SECTION_SLOTS: [usize; 5] = [3, 4, 5, 6, 7];
const ALL_SLOTS: [usize; SLOT_COUNT] = [0, 1, 2, 3, 4, 5, 6, 7];
const LETTER_SLOT: usize = 6;
const TARGET_SLOT: usize = 7;

fn end_slot(channel: usize) -> usize {
    CHANNELS.len() + channel
}

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
// the exterior boundary: the curated cut and its letters' aeons

/// **The curated cut** (`curated-cut.bin`, one little-endian u16 code a cell), each section
/// letter's aeon ordinal (`curated-cut.aeons.bin`), and its manifest's declared population,
/// alphabet, held-out start and conversations, read by the numbers after their keys.
struct CuratedCut {
    codes: Vec<usize>,
    aeons: Vec<usize>,
    conversations: usize,
    population: u64,
    held: Range<usize>,
}

#[allow(clippy::disallowed_types, clippy::disallowed_methods)]
fn read_u16(path: &str) -> Vec<usize> {
    let raw = std::fs::read(path).unwrap_or_else(|error| panic!("read a curated file: {error}"));
    assert_eq!(raw.len() % 2, 0, "u16 codes");
    raw.chunks_exact(2)
        .map(|pair| usize::from(u16::from_le_bytes([pair[0], pair[1]])))
        .collect()
}

fn read_curated(path: &str) -> CuratedCut {
    let codes = read_u16(path);
    let aeons = read_u16(
        &path
            .strip_suffix(".bin")
            .map(|stem| format!("{stem}.aeons.bin"))
            .expect("a .bin cut"),
    );
    let cells = manifest_number(path, "\"cells\":");
    let alphabet = manifest_number(path, "\"alphabet\":");
    let population = manifest_number(path, "\"population\":");
    let held_start = manifest_number(path, "\"held_out_start\":");
    let letters = manifest_number(path, "\"section_letters\":");
    let conversations = manifest_number(path, "\"conversations\":");
    assert_eq!(
        codes.len(),
        cells,
        "the cut's length is its manifest's cells"
    );
    assert!(
        cells <= population,
        "the declared population bounds the cut"
    );
    assert_eq!(alphabet, BYTES + LETTERS, "the declared chart");
    assert!(
        codes.iter().all(|&code| code < alphabet),
        "every code in the chart"
    );
    assert!(held_start <= cells, "the held-out start lies in the cut");
    assert_eq!(aeons.len(), letters, "one aeon a section letter");
    assert!(
        aeons.iter().all(|&aeon| aeon < conversations),
        "every aeon among the declared conversations"
    );
    CuratedCut {
        codes,
        aeons,
        conversations,
        population: population as u64,
        held: held_start..cells,
    }
}

/// A section letter's kind and channel.
fn section(code: usize) -> (usize, usize) {
    let letter = code - BYTES;
    (letter / CHANNELS.len(), letter % CHANNELS.len())
}

/// **A part of the cut**: its letter's position, kind and channel, its aeon, and its bytes.
struct Part {
    at: usize,
    kind: usize,
    channel: usize,
    aeon: usize,
    bytes: Range<usize>,
}

/// **The cut's parts**, read from the coded letters: the cut opens at a letter (the codec's pin),
/// and each part runs to the next letter.
fn parts(codes: &[usize], aeons: &[usize]) -> Vec<Part> {
    let positions: Vec<usize> = (0..codes.len()).filter(|&p| codes[p] >= BYTES).collect();
    assert_eq!(positions.len(), aeons.len(), "one aeon a section letter");
    assert_eq!(
        positions.first(),
        Some(&0),
        "the cut opens at a section letter"
    );
    positions
        .iter()
        .enumerate()
        .map(|(k, &at)| {
            let (kind, channel) = section(codes[at]);
            Part {
                at,
                kind,
                channel,
                aeon: aeons[k],
                bytes: at + 1..positions.get(k + 1).copied().unwrap_or(codes.len()),
            }
        })
        .collect()
}

/// **The switch targets' recency ranks**, and the check that each letter's aeon agrees with its
/// kind: `open` meets a new aeon, `switch` leaves its aeon for the one at its rank among the aeons
/// met in the cut, most recent first (`0`: not yet met), and `turn` and `part` stay (the cut's first
/// part excepted: its aeon's past lies before the cut).
fn targets(parts: &[Part]) -> Vec<Option<usize>> {
    let mut recency: Vec<usize> = Vec::new();
    parts
        .iter()
        .enumerate()
        .map(|(k, part)| {
            let met = recency.iter().position(|&aeon| aeon == part.aeon);
            let rank = match part.kind {
                OPEN => {
                    assert!(met.is_none(), "an opened aeon is new");
                    None
                }
                SWITCH => {
                    assert_ne!(met, Some(0), "a switch leaves its aeon");
                    Some(met.unwrap_or(0))
                }
                _ => {
                    if k > 0 {
                        assert_eq!(met, Some(0), "a turn or a part stays in its aeon");
                    }
                    None
                }
            };
            if let Some(at) = met {
                recency.remove(at);
            }
            recency.insert(0, part.aeon);
            rank
        })
        .collect()
}

// -------------------------------------------------------------------------------------------
// the navigators and their passages

/// **One emission**: its position on the joint clock (its population), the span and tick its
/// address is read before, its class and its reading slot.
#[derive(Clone, Copy)]
struct Emission {
    joint: usize,
    span: usize,
    at: usize,
    class: usize,
    slot: usize,
}

/// **A tree of a navigator**: its chart and its emissions in the cut's order.
struct Tree {
    alphabet: usize,
    emissions: Vec<Emission>,
}

/// **A navigator**: its spans (the ticks its addresses read), its trees at one depth, and the
/// joint position where its held-out emissions begin.
struct Navigator {
    name: String,
    spans: Vec<Vec<usize>>,
    trees: Vec<Tree>,
    development: usize,
}

/// **The flat tree's navigator**: one span, the flat bytes, each emitted on its channel's slot.
fn flat_navigator(cut: &[usize], parts: &[Part], development: usize) -> Navigator {
    let mut span = Vec::new();
    let mut emissions = Vec::new();
    for part in parts {
        for j in part.bytes.clone() {
            emissions.push(Emission {
                joint: span.len(),
                span: 0,
                at: span.len(),
                class: cut[j],
                slot: part.channel,
            });
            span.push(cut[j]);
        }
    }
    Navigator {
        name: "the flat tree".to_string(),
        spans: vec![span],
        trees: vec![Tree {
            alphabet: BYTES,
            emissions,
        }],
        development,
    }
}

/// **A port's navigator**: its spans, one per aeon, each part's kind then its bytes; its bytes
/// emitted in order and, at each of its parts' closes, `END` at the next letter's position.
fn port_navigator(cut: &[usize], parts: &[Part], channel: usize, development: usize) -> Navigator {
    let mut spans: Vec<Vec<usize>> = Vec::new();
    let mut span_of: BTreeMap<usize, usize> = BTreeMap::new();
    let mut emissions = Vec::new();
    for (k, part) in parts.iter().enumerate() {
        if let Some(previous) = k.checked_sub(1).map(|i| &parts[i])
            && previous.channel == channel
        {
            let span = span_of[&previous.aeon];
            emissions.push(Emission {
                joint: part.at,
                span,
                at: spans[span].len(),
                class: END,
                slot: end_slot(channel),
            });
        }
        if part.channel != channel {
            continue;
        }
        let span = *span_of.entry(part.aeon).or_insert_with(|| {
            spans.push(Vec::new());
            spans.len() - 1
        });
        spans[span].push(BYTES + part.kind);
        for j in part.bytes.clone() {
            emissions.push(Emission {
                joint: j,
                span,
                at: spans[span].len(),
                class: cut[j],
                slot: channel,
            });
            spans[span].push(cut[j]);
        }
    }
    Navigator {
        name: format!("the {} port's tree", CHANNELS[channel]),
        spans,
        trees: vec![Tree {
            alphabet: PORT_ALPHABET,
            emissions,
        }],
        development,
    }
}

/// **The shared port tree** (the development diagnostic): one tree for every port, so the ports
/// share their landmarks as the flat tree's bytes do, each emission still addressed on its own port
/// span in its own aeon; a span's opening tick is the whole section letter (`BYTES + kind × channel`:
/// the channel read once, at the section), and `END` is `SHARED_END`.
const SHARED_END: usize = BYTES + LETTERS;

fn shared_navigator(cut: &[usize], parts: &[Part], development: usize) -> Navigator {
    let mut spans: Vec<Vec<usize>> = Vec::new();
    let mut span_of: BTreeMap<(usize, usize), usize> = BTreeMap::new();
    let mut emissions = Vec::new();
    for (k, part) in parts.iter().enumerate() {
        if let Some(previous) = k.checked_sub(1).map(|i| &parts[i]) {
            let span = span_of[&(previous.aeon, previous.channel)];
            emissions.push(Emission {
                joint: part.at,
                span,
                at: spans[span].len(),
                class: SHARED_END,
                slot: end_slot(previous.channel),
            });
        }
        let span = *span_of.entry((part.aeon, part.channel)).or_insert_with(|| {
            spans.push(Vec::new());
            spans.len() - 1
        });
        spans[span].push(cut[part.at]);
        for j in part.bytes.clone() {
            emissions.push(Emission {
                joint: j,
                span,
                at: spans[span].len(),
                class: cut[j],
                slot: part.channel,
            });
            spans[span].push(cut[j]);
        }
    }
    Navigator {
        name: "the shared port tree (diagnostic)".to_string(),
        spans,
        trees: vec![Tree {
            alphabet: SHARED_END + 1,
            emissions,
        }],
        development,
    }
}

/// **The section navigator**: one span, the section letters (the section epochs' clock); its
/// letter tree emits each letter, its target tree each switch's rank, both at the letter's position.
fn section_navigator(
    parts: &[Part],
    ranks: &[Option<usize>],
    conversations: usize,
    development: usize,
) -> Navigator {
    let span: Vec<usize> = parts
        .iter()
        .map(|part| CHANNELS.len() * part.kind + part.channel)
        .collect();
    let letters = Tree {
        alphabet: LETTERS,
        emissions: parts
            .iter()
            .enumerate()
            .map(|(k, part)| Emission {
                joint: part.at,
                span: 0,
                at: k,
                class: span[k],
                slot: LETTER_SLOT,
            })
            .collect(),
    };
    let targets = Tree {
        alphabet: conversations,
        emissions: parts
            .iter()
            .zip(ranks)
            .enumerate()
            .filter_map(|(k, (part, rank))| {
                rank.map(|rank| Emission {
                    joint: part.at,
                    span: 0,
                    at: k,
                    class: rank,
                    slot: TARGET_SLOT,
                })
            })
            .collect(),
    };
    Navigator {
        name: "the section navigator".to_string(),
        spans: vec![span],
        trees: vec![letters, targets],
        development,
    }
}

/// **One passage of a navigator at a depth**, its emissions before `end` on the joint clock: the
/// faces' products per population and slot, the certified residuals summed, the stored nodes and
/// label letters, each tree's widths and whether its largest residual lies within its rule, the
/// rebases and the largest drift, and wall time.
struct Pass {
    depth: usize,
    codes: [[PassageCode; SLOT_COUNT]; 2],
    residuals: [Rat; 2],
    largest: Rat,
    within: bool,
    nodes: usize,
    held: usize,
    widths: Vec<Widths>,
    rebases: u64,
    drift: Rat,
    wall: u128,
}

fn declared(alphabet: usize, depth: usize, population: u64, grain: u64) -> LandmarkDeclaration {
    LandmarkDeclaration {
        alphabet,
        depth,
        forced: 0,
        population,
        grain,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    }
}

fn pass(navigator: &Navigator, depth: usize, end: usize, population: u64, grain: u64) -> Pass {
    let clock = Instant::now();
    let mut codes = [[PassageCode::new(); SLOT_COUNT]; 2];
    let mut residuals = [Rat::zero(), Rat::zero()];
    let (mut largest, mut drift) = (Rat::zero(), Rat::zero());
    let (mut within, mut nodes, mut held, mut rebases) = (true, 0, 0, 0);
    let mut widths = Vec::new();
    for tree in &navigator.trees {
        let mut landmarks = Landmarks::new(declared(tree.alphabet, depth, population, grain))
            .expect("a declared tree");
        let mut tree_largest = Rat::zero();
        for emission in tree.emissions.iter().take_while(|e| e.joint < end) {
            let span = &navigator.spans[emission.span];
            let address: Vec<Letter> = (1..=depth)
                .map(|back| {
                    emission
                        .at
                        .checked_sub(back)
                        .map_or(Letter::Boundary, |tick| Letter::Cell(span[tick]))
                })
                .collect();
            let reading = landmarks
                .receive(&address, emission.class)
                .expect("an emission within the declaration");
            let part = usize::from(emission.joint >= navigator.development);
            codes[part][emission.slot]
                .face(&reading.executed)
                .expect("a positive face");
            residuals[part] += &reading.residual;
            if reading.residual > tree_largest {
                tree_largest = reading.residual;
            }
        }
        within &= tree_largest <= landmarks.face_rule();
        if tree_largest > largest {
            largest = tree_largest;
        }
        let chart = landmarks.chart();
        rebases += chart.rebases;
        if chart.drift > drift {
            drift = chart.drift;
        }
        nodes += landmarks.nodes();
        held += landmarks.held();
        widths.push(landmarks.widths());
    }
    Pass {
        depth,
        codes,
        residuals,
        largest,
        within,
        nodes,
        held,
        widths,
        rebases,
        drift,
        wall: clock.elapsed().as_millis(),
    }
}

/// The product of a population's faces over the named slots.
fn joined(codes: &[PassageCode; SLOT_COUNT], slots: &[usize]) -> PassageCode {
    let mut all = PassageCode::new();
    for &slot in slots {
        all.join(&codes[slot]);
    }
    all
}

fn bits(code: &PassageCode) -> ExactInterval {
    code.bits().expect("an enclosure")
}

/// **The deepest depth a chart's carriers admit** at the population (`Landmarks::new` refuses past
/// it).
fn deepest_admitted(alphabet: usize, population: u64, grain: u64) -> usize {
    let mut depth = 1;
    while Landmarks::new(declared(alphabet, depth + 1, population, grain)).is_ok() {
        depth += 1;
    }
    depth
}

/// **A navigator's declared doubling family**: `D = 6, 12, 24, 48` below the deepest all its trees'
/// carriers admit, then that deepest.
fn family_of(navigator: &Navigator, population: u64, grain: u64) -> Vec<usize> {
    let deepest = navigator
        .trees
        .iter()
        .map(|tree| deepest_admitted(tree.alphabet, population, grain))
        .min()
        .expect("a tree");
    DOUBLING
        .iter()
        .copied()
        .filter(|&depth| depth < deepest)
        .chain([deepest])
        .collect()
}

/// **A passage's a-priori memory** at a depth over its emissions: each tree at most `2 n B` stored
/// nodes and `n D` label letters, at the bytes each occupies, doubled for the vectors' and the
/// table's growth.
fn projected(navigator: &Navigator, depth: usize, end: usize) -> u128 {
    navigator
        .trees
        .iter()
        .map(|tree| {
            let n = tree.emissions.iter().take_while(|e| e.joint < end).count() as u128;
            let digits = u128::from(odometer_digits(tree.alphabet));
            2 * (2 * n * digits * NODE_BYTES + n * depth as u128 * LETTER_BYTES)
        })
        .sum()
}

/// **One navigator's depth sweep on the development cells**: the family's depths in order while
/// the code falls strictly (`DepthSweep`'s rule) and no passage passed the budget.
struct Sweep {
    family: Vec<usize>,
    passes: Vec<Pass>,
    choice: DepthSweep,
    stopped: Option<String>,
}

fn sweep(navigator: &Navigator, population: u64, grain: u64) -> Sweep {
    let family = family_of(navigator, population, grain);
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
        let run = pass(navigator, depth, navigator.development, population, grain);
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

/// The dyadic ceiling of a printed upper bound on `2^(−48)`.
fn dyadic_ceiling(value: &Rat) -> Rat {
    let scale: BigInt = BigInt::from(1) << 48usize;
    let scaled = value * Rat::from_integer(scale.clone());
    Rat::new(scaled.ceil().to_integer(), scale)
}

/// A passage's lines on a population: its code in all and an emission, per slot, its certified
/// residual, and its stored parts and wall time.
fn pass_lines(pass: &Pass, part: usize, counts: &[u64; SLOT_COUNT], grain: u64) {
    let all = bits(&joined(&pass.codes[part], &ALL_SLOTS));
    let emissions: u64 = counts.iter().sum();
    let widths: Vec<String> = pass
        .widths
        .iter()
        .map(|w| {
            format!(
                "B = {}, M_p = {}, W = {}, C = {}",
                w.digits, w.face, w.carrier, w.certificate
            )
        })
        .collect();
    println!(
        "  D = {} ({}): {}; an emission {}",
        pass.depth,
        widths.join("; "),
        enclosure(&all, grain),
        per(&all, emissions, grain)
    );
    for (slot, name) in SLOTS.iter().enumerate() {
        if counts[slot] == 0 {
            continue;
        }
        let code = bits(&pass.codes[part][slot]);
        println!(
            "    {name} ({}): {}; each {}",
            counts[slot],
            reading_of(&code, grain),
            per(&code, counts[slot], grain)
        );
    }
    println!(
        "    certified residuals summed ≤ {} bits; the largest ≤ {} bits, {} each tree's rule; {} rebases, the largest drift ≤ {} bits; {} nodes stored, {} label letters; {} ms",
        exact(&dyadic_ceiling(&pass.residuals[part])),
        exact(&dyadic_ceiling(&pass.largest)),
        if pass.within { "within" } else { "ABOVE" },
        pass.rebases,
        exact(&dyadic_ceiling(&pass.drift)),
        pass.nodes,
        pass.held,
        pass.wall
    );
}

/// Each slot's emissions on each population.
fn slot_counts(navigator: &Navigator) -> [[u64; SLOT_COUNT]; 2] {
    let mut counts = [[0u64; SLOT_COUNT]; 2];
    for tree in &navigator.trees {
        for emission in &tree.emissions {
            counts[usize::from(emission.joint >= navigator.development)][emission.slot] += 1;
        }
    }
    counts
}

/// **The curated stream's code on a population**: its navigators' passes joined slot by slot (the
/// slots are disjoint across navigators).
fn curated_codes(passes: &[&Pass], part: usize) -> [PassageCode; SLOT_COUNT] {
    let mut codes = [PassageCode::new(); SLOT_COUNT];
    for pass in passes {
        for (slot, code) in codes.iter_mut().enumerate() {
            code.join(&pass.codes[part][slot]);
        }
    }
    codes
}

/// **The readings on one population**: per port, the port tree against the flat tree on identical
/// bytes (uncharged); the section cost; the whole codes charged.
fn readings(
    flat: &[PassageCode; SLOT_COUNT],
    flat_charge: u64,
    curated: &[PassageCode; SLOT_COUNT],
    curated_charge: u64,
    counts: &[u64; SLOT_COUNT],
    grain: u64,
) {
    let bytes: u64 = BYTE_SLOTS.iter().map(|&slot| counts[slot]).sum();
    println!("  a. identical bytes, each port's tree against the flat tree, uncharged:");
    for &slot in &BYTE_SLOTS {
        if counts[slot] == 0 {
            println!("    {}: none", SLOTS[slot]);
            continue;
        }
        let (a, b) = (bits(&curated[slot]), bits(&flat[slot]));
        println!(
            "    {} ({}): port {} each {}; flat {} each {}",
            SLOTS[slot],
            counts[slot],
            reading_of(&a, grain),
            per(&a, counts[slot], grain),
            reading_of(&b, grain),
            per(&b, counts[slot], grain)
        );
        ordering(
            &format!("    {}, the port against the flat tree", SLOTS[slot]),
            &a,
            &b,
            counts[slot],
            grain,
        );
    }
    let (port_bytes, flat_bytes) = (
        bits(&joined(curated, &BYTE_SLOTS)),
        bits(&joined(flat, &BYTE_SLOTS)),
    );
    ordering(
        &format!("    every byte ({bytes}), the ports against the flat tree"),
        &port_bytes,
        &flat_bytes,
        bytes,
        grain,
    );
    let letters = counts[LETTER_SLOT];
    println!("  b. the sections' cost ({letters} letters):");
    for &slot in &SECTION_SLOTS {
        if counts[slot] == 0 {
            continue;
        }
        let code = bits(&curated[slot]);
        println!(
            "    {} ({}): {}; each {}",
            SLOTS[slot],
            counts[slot],
            reading_of(&code, grain),
            per(&code, counts[slot], grain)
        );
    }
    let sections = bits(&joined(curated, &SECTION_SLOTS));
    println!(
        "    in all: {}; a letter {}",
        enclosure(&sections, grain),
        per(&sections, letters, grain)
    );
    let curated_all = charged(&bits(&joined(curated, &ALL_SLOTS)), curated_charge);
    let flat_all = charged(&bits(&joined(flat, &ALL_SLOTS)), flat_charge);
    println!(
        "  c. the whole codes: the curated stream (its bytes and its sections) charged {curated_charge} bits, against the flat stream (its bytes alone) charged {flat_charge}:"
    );
    println!("    curated {}", enclosure(&curated_all, grain));
    println!("    flat    {}", enclosure(&flat_all, grain));
    ordering(
        "    curated with its sections against flat, charged, a byte",
        &curated_all,
        &flat_all,
        bytes,
        grain,
    );
}

// -------------------------------------------------------------------------------------------
// the harness

#[allow(clippy::too_many_lines)]
fn curated_harness(curated_path: &str, flat_path: &str) {
    let setup = Instant::now();
    let cut = read_curated(curated_path);
    let (flat_bytes, flat_count, flat_held) = read_cut(flat_path);
    let declared_population = manifest_number(flat_path, "\"declared_population\":") as u64;
    assert_eq!(
        declared_population, cut.population,
        "one declared population"
    );
    let parts = parts(&cut.codes, &cut.aeons);
    let ranks = targets(&parts);

    // 0. The identical cells: the curated cut without its letters is the flat cut.
    let identical = cut.codes.iter().filter(|&&c| c < BYTES).count() == flat_count
        && cut
            .codes
            .iter()
            .filter(|&&c| c < BYTES)
            .zip(&flat_bytes)
            .all(|(&a, &b)| a == usize::from(b));
    assert!(identical, "the flat cut is the curated cut's bytes");
    let flat_held_start = cut.codes[..cut.held.start]
        .iter()
        .filter(|&&c| c < BYTES)
        .count();
    assert_eq!(flat_held.start, flat_held_start, "identical held-out bytes");

    let field = Field::declare(FieldDeclaration::campaign_one(cut.population))
        .expect("campaign 1's declared field at the population");
    let grain = exterior::receiver_grain(&field);
    assert_eq!(field.alphabet(), BYTES, "the flat chart is campaign 1's");
    let population = cut.population;

    let flat = flat_navigator(&cut.codes, &parts, flat_held.start);
    let ports: Vec<Navigator> = (0..CHANNELS.len())
        .map(|channel| port_navigator(&cut.codes, &parts, channel, cut.held.start))
        .collect();
    let sections = section_navigator(&parts, &ranks, cut.conversations, cut.held.start);
    let flat_counts = slot_counts(&flat);
    let mut counts = [[0u64; SLOT_COUNT]; 2];
    for navigator in ports.iter().chain([&sections]) {
        for (part, row) in slot_counts(navigator).iter().enumerate() {
            for (slot, &count) in row.iter().enumerate() {
                counts[part][slot] += count;
            }
        }
    }
    for part in 0..2 {
        assert_eq!(
            flat_counts[part][..CHANNELS.len()],
            counts[part][..CHANNELS.len()],
            "identical bytes on each port"
        );
    }
    let closes: u64 = counts.iter().map(|c| c[3] + c[4] + c[5]).sum();
    assert_eq!(
        closes + 1,
        parts.len() as u64,
        "a close before every letter but the first"
    );

    println!(
        "hnn_curated curated: the curated conversation source read by its own navigators (a tree per port, a navigator for its sections) against the flat stream of the same bytes (campaign 5's input; #73, #148)"
    );
    println!(
        "0. the cut: {} curated cells (|A| = 256 bytes + {LETTERS} section letters), {flat_count} flat bytes, identical: {identical}; {} letters in {} aeons met in the cut ({} declared); n* = {population}, L_R = {grain}",
        cut.codes.len(),
        parts.len(),
        parts
            .iter()
            .map(|p| p.aeon)
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        cut.conversations
    );
    println!(
        "  the aeons agree with the letters: open founds, turn and part stay, switch leaves (checked)"
    );
    for (part, name) in ["development", "held out"].iter().enumerate() {
        let letter_range = |k: usize| usize::from(parts[k].at >= cut.held.start) == part;
        let mut letters = [[0u64; 3]; 4];
        let mut ranks_seen: BTreeMap<usize, u64> = BTreeMap::new();
        for (k, p) in parts.iter().enumerate() {
            if letter_range(k) {
                letters[p.kind][p.channel] += 1;
                if let Some(rank) = ranks[k] {
                    *ranks_seen.entry(rank).or_default() += 1;
                }
            }
        }
        println!(
            "  {name}: human bytes {}, agent bytes {}, tool bytes {}; closes human {}, agent {}, tool {}; letters {}",
            counts[part][0],
            counts[part][1],
            counts[part][2],
            counts[part][3],
            counts[part][4],
            counts[part][5],
            counts[part][LETTER_SLOT]
        );
        for (kind, kind_name) in KINDS.iter().enumerate() {
            println!(
                "    {kind_name} letters: human {}, agent {}, tool {}",
                letters[kind][0], letters[kind][1], letters[kind][2]
            );
        }
        println!(
            "    switch targets by recency rank (0: an aeon not yet met in the cut): {}",
            ranks_seen
                .iter()
                .map(|(rank, count)| format!("{rank}: {count}"))
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    for (channel, port) in ports.iter().enumerate() {
        println!(
            "  the {} port: {} spans (aeons), {} ticks",
            CHANNELS[channel],
            port.spans.len(),
            port.spans.iter().map(Vec::len).sum::<usize>()
        );
    }
    println!();

    // 1. The declarations, their families and the memory.
    let shared = shared_navigator(&cut.codes, &parts, cut.held.start);
    let navigators: Vec<&Navigator> = [&flat]
        .into_iter()
        .chain(ports.iter().filter(|p| !p.trees[0].emissions.is_empty()))
        .chain([&sections, &shared])
        .collect();
    // The declared reader's navigators (the ports' and the sections'), after the flat tree; the
    // shared port tree, last, is read on the development cells only.
    let reader = 1..navigators.len() - 1;
    println!(
        "1. the declarations: each tree cell-only, the ½ stop prior, the KT node (c = ∞), stored where paths part, at n* = {population}; the flat chart 256, a port's 256 + 4 kinds + END = {PORT_ALPHABET}, the letters {LETTERS}, the targets {} (the declared conversations); each navigator's family doubling from 6 to its carriers' deepest, charged ⌈log₂⌉ of its length",
        cut.conversations
    );
    for port in ports.iter().filter(|p| p.trees[0].emissions.is_empty()) {
        println!(
            "  {}: declared, no cells; it reads nothing and is charged nothing",
            port.name
        );
    }
    let mut total_projection = 0u128;
    for navigator in &navigators {
        let depths = family_of(navigator, population, grain);
        let deepest = *depths.last().expect("a family");
        let projection = projected(navigator, deepest, navigator.development);
        total_projection += projection;
        println!(
            "  {}: D = {depths:?}, charged ⌈log₂ {}⌉ = {} bits; the a-priori memory at D = {deepest}: {projection} bytes",
            navigator.name,
            depths.len(),
            ceil_log2(&BigUint::from(depths.len())),
        );
    }
    let available = exterior::available_memory();
    let together = total_projection <= CAP && available.is_none_or(|free| total_projection <= free);
    println!(
        "  the sweeps together: {total_projection} bytes a priori, the cap {CAP}, {} bytes available: {}",
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
            let handles: Vec<_> = navigators
                .iter()
                .map(|navigator| scope.spawn(move || sweep(navigator, population, grain)))
                .collect();
            handles
                .into_iter()
                .map(|handle| handle.join().expect("a sweep"))
                .collect()
        })
    } else {
        navigators
            .iter()
            .map(|navigator| sweep(navigator, population, grain))
            .collect()
    };
    println!(
        "2. the sweeps on the development cells ({} ms in all):",
        clock.elapsed().as_millis()
    );
    for (navigator, result) in navigators.iter().zip(&sweeps) {
        println!("  {}:", navigator.name);
        let dev = slot_counts(navigator)[0];
        for run in &result.passes {
            pass_lines(run, 0, &dev, grain);
        }
        if let Some(reason) = &result.stopped {
            println!("    the sweep stopped: {reason}");
        }
    }
    println!();

    // 3. The choices.
    println!("3. the choices on the development cells:");
    for (navigator, result) in navigators.iter().zip(&sweeps) {
        println!(
            "  {}: D = {} of {:?} tried ({}), charged {} bits",
            navigator.name,
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
    let flat_charge = sweeps[0].charge();
    let curated_charge: u64 = sweeps[reader.clone()].iter().map(Sweep::charge).sum();
    println!(
        "  the curated stream's navigators charged {curated_charge} bits in all, the flat tree {flat_charge}"
    );
    println!();

    // 4. The development readings.
    println!(
        "4. the development readings ({} bytes and {} section letters), bits at L_R = {grain}:",
        BYTE_SLOTS.iter().map(|&s| counts[0][s]).sum::<u64>(),
        counts[0][LETTER_SLOT]
    );
    let chosen: Vec<&Pass> = sweeps[reader.clone()].iter().map(Sweep::chosen).collect();
    readings(
        &sweeps[0].chosen().codes[0],
        flat_charge,
        &curated_codes(&chosen, 0),
        curated_charge,
        &counts[0],
        grain,
    );
    // The diagnostic: the ports' landmarks shared, the sections' navigator unchanged.
    let shared_sweep = sweeps.last().expect("the shared port tree's sweep");
    let section_sweep = &sweeps[reader.end - 1];
    let shared_charge = shared_sweep.charge() + section_sweep.charge();
    println!(
        "  the diagnostic, development only (its held-out passage is not taken: the held-out cells are read once, by the declared reader): the shared port tree at D = {} with the section navigator, charged {shared_charge} bits:",
        shared_sweep.choice.chosen
    );
    readings(
        &sweeps[0].chosen().codes[0],
        flat_charge,
        &curated_codes(&[shared_sweep.chosen(), section_sweep.chosen()], 0),
        shared_charge,
        &counts[0],
        grain,
    );
    let (separate, together) = (
        bits(&joined(&curated_codes(&chosen, 0), &ALL_SLOTS)),
        bits(&joined(
            &curated_codes(&[shared_sweep.chosen(), section_sweep.chosen()], 0),
            &ALL_SLOTS,
        )),
    );
    ordering(
        "  the shared port tree against the trees per port, each with the section navigator, uncharged",
        &together,
        &separate,
        counts[0].iter().sum(),
        grain,
    );
    println!();

    // 5. One held-out passage of each at its chosen depth.
    let clock = Instant::now();
    let navigators = &navigators[..reader.end];
    let sweeps = &sweeps[..reader.end];
    let held_projection: u128 = navigators
        .iter()
        .zip(sweeps)
        .map(|(navigator, result)| projected(navigator, result.choice.chosen, usize::MAX))
        .sum();
    let available = exterior::available_memory();
    if held_projection > CAP || available.is_some_and(|free| held_projection > free) {
        println!(
            "5. the held-out passages REFUSED: {held_projection} bytes a priori against the cap {CAP} and {} available",
            available.map_or_else(|| "unread".to_string(), |free| free.to_string())
        );
        return;
    }
    let wholes: Vec<Pass> = std::thread::scope(|scope| {
        let handles: Vec<_> = navigators
            .iter()
            .zip(sweeps)
            .map(|(navigator, result)| {
                let depth = result.choice.chosen;
                scope.spawn(move || pass(navigator, depth, usize::MAX, population, grain))
            })
            .collect();
        handles
            .into_iter()
            .map(|handle| handle.join().expect("a passage"))
            .collect()
    });
    println!(
        "5. one held-out passage of each navigator at its chosen depth over the whole cut, every emission scored at the standing before its own deposit ({} ms; {held_projection} bytes a priori):",
        clock.elapsed().as_millis()
    );
    let checks: Vec<String> = navigators
        .iter()
        .zip(wholes.iter().zip(sweeps))
        .map(|(navigator, (whole, result))| {
            format!(
                "{} {}",
                navigator.name,
                bits(&joined(&whole.codes[0], &ALL_SLOTS))
                    == bits(&joined(&result.chosen().codes[0], &ALL_SLOTS))
            )
        })
        .collect();
    println!(
        "  checks, each passage's development code is its sweep's: {}",
        checks.join("; ")
    );
    for (navigator, whole) in navigators.iter().zip(&wholes) {
        println!("  {}, held out:", navigator.name);
        pass_lines(whole, 1, &slot_counts(navigator)[1], grain);
    }
    println!(
        "  held out ({} bytes and {} section letters), bits at L_R = {grain}:",
        BYTE_SLOTS.iter().map(|&s| counts[1][s]).sum::<u64>(),
        counts[1][LETTER_SLOT]
    );
    let held: Vec<&Pass> = wholes[reader].iter().collect();
    readings(
        &wholes[0].codes[1],
        flat_charge,
        &curated_codes(&held, 1),
        curated_charge,
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
