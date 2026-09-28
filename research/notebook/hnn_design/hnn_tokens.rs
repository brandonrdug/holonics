//! **F0 candidate 3: learned tokens with the receiving tree over them** (THE_REBUILD F0, candidate 3
//! "word contexts"; #73, #148). Count-only **development receipts**, a committed command run once in
//! release, never a test of the machinery: its own fixtures are tested below.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_tokens -- probe .local/cuts/curated-f4-passage-cut.bin
//! cargo run --release -p holonics --example hnn_tokens -- f0 .local/cuts/curated-f4-passage-cut.bin .local/cuts/curated-f4-passage-flat-cut.bin .local/cuts/f0-token-dictionary-f4.bin
//! cargo run --release -p holonics --example hnn_tokens -- release .local/cuts/curated-f5-choosing-cut.bin .local/cuts/f5-blind-input.json .local/cuts/f0-token-releases.json .local/cuts/f0-token-dictionary-f5.bin <K> <D>
//! cargo test -p holonics --example hnn_tokens
//! ```
//!
//! [definition; agent-inferred] **The lens: learned merges, never a hand-authored segmentation.**
//! On the choosing role's curated cells alone, byte-pair merges are learned greedily: the pair of
//! adjacent tokens met most often **within a part** (never across a section letter: a section letter
//! is never an operand, so no pair holds one) becomes a new token over the two, ties to the least
//! `(left, right)`, until `2^12` merges or no pair is met twice. Token `268 + i` is merge `i`; the
//! bytes keep `0..256` and the section letters `256..268` (`SectionChart::curated`). Frequency is the
//! **proposal** order, never the acceptance (the merge record of September 25, §5): the acceptance is
//! the charged code below, read at the rungs of a declared ladder.
//!
//! [definition] **The canonical parse** applies the merges in their learned order, each to every
//! occurrence left to right without overlap (realized as the least rank first, the leftmost first:
//! a merge's new pairs hold its new token, so their ranks are later). It decodes exactly to its
//! cells (`decode(encode x) = x`). It is one admitted parse of the segmentation lattice, so the tree's
//! mass of the canonical token stream is at most the lattice's `P_G(x) = Σ_(D z = x) P(z)` and its
//! `−log₂` is a valid prefix code for the bytes, conservative by the non-canonical parses' mass.
//!
//! [definition; agent-inferred] **The choosing role's charged code chooses `K` and `D`.** For each
//! `K ∈ {2^8, 2^10, 2^12}` (the first `K` merges: greedy learning makes the prefix the dictionary `K`
//! merges would learn) and each depth `D ∈ {2, 3, 4, 6}` in tokens, the receiving tree
//! (`TreeFamily`: cell-only letters over the token alphabet `268 + K`, the `½` stop prior, KT nodes,
//! `n*` the passage's population, `L_R = 16`) reads the choosing role's canonical token stream
//! prequentially. Its charged code is that stream's code plus the dictionary's description: merge
//! `i` names its two operands among the `256 + i` byte-and-merge tokens before it,
//! `2⌈log₂(256 + i)⌉` bits (the operands are never section letters, so the letters are not in their
//! alphabet), plus the Elias-gamma `2⌊log₂ K⌋ + 1` bits of `K`. The least charged enclosure chooses
//! `(K, D)`. The sweep over `3 · 4` rungs is charged `⌈log₂ 3⌉ + ⌈log₂ 4⌉ = 4` bits.
//!
//! [definition] **The comparison, like with like (F0's rule).** One passage: the chosen tree reads
//! the choosing tokens, then the validation tokens once. The flat byte tree (`D = 48`, charged its
//! recorded sweep among 5, 3 bits) reads the flat twin once. The validation **bytes'** code is each
//! byte token's face; the section letters' tokens are coded and reported apart, and not charged in
//! the like-with-like reading, since a conversation supplies them to both sides. The dictionary is
//! choosing standing (sunk before validation, like the flat tree's choosing counts); the reading
//! with it charged is printed beside. Bits are enclosures with exact endpoints, read at `L_R = 16`
//! as `n + k/16 + ε`; no decimal is printed.
//!
//! [definition; agent-inferred] **Releases on the diagnostic requests** (`release`, F5's spent split,
//! development only): merges are learned on the F5 choosing cut the same way at the `K` chosen on
//! F4's choosing role (no second choice), and the tree at F4's chosen `D` reads the whole F5
//! choosing cut. Each request branches that standing, receives the human turn letter, the
//! request's canonical tokens and the agent turn letter, then draws tokens by exact inverse CDF on the
//! tree's exact face with the seeded draw navigator (`Draw`, seed `SEED + i` for request `i`),
//! realized as the dyadic heap's descent ([`Descent`]; its first 4 draws in each release are checked
//! equal to `select_family_class` on the full face), receiving each, until a section letter (the
//! stop) or `600` released
//! bytes (the cap; an incomplete trailing UTF-8 scalar at the cap is the unresolved fibre and is
//! dropped). A release that is not UTF-8 is a typed refusal. Releases are written owner-only;
//! only counts are printed.
//!
//! [definition] The computational object is the helical pair interaction: the token navigator meeting
//! the receiving tree at its section. Of the winding guide's six general objects this touches
//! **faces and placement** (each token's face at its address) and the **tower thread** (a merge is a
//! coarsening whose restriction is its bytes; a section restricts a part, and no token crosses one);
//! the helix, the pair, the cell holonomy and the tube stay attached through the tree's owner.

#[path = "exterior.rs"]
mod exterior;

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, VecDeque};
use std::time::Instant;

use holonics::compression::landmark::context::{
    Capacity, LandmarkDeclaration, Landmarks, Letter, LetterFamily, PassageCode, Section,
    SectionChart, Splits, StopPrior, odometer_digits,
};
use holonics::holarchy::terrain::Draw;
use holonics::ratio::Rat;
use holonics::ratio::algebraic::{ExactInterval, interval_sum};
use holonics::receiver::population::{Family, TreeFamily, select_family_class};
use num_bigint::BigInt;

use exterior::{against, enclosure, per, read_curated, read_cut, reading_of, resident_set};

/// The receiver's grain `L_R`.
const GRAIN: u64 = 16;

/// The merge ladder `K ∈ {2^8, 2^10, 2^12}`.
const MERGES: [usize; 3] = [1 << 8, 1 << 10, 1 << 12];

/// The depth ladder in tokens.
const DEPTHS: [usize; 4] = [2, 3, 4, 6];

/// The flat byte tree's recorded depth and its recorded sweep among 5 (`hnn_population_curated`).
const FLAT_DEPTH: usize = 48;
const FLAT_SWEEP: u64 = 5;

/// The declared seed of the release draws (request `i` draws with `SEED + i`).
const SEED: u64 = 20_260_928;

/// The release cap in bytes.
const RELEASE_BYTES: usize = 600;

/// The probe's tokens a rung.
const PROBE_TOKENS: usize = 1 << 15;

/// The draws of each release checked against the full face's certified inverse CDF.
const VERIFIED: usize = 4;

/// A removed stream slot, and no neighbour.
const DEAD: u32 = u32::MAX;
const NONE: u32 = u32::MAX;

fn key(left: u32, right: u32) -> u64 {
    (u64::from(left) << 32) | u64::from(right)
}

fn ceil_log2(count: u64) -> u64 {
    u64::from(count.next_power_of_two().trailing_zeros())
}

fn point(bits: u64) -> ExactInterval {
    ExactInterval::point(Rat::from_integer(BigInt::from(bits)))
}

fn sum(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    interval_sum(a, b).expect("an enclosure")
}

fn minus(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower - &b.upper,
        upper: &a.upper - &b.lower,
    }
}

fn bits(code: &PassageCode) -> ExactInterval {
    code.bits().expect("an enclosure")
}

fn joined<'a>(codes: impl IntoIterator<Item = &'a PassageCode>) -> ExactInterval {
    let mut all = PassageCode::new();
    for code in codes {
        all.join(code);
    }
    bits(&all)
}

// -------------------------------------------------------------------------------------------
// the stream the merges act on

/// A token stream as a list linked in cell order: a merge keeps its left slot and removes its right.
struct Stream {
    symbols: Vec<u32>,
    previous: Vec<u32>,
    next: Vec<u32>,
}

impl Stream {
    fn new(codes: &[u32]) -> Self {
        let n = u32::try_from(codes.len()).expect("a stream within u32 slots");
        Self {
            symbols: codes.to_vec(),
            previous: (0..n).map(|i| if i == 0 { NONE } else { i - 1 }).collect(),
            next: (0..n)
                .map(|i| if i + 1 == n { NONE } else { i + 1 })
                .collect(),
        }
    }

    /// Merge the slot `at` with its successor into `token`; returns the successor's successor.
    fn merge(&mut self, at: u32, token: u32) -> u32 {
        let right = self.next[at as usize];
        let after = self.next[right as usize];
        self.symbols[at as usize] = token;
        self.symbols[right as usize] = DEAD;
        self.previous[right as usize] = NONE;
        self.next[right as usize] = NONE;
        self.next[at as usize] = after;
        if after != NONE {
            self.previous[after as usize] = at;
        }
        after
    }

    /// The living tokens in order (slot 0 always lives: a merge keeps its left slot).
    fn tokens(&self) -> Vec<u32> {
        let mut out = Vec::new();
        let mut at = if self.symbols.is_empty() { NONE } else { 0 };
        while at != NONE {
            out.push(self.symbols[at as usize]);
            at = self.next[at as usize];
        }
        out
    }
}

// -------------------------------------------------------------------------------------------
// the dictionary

/// [definition] **The learned merges** over a section chart: token `chart.alphabet() + i` is
/// `merges[i] = (left, right)`, each operand a byte or an earlier merge.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Dictionary {
    chart: SectionChart,
    merges: Vec<(u32, u32)>,
}

impl Dictionary {
    fn base(&self) -> u32 {
        u32::try_from(self.chart.alphabet()).expect("a chart within u32")
    }

    /// The token alphabet: the chart's cells and the merges.
    fn alphabet(&self) -> usize {
        self.chart.alphabet() + self.merges.len()
    }

    fn is_letter(&self, token: u32) -> bool {
        (self.chart.bytes() as u32..self.base()).contains(&token)
    }

    /// The first `k` merges.
    fn prefix(&self, k: usize) -> Self {
        Self {
            chart: self.chart,
            merges: self.merges[..k].to_vec(),
        }
    }

    /// Each merge token's bytes.
    fn expansions(&self) -> Vec<Vec<u8>> {
        let mut out: Vec<Vec<u8>> = Vec::with_capacity(self.merges.len());
        let base = self.base();
        for &(left, right) in &self.merges {
            let mut bytes = Vec::new();
            for operand in [left, right] {
                if operand < self.chart.bytes() as u32 {
                    bytes.push(u8::try_from(operand).expect("a byte"));
                } else {
                    bytes.extend_from_slice(&out[(operand - base) as usize]);
                }
            }
            out.push(bytes);
        }
        out
    }

    /// A token's byte length (a section letter's is zero).
    fn lengths(&self) -> Vec<usize> {
        let bytes = self.chart.bytes();
        let mut lengths = vec![1usize; bytes];
        lengths.extend(std::iter::repeat_n(0, self.chart.letters()));
        let expansions = self.expansions();
        lengths.extend(expansions.iter().map(Vec::len));
        lengths
    }

    /// **Decode** a token stream to its cells.
    fn decode(&self, tokens: &[u32]) -> Vec<u32> {
        let expansions = self.expansions();
        let base = self.base();
        let mut out = Vec::with_capacity(tokens.len());
        for &token in tokens {
            if token < base {
                out.push(token);
            } else {
                out.extend(
                    expansions[(token - base) as usize]
                        .iter()
                        .map(|&b| u32::from(b)),
                );
            }
        }
        out
    }

    /// **The canonical parse** (module header): the merges in learned order, each left to right
    /// without overlap, realized as the least rank first and the leftmost first.
    fn encode(&self, codes: &[u32]) -> Vec<u32> {
        if codes.is_empty() {
            return Vec::new();
        }
        let ranks: HashMap<u64, u32> = self
            .merges
            .iter()
            .enumerate()
            .map(|(rank, &(left, right))| {
                (
                    key(left, right),
                    u32::try_from(rank).expect("a rank in u32"),
                )
            })
            .collect();
        let base = self.base();
        let mut stream = Stream::new(codes);
        let mut heap: BinaryHeap<Reverse<(u32, u32)>> = (0..codes.len() - 1)
            .filter_map(|i| {
                ranks
                    .get(&key(codes[i], codes[i + 1]))
                    .map(|&rank| Reverse((rank, i as u32)))
            })
            .collect();
        while let Some(Reverse((rank, at))) = heap.pop() {
            let left = stream.symbols[at as usize];
            if left == DEAD {
                continue;
            }
            let right_slot = stream.next[at as usize];
            if right_slot == NONE
                || ranks.get(&key(left, stream.symbols[right_slot as usize])) != Some(&rank)
            {
                continue;
            }
            let token = base + rank;
            let after = stream.merge(at, token);
            let before = stream.previous[at as usize];
            if before != NONE
                && let Some(&formed) = ranks.get(&key(stream.symbols[before as usize], token))
            {
                heap.push(Reverse((formed, before)));
            }
            if after != NONE
                && let Some(&formed) = ranks.get(&key(token, stream.symbols[after as usize]))
            {
                heap.push(Reverse((formed, at)));
            }
        }
        stream.tokens()
    }

    /// **The dictionary's description** in bits: `2⌈log₂(256 + i)⌉` for merge `i` and the
    /// Elias-gamma `2⌊log₂ K⌋ + 1` of `K ≥ 1`.
    fn description(&self) -> u64 {
        let bytes = self.chart.bytes() as u64;
        let operands: u64 = (0..self.merges.len() as u64)
            .map(|i| 2 * ceil_log2(bytes + i))
            .sum();
        let k = self.merges.len() as u64;
        let gamma = if k == 0 {
            0
        } else {
            2 * u64::from(63 - k.leading_zeros()) + 1
        };
        operands + gamma
    }

    /// The owner-only wire form: `HTOK1\0\0\0`, the chart's bytes, channels and kinds and `K` as
    /// little-endian u32, then each merge's operands as little-endian u32.
    fn to_bytes(&self) -> Vec<u8> {
        let mut out = b"HTOK1\0\0\0".to_vec();
        for value in [
            self.chart.bytes(),
            self.chart.channels(),
            self.chart.kinds(),
            self.merges.len(),
        ] {
            out.extend_from_slice(&u32::try_from(value).expect("u32").to_le_bytes());
        }
        for &(left, right) in &self.merges {
            out.extend_from_slice(&left.to_le_bytes());
            out.extend_from_slice(&right.to_le_bytes());
        }
        out
    }
}

/// **Learn up to `most` merges** on the given cells (module header): the most frequent adjacent pair
/// within a part, ties to the least `(left, right)`, until `most` or no pair is met twice. Returns
/// the dictionary and the learned stream after its last merge.
fn learn(chart: SectionChart, codes: &[u32], most: usize) -> (Dictionary, Vec<u32>) {
    let base = u32::try_from(chart.alphabet()).expect("u32");
    let bytes = chart.bytes() as u32;
    let letter = |token: u32| (bytes..base).contains(&token);
    let mut stream = Stream::new(codes);
    let mut counts: HashMap<u64, u64> = HashMap::new();
    let mut at: HashMap<u64, Vec<u32>> = HashMap::new();
    for i in 0..codes.len().saturating_sub(1) {
        let (left, right) = (codes[i], codes[i + 1]);
        if !letter(left) && !letter(right) {
            *counts.entry(key(left, right)).or_insert(0) += 1;
            at.entry(key(left, right)).or_default().push(i as u32);
        }
    }
    let mut heap: BinaryHeap<(u64, Reverse<u64>)> = counts
        .iter()
        .map(|(&pair, &count)| (count, Reverse(pair)))
        .collect();
    let mut merges = Vec::new();
    while merges.len() < most {
        let Some((count, Reverse(pair))) = heap.pop() else {
            break;
        };
        if counts.get(&pair).copied().unwrap_or(0) != count {
            continue;
        }
        if count < 2 {
            break;
        }
        let (a, b) = ((pair >> 32) as u32, pair as u32);
        let token = base + merges.len() as u32;
        merges.push((a, b));
        let mut positions = at.remove(&pair).unwrap_or_default();
        positions.sort_unstable();
        positions.dedup();
        let mut touched: Vec<u64> = Vec::new();
        let mut change = |counts: &mut HashMap<u64, u64>, pair: u64, up: bool| {
            let entry = counts.entry(pair).or_insert(0);
            if up {
                *entry += 1;
            } else {
                *entry -= 1;
            }
            touched.push(pair);
        };
        for slot in positions {
            if stream.symbols[slot as usize] != a {
                continue;
            }
            let right = stream.next[slot as usize];
            if right == NONE || stream.symbols[right as usize] != b {
                continue;
            }
            let before = stream.previous[slot as usize];
            let after = stream.next[right as usize];
            if before != NONE && !letter(stream.symbols[before as usize]) {
                change(&mut counts, key(stream.symbols[before as usize], a), false);
            }
            change(&mut counts, pair, false);
            if after != NONE && !letter(stream.symbols[after as usize]) {
                change(&mut counts, key(b, stream.symbols[after as usize]), false);
            }
            stream.merge(slot, token);
            if before != NONE && !letter(stream.symbols[before as usize]) {
                let formed = key(stream.symbols[before as usize], token);
                change(&mut counts, formed, true);
                at.entry(formed).or_default().push(before);
            }
            if after != NONE && !letter(stream.symbols[after as usize]) {
                let formed = key(token, stream.symbols[after as usize]);
                change(&mut counts, formed, true);
                at.entry(formed).or_default().push(slot);
            }
        }
        touched.sort_unstable();
        touched.dedup();
        for pair in touched {
            match counts.get(&pair).copied() {
                Some(0) => {
                    counts.remove(&pair);
                }
                Some(count) => heap.push((count, Reverse(pair))),
                None => {}
            }
        }
    }
    (Dictionary { chart, merges }, stream.tokens())
}

// -------------------------------------------------------------------------------------------
// the receiving tree over tokens

fn tree(alphabet: usize, depth: usize, population: u64) -> TreeFamily {
    TreeFamily::new(
        LandmarkDeclaration {
            alphabet,
            depth,
            forced: 0,
            population,
            grain: GRAIN,
            family: LetterFamily::cells(),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        },
        0,
    )
    .expect("a declared tree")
}

/// A passage's readings: the bytes' faces per channel (human, agent, tool) and the section letters'.
#[derive(Clone, Default)]
struct Readings {
    bytes: [PassageCode; 3],
    letters: PassageCode,
    byte_count: [u64; 3],
    letter_count: u64,
    tokens: u64,
}

impl Readings {
    fn bytes(&self) -> ExactInterval {
        joined(&self.bytes)
    }

    fn all(&self) -> ExactInterval {
        joined(self.bytes.iter().chain([&self.letters]))
    }

    fn byte_total(&self) -> u64 {
        self.byte_count.iter().sum()
    }
}

/// Read a token stream through a tree, each token scored at the standing before its deposit.
fn read(
    tree: &mut TreeFamily,
    tokens: &[u32],
    dictionary: &Dictionary,
    lengths: &[usize],
    open: &mut Option<usize>,
    readings: &mut Readings,
) {
    for &token in tokens {
        let face = tree
            .receive(token as usize)
            .expect("a token of the alphabet");
        readings.tokens += 1;
        if dictionary.is_letter(token) {
            readings.letters.face(&face).expect("a positive face");
            readings.letter_count += 1;
            *open = Some(
                dictionary
                    .chart
                    .section(token as usize)
                    .expect("a letter")
                    .channel,
            );
        } else {
            let channel = open.expect("a part opens at a section letter");
            readings.bytes[channel]
                .face(&face)
                .expect("a positive face");
            readings.byte_count[channel] += lengths[token as usize] as u64;
        }
    }
}

/// [definition] **The exact inverse CDF by the dyadic heap's descent.** The tree's exact face is its
/// splits multiplied down the dyadic heap of the class index, most significant digit first
/// (`LandmarkFace::of_splits`: at a splitting cell the children take `z/2^M` and `1 − z/2^M`, at a
/// held cell that does not split the left child takes all). The classes' order is the leaves'
/// left-to-right order, so the class whose cumulative interval `[F(c − 1), F(c))` holds the draw `u`
/// is found by descent: at a splitting cell go left when `u < z/2^M` and read `u/(z/2^M)`, else go
/// right and read `(u − z/2^M)/(1 − z/2^M)`. This is the inverse CDF of `select_family_class` on the
/// same face, reading `D` splits' worth of cells instead of every class (checked against it in the
/// tests and on sampled release draws).
struct Descent {
    digits: usize,
    split: Vec<Option<usize>>,
}

impl Descent {
    fn new(tree: &Landmarks) -> Self {
        let digits = usize::try_from(odometer_digits(tree.declaration().alphabet)).expect("digits");
        let mut split = vec![None; 1 << digits];
        for (index, h) in tree.splitting().into_iter().enumerate() {
            split[h] = Some(index);
        }
        Self { digits, split }
    }

    fn class(&self, splits: &Splits, draw: &Rat) -> usize {
        let scale = BigInt::from(1u8) << usize::try_from(splits.face_bits).expect("face bits");
        let one = Rat::from_integer(BigInt::from(1u8));
        let mut u = draw.clone();
        let mut h = 1usize;
        for _ in 0..self.digits {
            h = match self.split[h] {
                Some(index) => {
                    let zero = Rat::new(BigInt::from(splits.numerators[index]), scale.clone());
                    if u < zero {
                        u /= &zero;
                        2 * h
                    } else {
                        u = (u - &zero) / (&one - &zero);
                        2 * h + 1
                    }
                }
                None => 2 * h,
            };
        }
        h - (1 << self.digits)
    }
}

/// The address a tree family reads its next cell at (`TreeFamily`'s own law, cell-only letters):
/// the last `D` tokens, newest first, `Boundary` before the first.
fn address(past: &VecDeque<u32>, depth: usize) -> Vec<Letter> {
    (0..depth)
        .map(|back| {
            past.len()
                .checked_sub(back + 1)
                .map_or(Letter::Boundary, |at| Letter::Cell(past[at] as usize))
        })
        .collect()
}

/// Receive a token into a tree and its tracked address.
fn push(tree: &mut TreeFamily, past: &mut VecDeque<u32>, token: u32) -> Rat {
    let face = tree
        .receive(token as usize)
        .expect("a token of the alphabet");
    past.push_back(token);
    if past.len() > tree.tree().declaration().depth {
        past.pop_front();
    }
    face
}

/// **One exact draw** at a tree's current address: the descent's class, and, when `verify`, the
/// certified inverse CDF of the full exact face asserted equal to it.
fn draw_class(
    tree: &TreeFamily,
    past: &VecDeque<u32>,
    descent: &Descent,
    draw: &Rat,
    verify: bool,
) -> usize {
    let depth = tree.tree().declaration().depth;
    let splits = tree
        .tree()
        .splits(&address(past, depth))
        .expect("the splits at the address");
    let class = descent.class(&splits, draw);
    if verify {
        let face = tree.face().expect("the exact face");
        let certified = select_family_class(&face, draw)
            .expect("an exact normalized face certifies its class")
            .class;
        assert_eq!(class, certified, "the descent is the face's inverse CDF");
    }
    class
}

fn to_u32(codes: &[usize]) -> Vec<u32> {
    codes
        .iter()
        .map(|&code| u32::try_from(code).expect("a code in u32"))
        .collect()
}

/// Counts the bytes a standing encodes to.
fn standing_bytes(tree: &TreeFamily) -> u64 {
    tree.encode_checkpoint().len() as u64
}

// -------------------------------------------------------------------------------------------
// the exterior: owner-only files and the blind input's strings

#[allow(clippy::disallowed_types, clippy::disallowed_methods)]
fn write_private(path: &str, bytes: &[u8]) {
    use std::io::Write;
    use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
    let parent = std::path::Path::new(path)
        .parent()
        .expect("a private directory");
    assert_eq!(
        std::fs::metadata(parent)
            .expect("the private directory")
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
        .expect("an owner-only file");
    file.set_permissions(std::fs::Permissions::from_mode(0o600))
        .expect("owner-only");
    file.write_all(bytes).expect("write the private file");
    file.sync_all().expect("durable");
}

/// One JSON string's value, from just after its opening quote; returns it and the index after its
/// closing quote.
fn json_string(text: &str, start: usize) -> (String, usize) {
    let mut out = String::new();
    let mut chars = text[start..].char_indices();
    let hex = |chars: &mut std::str::CharIndices<'_>| -> u32 {
        (0..4).fold(0, |value, _| {
            let (_, c) = chars.next().expect("a hex digit");
            value * 16 + c.to_digit(16).expect("a hex digit")
        })
    };
    while let Some((offset, c)) = chars.next() {
        match c {
            '"' => return (out, start + offset + 1),
            '\\' => {
                let (_, escaped) = chars.next().expect("an escape");
                match escaped {
                    '"' => out.push('"'),
                    '\\' => out.push('\\'),
                    '/' => out.push('/'),
                    'b' => out.push('\u{8}'),
                    'f' => out.push('\u{c}'),
                    'n' => out.push('\n'),
                    'r' => out.push('\r'),
                    't' => out.push('\t'),
                    'u' => {
                        let unit = hex(&mut chars);
                        let scalar = if (0xD800..0xDC00).contains(&unit) {
                            assert_eq!(chars.next().map(|(_, c)| c), Some('\\'));
                            assert_eq!(chars.next().map(|(_, c)| c), Some('u'));
                            let low = hex(&mut chars);
                            0x10000 + ((unit - 0xD800) << 10) + (low - 0xDC00)
                        } else {
                            unit
                        };
                        out.push(char::from_u32(scalar).expect("a scalar"));
                    }
                    other => panic!("an unknown escape {other:?}"),
                }
            }
            c => out.push(c),
        }
    }
    panic!("an unterminated JSON string")
}

/// Every value of a string-valued key, in document order (the blind input is compact JSON; an
/// escaped quote never forms `"key":"`).
fn json_strings(text: &str, name: &str) -> Vec<String> {
    let pattern = format!("\"{name}\":\"");
    let mut out = Vec::new();
    let mut from = 0;
    while let Some(found) = text[from..].find(&pattern) {
        let (value, end) = json_string(text, from + found + pattern.len());
        out.push(value);
        from = end;
    }
    out
}

fn json_quote(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// -------------------------------------------------------------------------------------------
// the harnesses

/// The choosing and validation cells of a curated passage cut, split at its held-out start.
#[allow(clippy::type_complexity)]
fn passage(curated_path: &str) -> (SectionChart, Vec<u32>, Vec<u32>, u64) {
    let chart = SectionChart::curated();
    let cut = read_curated(curated_path, &chart);
    let codes = to_u32(&cut.codes);
    let start = cut.held.start;
    assert!(
        chart.section(codes[start] as usize).is_some(),
        "validation opens at a section letter, so no part spans the split"
    );
    (
        chart,
        codes[..start].to_vec(),
        codes[start..].to_vec(),
        cut.population,
    )
}

/// **`probe`**: the merges learned, then each rung's tree over the first `2^15` choosing tokens,
/// timed, and the full work projected against ten minutes and 20 GB.
fn probe(curated_path: &str) {
    let clock = Instant::now();
    let (chart, choosing, validation, population) = passage(curated_path);
    let learning = Instant::now();
    let (dictionary, _) = learn(chart, &choosing, MERGES[MERGES.len() - 1]);
    let learn_ms = learning.elapsed().as_millis();
    println!(
        "hnn_tokens probe: {} choosing cells, {} validation cells; {} merges learned in {learn_ms} ms",
        choosing.len(),
        validation.len(),
        dictionary.merges.len()
    );
    let mut projected_ms: u128 = 0;
    for &k in &MERGES {
        let prefix = dictionary.prefix(k);
        let encoding = Instant::now();
        let tokens = prefix.encode(&choosing);
        let encode_ms = encoding.elapsed().as_millis();
        println!(
            "  K = {k}: {} choosing tokens ({} cells), encoded in {encode_ms} ms",
            tokens.len(),
            choosing.len()
        );
        // The validation tokens, projected at the choosing ratio (validation is not read here).
        let scale = |count: usize| -> u128 {
            (count as u128 * (choosing.len() + validation.len()) as u128) / choosing.len() as u128
        };
        for &depth in &DEPTHS {
            let mut family = tree(prefix.alphabet(), depth, population);
            let reading = Instant::now();
            let probe = &tokens[..tokens.len().min(PROBE_TOKENS)];
            for &token in probe {
                family.receive(token as usize).expect("a token");
            }
            let probe_ms = reading.elapsed().as_millis();
            let sweep = probe_ms * tokens.len() as u128 / probe.len() as u128;
            projected_ms += sweep;
            println!(
                "    D = {depth}: {} tokens in {probe_ms} ms; the choosing pass projects {sweep} ms, the whole passage {} ms; resident set {:?}",
                probe.len(),
                probe_ms * scale(tokens.len()) / probe.len() as u128,
                resident_set()
            );
        }
    }
    // The release face at the largest rung: the full exact face against the heap's descent.
    let prefix = dictionary.prefix(MERGES[MERGES.len() - 1]);
    let tokens = prefix.encode(&choosing);
    let depth = DEPTHS[DEPTHS.len() - 1];
    let mut family = tree(prefix.alphabet(), depth, population);
    let mut past = VecDeque::new();
    for &token in &tokens[..tokens.len().min(PROBE_TOKENS)] {
        push(&mut family, &mut past, token);
    }
    let descent = Descent::new(family.tree());
    let mut draw = Draw::new(SEED);
    let values: Vec<Rat> = (0..64)
        .map(|_| Rat::new(BigInt::from(draw.next()), BigInt::from(1u8) << 64))
        .collect();
    let facing = Instant::now();
    for value in &values[..16] {
        draw_class(&family, &past, &descent, value, true);
    }
    let face_ms = facing.elapsed().as_millis();
    let descending = Instant::now();
    for value in &values {
        draw_class(&family, &past, &descent, value, false);
    }
    let descent_ms = descending.elapsed().as_millis();
    println!(
        "  the release draw at K = {}, D = {depth}: 16 full-face draws (each checked equal to the descent) in {face_ms} ms; 64 descents in {descent_ms} ms; 32 releases of at most {RELEASE_BYTES} draws by descent project {} ms, with 4 full-face checks each {} ms",
        MERGES[MERGES.len() - 1],
        (descent_ms * 32 * RELEASE_BYTES as u128).div_ceil(64),
        face_ms * 32 * 4 / 16
    );
    println!(
        "  the choosing sweep projects {projected_ms} ms (limit 600000); probe wall {} ms; resident set (now, peak) {:?}",
        clock.elapsed().as_millis(),
        resident_set()
    );
}

/// The sweep's rung: its charged code and receipt.
struct Rung {
    merges: usize,
    depth: usize,
    stream: ExactInterval,
    charged: ExactInterval,
    tokens: u64,
    ms: u128,
}

/// **`f0`** (module header): the choosing sweep, the one validation passage against the flat tree.
#[allow(clippy::too_many_lines)]
fn f0(curated_path: &str, flat_path: &str, dictionary_path: &str) {
    let clock = Instant::now();
    let (chart, choosing, validation, population) = passage(curated_path);
    let (flat_bytes, flat_count, flat_held) = read_cut(flat_path);
    let byte_of = |codes: &[u32]| -> Vec<u8> {
        codes
            .iter()
            .filter(|&&code| chart.section(code as usize).is_none())
            .map(|&code| u8::try_from(code).expect("a byte"))
            .collect()
    };
    let (choosing_bytes, validation_bytes) = (byte_of(&choosing), byte_of(&validation));
    assert_eq!(
        choosing_bytes.len() + validation_bytes.len(),
        flat_count,
        "the flat cut is the curated cut's bytes"
    );
    assert_eq!(flat_held.start, choosing_bytes.len(), "identical split");
    assert!(
        choosing_bytes
            .iter()
            .chain(&validation_bytes)
            .zip(&flat_bytes)
            .all(|(a, b)| a == b),
        "identical bytes"
    );
    println!(
        "hnn_tokens f0: F0 candidate 3 on F4's development passage: learned tokens with the receiving tree over them, against the flat byte tree (#73, #148)"
    );
    println!(
        "0. the cut: {} choosing cells ({} bytes), {} validation cells ({} bytes); n* = {population}, L_R = {GRAIN}",
        choosing.len(),
        choosing_bytes.len(),
        validation.len(),
        validation_bytes.len()
    );

    // 1. The merges, on the choosing cells only.
    let learning = Instant::now();
    let (dictionary, learned) = learn(chart, &choosing, MERGES[MERGES.len() - 1]);
    let learn_ms = learning.elapsed().as_millis();
    assert_eq!(
        dictionary.merges.len(),
        MERGES[MERGES.len() - 1],
        "the ladder's top rung is learned"
    );
    assert!(
        dictionary
            .merges
            .iter()
            .all(|&(a, b)| !dictionary.is_letter(a) && !dictionary.is_letter(b)),
        "no merge holds a section letter"
    );
    assert_eq!(
        dictionary.encode(&choosing),
        learned,
        "the canonical parse is the learned stream"
    );
    println!(
        "1. the merges, learned on the choosing cells only: {} in {learn_ms} ms; no operand is a section letter",
        dictionary.merges.len()
    );

    // 2. The sweep on the choosing role.
    let sweep_clock = Instant::now();
    let mut rungs: Vec<Rung> = Vec::new();
    for &k in &MERGES {
        let prefix = dictionary.prefix(k);
        let lengths = prefix.lengths();
        let tokens = prefix.encode(&choosing);
        assert_eq!(
            prefix.decode(&tokens),
            choosing,
            "the parse decodes exactly"
        );
        let description = prefix.description();
        println!(
            "2. K = {k}: alphabet {}, {} choosing tokens, the dictionary's description {description} bits",
            prefix.alphabet(),
            tokens.len()
        );
        for &depth in &DEPTHS {
            let rung_clock = Instant::now();
            let mut family = tree(prefix.alphabet(), depth, population);
            let mut readings = Readings::default();
            read(
                &mut family,
                &tokens,
                &prefix,
                &lengths,
                &mut None,
                &mut readings,
            );
            let stream = readings.all();
            let charged = sum(&stream, &point(description));
            let ms = rung_clock.elapsed().as_millis();
            println!(
                "    D = {depth}: the stream {}; charged {}; {ms} ms",
                reading_of(&stream, GRAIN),
                reading_of(&charged, GRAIN)
            );
            rungs.push(Rung {
                merges: k,
                depth,
                stream,
                charged,
                tokens: readings.tokens,
                ms,
            });
        }
    }
    let chosen = rungs
        .iter()
        .enumerate()
        .min_by(|a, b| a.1.charged.lower.cmp(&b.1.charged.lower))
        .map(|(index, _)| index)
        .expect("a rung");
    let decided = rungs
        .iter()
        .enumerate()
        .all(|(index, rung)| index == chosen || rungs[chosen].charged.upper < rung.charged.lower);
    let (k, depth) = (rungs[chosen].merges, rungs[chosen].depth);
    println!(
        "  chosen by the choosing role's charged code: K = {k}, D = {depth} ({} tokens, stream {}, {} ms), decided below every other rung: {decided}; sweep {} ms",
        rungs[chosen].tokens,
        reading_of(&rungs[chosen].stream, GRAIN),
        rungs[chosen].ms,
        sweep_clock.elapsed().as_millis()
    );
    let runner = rungs
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != chosen)
        .min_by(|a, b| a.1.charged.lower.cmp(&b.1.charged.lower))
        .map(|(_, rung)| rung)
        .expect("a second rung");
    println!(
        "  the next rung K = {}, D = {}: charged {} above the chosen by {}",
        runner.merges,
        runner.depth,
        reading_of(&runner.charged, GRAIN),
        reading_of(&minus(&runner.charged, &rungs[chosen].charged), GRAIN)
    );
    let prefix = dictionary.prefix(k);
    let wire = prefix.to_bytes();
    write_private(dictionary_path, &wire);
    println!(
        "  the chosen dictionary written owner-only: {} bytes ({} merges; its SHA-256 is read by the exterior)",
        wire.len(),
        k
    );
    println!();

    // 3. One passage: the chosen tree reads the choosing tokens, then the validation tokens once.
    let passage_clock = Instant::now();
    let lengths = prefix.lengths();
    let choosing_tokens = prefix.encode(&choosing);
    let validation_tokens = prefix.encode(&validation);
    assert_eq!(
        prefix.decode(&validation_tokens),
        validation,
        "the parse decodes exactly"
    );
    let mut family = tree(prefix.alphabet(), depth, population);
    let mut open = None;
    let mut parts = [Readings::default(), Readings::default()];
    read(
        &mut family,
        &choosing_tokens,
        &prefix,
        &lengths,
        &mut open,
        &mut parts[0],
    );
    assert_eq!(
        parts[0].all(),
        rungs[chosen].stream,
        "the passage's choosing code is the sweep's"
    );
    read(
        &mut family,
        &validation_tokens,
        &prefix,
        &lengths,
        &mut open,
        &mut parts[1],
    );
    let passage_ms = passage_clock.elapsed().as_millis();
    let standing = standing_bytes(&family);
    let resident = resident_set();
    drop(family);
    let cells = (choosing.len() + validation.len()) as u64;
    let tokens = parts[0].tokens + parts[1].tokens;
    let standing_all = standing + wire.len() as u64;
    println!(
        "3. one passage of the token tree (K = {k}, D = {depth}): {passage_ms} ms; resident set (now, peak) {resident:?} bytes"
    );
    println!(
        "  standing: the tree {standing} bytes and the dictionary {} bytes, {standing_all} bytes after {cells} cells ({} a cell, remainder {}) and {tokens} tokens ({} a token, remainder {})",
        wire.len(),
        standing_all / cells,
        standing_all % cells,
        standing_all / tokens,
        standing_all % tokens
    );

    // 4. The flat tree over the flat twin, once.
    let flat_clock = Instant::now();
    let mut flat = tree(256, FLAT_DEPTH, population);
    let mut flat_parts = [Readings::default(), Readings::default()];
    let channels: Vec<usize> = {
        let mut open = None;
        choosing
            .iter()
            .chain(&validation)
            .filter_map(|&code| match chart.section(code as usize) {
                Some(section) => {
                    open = Some(section.channel);
                    None
                }
                None => Some(open.expect("a part opens at a letter")),
            })
            .collect()
    };
    for (position, &byte) in flat_bytes.iter().enumerate() {
        let face = flat.receive(usize::from(byte)).expect("a byte");
        let part = &mut flat_parts[usize::from(position >= flat_held.start)];
        part.bytes[channels[position]]
            .face(&face)
            .expect("a positive face");
        part.byte_count[channels[position]] += 1;
        part.tokens += 1;
    }
    let flat_ms = flat_clock.elapsed().as_millis();
    let flat_standing = standing_bytes(&flat);
    drop(flat);
    println!(
        "4. the flat tree at D = {FLAT_DEPTH}, one passage over the flat twin: {flat_ms} ms; standing {flat_standing} bytes after {flat_count} cells ({} a cell, remainder {})",
        flat_standing / flat_count as u64,
        flat_standing % flat_count as u64
    );
    println!();

    // 5. The readings.
    let sweep_charge = ceil_log2(MERGES.len() as u64) + ceil_log2(DEPTHS.len() as u64);
    let flat_charge = ceil_log2(FLAT_SWEEP);
    let names = ["human", "agent", "tool"];
    for (part, name) in ["choosing", "validation"].iter().enumerate() {
        let (tokens, flat) = (&parts[part], &flat_parts[part]);
        assert_eq!(
            tokens.byte_count, flat.byte_count,
            "the same bytes on each channel"
        );
        let count = tokens.byte_total();
        println!(
            "{}. {name} ({count} bytes in {} tokens, {} section letters), bits at L_R = {GRAIN}:",
            5 + part,
            tokens.tokens - tokens.letter_count,
            tokens.letter_count
        );
        for (channel, channel_name) in names.iter().enumerate() {
            let (a, b) = (bits(&tokens.bytes[channel]), bits(&flat.bytes[channel]));
            let n = tokens.byte_count[channel];
            println!(
                "  {channel_name} bytes ({n}): tokens {} (a byte {}), flat {} (a byte {}); tokens {} flat by {}",
                reading_of(&a, GRAIN),
                per(&a, n, GRAIN),
                reading_of(&b, GRAIN),
                per(&b, n, GRAIN),
                against(&a, &b),
                reading_of(&minus(&a, &b), GRAIN)
            );
        }
        let (a, b) = (tokens.bytes(), flat.bytes());
        println!(
            "  every byte: tokens {}; a byte {}",
            enclosure(&a, GRAIN),
            per(&a, count, GRAIN)
        );
        println!(
            "  every byte: flat {}; a byte {}",
            enclosure(&b, GRAIN),
            per(&b, count, GRAIN)
        );
        let letters = bits(&tokens.letters);
        println!(
            "  the section letters, coded by the token tree only (not charged like with like): {} over {} letters",
            reading_of(&letters, GRAIN),
            tokens.letter_count
        );
        let (charged, flat_charged) = (sum(&a, &point(sweep_charge)), sum(&b, &point(flat_charge)));
        let delta = minus(&charged, &flat_charged);
        println!(
            "  like with like: the token bytes charged {sweep_charge} (the sweep) {} against the flat bytes charged {flat_charge} {}: {}, difference {}, a byte {}",
            reading_of(&charged, GRAIN),
            reading_of(&flat_charged, GRAIN),
            against(&charged, &flat_charged),
            enclosure(&delta, GRAIN),
            per(&delta, count, GRAIN)
        );
        let with_dictionary = sum(&charged, &point(prefix.description()));
        println!(
            "  beside: with the dictionary's {} bits charged as well, {} against flat, difference {}",
            prefix.description(),
            against(&with_dictionary, &flat_charged),
            reading_of(&minus(&with_dictionary, &flat_charged), GRAIN)
        );
    }
    println!(
        "wall time in all: {} ms; resident set (now, peak) {:?} bytes",
        clock.elapsed().as_millis(),
        resident_set()
    );
}

/// **`release`** (module header): the F5 choosing standing, 32 branches, owner-only releases.
#[allow(clippy::too_many_lines, clippy::disallowed_methods)]
fn release(
    choosing_path: &str,
    input_path: &str,
    output_path: &str,
    dictionary_path: &str,
    k: usize,
    depth: usize,
) {
    let clock = Instant::now();
    let chart = SectionChart::curated();
    let cut = read_curated(choosing_path, &chart);
    let codes = to_u32(&cut.codes);
    let (dictionary, learned) = learn(chart, &codes, k);
    assert_eq!(dictionary.merges.len(), k, "K merges learned");
    let wire = dictionary.to_bytes();
    write_private(dictionary_path, &wire);
    let lengths = dictionary.lengths();
    let expansions = dictionary.expansions();
    let mut base = tree(dictionary.alphabet(), depth, cut.population);
    let mut readings = Readings::default();
    read(
        &mut base,
        &learned,
        &dictionary,
        &lengths,
        &mut None,
        &mut readings,
    );
    assert_eq!(dictionary.decode(&learned), codes, "exact decode");
    println!(
        "hnn_tokens release: the F5 choosing cut, {} cells in {} tokens (K = {k} merges learned on it, dictionary {} bytes written owner-only; D = {depth}); standing {} bytes; preparation {} ms; resident set {:?}",
        codes.len(),
        learned.len(),
        wire.len(),
        standing_bytes(&base),
        clock.elapsed().as_millis(),
        resident_set()
    );
    let input = std::fs::read_to_string(input_path).expect("the owner-only blind input");
    let requests = json_strings(&input, "request");
    assert_eq!(requests.len(), 32, "the 32 diagnostic requests");
    let human = chart
        .letter(Section {
            kind: 2,
            channel: 0,
        })
        .expect("the human turn");
    let agent = chart
        .letter(Section {
            kind: 2,
            channel: 1,
        })
        .expect("the agent turn");
    let descent = Descent::new(base.tree());
    let base_past: VecDeque<u32> = learned[learned.len().saturating_sub(depth)..]
        .iter()
        .copied()
        .collect();
    let mut cases = Vec::new();
    let (mut stopped, mut capped, mut refused, mut released_bytes, mut drawn, mut checked) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);
    let mut longest_ms = 0u128;
    for (index, request) in requests.iter().enumerate() {
        let started = Instant::now();
        let mut branch = base.clone();
        let mut past = base_past.clone();
        let request_codes: Vec<u32> = request.bytes().map(u32::from).collect();
        let request_tokens = dictionary.encode(&request_codes);
        push(&mut branch, &mut past, human as u32);
        for &token in &request_tokens {
            push(&mut branch, &mut past, token);
        }
        push(&mut branch, &mut past, agent as u32);
        let mut draw = Draw::new(SEED + index as u64);
        let mut bytes: Vec<u8> = Vec::new();
        let mut stop = false;
        let mut draws = 0usize;
        while bytes.len() < RELEASE_BYTES {
            let value = Rat::new(BigInt::from(draw.next()), BigInt::from(1u8) << 64);
            let verify = draws < VERIFIED;
            let class = draw_class(&branch, &past, &descent, &value, verify);
            checked += usize::from(verify);
            draws += 1;
            let token = u32::try_from(class).expect("u32");
            push(&mut branch, &mut past, token);
            drawn += 1;
            if dictionary.is_letter(token) {
                stop = true;
                break;
            }
            if token < 256 {
                bytes.push(u8::try_from(token).expect("a byte"));
            } else {
                bytes.extend_from_slice(&expansions[(token - dictionary.base()) as usize]);
            }
        }
        if !stop {
            // The cap: an incomplete trailing UTF-8 scalar is the unresolved fibre, dropped.
            if let Err(error) = std::str::from_utf8(&bytes)
                && error.error_len().is_none()
            {
                bytes.truncate(error.valid_up_to());
            }
        }
        let text = match String::from_utf8(bytes) {
            Ok(text) => {
                released_bytes += text.len();
                if stop {
                    stopped += 1;
                } else {
                    capped += 1;
                }
                text
            }
            Err(_) => {
                refused += 1;
                "[typed refusal: invalid-utf8-token-path]".to_string()
            }
        };
        longest_ms = longest_ms.max(started.elapsed().as_millis());
        cases.push(format!(
            "{{\"request\":{},\"responses\":{{\"athena\":{{\"label\":{},\"text\":{}}}}}}}",
            json_quote(request),
            json_quote("F0 candidate 3: token tree release, development diagnostic"),
            json_quote(&text)
        ));
        println!(
            "  request {index}: {} request tokens; {}; branch and draws {} ms",
            request_tokens.len(),
            if text.starts_with("[typed refusal") {
                "typed refusal (invalid UTF-8)".to_string()
            } else if stop {
                format!("stopped at a section letter, {} bytes", text.len())
            } else {
                format!("capped, {} bytes", text.len())
            },
            started.elapsed().as_millis()
        );
    }
    let document = format!(
        "{{\"schema\":\"holonics.f0-token-releases.v1\",\"cases\":[{}]}}\n",
        cases.join(",")
    );
    write_private(output_path, document.as_bytes());
    println!(
        "release aggregate: {} requests; stopped at a section letter {stopped}; capped at {RELEASE_BYTES} bytes {capped}; typed refusals {refused}; released bytes {released_bytes}; tokens drawn {drawn}, of which {checked} checked equal to the full face's certified inverse CDF; longest request {longest_ms} ms; wall {} ms; resident set (now, peak) {:?}",
        requests.len(),
        clock.elapsed().as_millis(),
        resident_set()
    );
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("probe") => probe(&args[2]),
        Some("f0") => f0(&args[2], &args[3], &args[4]),
        Some("release") => release(
            &args[2],
            &args[3],
            &args[4],
            &args[5],
            args[6].parse().expect("K"),
            args[7].parse().expect("D"),
        ),
        _ => panic!(
            "hnn_tokens probe <curated cut> | f0 <curated cut> <flat cut> <dictionary out> | release <choosing cut> <blind input> <releases out> <dictionary out> <K> <D>"
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A fixture over the curated chart: parts of repeated words, each opened by a letter.
    fn fixture(chart: SectionChart) -> Vec<u32> {
        let letter = |kind, channel| chart.letter(Section { kind, channel }).unwrap() as u32;
        let mut codes = Vec::new();
        for (index, part) in [
            "the cat sat on the mat",
            "aaaa aaa the the cat",
            "abababa, the hat",
            "",
            "cat cat cat mat",
        ]
        .iter()
        .enumerate()
        {
            codes.push(letter(index % 4, index % 3));
            codes.extend(part.bytes().map(u32::from));
        }
        codes
    }

    #[test]
    fn the_canonical_parse_decodes_exactly_and_is_the_learned_stream() {
        let chart = SectionChart::curated();
        let codes = fixture(chart);
        let (dictionary, learned) = learn(chart, &codes, 64);
        assert!(!dictionary.merges.is_empty());
        assert_eq!(dictionary.encode(&codes), learned);
        assert_eq!(dictionary.decode(&learned), codes);
        for k in 0..=dictionary.merges.len() {
            let prefix = dictionary.prefix(k);
            let tokens = prefix.encode(&codes);
            assert_eq!(prefix.decode(&tokens), codes, "K = {k}");
            let (again, stream) = learn(chart, &codes, k);
            assert_eq!(
                again, prefix,
                "greedy learning: the prefix is the K-merge dictionary"
            );
            assert_eq!(stream, tokens, "K = {k}");
        }
        // Overlapping runs merge left to right: `aaa` under `(a, a)` is `[aa, a]`.
        let run: Vec<u32> = [chart.alphabet() as u32 - 1]
            .into_iter()
            .chain("aaa".bytes().map(u32::from))
            .collect();
        let pair = Dictionary {
            chart,
            merges: vec![(u32::from(b'a'), u32::from(b'a'))],
        };
        let base = chart.alphabet() as u32;
        assert_eq!(pair.encode(&run), vec![run[0], base, u32::from(b'a')]);
    }

    #[test]
    fn the_merges_never_cross_a_section_letter() {
        let chart = SectionChart::curated();
        let letter = chart
            .letter(Section {
                kind: 3,
                channel: 1,
            })
            .unwrap() as u32;
        // One-byte parts `x`, `y`, `x`, `y`, …: the most frequent adjacency of bytes crosses a letter.
        let mut codes = vec![letter];
        for _ in 0..40 {
            codes.extend([u32::from(b'x'), letter, u32::from(b'y'), letter]);
        }
        codes.extend("zw zw".bytes().map(u32::from));
        let (dictionary, learned) = learn(chart, &codes, 16);
        assert!(
            dictionary
                .merges
                .iter()
                .all(|&(a, b)| !dictionary.is_letter(a) && !dictionary.is_letter(b))
        );
        let (x, y) = (u32::from(b'x'), u32::from(b'y'));
        assert!(
            !dictionary
                .merges
                .iter()
                .any(|&pair| pair == (x, y) || pair == (y, x))
        );
        assert_eq!(
            dictionary.merges.len(),
            1,
            "only `zw` is met twice within a part"
        );
        // Every letter keeps its place: the tokens' letters are the cells' letters.
        let letters = |tokens: &[u32]| -> Vec<u32> {
            tokens
                .iter()
                .copied()
                .filter(|&t| dictionary.is_letter(t))
                .collect()
        };
        assert_eq!(letters(&learned), letters(&codes));
    }

    /// **The code is a valid prefix code on a tiny chart** (module header): over every byte string
    /// `x` of at most `L` bytes, the tree's exact mass of the canonical stream `open · parse(x) · stop`
    /// sums to at most one, and strictly below (the non-canonical parses and the other letters keep
    /// mass).
    #[test]
    fn the_canonical_code_is_a_prefix_code() {
        let chart = SectionChart::new(2, 2, 1).unwrap();
        let (open, stop) = (2u32, 3u32);
        let dictionary = Dictionary {
            chart,
            merges: vec![(0, 1), (4, 0), (1, 1)],
        };
        let longest = 5;
        let mut total = Rat::from_integer(BigInt::from(0));
        let mut strings = 0;
        for length in 0..=longest {
            for word in 0..(1u32 << length) {
                let cells: Vec<u32> = (0..length).map(|bit| (word >> bit) & 1).collect();
                let mut stream = dictionary.encode(&cells);
                assert_eq!(dictionary.decode(&stream), cells, "exact decode");
                stream.push(stop);
                // The opening letter is observed: the mass is conditional on it.
                let mut family = tree(dictionary.alphabet(), 2, 64);
                family.receive(open as usize).unwrap();
                let mut mass = Rat::from_integer(BigInt::from(1));
                for &token in &stream {
                    mass *= family.receive(token as usize).unwrap();
                }
                total += mass;
                strings += 1;
            }
        }
        assert_eq!(strings, 63);
        assert!(total < Rat::from_integer(BigInt::from(1)), "Kraft: {total}");
        assert!(total > Rat::from_integer(BigInt::from(0)));
    }

    /// **The descent is the face's inverse CDF**: on a tree over an alphabet that is not a power of
    /// two, after a passage, the heap's descent selects the class `select_family_class` certifies on
    /// the full exact face, for seeded draws and at every exact cumulative boundary `F(c − 1)`.
    #[test]
    fn the_descent_is_the_faces_inverse_cdf() {
        for (alphabet, depth) in [(7usize, 2usize), (11, 3), (300, 2)] {
            let mut family = tree(alphabet, depth, 1 << 12);
            let mut past = VecDeque::new();
            let mut draw = Draw::new(SEED);
            for step in 0..200u64 {
                let token =
                    u32::try_from(draw.below(alphabet.min(5 + (step % 3) as usize))).unwrap();
                push(&mut family, &mut past, token);
            }
            let descent = Descent::new(family.tree());
            for _ in 0..64 {
                let value = Rat::new(BigInt::from(draw.next()), BigInt::from(1u8) << 64);
                draw_class(&family, &past, &descent, &value, true);
            }
            let face = family.face().unwrap();
            let splits = family.tree().splits(&address(&past, depth)).unwrap();
            let mut before = Rat::from_integer(BigInt::from(0));
            for (class, mass) in face.iter().enumerate() {
                assert_eq!(descent.class(&splits, &before), class, "F({class} − 1)");
                assert_eq!(select_family_class(&face, &before).unwrap().class, class);
                before += mass;
            }
            assert_eq!(before, Rat::from_integer(BigInt::from(1)));
        }
    }

    #[test]
    fn the_description_counts_each_merges_operands_and_gamma_k() {
        let chart = SectionChart::curated();
        let dictionary = Dictionary {
            chart,
            merges: vec![(0, 1); 3],
        };
        // 2·8 for merge 0 (256 operands), 2·9 for merges 1 and 2, and gamma(3) = 3.
        assert_eq!(dictionary.description(), 16 + 18 + 18 + 3);
    }

    #[test]
    fn json_strings_round_trip() {
        let text = "a\"b\\c\nd\u{1}é😀";
        let document = format!("{{\"cases\":[{{\"request\":{}}}]}}", json_quote(text));
        assert_eq!(json_strings(&document, "request"), vec![text.to_string()]);
        let escaped = "{\"request\":\"\\ud83d\\ude00\\u00e9\\/\"}";
        assert_eq!(json_strings(escaped, "request"), vec!["😀é/".to_string()]);
    }
}
