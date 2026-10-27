//! **Units founded by their code length: adjacent units merge when the whole code falls** (#405,
//! #404).
//!
//! [definition; agent-inferred, October 23] Why it is built. The moment tower read GSM8K at the
//! codec's byte classes and its releases spell letter by letter: after three passes over all 6,726
//! problems it codes 2.3 bits a byte and its continuations of a question are strings of misspelt
//! fragments. A unit above the byte lets the tower release a founded piece of the passage whole,
//! and lets each of its modes span several times the text a byte-clocked mode spans. The units are
//! the passage's own: they are founded from the passage by the merge law of
//! `receiver::population::merge` (Lean `Compression/Landmark/Context/Merge.merge_cost_mass_iff`):
//! **a merge is accepted exactly when it lowers the complete code**, the description of the units
//! plus the code of the passage read in them. Frequency only proposes; the price accepts.
//!
//! ```text
//! units      V = {bytes} ∪ {z_i = (a_i, b_i)},  D(z_i) = D(a_i) D(b_i)        founded in order
//! receiver   order-one KT over units:  W(z) = ∏_s KT(n_s·),
//!            −log₂ KT(n_s·) = L(2n_s + A) − L(A) − Σ_c (L(2n_sc + 1) − L(1)),  L(k) = log₂ Γ(k/2)
//! table      L(k + 2) = L(k) + log₂ k − 1    (the recurrence of Γ, on the code grain)
//! describe   a founded unit names its ordered pair of the A units standing: 2 log₂ A bits, and one
//!            bit for "another unit" (the founding list is a prefix code)
//! merge      (a, b) → z over the occurrences taken left to right without overlap; accepted iff
//!            Δ = ΔW + growth(A → A + 1) + 2 log₂ A + 1 < −(the table's enclosure)
//! parse      a passage is read by replaying the founded merges in order (decode(parse(x)) = x)
//! ```
//!
//! [definition; agent-inferred] **Why order one.** Under an order-zero receiver every frequent
//! co-occurrence pays, and the units grow toward every repeated word. Under order one a pair pays
//! only by what the unit before it does not already predict, and each new unit raises the
//! alphabet every context pays for (`growth`), so the founding reaches its own equilibrium: it
//! ends when no proposed pair lowers the complete code. The receiver that reads the units (the
//! tower) is richer than order one, so this price is a declared, cheaper receiver's, recorded as
//! such.
//!
//! [definition; agent-inferred] **The parse is one path of the segmentation lattice.** A passage
//! is read in the units by replaying the founded merges; its code under any receiver bounds from
//! above the code of the lattice of all parses (Lean `segmentation_code_le`), so a reading in
//! bits a byte is honest, never better than the lattice. The lattice read is owed (#410).
//!
//! [definition; agent-inferred] **Proposal and acceptance.** Pairs are proposed in the order of
//! their adjacent count; each is priced exactly and accepted or refused. A refused pair is priced
//! again when its count changes. The founding ends when every pair standing has been refused at
//! its count. The code's grain is `2^(−32)` bits; the table's enclosure is one grain a recurrence
//! step it spans, and a merge whose price lies inside its enclosure is refused and counted as
//! undecided.
//!
//! [definition] The computational object is the helical pair interaction, read here as the
//! passage's adjacent pairs and the units they found. Of the winding guide's six general objects
//! this owner touches the **pair** (each merge prices one adjacent pair), **faces and placement**
//! (the order-one faces the price reads) and the **tower thread** (a unit restricts to its two
//! constituents and decodes to its bytes); the helix, the cell holonomy and the tube stay attached
//! through the tower that reads the units. Nothing here is text-specific: the founding reads any
//! passage of byte classes (an acoustic or motor code's classes alike).
//!
//! [definition; agent-inferred, October 27] **The codec's chart**
//! ([the review](../../../../research/records/2026-10-27_THE_REVIEW_FINDS_THE_CODEC_CUTS_THE_NUMERAL_THE_CREDIT_STOPS_AT_THE_SECTION_AND_THE_EQUALS_HAS_ONE_STEP.md)
//! §2). The order-one price founds whatever lowers the code, and on GSM8K it founded units that
//! join a mark to the digit after it (`=3`, `0>>`): a read cut at the equals then asks for a
//! continuation the founded passage never holds, and a numeral is cut where frequency cuts it, not
//! by place. A founding may therefore declare a chart of its byte classes:
//!
//! ```text
//! kinds      each byte class has a kind; (a, b) is proposed only when both are of one kind, so no
//!            founded unit crosses a class of another kind, and a cut at a mark falls where every
//!            reading of the passage has a boundary
//! counted    the counted classes (value order) never merge: a run of them is a word on its base's
//!            tower, each class read with its place, the power of the base it stands at;
//!            12,400 = 1·10⁴ + 2·10³ + 4·10² + 0·10¹ + 0·10⁰, so its 4 is read as "4 at place 2"
//! marks      the point ends the whole places (the places after it are −1, −2, …); a group mark
//!            followed by exactly its width of counted classes continues a run no longer than it
//! classes    a counted class at place 0 is its byte's own class; every other founded place adds
//!            one class a value, decoding to the same byte, so decode(parse(x)) = x
//! founded    the places are those the passage holds; a place past them reads as the outermost
//!            founded place (the founding's grain), which `Units::outside` counts
//! ```
//!
//! The chart is declared by the application's boundary codec (for text: the digits counted, `.` the
//! point, `,` a group of three, every mark a kind alone); nothing in this owner names a modality.

use std::collections::{BinaryHeap, HashMap};

use crate::hnn::keyed_modes::log2_face;

/// The code's grain, `2^(−32)` bits.
pub const CODE_BITS: u32 = 32;
const NONE: u32 = u32::MAX;
const UNIT_BITS: u32 = 62;
/// The kind of a class that never merges: a counted class at any place.
const FENCED: u16 = u16::MAX;

/// Refusals of the founding.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum UnitsError {
    #[error("units refused: {0}")]
    Refused(&'static str),
}

type Result<T> = std::result::Result<T, UnitsError>;

fn refuse<T>(why: &'static str) -> Result<T> {
    Err(UnitsError::Refused(why))
}

/// `log₂ k` on `2^(−32)`, `k ≥ 1`, its fraction read by `log2_face` (truncated, one grain at most).
fn log2_int(k: u64) -> i64 {
    let width = 64 - k.leading_zeros(); // k in [2^(width−1), 2^width)
    let fraction = log2_face((k as u128) << (UNIT_BITS - width), CODE_BITS); // log₂(k/2^width) ∈ [−1, 0)
    ((width as i64) << CODE_BITS) + fraction as i64
}

/// `L(k) = log₂ Γ(k/2)` on `2^(−32)`, relative within each parity (`L(1) = L(2) = 0`): every code
/// reads differences of one parity, so the bases cancel.
#[derive(Default)]
struct GammaTable {
    l: Vec<i64>,
}

impl GammaTable {
    fn at(&mut self, k: usize) -> i64 {
        if self.l.len() <= k {
            if self.l.is_empty() {
                self.l.extend([0, 0, 0]);
            }
            let want = (k + 1).max(2 * self.l.len());
            while self.l.len() < want {
                let m = self.l.len(); // L(m) = L(m − 2) + log₂(m − 2) − 1
                let v = self.l[m - 2] + log2_int((m - 2) as u64) - (1 << CODE_BITS);
                self.l.push(v);
            }
        }
        self.l[k]
    }

    /// A context's code `L(2n + A) − L(A)`.
    fn context(&mut self, n: u64, alphabet: usize) -> i64 {
        self.at(2 * n as usize + alphabet) - self.at(alphabet)
    }

    /// A cell's credit `L(2n + 1) − L(1)`.
    fn cell(&mut self, n: u64) -> i64 {
        self.at(2 * n as usize + 1)
    }
}

fn key(a: u32, b: u32) -> u64 {
    ((a as u64) << 32) | b as u64
}

fn pair(k: u64) -> (u32, u32) {
    ((k >> 32) as u32, k as u32)
}

/// **The codec's chart** of byte classes (module doc): each class's kind, the counted classes in
/// value order with their point and group mark, and the places a founding found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chart {
    kinds: Vec<u16>,
    counted: Vec<u8>,
    point: Option<u8>,
    group: Option<(u8, usize)>,
    /// The founded places: whole places `0..up`, fractional places `1..=down`.
    up: usize,
    down: usize,
}

impl Chart {
    /// Declare a chart: one kind for each of the 256 byte classes, the counted classes in value
    /// order (at least two, each once), the point, and the group mark with its width. Refused when
    /// a mark is counted, the point and the group are one class, or a group has no width.
    pub fn declare(kinds: Vec<u16>, counted: Vec<u8>, point: Option<u8>, group: Option<(u8, usize)>) -> Result<Chart> {
        if kinds.len() != 256 || kinds.contains(&FENCED) {
            return refuse("a chart names one declared kind for each of the 256 byte classes");
        }
        let mut seen = [false; 256];
        for &c in &counted {
            if seen[c as usize] {
                return refuse("a chart counts each class once");
            }
            seen[c as usize] = true;
        }
        if counted.len() < 2 {
            return refuse("a chart counts at least two classes");
        }
        if point.is_some_and(|p| seen[p as usize]) || group.is_some_and(|(g, w)| seen[g as usize] || w == 0 || Some(g) == point) {
            return refuse("a chart's point and group mark are two classes it does not count, and a group has a width");
        }
        Ok(Chart { kinds, counted, point, group, up: 1, down: 0 })
    }

    /// The founded places: whole places `0..up` and fractional places `1..=down`.
    pub fn founded_places(&self) -> (usize, usize) {
        (self.up, self.down)
    }

    fn base(&self) -> usize {
        self.counted.len()
    }

    fn value(&self, b: u8) -> Option<usize> {
        self.counted.iter().position(|&c| c == b)
    }

    /// Each byte's place on its base's tower: `Some(k)` for a counted byte of a numeral, `None` for
    /// every other byte.
    fn read_places(&self, bytes: &[u8]) -> Vec<Option<i64>> {
        let counted = |i: usize| i < bytes.len() && self.value(bytes[i]).is_some();
        let mut place = vec![None; bytes.len()];
        let mut i = 0;
        while i < bytes.len() {
            if !counted(i) {
                i += 1;
                continue;
            }
            let mut whole = Vec::new();
            let mut j = i;
            while counted(j) {
                whole.push(j);
                j += 1;
            }
            if let Some((g, w)) = self.group {
                if whole.len() <= w {
                    while j < bytes.len() && bytes[j] == g && (1..=w).all(|t| counted(j + t)) && !counted(j + w + 1) {
                        whole.extend(j + 1..=j + w);
                        j += w + 1;
                    }
                }
            }
            for (t, &at) in whole.iter().enumerate() {
                place[at] = Some((whole.len() - 1 - t) as i64);
            }
            if let Some(p) = self.point {
                if j < bytes.len() && bytes[j] == p && counted(j + 1) {
                    let mut k = j + 1;
                    while counted(k) {
                        place[k] = Some(-((k - j) as i64));
                        k += 1;
                    }
                    j = k;
                }
            }
            i = j;
        }
        place
    }

    /// The class of `value` at `place`, and whether the place lies past the founded ones (then the
    /// class is the outermost founded place's on that side, or the byte's own when that side founded
    /// none).
    fn class(&self, value: usize, place: i64) -> (u32, bool) {
        let byte = self.counted[value] as u32;
        let index = if place > 0 {
            let k = place as usize;
            if self.up <= 1 {
                return (byte, true);
            }
            (k.min(self.up - 1) - 1, k >= self.up)
        } else if place < 0 {
            let k = (-place) as usize;
            if self.down == 0 {
                return (byte, true);
            }
            (self.up - 1 + k.min(self.down) - 1, k > self.down)
        } else {
            return (byte, false);
        };
        ((256 + index.0 * self.base() + value) as u32, index.1)
    }

    /// The passage's classes under the chart, and how many counted bytes read past the founded
    /// places.
    fn classes(&self, bytes: &[u8]) -> (Vec<u32>, usize) {
        let mut outside = 0;
        let classes = bytes
            .iter()
            .zip(self.read_places(bytes))
            .map(|(&b, place)| match place {
                Some(k) => {
                    let (class, past) = self.class(self.value(b).expect("a placed byte is counted"), k);
                    outside += usize::from(past);
                    class
                }
                None => b as u32,
            })
            .collect();
        (classes, outside)
    }

    /// The places a passage holds: one past its largest whole place, and its deepest fractional one.
    fn found_places(&mut self, bytes: &[u8]) {
        let places = self.read_places(bytes);
        self.up = 1 + places.iter().flatten().filter(|&&k| k > 0).max().copied().unwrap_or(0) as usize;
        self.down = places.iter().flatten().filter(|&&k| k < 0).map(|&k| (-k) as usize).max().unwrap_or(0);
    }

    fn placed_classes(&self) -> usize {
        self.base() * (self.up - 1 + self.down)
    }
}

/// The founded units: the 256 bytes, then each founded place's classes (a chart's), then each
/// merge's unit in founding order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Units {
    merges: Vec<(u32, u32)>,
    pieces: Vec<Vec<u8>>,
    chart: Option<Chart>,
}

/// The founding's receipt: the units founded and what each cost, the pairs refused or undecided,
/// and the complete code before and after, on `2^(−32)` bits.
#[derive(Clone, Debug, Default)]
pub struct FoundingReceipt {
    pub founded: usize,
    pub refused: usize,
    pub undecided: usize,
    pub priced: usize,
    pub symbols_before: usize,
    pub symbols_after: usize,
    /// The passage's order-one code in the bytes, and in the founded units.
    pub code_before: i128,
    pub code_after: i128,
    /// The founding list's description, `Σ (2 log₂ A + 1)`.
    pub description: i128,
}

/// A passage carried as a list: each position's unit and its neighbours, with every adjacent
/// pair's positions (validated when read) and the order-one counts the price reads.
struct Passage {
    unit: Vec<u32>,
    next: Vec<u32>,
    prev: Vec<u32>,
    positions: HashMap<u64, Vec<u32>>,
}

impl Passage {
    fn new(unit: Vec<u32>) -> Result<Self> {
        if unit.len() >= NONE as usize {
            return refuse("a passage past 2^32 − 1 positions");
        }
        let n = unit.len();
        let next = (0..n).map(|i| if i + 1 < n { (i + 1) as u32 } else { NONE }).collect();
        let prev = (0..n).map(|i| if i > 0 { (i - 1) as u32 } else { NONE }).collect();
        let mut positions: HashMap<u64, Vec<u32>> = HashMap::new();
        for i in 0..n.saturating_sub(1) {
            positions.entry(key(unit[i], unit[i + 1])).or_default().push(i as u32);
        }
        Ok(Passage { unit, next, prev, positions })
    }

    /// The occurrences of `(a, b)` taken left to right without overlap, their stale positions
    /// pruned from the list.
    fn occurrences(&mut self, a: u32, b: u32) -> Vec<(u32, u32)> {
        let Some(list) = self.positions.get_mut(&key(a, b)) else { return Vec::new() };
        list.sort_unstable();
        list.dedup();
        let (unit, next) = (&self.unit, &self.next);
        list.retain(|&i| unit[i as usize] == a && next[i as usize] != NONE && unit[next[i as usize] as usize] == b);
        let mut taken = Vec::with_capacity(list.len());
        let mut consumed = NONE;
        for &i in list.iter() {
            if i != consumed {
                let j = next[i as usize];
                taken.push((i, j));
                consumed = j;
            }
        }
        taken
    }

    /// The order-one cells and context counts each occurrence of `(a, b) → z` changes, in the
    /// order a left-to-right merge changes them.
    fn changes(&self, taken: &[(u32, u32)], a: u32, b: u32, z: u32) -> (HashMap<u64, i64>, HashMap<u32, i64>) {
        let mut cells: HashMap<u64, i64> = HashMap::new();
        let mut contexts: HashMap<u32, i64> = HashMap::new();
        for (t, &(i, j)) in taken.iter().enumerate() {
            *cells.entry(key(a, b)).or_default() -= 1;
            *contexts.entry(a).or_default() -= 1;
            let x = self.prev[i as usize];
            let left_merged = t > 0 && taken[t - 1].1 == x;
            if x != NONE && !left_merged {
                let s = self.unit[x as usize];
                *cells.entry(key(s, a)).or_default() -= 1;
                *cells.entry(key(s, z)).or_default() += 1;
            }
            let y = self.next[j as usize];
            if y != NONE {
                *contexts.entry(b).or_default() -= 1;
                *contexts.entry(z).or_default() += 1;
                let right_merged = t + 1 < taken.len() && taken[t + 1].0 == y;
                let c = if right_merged { z } else { self.unit[y as usize] };
                let c_before = self.unit[y as usize];
                *cells.entry(key(b, c_before)).or_default() -= 1;
                *cells.entry(key(z, c)).or_default() += 1;
            }
        }
        cells.retain(|_, d| *d != 0);
        contexts.retain(|_, d| *d != 0);
        (cells, contexts)
    }

    /// Merge the taken occurrences of `(a, b)` into `z`, recording each new adjacency's position.
    fn merge(&mut self, taken: &[(u32, u32)], z: u32) {
        for &(i, j) in taken {
            let (iu, ju) = (i as usize, j as usize);
            self.unit[iu] = z;
            let y = self.next[ju];
            self.next[iu] = y;
            self.unit[ju] = NONE;
            self.next[ju] = NONE;
            self.prev[ju] = NONE;
            if y != NONE {
                self.prev[y as usize] = i;
                self.positions.entry(key(z, self.unit[y as usize])).or_default().push(i);
            }
            let x = self.prev[iu];
            if x != NONE {
                self.positions.entry(key(self.unit[x as usize], z)).or_default().push(x);
            }
        }
        // Every position whose right element is merged into its left moves its pair to the new unit:
        // a position x left of a merged pair now pairs (unit x, z), recorded above; an adjacent run of
        // merged pairs pairs (z, z), recorded at the later pair's left neighbour.
    }

    fn read(&self) -> Vec<u32> {
        let mut out = Vec::new();
        let mut i = if self.unit.is_empty() { NONE } else { 0 };
        while i != NONE {
            out.push(self.unit[i as usize]);
            i = self.next[i as usize];
        }
        out
    }
}

/// The order-one code of a passage under an alphabet of `alphabet` units, on `2^(−32)` bits.
fn order_one_code(table: &mut GammaTable, units: &[u32], alphabet: usize) -> i128 {
    let mut cells: HashMap<u64, u64> = HashMap::new();
    let mut contexts: HashMap<u32, u64> = HashMap::new();
    for w in units.windows(2) {
        *cells.entry(key(w[0], w[1])).or_default() += 1;
        *contexts.entry(w[0]).or_default() += 1;
    }
    let ctx: i128 = contexts.values().map(|&n| table.context(n, alphabet) as i128).sum();
    let cell: i128 = cells.values().map(|&n| table.cell(n) as i128).sum();
    ctx - cell
}

impl Units {
    /// The bytes alone, before any founding.
    pub fn bytes() -> Self {
        Units { merges: Vec::new(), pieces: (0..=255u8).map(|b| vec![b]).collect(), chart: None }
    }

    /// The bytes and a chart's founded places, before any merge: each place's class of a value
    /// decodes to that value's byte.
    fn charted(chart: Chart) -> Self {
        let mut pieces: Vec<Vec<u8>> = (0..=255u8).map(|b| vec![b]).collect();
        for _ in 0..chart.up - 1 + chart.down {
            pieces.extend(chart.counted.iter().map(|&c| vec![c]));
        }
        Units { merges: Vec::new(), pieces, chart: Some(chart) }
    }

    /// The chart the units were founded under, if any.
    pub fn chart(&self) -> Option<&Chart> {
        self.chart.as_ref()
    }

    /// The first merge's unit: past the bytes and the founded places' classes.
    fn first_merge(&self) -> usize {
        self.pieces.len() - self.merges.len()
    }

    /// The kind of each standing unit: a byte's declared kind, `FENCED` for a counted class at any
    /// place, a merge's its pieces' kind; one kind for every unit when no chart is declared.
    fn kinds(&self) -> Vec<u16> {
        let mut kinds: Vec<u16> = match &self.chart {
            None => vec![0; 256],
            Some(c) => (0..256).map(|b| if c.value(b as u8).is_some() { FENCED } else { c.kinds[b] }).collect(),
        };
        kinds.resize(self.first_merge(), FENCED);
        for &(a, _) in &self.merges {
            kinds.push(kinds[a as usize]);
        }
        kinds
    }

    /// The passage's classes before any merge (its bytes, each counted byte read at its place when a
    /// chart is declared), and how many counted bytes read past the founded places.
    fn classes(&self, passage: &[u8]) -> (Vec<u32>, usize) {
        match &self.chart {
            None => (passage.iter().map(|&b| b as u32).collect(), 0),
            Some(c) => c.classes(passage),
        }
    }

    /// How many counted bytes of `passage` read past the founded places (each read at the outermost
    /// founded place on its side): the place released at the founding's grain.
    pub fn outside(&self, passage: &[u8]) -> usize {
        self.classes(passage).1
    }

    pub fn len(&self) -> usize {
        self.pieces.len()
    }

    pub fn is_empty(&self) -> bool {
        self.pieces.is_empty()
    }

    /// The bytes a unit decodes to.
    pub fn piece(&self, unit: usize) -> &[u8] {
        &self.pieces[unit]
    }

    /// The founded merges, in order.
    pub fn merges(&self) -> &[(u32, u32)] {
        &self.merges
    }

    fn push(&mut self, a: u32, b: u32) -> u32 {
        let z = self.pieces.len() as u32;
        let mut piece = self.pieces[a as usize].clone();
        piece.extend_from_slice(&self.pieces[b as usize]);
        self.pieces.push(piece);
        self.merges.push((a, b));
        z
    }

    /// **Found units from a passage** by the module's law; returns the units, the passage read in
    /// them, and the receipt.
    pub fn found(passage: &[u8]) -> Result<(Units, Vec<u32>, FoundingReceipt)> {
        Units::found_on(passage, Units::bytes())
    }

    /// **Found units under a chart** (module doc): the chart's places are founded from the passage,
    /// and a pair is proposed only when both its units are of one kind and neither is counted. The
    /// receipt's code before is the passage's in the charted classes.
    pub fn found_charted(passage: &[u8], mut chart: Chart) -> Result<(Units, Vec<u32>, FoundingReceipt)> {
        chart.found_places(passage);
        Units::found_on(passage, Units::charted(chart))
    }

    fn found_on(passage: &[u8], mut units: Units) -> Result<(Units, Vec<u32>, FoundingReceipt)> {
        let classes = units.classes(passage).0;
        let mut kinds = units.kinds();
        let mut text = Passage::new(classes.clone())?;
        let mut table = GammaTable::default();
        let mut cells: HashMap<u64, u64> = HashMap::new();
        let mut contexts: Vec<u64> = vec![0; units.len()];
        for w in classes.windows(2) {
            *cells.entry(key(w[0], w[1])).or_default() += 1;
            contexts[w[0] as usize] += 1;
        }
        let mut receipt = FoundingReceipt { symbols_before: passage.len(), ..FoundingReceipt::default() };
        receipt.code_before = order_one_code(&mut table, &classes, units.len());
        let mut proposals: BinaryHeap<(u64, u64)> = cells.iter().map(|(&k, &n)| (n, k)).collect();
        let mut refused_at: HashMap<u64, u64> = HashMap::new();
        // The table's enclosure: four grains a recurrence step (the fraction's truncation and the
        // squarings' releases in `log2_face`); a price spans at most two steps a context's count
        // (the growth), eight an occurrence (its cells and contexts) and two for the description.
        let enclosure = |symbols: usize, taken: usize| -> i128 { 4 * (2 * symbols as i128 + 8 * taken as i128 + 2) };
        while let Some((count, k)) = proposals.pop() {
            if cells.get(&k).copied() != Some(count) || refused_at.get(&k) == Some(&count) {
                continue;
            }
            let (a, b) = pair(k);
            if kinds[a as usize] != kinds[b as usize] || kinds[a as usize] == FENCED {
                continue;
            }
            let alphabet = units.len();
            let z = alphabet as u32;
            let taken = text.occurrences(a, b);
            if taken.is_empty() {
                continue;
            }
            receipt.priced += 1;
            let (cell_changes, context_changes) = text.changes(&taken, a, b, z);
            // ΔW: the cells' credit falls by L(2n' + 1) − L(2n + 1).
            let mut price: i128 = 0;
            for (&ck, &d) in &cell_changes {
                let n = cells.get(&ck).copied().unwrap_or(0);
                let after = (n as i64 + d) as u64;
                price -= table.cell(after) as i128 - table.cell(n) as i128;
            }
            // Every context's code under the grown alphabet; the changed ones at their new counts.
            let mut growth: i128 = 0;
            for &n in contexts.iter().filter(|&&n| n > 0) {
                growth += table.context(n, alphabet + 1) as i128 - table.context(n, alphabet) as i128;
            }
            for (&s, &d) in &context_changes {
                let n = contexts.get(s as usize).copied().unwrap_or(0);
                let after = (n as i64 + d) as u64;
                if n > 0 {
                    growth -= table.context(n, alphabet + 1) as i128 - table.context(n, alphabet) as i128;
                }
                price += table.context(after, alphabet + 1) as i128 - table.context(n, alphabet) as i128;
            }
            price += growth;
            let describe = 2 * log2_int(alphabet as u64) as i128 + (1i128 << CODE_BITS);
            price += describe;
            let bound = enclosure(passage.len(), taken.len());
            if price < -bound {
                for (&ck, &d) in &cell_changes {
                    let n = cells.entry(ck).or_default();
                    *n = (*n as i64 + d) as u64;
                    if *n == 0 {
                        cells.remove(&ck);
                    } else {
                        proposals.push((*n, ck));
                    }
                }
                contexts.push(0);
                for (&s, &d) in &context_changes {
                    let n = &mut contexts[s as usize];
                    *n = (*n as i64 + d) as u64;
                }
                text.merge(&taken, z);
                units.push(a, b);
                kinds.push(kinds[a as usize]);
                receipt.founded += 1;
                receipt.description += describe;
            } else {
                if price.abs() <= bound {
                    receipt.undecided += 1;
                }
                receipt.refused += 1;
                refused_at.insert(k, count);
            }
        }
        let read = text.read();
        receipt.symbols_after = read.len();
        receipt.code_after = order_one_code(&mut table, &read, units.len());
        Ok((units, read, receipt))
    }

    /// **A passage read in the units**: the founded merges replayed in order, each over its
    /// occurrences left to right; `decode(parse(x)) = x`.
    pub fn parse(&self, passage: &[u8]) -> Result<Vec<u32>> {
        let mut text = Passage::new(self.classes(passage).0)?;
        let first = self.first_merge();
        for (i, &(a, b)) in self.merges.iter().enumerate() {
            let taken = text.occurrences(a, b);
            if !taken.is_empty() {
                text.merge(&taken, (first + i) as u32);
            }
            text.positions.remove(&key(a, b));
        }
        Ok(text.read())
    }

    /// The bytes of a passage read in the units.
    pub fn decode(&self, units: &[u32]) -> Vec<u8> {
        units.iter().flat_map(|&u| self.pieces[u as usize].iter().copied()).collect()
    }

    /// The founding list as text: a header, the chart when one is declared (its kinds, then its
    /// counted classes, marks and founded places), then one merge a line.
    pub fn to_text(&self) -> String {
        let mut s = match &self.chart {
            None => format!("founded-units-v1 {}\n", self.merges.len()),
            Some(c) => {
                let list = |v: &[u8]| v.iter().map(u8::to_string).collect::<Vec<_>>().join(",");
                let kinds = c.kinds.iter().map(u16::to_string).collect::<Vec<_>>().join(" ");
                let point = c.point.map_or("none".to_string(), |p| p.to_string());
                let group = c.group.map_or("none".to_string(), |(g, w)| format!("{g}:{w}"));
                format!(
                    "founded-units-v2 {}\nkinds {kinds}\nchart counted={} point={point} group={group} up={} down={}\n",
                    self.merges.len(),
                    list(&c.counted),
                    c.up,
                    c.down
                )
            }
        };
        for &(a, b) in &self.merges {
            s.push_str(&format!("{a} {b}\n"));
        }
        s
    }

    /// The founding list from its text, refused unless the chart is a declared chart, and each merge
    /// names two units standing, of one kind and neither counted.
    pub fn from_text(text: &str) -> Result<Self> {
        let mut lines = text.lines();
        let head: Vec<&str> = lines.next().unwrap_or("").split(' ').collect();
        if head.len() != 2 || (head[0] != "founded-units-v1" && head[0] != "founded-units-v2") {
            return refuse("not a founding list's text");
        }
        let count: usize = head[1].parse().map_err(|_| UnitsError::Refused("a founding count that is not a count"))?;
        let mut units = if head[0] == "founded-units-v1" { Units::bytes() } else { Units::charted(chart_from(&mut lines)?) };
        let mut kinds = units.kinds();
        for line in lines {
            let (a, b) = line.split_once(' ').ok_or(UnitsError::Refused("a merge names two units"))?;
            let a: u32 = a.parse().map_err(|_| UnitsError::Refused("a merge's unit that is not a count"))?;
            let b: u32 = b.parse().map_err(|_| UnitsError::Refused("a merge's unit that is not a count"))?;
            if a as usize >= units.len() || b as usize >= units.len() {
                return refuse("a merge names a unit not yet founded");
            }
            if kinds[a as usize] != kinds[b as usize] || kinds[a as usize] == FENCED {
                return refuse("a merge joins units of two kinds, or a counted class");
            }
            units.push(a, b);
            kinds.push(kinds[a as usize]);
        }
        if units.merges.len() != count {
            return refuse("the founding list's count differs from its merges");
        }
        Ok(units)
    }
}

/// A chart from its two lines of a founding list's text.
fn chart_from<'a>(lines: &mut impl Iterator<Item = &'a str>) -> Result<Chart> {
    let bad = || UnitsError::Refused("a chart's lines are its kinds, then its counted classes, marks and places");
    let kinds: Vec<u16> = lines
        .next()
        .and_then(|l| l.strip_prefix("kinds "))
        .ok_or_else(bad)?
        .split(' ')
        .map(|k| k.parse().map_err(|_| bad()))
        .collect::<Result<_>>()?;
    let fields: Vec<&str> = lines.next().and_then(|l| l.strip_prefix("chart ")).ok_or_else(bad)?.split(' ').collect();
    let field = |name: &str| fields.iter().find_map(|f| f.strip_prefix(name).and_then(|v| v.strip_prefix('='))).ok_or_else(bad);
    let byte = |v: &str| v.parse::<u8>().map_err(|_| bad());
    let counted: Vec<u8> = field("counted")?.split(',').map(byte).collect::<Result<_>>()?;
    let point = match field("point")? {
        "none" => None,
        p => Some(byte(p)?),
    };
    let group = match field("group")? {
        "none" => None,
        g => {
            let (g, w) = g.split_once(':').ok_or_else(bad)?;
            Some((byte(g)?, w.parse::<usize>().map_err(|_| bad())?))
        }
    };
    let mut chart = Chart::declare(kinds, counted, point, group)?;
    chart.up = field("up")?.parse().map_err(|_| bad())?;
    chart.down = field("down")?.parse().map_err(|_| bad())?;
    if chart.up == 0 {
        return refuse("a chart founds at least the place of one");
    }
    Ok(chart)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn passage() -> Vec<u8> {
        let mut text = Vec::new();
        for i in 0..400u32 {
            text.extend_from_slice(b"the cat sat on the mat. ");
            if i % 3 == 0 {
                text.extend_from_slice(b"a dog ran. ");
            }
        }
        text
    }

    /// A chart of the text codec's form: letters and the space one kind, every other byte a kind
    /// alone, the decimal digits counted with `.` the point and `,` a group of three.
    fn chart() -> Chart {
        let kinds = (0..=255u8).map(|b| if b.is_ascii_alphabetic() || b == b' ' { 0 } else { 1 + u16::from(b) }).collect();
        Chart::declare(kinds, (b'0'..=b'9').collect(), Some(b'.'), Some((b',', 3))).unwrap()
    }

    #[test]
    fn the_chart_reads_each_counted_byte_at_its_place() {
        let c = chart();
        let text = b"It cost 12,400.50 or 3.5, 1,23 and 1234,567 at 8.";
        let places: Vec<(char, i64)> =
            text.iter().zip(c.read_places(text)).filter_map(|(&b, k)| k.map(|k| (b as char, k))).collect();
        let want = [
            ('1', 4), ('2', 3), ('4', 2), ('0', 1), ('0', 0), ('5', -1), ('0', -2),
            ('3', 0), ('5', -1),
            ('1', 0), ('2', 1), ('3', 0),
            ('1', 3), ('2', 2), ('3', 1), ('4', 0), ('5', 2), ('6', 1), ('7', 0),
            ('8', 0),
        ];
        assert_eq!(places, want);
        // Refusals: a counted mark, a class counted twice, a group without width.
        let kinds: Vec<u16> = vec![0; 256];
        assert!(Chart::declare(kinds.clone(), vec![b'0', b'1'], Some(b'1'), None).is_err());
        assert!(Chart::declare(kinds.clone(), vec![b'0', b'0'], None, None).is_err());
        assert!(Chart::declare(kinds.clone(), vec![b'0', b'1'], None, Some((b',', 0))).is_err());
        assert!(Chart::declare(vec![0; 255], vec![b'0', b'1'], None, None).is_err());
    }

    #[test]
    fn the_charted_founding_never_crosses_a_kind_and_decodes() {
        let mut text = Vec::new();
        for i in 0..300u32 {
            text.extend_from_slice(format!("the cat had <<{}+3={}>>{} toys, 1,200 in all. ", i % 7, i % 7 + 3, i % 7 + 3).as_bytes());
        }
        let (units, read, receipt) = Units::found_charted(&text, chart()).unwrap();
        assert!(receipt.founded > 0);
        assert_eq!(units.chart().unwrap().founded_places(), (4, 0));
        // Every unit's bytes are of one kind, and a counted byte stands alone at its place.
        let kinds = units.kinds();
        for u in 256..units.len() {
            let piece = units.piece(u);
            if kinds[u] == FENCED {
                assert_eq!(piece.len(), 1);
                assert!(piece[0].is_ascii_digit());
            } else {
                assert!(piece.iter().all(|&b| !b.is_ascii_digit() && units.chart().unwrap().kinds[b as usize] == kinds[u]), "{piece:?}");
            }
        }
        // The equals is a boundary on both sides wherever the passage holds it.
        let mut at = 0;
        let mut ends = std::collections::HashSet::new();
        for &u in &read {
            ends.insert(at);
            at += units.piece(u as usize).len();
        }
        ends.insert(at);
        for (i, &b) in text.iter().enumerate() {
            if b == b'=' {
                assert!(ends.contains(&i) && ends.contains(&(i + 1)));
            }
        }
        // 1,200 reads its 1 at place 3, its 2 at place 2.
        let one = units.parse(b"1,200").unwrap();
        assert_eq!(one.len(), 5);
        assert_eq!(units.decode(&one), b"1,200");
        assert_eq!([one[0], one[1], one[2], one[3], one[4]], [256 + 2 * 10 + 1, u32::from(b','), 256 + 10 + 2, 256, u32::from(b'0')]);
        assert_eq!(units.decode(&read), text);
        assert_eq!(units.parse(&text).unwrap(), read);
        assert_eq!(units.outside(&text), 0);
        // A numeral past the founded places reads its outer places at the outermost one, exactly.
        let long = b"98765 and 0.25";
        assert_eq!(units.outside(long), 1 + 2);
        assert_eq!(units.decode(&units.parse(long).unwrap()), long);
        // The list restores whole, and refuses a merge across kinds.
        assert_eq!(Units::from_text(&units.to_text()).unwrap(), units);
        let mut forged = units.to_text();
        forged = forged.replacen(&format!("founded-units-v2 {}", units.merges().len()), &format!("founded-units-v2 {}", units.merges().len() + 1), 1);
        forged.push_str(&format!("{} {}\n", b'=', b'3'));
        assert!(Units::from_text(&forged).is_err());
    }

    #[test]
    fn the_table_reads_the_gamma_recurrence() {
        let mut t = GammaTable::default();
        // L(2n + 2) − L(2) = log₂ Γ(n + 1) = log₂ n!; 5! = 120.
        let read = t.at(12) - t.at(2);
        let truth = log2_int(120);
        assert!((read - truth).abs() <= 8, "{read} {truth}");
        assert_eq!(log2_int(8), 3 << CODE_BITS);
        // log₂ 3000! read whole against the table: inside four grains a step.
        let mut factorial = num_bigint::BigUint::from(1u32);
        for j in 2..=3000u32 {
            factorial *= j;
        }
        let width = factorial.bits();
        let top: u128 = (&factorial >> (width - 62) as usize).try_into().unwrap();
        let whole = ((width as i128) << CODE_BITS) + log2_face(top, CODE_BITS);
        let read = (t.at(6002) - t.at(2)) as i128;
        assert!((read - whole).abs() <= 4 * 3000, "{read} {whole}");
    }

    #[test]
    fn the_founding_lowers_the_complete_code_and_its_parse_decodes() {
        let text = passage();
        let (units, read, receipt) = Units::found(&text).unwrap();
        assert!(receipt.founded > 0);
        assert!(receipt.code_after + receipt.description < receipt.code_before, "{receipt:?}");
        assert_eq!(units.decode(&read), text);
        // Replaying the founded merges reads the passage exactly as the founding left it.
        assert_eq!(units.parse(&text).unwrap(), read);
        // A passage the founding never saw decodes whole.
        let other = b"the dog sat on a cat; zebras ran.".to_vec();
        assert_eq!(units.decode(&units.parse(&other).unwrap()), other);
        // The list restores whole.
        assert_eq!(Units::from_text(&units.to_text()).unwrap(), units);
    }

    #[test]
    fn each_price_is_the_change_of_the_order_one_code() {
        // One merge priced, applied, and the order-one code read again: the code moves by the price
        // less the description.
        let text = passage();
        let mut table = GammaTable::default();
        let mut passage = Passage::new(text.iter().map(|&b| b as u32).collect()).unwrap();
        let before = order_one_code(&mut table, &passage.read(), 256);
        let (a, b) = (b'a' as u32, b't' as u32);
        let taken = passage.occurrences(a, b);
        let (cell_changes, context_changes) = passage.changes(&taken, a, b, 256);
        let mut cells: HashMap<u64, u64> = HashMap::new();
        let mut contexts: HashMap<u32, u64> = HashMap::new();
        for w in text.windows(2) {
            *cells.entry(key(w[0] as u32, w[1] as u32)).or_default() += 1;
            *contexts.entry(w[0] as u32).or_default() += 1;
        }
        let mut price: i128 = 0;
        for (&k, &d) in &cell_changes {
            let n = cells.get(&k).copied().unwrap_or(0);
            price -= table.cell((n as i64 + d) as u64) as i128 - table.cell(n) as i128;
        }
        let mut changed = contexts.clone();
        for (&s, &d) in &context_changes {
            let n = changed.entry(s).or_default();
            *n = (*n as i64 + d) as u64;
        }
        let old: i128 = contexts.values().map(|&n| table.context(n, 256) as i128).sum();
        let new: i128 = changed.values().filter(|&&n| n > 0).map(|&n| table.context(n, 257) as i128).sum();
        price += new - old;
        passage.merge(&taken, 256);
        let after = order_one_code(&mut table, &passage.read(), 257);
        assert_eq!(after - before, price);
    }
}
