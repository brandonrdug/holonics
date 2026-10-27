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

use std::collections::{BinaryHeap, HashMap};

use crate::hnn::keyed_modes::log2_face;

/// The code's grain, `2^(−32)` bits.
pub const CODE_BITS: u32 = 32;
const NONE: u32 = u32::MAX;
const UNIT_BITS: u32 = 62;

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

/// The founded units: the 256 bytes, then each merge's unit in founding order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Units {
    merges: Vec<(u32, u32)>,
    pieces: Vec<Vec<u8>>,
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
    fn new(bytes: &[u8]) -> Result<Self> {
        if bytes.len() >= NONE as usize {
            return refuse("a passage past 2^32 − 1 positions");
        }
        let n = bytes.len();
        let unit: Vec<u32> = bytes.iter().map(|&b| b as u32).collect();
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
        Units { merges: Vec::new(), pieces: (0..=255u8).map(|b| vec![b]).collect() }
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
        let mut units = Units::bytes();
        let mut text = Passage::new(passage)?;
        let mut table = GammaTable::default();
        let mut cells: HashMap<u64, u64> = HashMap::new();
        let mut contexts: Vec<u64> = vec![0; 256];
        for w in passage.windows(2) {
            *cells.entry(key(w[0] as u32, w[1] as u32)).or_default() += 1;
            contexts[w[0] as usize] += 1;
        }
        let mut receipt = FoundingReceipt { symbols_before: passage.len(), ..FoundingReceipt::default() };
        receipt.code_before = order_one_code(&mut table, &text.read(), 256);
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
        let mut text = Passage::new(passage)?;
        for (i, &(a, b)) in self.merges.iter().enumerate() {
            let taken = text.occurrences(a, b);
            if !taken.is_empty() {
                text.merge(&taken, (256 + i) as u32);
            }
            text.positions.remove(&key(a, b));
        }
        Ok(text.read())
    }

    /// The bytes of a passage read in the units.
    pub fn decode(&self, units: &[u32]) -> Vec<u8> {
        units.iter().flat_map(|&u| self.pieces[u as usize].iter().copied()).collect()
    }

    /// The founding list as text: a header, then one merge a line.
    pub fn to_text(&self) -> String {
        let mut s = format!("founded-units-v1 {}\n", self.merges.len());
        for &(a, b) in &self.merges {
            s.push_str(&format!("{a} {b}\n"));
        }
        s
    }

    /// The founding list from its text, refused unless each merge names two units standing.
    pub fn from_text(text: &str) -> Result<Self> {
        let mut lines = text.lines();
        let head: Vec<&str> = lines.next().unwrap_or("").split(' ').collect();
        if head.len() != 2 || head[0] != "founded-units-v1" {
            return refuse("not a founding list's text");
        }
        let count: usize = head[1].parse().map_err(|_| UnitsError::Refused("a founding count that is not a count"))?;
        let mut units = Units::bytes();
        for line in lines {
            let (a, b) = line.split_once(' ').ok_or(UnitsError::Refused("a merge names two units"))?;
            let a: u32 = a.parse().map_err(|_| UnitsError::Refused("a merge's unit that is not a count"))?;
            let b: u32 = b.parse().map_err(|_| UnitsError::Refused("a merge's unit that is not a count"))?;
            if a as usize >= units.len() || b as usize >= units.len() {
                return refuse("a merge names a unit not yet founded");
            }
            units.push(a, b);
        }
        if units.merges.len() != count {
            return refuse("the founding list's count differs from its merges");
        }
        Ok(units)
    }
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
        let mut passage = Passage::new(&text).unwrap();
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
