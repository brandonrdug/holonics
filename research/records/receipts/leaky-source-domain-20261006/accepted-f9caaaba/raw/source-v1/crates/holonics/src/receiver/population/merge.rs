//! **Merges: species of cells, priced by their code-length pair** (campaign 5 on the population;
//! #73, #148; Lean `Compression/Landmark/Context/Merge.{expand_merge, merge_cost_iff,
//! merge_cost_mass_iff, restaurant_merge_ratio, restaurant_found, restaurant_join,
//! restaurant_step_sum, segmentation_mass, encoding_square_or_separator,
//! release_merge_iff_future_equivalent, release_merge_code}`; the record
//! `research/records/2026-09-25_THE_COMPRESSION_IS_OF_LANDMARKS_A_TREE_COCYCLE_AND_MERGES_PRICED_BY_
//! THEIR_CODE_LENGTH_PAIR.md`, §5).
//!
//! [definition; agent-inferred] **Cells and blocks.** A receiver reads a Krichevsky–Trofimov face
//! per cell of a partition ([`Blocks`]): each **item** (a fine cell: a last-byte value, a port's
//! cell) carries its counts per **lane** (a channel whose counts the item's class keeps apart) and
//! per class of the face's alphabet `A`, and belongs to a **group** (merges stay within one). A
//! **block** pools its members' counts and reads one KT face per lane; every member keeps its own
//! counts (its seed), so a block **splits** exactly ([`Blocks::split`]). Merging items is the
//! species collapse of `species` applied to cells: two cells one species.
//!
//! [proved-derived; formal-checked] **The two merges.**
//! - **A release** changes no admitted face: members whose faces agree at every admitted reading
//!   read one face (Lean `release_merge_iff_future_equivalent`, `release_merge_code`). For count
//!   cells whose counts keep moving, a deposit to one member separates them, so the admitted reading
//!   is the standing's face as it stands (the frozen reading at a closed aeon, or the next cell
//!   before any deposit): [`Blocks::species`] groups the blocks whose faces agree exactly on every
//!   lane, and nothing moves.
//! - **A priced merge** pools the members' counts, changing faces. For a partition `G` read on the
//!   received cells `z` the likelihood is the product of its blocks' KT masses
//!   `W_G(z) = ∏_B ∏_lanes KT(n_B)` (KT is exchangeable within a block: `Tree.ktSeq`, the counts are
//!   the whole likelihood), `KT(n) = ∏_c ∏_(j<n_c)(2j + 1) / ∏_(j<Σn)(2j + |A|)`. With the
//!   description a mass `P(G)`, **the merge is accepted exactly when it lowers the complete code
//!   `−log₂ P(G) − log₂ W_G(z)`**, `P(G)·W_G(z) < P(G′)·W_(G′)(z′)` (Lean `merge_cost_mass_iff`;
//!   `merge_cost_iff` with `d = −log₂(P′/P)`): `R·E > 1`, `R = W′/W` and `E = P′/P`, one comparison
//!   of positive integers. It is decided by the integer bounds of [`ProductBound`] (each product
//!   kept at 127 bits and rounded outward): accepted when the lower bound of `R·E`'s numerator
//!   passes the upper bound of its denominator, refused when the reverse, and **undecided** (kept
//!   apart, and counted in the receipt) when the bounds overlap.
//!
//! [definition; agent-inferred] **The description of a partition** is the restaurant mass at
//! `α = ½` over each group's items (Lean `restaurant_found`, `restaurant_join`,
//! `restaurant_step_sum`: KT's one-per-two for partitions, a sequential face at every seating;
//! [proved-standard] Ewens: it sums to one over the set partitions, so its `−log₂` is a prefix code):
//! `P = ∏_groups 2^(N − k) ∏_B (|B| − 1)! / ∏_(j<N)(2j + 1)`, `N` the group's items and `k` its
//! blocks. **A merge of blocks of `a` and `b` items multiplies it by
//! `E = 2·(a + b − 1)!/((a − 1)!(b − 1)!)`** (`restaurant_merge_ratio`), never below `2`: the
//! likelihood may fall by less than the description saves. [agent-inferred] Why this charge: it
//! needs no list of candidate merges and no length of the decoder chosen after the cells; it prices
//! the partition itself, one seating at a time, as the KT face prices the cells.
//!
//! [definition; agent-inferred] **Learning** ([`Blocks::learn`]): every pair of blocks in one group
//! is priced; the accepted merge whose `R·E` has the largest lower bound is taken (the proposal is an
//! order, never the acceptance: BPE's frequency is a proposal), the pairs it touched are priced
//! again, and the passage ends when no pair is accepted. The receipt ([`MergeReceipt`]) keeps the
//! blocks before and after, every accepted merge with its gain enclosed, the pairs left undecided,
//! and the likelihood's and the description's code before and after.
//!
//! [definition] **The hazard's learned partition** (`learn_hazard_partition`, the boundary egg's
//! last-byte classes and shared port counts learned by these merges) was retired September 30 with
//! the byte-tree text line (history at `f5fd8f3b`); the merge law it read stays here and in Lean.
//!
//! [definition] The computational object is the helical pair interaction, read here as the
//! receiver's cells and their merges. Of the winding guide's six general objects this owner touches
//! **faces and placement** (the cells of a partition and their faces) and the **tower thread** (a
//! merge is a coarsening: members restrict to their block, a split refines back); the helix, the
//! pair, the cell holonomy and the tube stay attached through the owners whose cells it reads.

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use super::{PopulationError, refuse};
use crate::compression::landmark::context::{ProductBound, ratio_code_length};
use crate::ratio::Rat;
use crate::ratio::algebraic::{ExactInterval, LOG_OCTAVES, interval_sum};

/// The integer bounds `[lower, upper]` of a positive product.
type Bounds = [ProductBound; 2];

const ONE: Bounds = [ProductBound::ONE; 2];

fn times(a: Bounds, b: Bounds) -> Bounds {
    [a[0].times_bound(b[0], false), a[1].times_bound(b[1], true)]
}

fn times_integer(a: Bounds, factor: &BigUint) -> Bounds {
    [
        a[0].times_integer(factor, false),
        a[1].times_integer(factor, true),
    ]
}

fn zero_interval() -> ExactInterval {
    ExactInterval {
        lower: Rat::zero(),
        upper: Rat::zero(),
    }
}

fn add(a: &ExactInterval, b: &ExactInterval) -> Result<ExactInterval, PopulationError> {
    Ok(interval_sum(a, b)?)
}

/// **`log₂(N/D)`, enclosed** from the bounds of `N` and `D` (the certified `binary_log` at
/// `O + 1` fraction bits, rounded out on the enclosure grid).
fn log_ratio(numerator: Bounds, denominator: Bounds) -> Result<ExactInterval, PopulationError> {
    let bits = LOG_OCTAVES + 1;
    let (numerator_low, _) = numerator[0].log2(bits);
    let (_, numerator_high) = numerator[1].log2(bits);
    let (denominator_low, _) = denominator[0].log2(bits);
    let (_, denominator_high) = denominator[1].log2(bits);
    let enclosure = ExactInterval::new(
        numerator_low - denominator_high,
        numerator_high - denominator_low,
    )
    .map_err(|_| refuse("a log ratio", "its bounds are ordered"))?;
    add(&zero_interval(), &enclosure)
}

/// The negated interval.
fn negated(interval: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: -interval.upper.clone(),
        upper: -interval.lower.clone(),
    }
}

/// [definition] **The KT masses' tables** over an alphabet `A`: the bounds of
/// `∏_(j<m)(2j + 1)` (a class's numerator) and `∏_(j<m)(2j + |A|)` (the denominator), grown as the
/// counts need.
#[derive(Clone, Debug)]
pub struct KtTables {
    alphabet: u64,
    odd: Vec<Bounds>,
    pooled: Vec<Bounds>,
}

impl KtTables {
    /// The tables over an alphabet of at least two classes.
    pub fn new(alphabet: usize) -> Result<Self, PopulationError> {
        if alphabet < 2 {
            return Err(refuse("KT tables", "the alphabet holds at least two classes"));
        }
        Ok(Self {
            alphabet: alphabet as u64,
            odd: vec![ONE],
            pooled: vec![ONE],
        })
    }

    fn grow(&mut self, count: u64) {
        while (self.odd.len() as u64) <= count {
            let j = self.odd.len() as u64 - 1;
            let (odd, pooled) = (self.odd[j as usize], self.pooled[j as usize]);
            self.odd.push([
                odd[0].times(2 * j + 1, false),
                odd[1].times(2 * j + 1, true),
            ]);
            self.pooled.push([
                pooled[0].times(2 * j + self.alphabet, false),
                pooled[1].times(2 * j + self.alphabet, true),
            ]);
        }
    }

    /// **The KT mass of a count table**, its numerator's and denominator's bounds.
    pub fn mass(&mut self, counts: &[u64]) -> (Bounds, Bounds) {
        let total: u64 = counts.iter().sum();
        self.grow(total);
        let numerator = counts
            .iter()
            .fold(ONE, |product, &count| times(product, self.odd[count as usize]));
        (numerator, self.pooled[total as usize])
    }
}

/// [definition] **An item** (module header): its group and its counts per lane and class.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Item {
    pub group: usize,
    pub counts: Vec<Vec<u64>>,
}

/// [definition] **A merge's price** (module header): the two blocks, the description's ratio
/// `E = P′/P` exactly, the code it saves `log₂(R·E)` enclosed, and the decision (none: the bounds
/// overlap, so the blocks stay apart).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Price {
    pub blocks: (usize, usize),
    pub description: BigUint,
    pub gain: ExactInterval,
    pub accepted: Option<bool>,
    ratio: [Bounds; 2],
}

/// [definition] **A learning's receipt** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MergeReceipt {
    /// The blocks before and after.
    pub before: usize,
    pub after: usize,
    /// Each accepted merge: the blocks' members, and the code it saved, enclosed.
    pub accepted: Vec<(Vec<usize>, Vec<usize>, ExactInterval)>,
    /// The pairs left undecided at the end.
    pub undecided: usize,
    /// `−log₂ W` and the description's `−log₂ P`, before and after.
    pub likelihood: [ExactInterval; 2],
    pub description: [ExactInterval; 2],
}

/// [definition] **A partition of items into blocks** (module header): each block's members and its
/// pooled counts; every item keeps its own.
#[derive(Clone, Debug)]
pub struct Blocks {
    lanes: usize,
    classes: usize,
    items: Vec<Item>,
    block_of: Vec<usize>,
    members: Vec<Vec<usize>>,
    counts: Vec<Vec<Vec<u64>>>,
    tables: KtTables,
}

/// `n!` exactly.
fn factorial(n: usize) -> BigUint {
    (1..=n as u64).fold(BigUint::one(), |product, k| product * k)
}

/// **The restaurant ratio of a merge** of blocks of `a` and `b` items,
/// `E = 2·(a + b − 1)!/((a − 1)!(b − 1)!)`, exactly (Lean `restaurant_merge_ratio`).
pub fn restaurant_ratio(a: usize, b: usize) -> BigUint {
    debug_assert!(a >= 1 && b >= 1);
    BigUint::from(2u8) * factorial(a + b - 1) / (factorial(a - 1) * factorial(b - 1))
}

impl Blocks {
    /// **Every item its own block**, over `classes` classes and `lanes` lanes. Refused unless every
    /// item carries its lanes' counts over the classes.
    pub fn new(classes: usize, lanes: usize, items: Vec<Item>) -> Result<Self, PopulationError> {
        if lanes == 0
            || items.iter().any(|item| {
                item.counts.len() != lanes || item.counts.iter().any(|lane| lane.len() != classes)
            })
        {
            return Err(refuse(
                "a partition's items",
                "each carries its lanes' counts over the declared classes",
            ));
        }
        let tables = KtTables::new(classes)?;
        Ok(Self {
            lanes,
            classes,
            block_of: (0..items.len()).collect(),
            members: (0..items.len()).map(|item| vec![item]).collect(),
            counts: items.iter().map(|item| item.counts.clone()).collect(),
            items,
            tables,
        })
    }

    /// The items.
    pub fn items(&self) -> &[Item] {
        &self.items
    }

    /// The block holding an item.
    pub fn block_of(&self, item: usize) -> usize {
        self.block_of[item]
    }

    /// The live blocks, each its members ascending, ordered by their least member.
    pub fn blocks(&self) -> Vec<Vec<usize>> {
        self.members
            .iter()
            .filter(|members| !members.is_empty())
            .cloned()
            .collect()
    }

    fn live(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.members.len()).filter(|&block| !self.members[block].is_empty())
    }

    fn group(&self, block: usize) -> usize {
        self.items[self.members[block][0]].group
    }

    /// A block's pooled counts per lane.
    pub fn counts(&self, block: usize) -> &[Vec<u64>] {
        &self.counts[block]
    }

    fn pooled(&self, a: usize, b: usize) -> Vec<Vec<u64>> {
        self.counts[a]
            .iter()
            .zip(&self.counts[b])
            .map(|(x, y)| x.iter().zip(y).map(|(p, q)| p + q).collect())
            .collect()
    }

    /// **The price of merging two live blocks of one group** (module header).
    pub fn price(&mut self, a: usize, b: usize) -> Result<Price, PopulationError> {
        if a == b
            || self.members.get(a).is_none_or(Vec::is_empty)
            || self.members.get(b).is_none_or(Vec::is_empty)
            || self.group(a) != self.group(b)
        {
            return Err(refuse(
                "a merge's price",
                "it merges two live blocks of one group",
            ));
        }
        let pooled = self.pooled(a, b);
        let (mut numerator, mut denominator) = (ONE, ONE);
        for (lane, merged) in pooled.iter().enumerate() {
            if merged.iter().all(|&count| count == 0) {
                continue;
            }
            let (merged_n, merged_d) = self.tables.mass(merged);
            let (a_n, a_d) = self.tables.mass(&self.counts[a][lane]);
            let (b_n, b_d) = self.tables.mass(&self.counts[b][lane]);
            numerator = times(times(times(numerator, merged_n), a_d), b_d);
            denominator = times(times(times(denominator, merged_d), a_n), b_n);
        }
        let description = restaurant_ratio(self.members[a].len(), self.members[b].len());
        let numerator = times_integer(numerator, &description);
        let accepted = if numerator[0] > denominator[1] {
            Some(true)
        } else if numerator[1] <= denominator[0] {
            Some(false)
        } else {
            None
        };
        Ok(Price {
            blocks: (a.min(b), a.max(b)),
            description,
            gain: log_ratio(numerator, denominator)?,
            accepted,
            ratio: [numerator, denominator],
        })
    }

    /// Whether one accepted price's gain surely passes another's lower bound (`N_i/D_i` against
    /// `N_j/D_j`, their lower bounds compared by cross-multiplying): the proposal order.
    fn above(price: &Price, other: &Price) -> bool {
        let left = price.ratio[0][0].times_bound(other.ratio[1][1], false);
        let right = other.ratio[0][0].times_bound(price.ratio[1][1], false);
        left > right
    }

    /// **Merge two live blocks of one group** unconditionally: the lower id keeps the pooled counts
    /// and every member.
    fn join(&mut self, a: usize, b: usize) {
        let (keep, gone) = (a.min(b), a.max(b));
        self.counts[keep] = self.pooled(keep, gone);
        let moved = std::mem::take(&mut self.members[gone]);
        for &item in &moved {
            self.block_of[item] = keep;
        }
        self.members[keep].extend(moved);
        self.members[keep].sort_unstable();
        self.counts[gone] = vec![vec![0; self.classes]; self.lanes];
    }

    /// **A priced merge**: merged exactly when accepted (module header); its price returned.
    pub fn merge(&mut self, a: usize, b: usize) -> Result<Price, PopulationError> {
        let price = self.price(a, b)?;
        if price.accepted == Some(true) {
            self.join(a, b);
        }
        Ok(price)
    }

    /// **Split a block**: every member returns to its own block with its own counts (the seeds);
    /// the members returned.
    pub fn split(&mut self, block: usize) -> Vec<usize> {
        let members = std::mem::take(&mut self.members[block]);
        for &item in &members {
            self.block_of[item] = item;
            self.members[item] = vec![item];
            self.counts[item] = self.items[item].counts.clone();
        }
        members
    }

    /// **`−log₂ W`**: the partition's likelihood, `Σ_B Σ_lanes −log₂ KT(n_B)`, enclosed.
    pub fn likelihood_bits(&mut self) -> Result<ExactInterval, PopulationError> {
        let (mut numerator, mut denominator) = (ONE, ONE);
        let blocks: Vec<usize> = self.live().collect();
        for block in blocks {
            for lane in 0..self.lanes {
                let (n, d) = self.tables.mass(&self.counts[block][lane]);
                numerator = times(numerator, n);
                denominator = times(denominator, d);
            }
        }
        Ok(negated(&log_ratio(numerator, denominator)?))
    }

    /// **The description's code** `−log₂ P`: the restaurant mass at `α = ½` over each group's items
    /// (module header), enclosed.
    pub fn description_bits(&self) -> Result<ExactInterval, PopulationError> {
        let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for block in self.live() {
            groups
                .entry(self.group(block))
                .or_default()
                .push(self.members[block].len());
        }
        let (mut numerator, mut denominator) = (BigUint::one(), BigUint::one());
        for sizes in groups.values() {
            let items: usize = sizes.iter().sum();
            numerator <<= items - sizes.len();
            for &size in sizes {
                numerator *= factorial(size - 1);
            }
            for j in 0..items as u64 {
                denominator *= 2 * j + 1;
            }
        }
        Ok(ratio_code_length(&numerator, &denominator)?)
    }

    /// **The release reading** (module header): the live blocks grouped by their faces, exactly
    /// equal on every lane (`(2n_c + 1)/(2n + |A|)`); each species ascending by its least block.
    pub fn species(&self) -> Vec<Vec<usize>> {
        let classes = self.classes as u64;
        let face = |counts: &[u64]| -> Vec<Rat> {
            let total: u64 = counts.iter().sum();
            counts
                .iter()
                .map(|&count| {
                    Rat::new(
                        BigInt::from(2 * count + 1),
                        BigInt::from(2 * total + classes),
                    )
                })
                .collect()
        };
        let mut species: BTreeMap<Vec<Vec<Rat>>, Vec<usize>> = BTreeMap::new();
        for block in self.live() {
            let faces = self.counts[block].iter().map(|lane| face(lane)).collect();
            species.entry(faces).or_default().push(block);
        }
        let mut species: Vec<Vec<usize>> = species.into_values().collect();
        species.sort_by_key(|blocks| blocks[0]);
        species
    }

    /// **Learn by priced merges** (module header): the accepted pair of largest gain first, until
    /// none is accepted.
    pub fn learn(&mut self) -> Result<MergeReceipt, PopulationError> {
        let before = self.live().count();
        let likelihood_before = self.likelihood_bits()?;
        let description_before = self.description_bits()?;
        let mut by_group: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for block in self.live().collect::<Vec<_>>() {
            by_group.entry(self.group(block)).or_default().push(block);
        }
        let mut prices: BTreeMap<(usize, usize), Price> = BTreeMap::new();
        for blocks in by_group.values() {
            for (i, &a) in blocks.iter().enumerate() {
                for &b in &blocks[i + 1..] {
                    prices.insert((a, b), self.price(a, b)?);
                }
            }
        }
        let mut accepted = Vec::new();
        loop {
            let mut best: Option<&Price> = None;
            for price in prices.values() {
                if price.accepted == Some(true) && best.is_none_or(|best| Self::above(price, best)) {
                    best = Some(price);
                }
            }
            let Some(best) = best.cloned() else { break };
            let (a, b) = best.blocks;
            let members = (self.members[a].clone(), self.members[b].clone());
            self.join(a, b);
            accepted.push((members.0, members.1, best.gain));
            prices.retain(|&(x, y), _| x != a && x != b && y != a && y != b);
            let group = self.group(a);
            let others: Vec<usize> = self
                .live()
                .filter(|&c| c != a && self.group(c) == group)
                .collect();
            for c in others {
                prices.insert((a.min(c), a.max(c)), self.price(a, c)?);
            }
        }
        Ok(MergeReceipt {
            before,
            after: self.live().count(),
            accepted,
            undecided: prices
                .values()
                .filter(|price| price.accepted.is_none())
                .count(),
            likelihood: [likelihood_before, self.likelihood_bits()?],
            description: [description_before, self.description_bits()?],
        })
    }
}

#[cfg(test)]
#[path = "merge_tests.rs"]
mod tests;
