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
//! - **A priced birth** ([`birth_price`]) is the merge read from the birth's side: a newborn block
//!   split off its parent's is kept exactly when `P(G′)·W_(G′)(z) > P(G)·W_G(z)`, the newborn's
//!   description its draw from the reserved mass, `P(G′)/P(G) = 1/charge`. It is decided on the same
//!   integer bounds (undecided: not born). Its consumer is the passage's charged founding
//!   (`hnn::encoding::found_passage`), where a context class is born only where it shortens the
//!   founding passage's code.
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
//! [definition; agent-inferred] **The hazard's learned partition** ([`learn_hazard_partition`]; the
//! boundary egg's `HazardPartition`), decided on the cells it is given (the development cells only):
//! the part clock reads them, the hazard counts every fine cell (a port's channel with its last
//! byte's value, or after a sentence close its kind, phase and carry classes), then
//! 1. **the last-byte classes**: the byte values met on the declared `Other` branch are items, the
//!    channels their lanes, one group; the learned classes are adopted when their complete code
//!    (the development code under them plus their restaurant description) is below the declared
//!    classes' code (the declared classes are the sweep's law, charged there). A value never met is
//!    classed with the block of most values (the restaurant's most probable seating, `m/(N + α)`);
//! 2. **the shared counts**: the partition's cells are items, each group one rest (a cell read
//!    without its channel), one lane: a port's cell merged into another port's shares its counts
//!    (the thin human port's with the agent's). Adopted when the complete code falls below the
//!    first stage's.
//!
//! The receipt ([`PartitionReceipt`]) reads the cells before and after each stage, the codes and the
//! description charged, and the frozen standing's species (the learned cells whose faces agree at
//! the end of the cells: a release, which would change no face).
//!
//! [definition] The computational object is the helical pair interaction, read here as the
//! receiver's cells and their merges. Of the winding guide's six general objects this owner touches
//! **faces and placement** (the cells of a partition and their faces), the **tower thread** (a merge
//! is a coarsening: members restrict to their block, a split refines back) and, through the part
//! clock's port, the **helix** (the phase and the carry a cell is read at); the pair, the cell
//! holonomy and the tube stay attached through the trees' and the clock's owners.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use super::boundary::{BYTE_VALUES, HazardCell, HazardPartition, HazardRest, PartClock};
use super::{PopulationError, refuse};
use crate::compression::landmark::context::{ProductBound, SectionChart, ratio_code_length};
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

// -------------------------------------------------------------------------------------------
// the priced birth

/// [definition; agent-inferred, U6] **A birth's price**: the priced merge read from the birth's
/// side (module header, "The two merges"; Lean `merge_cost_mass_iff`). A birth splits cells off
/// their block into a newborn block; it is the merge's inverse, so it is kept exactly when the merge
/// would be refused: `P(G′) W_G′(z) > P(G) W_G(z)`, `G′` the partition with the newborn. The newborn
/// draws its description mass from the reserved mass, `P(G′)/P(G) = 1/charge` (the population's
/// birth from reserved mass `2^(−ℓ_g)`, `charge = 2^ℓ_g` an integer), so it is born exactly when
/// `W′ · D > W · D′ · charge` on the KT masses' integer bounds: accepted when the lower bound of the
/// left passes the upper bound of the right, refused when the reverse, undecided (not born, and
/// counted by the caller) when they overlap. Its gain `log₂(W′/(W · charge))` is enclosed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BirthPrice {
    pub gain: ExactInterval,
    pub accepted: Option<bool>,
    ratio: [Bounds; 2],
}

impl BirthPrice {
    /// Whether this price's gain surely passes another's lower bound (their lower bounds compared by
    /// cross-multiplying): the proposal order, never the acceptance.
    pub fn above(&self, other: &BirthPrice) -> bool {
        let left = self.ratio[0][0].times_bound(other.ratio[1][1], false);
        let right = other.ratio[0][0].times_bound(self.ratio[1][1], false);
        left > right
    }
}

/// The KT masses' product over blocks, its numerator's and denominator's bounds.
fn kt_product(tables: &mut KtTables, blocks: &[Vec<u64>]) -> (Bounds, Bounds) {
    let (mut numerator, mut denominator) = (ONE, ONE);
    for counts in blocks {
        let (n, d) = tables.mass(counts);
        numerator = times(numerator, n);
        denominator = times(denominator, d);
    }
    (numerator, denominator)
}

/// **The price of a birth** (see [`BirthPrice`]): the blocks' counts over the tables' alphabet
/// before and after the birth (the same received cells), and the newborn's charge `2^ℓ_g`.
pub fn birth_price(
    tables: &mut KtTables,
    before: &[Vec<u64>],
    after: &[Vec<u64>],
    charge: &BigUint,
) -> Result<BirthPrice, PopulationError> {
    let (w, d) = kt_product(tables, before);
    let (w_after, d_after) = kt_product(tables, after);
    let left = times(w_after, d);
    let right = times_integer(times(w, d_after), charge);
    let accepted = if left[0] > right[1] {
        Some(true)
    } else if left[1] <= right[0] {
        Some(false)
    } else {
        None
    };
    Ok(BirthPrice {
        gain: log_ratio(left, right)?,
        accepted,
        ratio: [left, right],
    })
}

/// **`−log₂ W`** of a partition read as its blocks' counts over the tables' alphabet: the KT masses'
/// product (each block's cells coded before its own deposit, in any order: KT is exchangeable),
/// enclosed.
pub fn partition_code(
    tables: &mut KtTables,
    blocks: &[Vec<u64>],
) -> Result<ExactInterval, PopulationError> {
    let (numerator, denominator) = kt_product(tables, blocks);
    Ok(negated(&log_ratio(numerator, denominator)?))
}

/// [definition] **The hazard's learned partition's receipt** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartitionReceipt {
    /// The hazard's deposits read, and the fine cells met.
    pub deposits: u64,
    pub fine_cells: usize,
    /// The declared partition's cells met and its code on the cells (`−log₂ W`).
    pub declared_cells: usize,
    pub declared_code: ExactInterval,
    /// The last-byte values met on the `Other` branch, and the first stage's learning; its classes
    /// adopted or not, the partition's cells and code after it.
    pub values_met: usize,
    pub classes: MergeReceipt,
    pub classes_adopted: bool,
    pub classes_cells: usize,
    pub classes_code: ExactInterval,
    /// The second stage's learning (the shared counts), its partition and its code, adopted or not.
    pub shares: MergeReceipt,
    pub shares_adopted: bool,
    pub shared: HazardPartition,
    pub shared_code: ExactInterval,
    /// The learned partition's cells met, its code on the cells, and its description charged (the
    /// adopted stages' restaurant codes).
    pub learned_cells: usize,
    pub learned_code: ExactInterval,
    pub description: ExactInterval,
    /// The frozen standing's species: the learned cells whose faces agree (a release).
    pub species: usize,
}

/// `−log₂ W` of a hazard's cells' counts, enclosed.
fn hazard_code(
    tables: &mut KtTables,
    counts: &BTreeMap<HazardCell, [u64; 2]>,
) -> Result<ExactInterval, PopulationError> {
    let (mut numerator, mut denominator) = (ONE, ONE);
    for pair in counts.values() {
        let (n, d) = tables.mass(pair);
        numerator = times(numerator, n);
        denominator = times(denominator, d);
    }
    Ok(negated(&log_ratio(numerator, denominator)?))
}

/// The fine counts pooled by a partition.
fn pooled_by(
    fine: &BTreeMap<HazardCell, [u64; 2]>,
    partition: &HazardPartition,
) -> BTreeMap<HazardCell, [u64; 2]> {
    let mut counts: BTreeMap<HazardCell, [u64; 2]> = BTreeMap::new();
    for (cell, pair) in fine {
        let pooled = counts.entry(partition.coarse(cell)).or_insert([0, 0]);
        pooled[0] += pair[0];
        pooled[1] += pair[1];
    }
    counts
}

/// **Learn the hazard's partition from the cells** (module header): the part clock reads them, the
/// hazard counts every fine cell, then the last-byte classes and the shared counts, each adopted
/// only where its complete code falls. Nothing else reads the cells.
pub fn learn_hazard_partition(
    chart: SectionChart,
    cells: &[usize],
) -> Result<(HazardPartition, PartitionReceipt), PopulationError> {
    let alphabet = chart.alphabet();
    let mut clock = PartClock::new(chart);
    let mut hazard = super::boundary::Hazard::with_partition(HazardPartition::finest());
    let mut deposits = 0;
    for &cell in cells {
        if cell >= alphabet {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        let port = clock.port();
        if port.section.is_some() {
            deposits += 1;
        }
        hazard.deposit(&port, chart.section(cell).is_some());
        clock.advance(cell);
    }
    let fine = hazard.fine_counts().clone();
    let mut tables = KtTables::new(2)?;
    let declared = HazardPartition::declared();
    let declared_counts = pooled_by(&fine, &declared);
    let declared_code = hazard_code(&mut tables, &declared_counts)?;
    let declared_cells = declared_counts.len();

    // 1. The last-byte classes: the values met on the `Other` branch, the channels as lanes.
    let channels = chart.channels();
    let mut values: BTreeMap<usize, Vec<Vec<u64>>> = BTreeMap::new();
    for (cell, pair) in &fine {
        if let HazardRest::Other { class } = cell.rest {
            values
                .entry(class)
                .or_insert_with(|| vec![vec![0, 0]; channels])[cell.channel] = pair.to_vec();
        }
    }
    let met: Vec<usize> = values.keys().copied().collect();
    let items = values
        .into_values()
        .map(|counts| Item { group: 0, counts })
        .collect();
    let mut blocks = Blocks::new(2, channels, items)?;
    let classes_receipt = blocks.learn()?;
    let learned_blocks = blocks.blocks();
    let default = learned_blocks
        .iter()
        .enumerate()
        .max_by(|(i, x), (j, y)| x.len().cmp(&y.len()).then(j.cmp(i)))
        .map_or(0, |(index, _)| index);
    let mut classes = vec![default; BYTE_VALUES];
    for (index, members) in learned_blocks.iter().enumerate() {
        for &item in members {
            classes[met[item]] = index;
        }
    }
    let first = HazardPartition::learned(classes, BTreeMap::new())?;
    let first_counts = pooled_by(&fine, &first);
    let first_code = hazard_code(&mut tables, &first_counts)?;
    let classes_complete = add(&first_code, &classes_receipt.description[1])?;
    let classes_adopted = classes_complete.upper < declared_code.lower;
    let (base, base_counts, base_code) = if classes_adopted {
        (first, first_counts, first_code)
    } else {
        (declared, declared_counts, declared_code.clone())
    };
    let (classes_cells, classes_code) = (base_counts.len(), base_code.clone());

    // 2. The shared counts: the base partition's cells, grouped by their rest, one lane.
    let rests: Vec<HazardRest> = base_counts
        .keys()
        .map(|cell| cell.rest)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let cells_of: Vec<HazardCell> = base_counts.keys().copied().collect();
    let items = base_counts
        .iter()
        .map(|(cell, pair)| Item {
            group: rests.binary_search(&cell.rest).unwrap_or(0),
            counts: vec![pair.to_vec()],
        })
        .collect();
    let mut shared = Blocks::new(2, 1, items)?;
    let shares_receipt = shared.learn()?;
    let mut shares: BTreeMap<HazardRest, Vec<usize>> = BTreeMap::new();
    for members in shared.blocks() {
        if members.len() < 2 {
            continue;
        }
        let rest = cells_of[members[0]].rest;
        let keep = members
            .iter()
            .map(|&item| cells_of[item].channel)
            .min()
            .unwrap_or(0);
        let map = shares
            .entry(rest)
            .or_insert_with(|| (0..channels).collect());
        for &item in &members {
            map[cells_of[item].channel] = keep;
        }
    }
    let second = HazardPartition::learned(base.classes().to_vec(), shares)?;
    let second_counts = pooled_by(&fine, &second);
    let second_code = hazard_code(&mut tables, &second_counts)?;
    let shares_complete = add(&second_code, &shares_receipt.description[1])?;
    let shares_adopted = shares_complete.upper < base_code.lower;
    let mut description = zero_interval();
    if classes_adopted {
        description = add(&description, &classes_receipt.description[1])?;
    }
    let (shared, shared_code) = (second.clone(), second_code.clone());
    let (partition, counts, code) = if shares_adopted {
        description = add(&description, &shares_receipt.description[1])?;
        (second, second_counts, second_code)
    } else {
        (base, base_counts, base_code)
    };
    let items = counts
        .values()
        .map(|pair| Item {
            group: 0,
            counts: vec![pair.to_vec()],
        })
        .collect();
    let species = Blocks::new(2, 1, items)?.species().len();
    let receipt = PartitionReceipt {
        deposits,
        fine_cells: fine.len(),
        declared_cells,
        declared_code,
        values_met: met.len(),
        classes: classes_receipt,
        classes_adopted,
        classes_cells,
        classes_code,
        shares: shares_receipt,
        shares_adopted,
        shared,
        shared_code,
        learned_cells: counts.len(),
        learned_code: code,
        description,
        species,
    };
    Ok((partition, receipt))
}

#[cfg(test)]
#[path = "merge_tests.rs"]
mod tests;
