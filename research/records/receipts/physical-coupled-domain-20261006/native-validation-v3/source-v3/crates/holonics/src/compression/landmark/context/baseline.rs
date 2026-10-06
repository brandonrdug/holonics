//! **The online context baselines: the fixed-order context codes the tree is read beside.**
//!
//! [definition] Order-0 and order-1 with the Krichevsky–Trofimov prior and PPM of order
//! [`PPM_ORDER`] with escape rule C are codes whose contexts have a fixed order: the empty context,
//! the preceding cell's address letter ([`Letter`]), and up to two preceding cells. Each is fitted
//! online on the same stream in the same order as the model it is read beside (prequential: every
//! cell is coded at the current counts, then counted), and each cell's face is exact and its code
//! length enclosed by the certified binary logarithm ([`code_length`]). They are codes, so their
//! owner is compression; the exposure (`hnn::reference`) and the tree's prequential measurement
//! read them.
//!
//! | Lean | Rust |
//! |---|---|
//! | `HNN/RegionCounts.ktProb` (the online Krichevsky–Trofimov face) | [`kt_probability`] |
//! | `Compression/Landmark/Context/Tree.depth_one_is_the_whole_cell_table` (order-1 is the depth-one forced case of the whole-cell emission) | [`Baselines`] |

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::One;

use super::{ContextError, Letter, code_length};
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;

/// [definition] **The online Krichevsky–Trofimov probability** of a class seen `count` times in
/// `total`: `(count + ½)/(total + |A|/2)`, exact (Lean `HNN/RegionCounts.ktProb`).
pub fn kt_probability(count: u64, total: u64, alphabet: usize) -> Rat {
    Rat::new(
        BigInt::from(2 * count + 1),
        BigInt::from(2 * total) + BigInt::from(alphabet),
    )
}

/// The online Krichevsky–Trofimov code length of one cell, `−log₂((count + ½)/(total + |A|/2))`,
/// enclosed by the certified integer binary logarithm ([`code_length`]): the same exact
/// value as `log2_enclosure` encloses, read in microseconds against milliseconds.
fn kt_bits(count: u64, total: u64, alphabet: usize) -> Result<ExactInterval, ContextError> {
    code_length(&kt_probability(count, total, alphabet))
}

/// [definition; agent-inferred] **The PPM baseline's declared order**: two context cells, the
/// least order above the order-1 baseline beside it.
pub const PPM_ORDER: usize = 2;

/// [definition] **Prediction by partial matching, exact and online** (Cleary and Witten; escape
/// rule C of Moffat): the counts of each symbol after each context of up to `order` cells, all
/// orders updated after each cell. A cell is coded from the longest context down: at a context
/// with counts `n_s` over the symbols not yet excluded, total `n` and `d` distinct, a seen symbol
/// has mass `n_s/(n + d)` and the escape `d/(n + d)`, which excludes those symbols below; a context
/// never seen escapes with mass one; below order 0 the declared prior is uniform over the symbols
/// not excluded. The cell's mass is the exact rational product, and its code length is enclosed.
#[derive(Clone, Debug)]
pub struct Ppm {
    order: usize,
    alphabet: usize,
    tables: Vec<BTreeMap<Vec<usize>, BTreeMap<usize, u64>>>,
    history: Vec<usize>,
}

impl Ppm {
    pub fn new(order: usize, alphabet: usize) -> Self {
        Self {
            order,
            alphabet,
            tables: vec![BTreeMap::new(); order + 1],
            history: Vec::new(),
        }
    }

    /// **The exact mass of the next cell** under the counts so far.
    pub fn mass(&self, symbol: usize) -> Rat {
        let mut mass = Rat::one();
        let mut excluded: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
        for k in (0..=self.order.min(self.history.len())).rev() {
            let context = &self.history[self.history.len() - k..];
            let Some(counts) = self.tables[k].get(context) else {
                continue;
            };
            let (mut total, mut distinct) = (0u64, 0u64);
            for (seen, count) in counts {
                if !excluded.contains(seen) {
                    total += count;
                    distinct += 1;
                }
            }
            if total == 0 {
                continue;
            }
            let denominator = BigInt::from(total + distinct);
            if let Some(count) = counts.get(&symbol).filter(|_| !excluded.contains(&symbol)) {
                return mass * Rat::new(BigInt::from(*count), denominator);
            }
            mass *= Rat::new(BigInt::from(distinct), denominator);
            excluded.extend(counts.keys().copied());
        }
        mass * Rat::new(
            BigInt::one(),
            BigInt::from(self.alphabet.saturating_sub(excluded.len()).max(1)),
        )
    }

    /// Count one cell at every order and extend the history.
    pub fn update(&mut self, symbol: usize) {
        for k in 0..=self.order.min(self.history.len()) {
            let context = self.history[self.history.len() - k..].to_vec();
            *self.tables[k]
                .entry(context)
                .or_default()
                .entry(symbol)
                .or_insert(0) += 1;
        }
        self.history.push(symbol);
        if self.history.len() > self.order {
            self.history.remove(0);
        }
    }

    /// **The cell's code length** `−log₂ P`, enclosed by the certified integer binary logarithm
    /// ([`code_length`]), then its count.
    pub fn code(&mut self, symbol: usize) -> Result<ExactInterval, ContextError> {
        let bits = code_length(&self.mass(symbol))?;
        self.update(symbol);
        Ok(bits)
    }
}

/// [definition] **One cell's code lengths under the online baselines**, each read at the standing
/// before the cell's own count: uniform, order-0 and order-1 Krichevsky–Trofimov, and PPM of order
/// [`PPM_ORDER`] with escape rule C, each enclosed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BaselineCodes {
    pub uniform: ExactInterval,
    pub order_zero: ExactInterval,
    pub order_one: ExactInterval,
    pub ppm: ExactInterval,
}

/// [definition] **One cell's exact faces under the online baselines**, read at the standing before
/// the cell's own count ([`Baselines::face_cell`]): the faces [`BaselineCodes`] encloses the code
/// lengths of, for a reader that multiplies a passage's faces ([`super::PassageCode`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BaselineFaces {
    pub uniform: Rat,
    pub order_zero: Rat,
    pub order_one: Rat,
    pub ppm: Rat,
}

/// [definition] **The online baselines, fitted on the same stream in the same order** as the model
/// they are read beside: every cell is coded at the current counts, then counted (prequential).
/// [agent-inferred] The order-1 baseline's contexts are the preceding cell's address letter
/// ([`Letter`]: `1 + code`, and the boundary `0` before the stream's first cell): the
/// preceding cell's region. Order-1 is the depth-one forced case of the whole-cell emission
/// (`|A|`-ary KT masses at a node, the region table; Lean
/// `Compression/Landmark/Context/Tree.depth_one_is_the_whole_cell_table`), which lives in Lean only; the executed tree
/// ([`super::Landmarks`]) emits the cell's odometer digits, and its depth-one forced case is
/// a product of binary KT faces at the preceding cell, a different law. The exposure
/// (`hnn::reference::Reference::expose`) and the landmark tree's prequential measurement
/// (`hnn::reference::prequential`) read them.
#[derive(Clone, Debug)]
pub struct Baselines {
    alphabet: usize,
    uniform: ExactInterval,
    order_zero: Vec<u64>,
    order_one: BTreeMap<(usize, usize), u64>,
    order_one_totals: Vec<u64>,
    previous: Option<usize>,
    seen: u64,
    ppm: Ppm,
}

impl Baselines {
    /// The baselines at their priors over `|A|` classes.
    pub fn new(alphabet: usize) -> Result<Self, ContextError> {
        Ok(Self {
            alphabet,
            uniform: code_length(&Rat::new(BigInt::one(), BigInt::from(alphabet)))?,
            order_zero: vec![0; alphabet],
            order_one: BTreeMap::new(),
            order_one_totals: vec![0; alphabet + 1],
            previous: None,
            seen: 0,
            ppm: Ppm::new(PPM_ORDER, alphabet),
        })
    }

    /// The order-1 context: the preceding cell's address letter's code.
    fn context(&self) -> usize {
        self.previous.map_or(Letter::Boundary, Letter::Cell).code() as usize
    }

    /// Count one cell in the Krichevsky–Trofimov baselines.
    fn count(&mut self, code: usize) {
        let context = self.context();
        self.order_zero[code] += 1;
        *self.order_one.entry((context, code)).or_insert(0) += 1;
        self.order_one_totals[context] += 1;
        self.previous = Some(code);
        self.seen += 1;
    }

    /// Count one cell in every baseline, uncoded.
    pub fn update(&mut self, code: usize) {
        self.count(code);
        self.ppm.update(code);
    }

    /// **Code one cell in every baseline at the current counts, then count it** (prequential).
    pub fn code_cell(&mut self, code: usize) -> Result<BaselineCodes, ContextError> {
        let context = self.context();
        let codes = BaselineCodes {
            uniform: self.uniform.clone(),
            order_zero: kt_bits(self.order_zero[code], self.seen, self.alphabet)?,
            order_one: kt_bits(
                self.order_one.get(&(context, code)).copied().unwrap_or(0),
                self.order_one_totals[context],
                self.alphabet,
            )?,
            ppm: self.ppm.code(code)?,
        };
        self.count(code);
        Ok(codes)
    }

    /// **Read one cell's exact faces in every baseline at the current counts, then count it**
    /// (prequential; [`Baselines::code_cell`]'s faces).
    pub fn face_cell(&mut self, code: usize) -> Result<BaselineFaces, ContextError> {
        if code >= self.alphabet {
            return Err(ContextError::CellOutside {
                code,
                alphabet: self.alphabet,
            });
        }
        let context = self.context();
        let faces = BaselineFaces {
            uniform: Rat::new(BigInt::one(), BigInt::from(self.alphabet)),
            order_zero: kt_probability(self.order_zero[code], self.seen, self.alphabet),
            order_one: kt_probability(
                self.order_one.get(&(context, code)).copied().unwrap_or(0),
                self.order_one_totals[context],
                self.alphabet,
            ),
            ppm: self.ppm.mass(code),
        };
        self.update(code);
        Ok(faces)
    }
}
