//! A candidate ring pays its description out of the code its phase-resolved pair moment shortens.
//!
//! [proved-derived; formalization owed #62] For `g = gcd(period, cell_clock)`, the node's
//! maximum-likelihood code is `ML_g = sum(n log2 n - sum_y N_y log2 N_y)`. The candidate's KT
//! sequential law is `Q`; the surplus is `ML_g - bits(Q)`. Its conservative lower endpoint must
//! strictly exceed the description cost.
//!
//! **The guarantee and its hypotheses** (universal inference with Ville's inequality):
//! - The null is any law `P` under which the class `y_k` depends on the past only through
//!   `(k mod g, y_(k-offset))`. `ML_g` is the shortest code among them, so `Q / P_ML <= Q / P`,
//!   and `Q / P` is a nonnegative `P`-martingale of mean one.
//! - The family and its costs are fixed at `open`, before the stream. Ville's inequality and the
//!   union over the family bound the probability that any node law explains a founding by
//!   `family_bound = sum 2^(-cost)`, at every read time however often the law is read.
//! - `open` refuses a family whose bound is not below one (a cost of zero among them), so the
//!   guarantee is never vacuous.
//! - Each `reopen` is a fresh e-process: its guarantee runs from its own first counted cell.
//! This reads the helical pair interaction at the declared offset, on classes of any modality.
//! It retains pair counts, their bounded product code and the last offset classes, never a tape.
//!
//! The phase's `k` counts every ingested cell, including the opening context. Only cells with a
//! full context enter the counts. A separate counted population sizes the logarithm precision.
//! Reopening resets `k` and the counts while preserving that context across the founding.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_bigint::BigInt;
use num_traits::{One, Zero};

use crate::compression::landmark::context::PassageCode;
use crate::hnn::HnnError;
use crate::ratio::Rat;
use crate::ratio::algebraic::{ExactInterval, LOG_OCTAVES, log2_enclosure_at};

/// [definition] **The description ceiling.** A cost is the field's description increment of one
/// founded ring (`Field::founding_cost`): two Elias-gamma lengths `2 bits(n+1) - 1` of `u64`
/// values plus the founded count's increment (zero or two). On `u64` each length is at most
/// `2 * 65 - 1`, so no field description exceeds this, and `open` refuses a larger cost before the
/// exact family bound's denominator `2^cost` is formed.
pub const DESCRIPTION_CEILING: u64 = 2 + 2 * (2 * (u64::BITS as u64 + 1) - 1);

/// One candidate period with its description cost, in bits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Candidate {
    pub period: u64,
    pub cost: u64,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Row {
    total: u64,
    classes: BTreeMap<usize, u64>,
}

// Unoccupied pair coordinates are exactly zero. Sparse storage does not impose a period cap or
// materialize period * alphabet squared cells when opening the law.
type Counts = BTreeMap<(u64, usize), Row>;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Split {
    candidate: Candidate,
    node: u64,
    counts: Counts,
    code: PassageCode,
}

/// The founding law's state since its opening: a quotient of the passage, never a tape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoundingLaw {
    alphabet: usize,
    offset: usize,
    cell_clock: u64,
    context: VecDeque<usize>,
    cells: u64,
    counted: u64,
    splits: Vec<Split>,
    nodes: BTreeMap<u64, Counts>,
    /// `sum 2^(-cost)` over the family fixed at `open`, below one.
    family_bound: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateRead {
    pub period: u64,
    /// `g = gcd(period, cell_clock)`, the node it splits.
    pub node: u64,
    /// The enclosure of the code it shortens by, in bits.
    pub surplus: ExactInterval,
    pub cost: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoundingRead {
    pub cells: u64,
    pub cell_clock: u64,
    pub candidates: Vec<CandidateRead>,
    /// `sum 2^(-cost)`, exact.
    pub family_bound: Rat,
    pub founded: Option<u64>,
}

fn refusal(what: &'static str) -> HnnError {
    HnnError::Founding { what }
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn preflight_count(counts: &Counts, at: (u64, usize), class: usize) -> Result<(), HnnError> {
    if let Some(row) = counts.get(&at) {
        row.total
            .checked_add(1)
            .ok_or_else(|| refusal("a pair row's population exceeds u64"))?;
        row.classes
            .get(&class)
            .copied()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or_else(|| refusal("a pair count exceeds u64"))?;
    }
    Ok(())
}

fn count(counts: &mut Counts, at: (u64, usize), class: usize) {
    let row = counts.entry(at).or_default();
    row.total += 1;
    *row.classes.entry(class).or_default() += 1;
}

/// Guard the bounded-product carrier's integer exponents before its infallible arithmetic.
fn appended(mut code: PassageCode, face: &Rat) -> Result<PassageCode, HnnError> {
    let (top, bottom, twos) = code.bounds();
    let numerator = face.numer().magnitude();
    let denominator = face.denom().magnitude();
    let shift = denominator.trailing_zeros().unwrap_or(0);
    let odd = denominator >> shift as usize;
    code.factors()
        .checked_add(1)
        .ok_or_else(|| refusal("the split code's factor count exceeds u64"))?;
    twos.checked_add(shift)
        .ok_or_else(|| refusal("the split code's dyadic exponent exceeds u64"))?;
    for (bounds, factor) in [(top, numerator), (bottom, &odd)] {
        for bound in bounds {
            bound
                .exponent
                .checked_add(factor.bits())
                .and_then(|e| e.checked_add(1))
                .ok_or_else(|| refusal("the split code's product exponent exceeds u64"))?;
        }
    }
    code.face(face)?;
    Ok(code)
}

impl FoundingLaw {
    /// Refused for a missing alphabet, offset or cell clock, a period below two or dividing the
    /// cell clock, duplicate periods, a cost above [`DESCRIPTION_CEILING`], or a family whose
    /// bound `sum 2^(-cost)` is not below one. Nothing is allocated in proportion to a period.
    pub fn open(
        alphabet: usize,
        offset: usize,
        cell_clock: u64,
        candidates: Vec<Candidate>,
    ) -> Result<Self, HnnError> {
        if alphabet < 2 || offset == 0 || cell_clock == 0 {
            return Err(refusal(
                "founding needs an alphabet, a positive offset and cell clock",
            ));
        }
        let mut periods = BTreeSet::new();
        let mut nodes = BTreeMap::new();
        let mut splits = Vec::with_capacity(candidates.len());
        let mut family_bound = Rat::zero();
        for candidate in candidates {
            if candidate.period < 2 || cell_clock.is_multiple_of(candidate.period) {
                return Err(refusal(
                    "a candidate period is at least two and does not divide the cell clock",
                ));
            }
            if !periods.insert(candidate.period) {
                return Err(refusal("candidate periods are distinct"));
            }
            if candidate.cost > DESCRIPTION_CEILING {
                return Err(refusal(
                    "a candidate's cost is a field description, within the description ceiling",
                ));
            }
            family_bound += Rat::new(BigInt::one(), BigInt::one() << candidate.cost as usize);
            let node = gcd(candidate.period, cell_clock);
            nodes.entry(node).or_insert_with(BTreeMap::new);
            splits.push(Split {
                candidate,
                node,
                counts: BTreeMap::new(),
                code: PassageCode::new(),
            });
        }
        if family_bound >= Rat::one() {
            return Err(refusal(
                "a founding family's bound sum 2^(-cost) is below one",
            ));
        }
        Ok(Self {
            alphabet,
            offset,
            cell_clock,
            context: VecDeque::new(),
            cells: 0,
            counted: 0,
            splits,
            nodes,
            family_bound,
        })
    }

    /// Append one class atomically. The KT face is read before the pair count changes.
    pub fn receive(&mut self, class: usize) -> Result<(), HnnError> {
        if class >= self.alphabet {
            return Err(refusal(
                "the received class is outside the founding alphabet",
            ));
        }
        let cells = self
            .cells
            .checked_add(1)
            .ok_or_else(|| refusal("the cell count exceeds u64"))?;
        if self.context.len() < self.offset {
            self.context.push_back(class);
            self.cells = cells;
            return Ok(());
        }
        let earlier = self.context[0];
        let counted = self
            .counted
            .checked_add(1)
            .ok_or_else(|| refusal("the counted population exceeds u64"))?;
        let mut codes = Vec::with_capacity(self.splits.len());
        for split in &self.splits {
            let at = (self.cells % split.candidate.period, earlier);
            preflight_count(&split.counts, at, class)?;
            let row = split.counts.get(&at);
            let total = row.map_or(0, |row| row.total);
            let seen = row
                .and_then(|row| row.classes.get(&class))
                .copied()
                .unwrap_or(0);
            let face = Rat::new(
                BigInt::from(seen) * 2 + 1,
                BigInt::from(total) * 2 + BigInt::from(self.alphabet),
            );
            codes.push(appended(split.code, &face)?);
        }
        for (&node, counts) in &self.nodes {
            preflight_count(counts, (self.cells % node, earlier), class)?;
        }
        // All fallible arithmetic is above this publication boundary.
        for (split, code) in self.splits.iter_mut().zip(codes) {
            split.code = code;
            count(
                &mut split.counts,
                (self.cells % split.candidate.period, earlier),
                class,
            );
        }
        for (&node, counts) in &mut self.nodes {
            count(counts, (self.cells % node, earlier), class);
        }
        self.context.pop_front();
        self.context.push_back(class);
        self.cells = cells;
        self.counted = counted;
        Ok(())
    }

    /// Read every candidate without changing the law. Greatest certified excess wins; ties use
    /// the least period. Empty counts have exactly zero maximum-likelihood code.
    ///
    /// [proved-derived] **The read's precision.** Each `m log2 m` is `m` times an enclosure of
    /// `log2 m` narrower than `3 * 2^(-p)` (`log2_enclosure_at`). A node's terms carry weights
    /// `m` that sum to `2n` (the rows' totals and their class counts, `n` counted cells each), so
    /// `ML_g`'s enclosure is narrower than `6n * 2^(-p)`. With `p = ceil(log2(6n)) + O` it is
    /// narrower than `2^(-O)`, the declared grid on which every code length is held
    /// ([`LOG_OCTAVES`]), the grid `bits(Q)` is read on.
    pub fn read(&self) -> Result<FoundingRead, HnnError> {
        // The weights' sum 2n times the enclosure's width factor 3.
        let width_factor = 6 * u128::from(self.counted.max(1));
        let precision = u128::BITS - (width_factor - 1).leading_zeros() + LOG_OCTAVES;
        let mut logs = BTreeMap::new();
        let mut ml = BTreeMap::new();
        for (&node, counts) in &self.nodes {
            let mut code = ExactInterval::point(Rat::zero());
            for row in counts.values() {
                let total = weighted_log(row.total, precision, &mut logs)?;
                code.lower += total.lower;
                code.upper += total.upper;
                for &n in row.classes.values() {
                    let term = weighted_log(n, precision, &mut logs)?;
                    code.lower -= term.upper;
                    code.upper -= term.lower;
                }
            }
            ml.insert(node, code);
        }
        let mut best: Option<(Rat, u64)> = None;
        let mut candidates = Vec::with_capacity(self.splits.len());
        for split in &self.splits {
            let node = &ml[&split.node];
            let bits = split.code.bits()?;
            let surplus = ExactInterval::new(&node.lower - bits.upper, &node.upper - bits.lower)?;
            let cost = split.candidate.cost;
            let excess = &surplus.lower - Rat::from_integer(BigInt::from(cost));
            let period = split.candidate.period;
            if excess > Rat::zero()
                && best
                    .as_ref()
                    .is_none_or(|(prior, at)| excess > *prior || (excess == *prior && period < *at))
            {
                best = Some((excess, period));
            }
            candidates.push(CandidateRead {
                period,
                node: split.node,
                surplus,
                cost,
            });
        }
        Ok(FoundingRead {
            cells: self.cells,
            cell_clock: self.cell_clock,
            candidates,
            family_bound: self.family_bound.clone(),
            founded: best.map(|(_, period)| period),
        })
    }

    pub fn cells(&self) -> u64 {
        self.cells
    }

    /// The key whose next tick enters phase `cells mod period`. Periods are candidates (>= 2);
    /// the zero-period query returns zero without dividing by zero.
    pub fn key(&self, period: u64) -> u64 {
        self.cells
            .checked_sub(1)
            .map_or(period.saturating_sub(1), |k| {
                k.checked_rem(period).unwrap_or(0)
            })
    }

    /// Reopen on the new clock atomically, preserving only the last offset classes.
    pub fn reopen(&mut self, cell_clock: u64, candidates: Vec<Candidate>) -> Result<(), HnnError> {
        let mut next = Self::open(self.alphabet, self.offset, cell_clock, candidates)?;
        next.context = self.context.clone();
        *self = next;
        Ok(())
    }
}

fn weighted_log(
    n: u64,
    precision: u32,
    cache: &mut BTreeMap<u64, ExactInterval>,
) -> Result<ExactInterval, HnnError> {
    if let Some(log) = cache.get(&n) {
        return Ok(log.clone());
    }
    let value = Rat::from_integer(BigInt::from(n));
    let log = if n == 0 {
        ExactInterval::point(Rat::zero())
    } else {
        let log = log2_enclosure_at(&value, precision)?;
        ExactInterval::new(&value * log.lower, &value * log.upper)?
    };
    cache.insert(n, log.clone());
    Ok(log)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::integer;

    // Fixed before the run. These are fixture descriptions, not costs selected from its output.
    const COSTS: [u64; 11] = [12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32];
    const PLANTED: [usize; 5] = [0, 0, 1, 0, 2];

    fn candidates() -> Vec<Candidate> {
        (2..=12)
            .zip(COSTS)
            .map(|(period, cost)| Candidate { period, cost })
            .collect()
    }

    // An independent, exact-rational oracle. It keeps its own dense test counts, multiplies
    // the KT probabilities exactly, and exponentiates integer counts to form the node MLE.
    // Thus log2(Q/P_ML)>cost is checked as Q/P_ML>2^cost, without logarithm enclosures. Cell
    // `k` (counted from the opening context) sits at phase `k mod period` with context
    // `stream[k - offset]`; its node is `gcd(period, clock)`.
    fn oracle(
        stream: &[usize],
        candidates: &[Candidate],
        alphabet: usize,
        offset: usize,
        clock: u64,
    ) -> Option<u64> {
        let mut best: Option<(Rat, u64)> = None;
        for candidate in candidates {
            let period = candidate.period as usize;
            let node = gcd(candidate.period, clock) as usize;
            let mut split = vec![vec![vec![0u64; alphabet]; alphabet]; period];
            let mut counts = vec![vec![vec![0u64; alphabet]; alphabet]; node];
            let mut probability = Rat::one();
            for k in offset..stream.len() {
                let (a, y) = (stream[k - offset], stream[k]);
                let row = &mut split[k % period][a];
                let total = row.iter().sum::<u64>();
                probability *= Rat::new(
                    BigInt::from(2 * row[y] + 1),
                    BigInt::from(2 * total + alphabet as u64),
                );
                row[y] += 1;
                counts[k % node][a][y] += 1;
            }
            let mut maximum = Rat::one();
            for row in counts.iter().flatten() {
                let total = row.iter().sum::<u64>();
                if total == 0 {
                    continue;
                }
                for &n in row {
                    if n > 0 {
                        maximum *= Rat::from_integer(BigInt::from(n).pow(n as u32));
                    }
                }
                maximum /= Rat::from_integer(BigInt::from(total).pow(total as u32));
            }
            let capital =
                probability / maximum / Rat::from_integer(BigInt::one() << candidate.cost as usize);
            if capital > Rat::one()
                && best.as_ref().is_none_or(|(value, period)| {
                    capital > *value || (capital == *value && candidate.period < *period)
                })
            {
                best = Some((capital, candidate.period));
            }
        }
        best.map(|(_, period)| period)
    }

    #[test]
    fn a_planted_period_founds_five_and_every_read_agrees_with_the_integer_power_oracle() {
        let candidates = candidates();
        let mut law = FoundingLaw::open(4, 1, 1, candidates.clone()).unwrap();
        let stream = (0..512).map(|k| PLANTED[k % 5]).collect::<Vec<_>>();
        let mut first = None;
        for (k, &class) in stream.iter().enumerate() {
            law.receive(class).unwrap();
            if (k + 1) % 64 == 0 {
                let before = law.clone();
                let read = law.read().unwrap();
                assert_eq!(law, before, "read is immutable");
                let exact = oracle(&stream[..=k], &candidates, 4, 1, 1);
                assert_eq!(read.founded, exact, "read at {} cells", k + 1);
                if let Some(period) = read.founded {
                    assert_eq!(period, 5);
                    assert_eq!(law.key(period), k as u64 % period);
                    first.get_or_insert(k + 1);
                }
                let family = candidates
                    .iter()
                    .map(|candidate| {
                        Rat::new(BigInt::one(), BigInt::one() << candidate.cost as usize)
                    })
                    .sum::<Rat>();
                assert_eq!(read.family_bound, family);
            }
        }
        assert!(
            first.is_some(),
            "the planted period founds within the stream"
        );
    }

    /// The oracle's decisions where the node splits (`g = gcd(period, clock) > 1`) and the
    /// context reaches past the previous cell (`offset > 1`), founding and not.
    #[test]
    fn nodes_above_one_and_longer_offsets_agree_with_the_integer_power_oracle() {
        let costed = |periods: &[u64]| -> Vec<Candidate> {
            periods
                .iter()
                .map(|&period| Candidate {
                    period,
                    cost: COSTS[period as usize - 2],
                })
                .collect()
        };
        const SIX: [usize; 6] = [0, 1, 2, 0, 3, 1];
        const QUIET: [usize; 6] = [0, 0, 1, 2, 3, 3];
        for (pattern, clock, offset, periods, founds) in [
            (SIX, 2, 3, vec![4, 6, 8, 10, 12], true),
            (SIX, 3, 2, vec![6, 9, 12], true),
            (SIX, 4, 3, vec![6, 10, 12], true),
            (QUIET, 3, 2, vec![6, 9, 12], false),
        ] {
            let candidates = costed(&periods);
            let mut law = FoundingLaw::open(4, offset, clock, candidates.clone()).unwrap();
            let stream = (0..512).map(|k| pattern[k % 6]).collect::<Vec<_>>();
            let mut founded = None;
            for (k, &class) in stream.iter().enumerate() {
                law.receive(class).unwrap();
                if (k + 1) % 64 == 0 {
                    let read = law.read().unwrap();
                    for candidate in &read.candidates {
                        assert_eq!(candidate.node, gcd(candidate.period, clock));
                    }
                    let exact = oracle(&stream[..=k], &candidates, 4, offset, clock);
                    assert_eq!(
                        read.founded,
                        exact,
                        "clock {clock} offset {offset} at {}",
                        k + 1
                    );
                    founded = founded.or(read.founded);
                }
            }
            assert_eq!(founded.is_some(), founds, "clock {clock} offset {offset}");
            if let Some(period) = founded {
                assert!(
                    gcd(period, clock) > 1,
                    "the founding reads a node above one"
                );
            }
        }
    }

    #[test]
    fn a_deterministic_context_law_has_nothing_to_found() {
        let mut law = FoundingLaw::open(16, 1, 1, candidates()).unwrap();
        let mut y = 0;
        for _ in 0..4096 {
            law.receive(y).unwrap();
            y = (3 * y + 1) % 16;
        }
        let read = law.read().unwrap();
        assert_eq!(read.founded, None);
        assert!(
            read.candidates
                .iter()
                .all(|candidate| candidate.surplus.upper < Rat::zero())
        );
    }

    #[test]
    fn a_class_carried_phase_leaves_the_split_and_node_kt_codes_identical() {
        let mut law = FoundingLaw::open(4, 1, 1, vec![Candidate { period: 2, cost: 1 }]).unwrap();
        let mut counts = vec![vec![0u64; 4]; 4];
        let mut node_code = PassageCode::new();
        let stream = (0..512)
            .map(|k| (k % 2) * 2 + ((k / 2) % 2))
            .collect::<Vec<_>>();
        for (k, &y) in stream.iter().enumerate() {
            if k > 0 {
                let row = &mut counts[stream[k - 1]];
                node_code
                    .face(&Rat::new(
                        BigInt::from(2 * row[y] + 1),
                        BigInt::from(2 * row.iter().sum::<u64>() + 4),
                    ))
                    .unwrap();
                row[y] += 1;
            }
            law.receive(y).unwrap();
            assert_eq!(law.splits[0].code, node_code);
        }
        assert_eq!(
            law.splits[0].code.bits().unwrap(),
            node_code.bits().unwrap()
        );
        assert_eq!(law.read().unwrap().founded, None);
    }

    #[test]
    fn reopening_keeps_the_context_and_resets_all_counts_codes_and_phase() {
        let mut law = FoundingLaw::open(4, 1, 1, candidates()).unwrap();
        let mut at = 0;
        loop {
            law.receive(PLANTED[at % 5]).unwrap();
            at += 1;
            if at % 64 == 0 && law.read().unwrap().founded == Some(5) {
                break;
            }
            assert!(at < 512);
        }
        let context = law.context.clone();
        let next = candidates()
            .into_iter()
            .filter(|candidate| candidate.period % 5 != 0)
            .collect();
        law.reopen(5, next).unwrap();
        assert_eq!(law.context, context);
        assert_eq!(law.cells(), 0);
        assert_eq!(law.counted, 0);
        assert_eq!(law.key(7), 6);
        assert!(law.nodes.values().all(BTreeMap::is_empty));
        assert!(
            law.splits
                .iter()
                .all(|split| split.counts.is_empty() && split.code == PassageCode::new())
        );
        for k in 0..4096 {
            law.receive(PLANTED[(at + k) % 5]).unwrap();
            if (k + 1) % 64 == 0 {
                assert_eq!(law.read().unwrap().founded, None);
            }
        }
        assert_eq!(
            law.counted, 4096,
            "the preserved context counts the first new cell"
        );
    }

    #[test]
    fn declarations_and_atomic_refusals_are_typed() {
        for (alphabet, offset, clock, periods) in [
            (1, 1, 1, vec![2]),
            (4, 0, 1, vec![2]),
            (4, 1, 0, vec![2]),
            (4, 1, 1, vec![1]),
            (4, 1, 6, vec![3]),
            (4, 1, 1, vec![2, 2]),
        ] {
            let candidates = periods
                .into_iter()
                .map(|period| Candidate { period, cost: 1 })
                .collect();
            assert!(matches!(
                FoundingLaw::open(alphabet, offset, clock, candidates),
                Err(HnnError::Founding { .. })
            ));
        }
        // A vacuous family (a bound of one or more) and a cost no field describes are refused.
        for costs in [
            vec![0],
            vec![1, 1],
            vec![1, 2, 2],
            vec![DESCRIPTION_CEILING + 1],
        ] {
            let candidates = costs
                .into_iter()
                .zip(2..)
                .map(|(cost, period)| Candidate { period, cost })
                .collect();
            assert!(matches!(
                FoundingLaw::open(4, 1, 1, candidates),
                Err(HnnError::Founding { .. })
            ));
        }
        let ceiling = FoundingLaw::open(
            4,
            1,
            1,
            vec![
                Candidate { period: 2, cost: 1 },
                Candidate {
                    period: 3,
                    cost: DESCRIPTION_CEILING,
                },
            ],
        )
        .unwrap();
        assert_eq!(
            ceiling.read().unwrap().family_bound,
            Rat::new(BigInt::one(), BigInt::from(2))
                + Rat::new(BigInt::one(), BigInt::one() << DESCRIPTION_CEILING as usize)
        );
        let mut law = FoundingLaw::open(4, 1, 1, vec![Candidate { period: 2, cost: 1 }]).unwrap();
        assert_eq!(law.read().unwrap().cells, 0);
        assert_eq!(law.key(2), 1);
        law.receive(0).unwrap();
        assert_eq!(law.cells(), 1);
        assert_eq!(law.counted, 0, "the opening class is context only");
        let before = law.clone();
        assert!(matches!(law.receive(4), Err(HnnError::Founding { .. })));
        assert_eq!(law, before);
        assert!(law.reopen(0, vec![]).is_err());
        assert_eq!(law, before);
        for target in 0..4 {
            let mut overflow = before.clone();
            match target {
                0 => overflow.cells = u64::MAX,
                1 => overflow.counted = u64::MAX,
                2 => {
                    overflow.splits[0].counts.insert(
                        (1, 0),
                        Row {
                            total: u64::MAX,
                            classes: BTreeMap::from([(1, u64::MAX)]),
                        },
                    );
                }
                _ => {
                    overflow.nodes.get_mut(&1).unwrap().insert(
                        (0, 0),
                        Row {
                            total: u64::MAX,
                            classes: BTreeMap::from([(1, u64::MAX)]),
                        },
                    );
                }
            }
            let frozen = overflow.clone();
            assert!(matches!(
                overflow.receive(1),
                Err(HnnError::Founding { .. })
            ));
            assert_eq!(overflow, frozen);
        }
    }

    #[test]
    fn node_counts_are_shared_by_gcd_and_nonunit_offsets_keep_their_own_context() {
        let mut law = FoundingLaw::open(
            4,
            2,
            6,
            vec![
                Candidate { period: 4, cost: 9 },
                Candidate { period: 8, cost: 9 },
            ],
        )
        .unwrap();
        for y in [0, 1, 2, 3] {
            law.receive(y).unwrap();
        }
        assert_eq!(law.cells(), 4);
        assert_eq!(law.counted, 2);
        assert_eq!(law.nodes.len(), 1);
        assert_eq!(law.nodes[&2][&(0, 0)].classes[&2], 1);
        assert_eq!(law.nodes[&2][&(1, 1)].classes[&3], 1);
        let read = law.read().unwrap();
        assert!(read.candidates.iter().all(|candidate| candidate.node == 2));
        assert_eq!(
            read.family_bound,
            Rat::new(BigInt::one(), BigInt::from(256))
        );
        assert_eq!(
            weighted_log(0, 8, &mut BTreeMap::new()).unwrap(),
            ExactInterval::point(integer(0))
        );
    }
}

impl FoundingLaw {
    pub(crate) fn admit_parameters(
        &self,
        alphabet: usize,
        offset: usize,
        clock: u64,
        candidates: &[Candidate],
    ) -> Result<(), HnnError> {
        if self.alphabet != alphabet
            || self.offset != offset
            || self.cell_clock != clock
            || self.splits.iter().map(|s| s.candidate).collect::<Vec<_>>() != candidates
        {
            return Err(refusal("the saved founding law against its field"));
        }
        Ok(())
    }

    /// Exact retained carriers, kept as a quotient rather than a replay of received cells.
    pub(crate) fn write_saved(&self, text: &mut String) {
        use crate::hnn::state_text::line;
        line(
            text,
            "founding-law",
            [
                self.alphabet as u64,
                self.offset as u64,
                self.cell_clock,
                self.cells,
                self.counted,
                self.splits.len() as u64,
                self.nodes.len() as u64,
            ],
        );
        line(text, "founding-context", self.context.iter());
        for split in &self.splits {
            line(
                text,
                "founding-split",
                [split.candidate.period, split.candidate.cost, split.node],
            );
            let (top, bottom, exponent) = split.code.bounds();
            let mut words = Vec::new();
            for bound in top.into_iter().chain(bottom) {
                words.push(bound.mantissa.to_string());
                words.push(bound.exponent.to_string());
            }
            words.push(exponent.to_string());
            words.push(split.code.factors().to_string());
            line(text, "founding-code", words);
            write_counts(text, &split.counts);
        }
        for (&node, counts) in &self.nodes {
            line(text, "founding-node", [node]);
            write_counts(text, counts);
        }
    }

    pub(crate) fn read_saved<'a>(
        next: crate::hnn::state_text::Next<'_, 'a>,
    ) -> Result<Self, HnnError> {
        use crate::compression::landmark::context::ProductBound;
        use crate::hnn::state_text::{counted, keyed, value};
        let head: Vec<u64> = counted(
            next("the founding law")?,
            "founding-law",
            7,
            "the founding law",
        )?;
        let alphabet =
            usize::try_from(head[0]).map_err(|_| refusal("the saved alphabet's carrier"))?;
        let offset = usize::try_from(head[1]).map_err(|_| refusal("the saved offset's carrier"))?;
        let words = keyed(
            next("the founding context")?,
            "founding-context",
            "the founding context",
        )?;
        let context = words
            .iter()
            .map(|word| value(Some(word), "the founding context"))
            .collect::<Result<VecDeque<usize>, _>>()?;
        if context.len() > offset
            || context.iter().any(|&c| c >= alphabet)
            || head[4] > head[3]
            || head[3] - head[4] > head[1]
            || (head[4] != 0 && context.len() != offset)
            || (context.len() as u64) < head[3].min(head[1])
        {
            return Err(refusal("the saved founding context and population"));
        }
        let mut splits = Vec::new();
        for _ in 0..head[5] {
            let header: Vec<u64> = counted(
                next("a founding split")?,
                "founding-split",
                3,
                "a founding split",
            )?;
            let words = keyed(next("a founding code")?, "founding-code", "a founding code")?;
            if words.len() != 10 {
                return Err(refusal("the founding code's ten carriers"));
            }
            let mut bounds = [ProductBound::ONE; 4];
            for (i, bound) in bounds.iter_mut().enumerate() {
                bound.mantissa = value(words.get(2 * i), "a product mantissa")?;
                bound.exponent = value(words.get(2 * i + 1), "a product exponent")?;
            }
            let factors = value(words.get(9), "the code's factors")?;
            if factors != head[4] {
                return Err(refusal("the split code's counted population"));
            }
            let code = PassageCode::from_bounds(
                [bounds[0], bounds[1]],
                [bounds[2], bounds[3]],
                value(words.get(8), "the code's twos")?,
                factors,
            )?;
            let counts = read_counts(next, header[0], alphabet, head[4])?;
            splits.push(Split {
                candidate: Candidate {
                    period: header[0],
                    cost: header[1],
                },
                node: header[2],
                counts,
                code,
            });
        }
        let mut law = Self::open(
            alphabet,
            offset,
            head[2],
            splits.iter().map(|s| s.candidate).collect(),
        )?;
        if law.nodes.len() as u64 != head[6]
            || splits
                .iter()
                .zip(&law.splits)
                .any(|(a, b)| a.node != b.node)
        {
            return Err(refusal("the saved split's declared node"));
        }
        for (&node, counts) in &mut law.nodes {
            let header: Vec<u64> = counted(
                next("a founding node")?,
                "founding-node",
                1,
                "a founding node",
            )?;
            if header[0] != node {
                return Err(refusal("the saved founding nodes in order"));
            }
            *counts = read_counts(next, node, alphabet, head[4])?;
        }
        // The node counts are the splits' marginals, and each split's bounded code encloses the
        // KT product its counts fix. The product is exact in any order; only the carriers'
        // rounding depends on it, so a genuine code meets the canonical one. A saved code that
        // does not is refused, and none can move a founding past the enclosures' own width.
        for split in &splits {
            let mut marginal = Counts::new();
            for (&(phase, context), row) in &split.counts {
                let folded = marginal.entry((phase % split.node, context)).or_default();
                folded.total += row.total;
                for (&class, &n) in &row.classes {
                    *folded.classes.entry(class).or_default() += n;
                }
            }
            if law.nodes.get(&split.node) != Some(&marginal) {
                return Err(refusal("the saved node counts are their splits' marginals"));
            }
            let (saved, canonical) = (
                split.code.bits()?,
                kt_code(&split.counts, alphabet)?.bits()?,
            );
            if saved.lower > canonical.upper || canonical.lower > saved.upper {
                return Err(refusal(
                    "a saved split code encloses the KT product of its counts",
                ));
            }
        }
        law.context = context;
        law.cells = head[3];
        law.counted = head[4];
        law.splits = splits;
        Ok(law)
    }

    pub(crate) fn retained_bits(&self) -> u64 {
        let gamma = |n: u64| 2 * (num_bigint::BigUint::from(n) + 1u32).bits() - 1;
        let count_bits = |counts: &Counts| -> u64 {
            gamma(counts.len() as u64)
                + counts
                    .iter()
                    .map(|(&(phase, context), row)| {
                        gamma(phase)
                            + gamma(context as u64)
                            + gamma(row.total)
                            + gamma(row.classes.len() as u64)
                            + row
                                .classes
                                .iter()
                                .map(|(&class, &n)| gamma(class as u64) + gamma(n))
                                .sum::<u64>()
                    })
                    .sum::<u64>()
        };
        gamma(self.alphabet as u64)
            + gamma(self.offset as u64)
            + gamma(self.cell_clock)
            + gamma(self.cells)
            + gamma(self.counted)
            + gamma(self.splits.len() as u64)
            + gamma(self.nodes.len() as u64)
            + self.context.iter().map(|&c| gamma(c as u64)).sum::<u64>()
            + self
                .splits
                .iter()
                .map(|split| {
                    let (top, bottom, twos) = split.code.bounds();
                    gamma(split.candidate.period)
                        + gamma(split.candidate.cost)
                        + gamma(split.node)
                        + top
                            .into_iter()
                            .chain(bottom)
                            .map(|bound| {
                                2 * (128 - (bound.mantissa + 1).leading_zeros()) as u64 - 1
                                    + gamma(bound.exponent)
                            })
                            .sum::<u64>()
                        + gamma(twos)
                        + gamma(split.code.factors())
                        + count_bits(&split.counts)
                })
                .sum::<u64>()
            + self
                .nodes
                .iter()
                .map(|(&node, counts)| gamma(node) + count_bits(counts))
                .sum::<u64>()
    }
}

/// The KT code its counts fix, faced row by row and class by class. Within a row the faces'
/// numerators are `2j + 1` for each class's `j`-th arrival and the denominators `2i + |A|` for the
/// row's `i`-th, whatever the arrival order, so the exact product is the counts'.
fn kt_code(counts: &Counts, alphabet: usize) -> Result<PassageCode, HnnError> {
    let mut code = PassageCode::new();
    for row in counts.values() {
        let mut seen = 0u64;
        for &n in row.classes.values() {
            for j in 0..n {
                let face = Rat::new(
                    BigInt::from(j) * 2 + 1,
                    BigInt::from(seen) * 2 + BigInt::from(alphabet),
                );
                code = appended(code, &face)?;
                seen += 1;
            }
        }
    }
    Ok(code)
}

fn write_counts(text: &mut String, counts: &Counts) {
    use crate::hnn::state_text::line;
    line(text, "founding-counts", [counts.len()]);
    for (&(phase, context), row) in counts {
        let mut words = vec![
            phase.to_string(),
            context.to_string(),
            row.total.to_string(),
            row.classes.len().to_string(),
        ];
        for (&class, &n) in &row.classes {
            words.push(class.to_string());
            words.push(n.to_string());
        }
        line(text, "founding-row", words);
    }
}

fn read_counts<'a>(
    next: crate::hnn::state_text::Next<'_, 'a>,
    period: u64,
    alphabet: usize,
    population: u64,
) -> Result<Counts, HnnError> {
    use crate::hnn::state_text::{counted, keyed, value};
    let head: Vec<usize> = counted(
        next("the founding counts")?,
        "founding-counts",
        1,
        "the founding counts",
    )?;
    let mut counts = Counts::new();
    let mut total = 0u64;
    for _ in 0..head[0] {
        let words = keyed(next("a founding row")?, "founding-row", "a founding row")?;
        let phase: u64 = value(words.first(), "a founding phase")?;
        let context: usize = value(words.get(1), "a founding context")?;
        let n: u64 = value(words.get(2), "a founding row population")?;
        let classes: usize = value(words.get(3), "a founding row's class count")?;
        let extent = classes
            .checked_mul(2)
            .and_then(|pairs| pairs.checked_add(4));
        if phase >= period
            || context >= alphabet
            || classes > alphabet
            || extent != Some(words.len())
            || n == 0
        {
            return Err(refusal("a saved founding row's domain"));
        }
        let mut row = Row {
            total: n,
            classes: BTreeMap::new(),
        };
        let mut sum = 0u64;
        for pair in words[4..].chunks_exact(2) {
            let class: usize = value(pair.first(), "a founding class")?;
            let count: u64 = value(pair.get(1), "a founding count")?;
            if class >= alphabet || count == 0 || row.classes.insert(class, count).is_some() {
                return Err(refusal("a saved founding class count"));
            }
            sum = sum
                .checked_add(count)
                .ok_or_else(|| refusal("a saved founding row overflow"))?;
        }
        if sum != n || counts.insert((phase, context), row).is_some() {
            return Err(refusal("a saved founding row's sum or duplicate"));
        }
        total = total
            .checked_add(n)
            .ok_or_else(|| refusal("saved founding population overflow"))?;
    }
    if total != population {
        return Err(refusal("the saved founding counts' population"));
    }
    Ok(counts)
}

#[cfg(test)]
mod saving_tests {
    use super::*;
    #[test]
    fn r4b_founding_quotient_roundtrips_without_replaying_the_passage() {
        let mut law = FoundingLaw::open(
            4,
            1,
            1,
            vec![
                Candidate {
                    period: 5,
                    cost: 16,
                },
                Candidate {
                    period: 7,
                    cost: 20,
                },
            ],
        )
        .unwrap();
        for k in 0..512 {
            law.receive([0, 0, 1, 0, 2][k % 5]).unwrap();
        }
        let mut text = String::new();
        law.write_saved(&mut text);
        let mut lines = text.lines();
        let mut restored = FoundingLaw::read_saved(&mut |what| {
            lines.next().ok_or(HnnError::ContinuingState { what })
        })
        .unwrap();
        assert_eq!(restored, law);
        assert_eq!(restored.read(), law.read());
        for k in 0..128 {
            let class = [0, 0, 1, 0, 2][(512 + k) % 5];
            law.receive(class).unwrap();
            restored.receive(class).unwrap();
        }
        assert_eq!(restored, law);
        law.reopen(
            5,
            vec![Candidate {
                period: 7,
                cost: 20,
            }],
        )
        .unwrap();
        let mut text = String::new();
        law.write_saved(&mut text);
        let mut lines = text.lines();
        assert_eq!(
            FoundingLaw::read_saved(&mut |what| lines
                .next()
                .ok_or(HnnError::ContinuingState { what }))
            .unwrap(),
            law
        );
    }

    /// A saved state whose node counts are not its splits' marginals, or whose split code does
    /// not enclose its counts' KT product, is refused, typed.
    #[test]
    fn a_forged_founding_quotient_is_refused() {
        let mut law = FoundingLaw::open(
            4,
            1,
            1,
            vec![
                Candidate {
                    period: 5,
                    cost: 16,
                },
                Candidate {
                    period: 7,
                    cost: 20,
                },
            ],
        )
        .unwrap();
        for k in 0..512 {
            law.receive([0, 0, 1, 0, 2][k % 5]).unwrap();
        }
        let mut text = String::new();
        law.write_saved(&mut text);
        let read = |text: &str| {
            let mut lines = text.lines();
            FoundingLaw::read_saved(&mut |what| {
                lines.next().ok_or(HnnError::ContinuingState { what })
            })
        };
        assert_eq!(read(&text).unwrap(), law);
        let lines: Vec<&str> = text.lines().collect();
        // The two splits' genuine codes exchanged: each is well formed, neither is its own.
        let codes: Vec<usize> = (0..lines.len())
            .filter(|&i| lines[i].starts_with("founding-code "))
            .collect();
        assert_eq!(codes.len(), 2);
        let mut swapped = lines.clone();
        swapped.swap(codes[0], codes[1]);
        assert!(matches!(
            read(&swapped.join("\n")),
            Err(HnnError::Founding { .. })
        ));
        // One node count moved between two classes of a row: every sum still holds.
        let node = lines
            .iter()
            .position(|line| line.starts_with("founding-node "))
            .unwrap();
        let (row, mut words) = (node + 1..lines.len())
            .find_map(|i| {
                let words: Vec<u64> = lines[i]
                    .strip_prefix("founding-row ")?
                    .split(' ')
                    .map(|word| word.parse().unwrap())
                    .collect();
                (words[3] >= 2 && words[5] >= 2).then_some((i, words))
            })
            .unwrap();
        words[5] -= 1;
        words[7] += 1;
        let moved = format!(
            "founding-row {}",
            words
                .iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(" ")
        );
        let mut forged = lines.clone();
        forged[row] = &moved;
        assert!(matches!(
            read(&forged.join("\n")),
            Err(HnnError::Founding { .. })
        ));
    }
}
