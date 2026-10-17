//! A candidate ring pays its description out of the code its phase-resolved pair moment shortens.
//!
//! [proved-derived; formalization owed #62] For `g = gcd(period, cell_clock)`, the node's
//! maximum-likelihood code is `ML_g = sum(n log2 n - sum_y N_y log2 N_y)`. The candidate's KT
//! sequential law is `Q`; the surplus is `ML_g - bits(Q)`. Its conservative lower endpoint must
//! strictly exceed the description cost. Under any fixed node law `P`, `Q / P_ML <= Q / P`;
//! Ville's inequality and the family union bound give `sum 2^(-cost)` at arbitrary read times.
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
use crate::ratio::algebraic::{ExactInterval, log2_enclosure_at};

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
    /// cell clock, or duplicate periods. Nothing is allocated in proportion to a period.
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
        for candidate in candidates {
            if candidate.period < 2 || cell_clock.is_multiple_of(candidate.period) {
                return Err(refusal(
                    "a candidate period is at least two and does not divide the cell clock",
                ));
            }
            if !periods.insert(candidate.period) {
                return Err(refusal("candidate periods are distinct"));
            }
            let node = gcd(candidate.period, cell_clock);
            nodes.entry(node).or_insert_with(BTreeMap::new);
            splits.push(Split {
                candidate,
                node,
                counts: BTreeMap::new(),
                code: PassageCode::new(),
            });
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
    pub fn read(&self) -> Result<FoundingRead, HnnError> {
        let six_n = 6 * u128::from(self.counted.max(1));
        let precision = u128::BITS - (six_n - 1).leading_zeros() + 8;
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
        let mut family_bound = Rat::zero();
        let mut best: Option<(Rat, u64)> = None;
        let mut candidates = Vec::with_capacity(self.splits.len());
        for split in &self.splits {
            let node = &ml[&split.node];
            let bits = split.code.bits()?;
            let surplus = ExactInterval::new(&node.lower - bits.upper, &node.upper - bits.lower)?;
            let cost = split.candidate.cost;
            let shift = usize::try_from(cost)
                .map_err(|_| refusal("the description cost exceeds the exact carrier's extent"))?;
            family_bound += Rat::new(BigInt::one(), BigInt::one() << shift);
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
            family_bound,
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
    // Thus log2(Q/P_ML)>cost is checked as Q/P_ML>2^cost, without logarithm enclosures.
    fn oracle(stream: &[usize], candidates: &[Candidate], clock: u64) -> Option<u64> {
        let mut best: Option<(Rat, u64)> = None;
        for candidate in candidates {
            let period = candidate.period as usize;
            let node = gcd(candidate.period, clock) as usize;
            let mut split = vec![vec![vec![0u64; 4]; 4]; period];
            let mut counts = vec![vec![vec![0u64; 4]; 4]; node];
            let mut probability = Rat::one();
            for k in 1..stream.len() {
                let (a, y) = (stream[k - 1], stream[k]);
                let row = &mut split[k % period][a];
                let total = row.iter().sum::<u64>();
                probability *= Rat::new(BigInt::from(2 * row[y] + 1), BigInt::from(2 * total + 4));
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
                let exact = oracle(&stream[..=k], &candidates, 1);
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
        println!(
            "REQ049 test1 first_founding_cells={} period=5",
            first.unwrap()
        );
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
        let mut law = FoundingLaw::open(4, 1, 1, vec![Candidate { period: 2, cost: 0 }]).unwrap();
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
