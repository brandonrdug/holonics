//! The quotient every receiver factors through, and the population a one-shot reading collapses.
//!
//! ## What this implements
//!
//! **H.0016, receiver-exact compression**, already a machine-checked definition in this project's
//! registry (`papers/source/holonics/foundations.typ`) and until now with no implementation:
//!
//! ```text
//!   a compression is a quotient q : X -> Q such that every receiver factors, rho = rho_bar . q
//!   x ~_R y  <->  for every rho in R,  rho(x) = rho(y)
//! ```
//!
//! Taken alone that definition is **vacuous as a check**: the quotient by `~_R` factors every
//! receiver by construction, so an organ that computed only this could never fail. `CLAUDE.md` §8
//! calls that a receipt that could not have come out otherwise.
//!
//! The content is in the clause `canon/01_CAUSAL_CALCULUS.md` adds: a quotient is exact only when
//! *"stateful successor conduct remains equivalent for every admitted input history"* — **"equal
//! one-shot output is inadequate."** That clause CAN fail, and its failure is the returned artifact.
//!
//! ## Why this is compression in Brandon's sense and not in the file-size sense
//!
//! His information hypothesis, from the laboratory's own documents and named there as his rather
//! than as a borrowed analogy: *"Compression is gauge-fixing the flat directions and keeping the
//! curvature"* — information is the gauge-invariant difference between entities; the chart you read
//! a value in is arbitrary. Refinement here does exactly that. It keeps precisely the distinctions
//! some later conduct can see and fixes everything else as flat, and the definition's own boundary
//! clause insists the result *"is not synonymous with fewer bytes, deduplication, averaging, or a
//! scalar quotient."*
//!
//! ## The standard name, and why it matters that there is one
//!
//! Receiver-exact compression plus the successor-conduct clause **is the Nerode congruence**, and
//! refining a one-shot partition until it is stable under successors is **Moore's partition
//! refinement**. That is worth stating rather than re-deriving: it means the construction is exact,
//! terminates, and — the part this module leans on — the round at which two items first separate is
//! the length of the *shortest input word that distinguishes them*.
//!
//! So the compression's exact loss is not a scalar and not an estimate. It is a **counted,
//! exhibitable population of pairs, each carrying the shortest context that separates it and the
//! receiver that finally sees the difference.** That is the shape `CLAUDE.md` §11 asks for when it
//! asks for a certified remainder, and `THE_RECOVERED_LAW.md` states it directly: compression's
//! exact loss is *"the population of collapsed pairs some later continuation can distinguish — not
//! initially a scalar."*
//!
//! ## Domain-free on purpose
//!
//! Brandon, 2026-07-29: *"the communication medium is arbitrary and it is the causal calculus that
//! informs common ecological invariants intersecting between domains."* Nothing below knows whether
//! an item is a language state, a circuit node, a phase germ, or a numeral. A caller supplies items,
//! receivers, and a successor relation.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde::{Deserialize, Serialize};

/// An item of the source population under compression.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ItemId(pub u64);

/// One declared future receiver.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverId(pub u64);

/// One admitted input that advances conduct.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct InputId(pub u64);

/// What a receiver returns from an item, exactly. An opaque exact token — never a magnitude, so
/// nothing here can be ordered, averaged, or thresholded.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Observation(pub u64);

/// The system being compressed: a population, a declared receiver family, and successor conduct.
///
/// `successor` returning `None` is a declared terminus, not an error — an item where that input
/// admits no continuation. Two items are distinguished by an input when one continues and the other
/// does not, which is why the absence is part of the conduct rather than a gap in it.
pub trait ObservedSystem {
    fn items(&self) -> Vec<ItemId>;
    fn receivers(&self) -> Vec<ReceiverId>;
    fn inputs(&self) -> Vec<InputId>;
    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation;
    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId>;
}

/// A partition of the population into blocks, canonically ordered so two runs compare directly.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Partition {
    pub blocks: Vec<BTreeSet<ItemId>>,
}

impl Partition {
    pub fn from_keys<K: Ord>(keyed: impl IntoIterator<Item = (ItemId, K)>) -> Self {
        let mut grouped: BTreeMap<K, BTreeSet<ItemId>> = BTreeMap::new();
        for (item, key) in keyed {
            grouped.entry(key).or_default().insert(item);
        }
        let mut blocks: Vec<BTreeSet<ItemId>> = grouped.into_values().collect();
        blocks.sort();
        Self { blocks }
    }

    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    pub fn block_of(&self, item: ItemId) -> Option<usize> {
        self.blocks.iter().position(|block| block.contains(&item))
    }

    /// Every pair this partition holds together.
    pub fn identified_pairs(&self) -> BTreeSet<(ItemId, ItemId)> {
        let mut pairs = BTreeSet::new();
        for block in &self.blocks {
            let members: Vec<ItemId> = block.iter().copied().collect();
            for (index, left) in members.iter().enumerate() {
                for right in &members[index + 1..] {
                    pairs.insert((*left, *right));
                }
            }
        }
        pairs
    }
}

/// One pair the one-shot reading merged and later conduct separates.
///
/// This is the artifact, not a count. `CLAUDE.md` §9: a returned obstruction must itself be
/// returned and inspected.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CollapsedPair {
    pub left: ItemId,
    pub right: ItemId,
    /// The shortest input word after which some receiver sees a difference. Empty is impossible
    /// here by construction — an empty word is the one-shot reading, which held these together.
    pub distinguishing_word: Vec<InputId>,
    /// The receiver that finally sees it, and what the two returned.
    pub witness: Option<(ReceiverId, Observation, Observation)>,
    /// True when the word separates them because one continues and the other does not, rather than
    /// because a receiver returned different observations. A terminus is a distinction.
    pub separated_by_terminus: bool,
}

/// What a compression returns.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverExactCompression {
    pub schema: String,
    /// `x ~_R y` — H.0016 exactly, one-shot.
    pub one_shot: Partition,
    /// The refinement under successor conduct. The Nerode congruence of the declared family.
    pub conduct: Partition,
    /// Refinement rounds to stability. Also the longest shortest-distinguishing-word length.
    pub rounds: usize,
    /// The exact loss: pairs one-shot identified that conduct separates, each with its witness.
    pub collapsed: Vec<CollapsedPair>,
}

impl ReceiverExactCompression {
    /// The one-shot quotient is receiver-exact — nothing later conduct can see was collapsed.
    pub fn is_exact(&self) -> bool {
        self.collapsed.is_empty()
    }

    /// How much the one-shot reading over-collapsed, as a block count rather than a ratio.
    pub fn refinement(&self) -> usize {
        self.conduct.len().saturating_sub(self.one_shot.len())
    }
}

/// Compute the one-shot receiver equivalence: H.0016 with no successor clause.
pub fn one_shot_partition(system: &dyn ObservedSystem) -> Partition {
    let receivers = system.receivers();
    Partition::from_keys(system.items().into_iter().map(|item| {
        let signature: Vec<Observation> = receivers
            .iter()
            .map(|receiver| system.observation(item, *receiver))
            .collect();
        (item, signature)
    }))
}

/// Refine the one-shot partition until successor conduct is stable — Moore's algorithm.
///
/// Two items survive together only if, for every admitted input, their successors lie in the same
/// block *and* they agree on whether a successor exists at all.
pub fn compress(system: &dyn ObservedSystem) -> ReceiverExactCompression {
    let one_shot = one_shot_partition(system);
    let items = system.items();
    let inputs = system.inputs();

    let mut current = one_shot.clone();
    let mut rounds = 0usize;
    loop {
        let index: BTreeMap<ItemId, usize> = items
            .iter()
            .filter_map(|item| current.block_of(*item).map(|block| (*item, block)))
            .collect();
        let refined = Partition::from_keys(items.iter().map(|item| {
            let signature: Vec<Option<usize>> = inputs
                .iter()
                .map(|input| {
                    system
                        .successor(*item, *input)
                        .and_then(|next| index.get(&next).copied())
                })
                .collect();
            (*item, (index.get(item).copied(), signature))
        }));
        if refined == current {
            break;
        }
        current = refined;
        rounds += 1;
    }

    let collapsed = exhibit_collapsed(system, &one_shot, &current);
    ReceiverExactCompression {
        schema: "holonic-engine.receiver-exact-compression.v1".to_owned(),
        one_shot,
        conduct: current,
        rounds,
        collapsed,
    }
}

/// For each pair the one-shot reading merged and conduct separates, find the **shortest** input
/// word that distinguishes them, and the receiver that sees it.
///
/// Breadth-first over input words, so the first word found is shortest. This is what makes the loss
/// exhibitable rather than merely counted.
fn exhibit_collapsed(
    system: &dyn ObservedSystem,
    one_shot: &Partition,
    conduct: &Partition,
) -> Vec<CollapsedPair> {
    let receivers = system.receivers();
    let inputs = system.inputs();
    let mut collapsed = Vec::new();

    for (left, right) in one_shot.identified_pairs() {
        if conduct.block_of(left) == conduct.block_of(right) {
            continue;
        }
        let mut seen = BTreeSet::from([(Some(left), Some(right))]);
        let mut frontier = VecDeque::from([(Some(left), Some(right), Vec::<InputId>::new())]);
        while let Some((here, there, word)) = frontier.pop_front() {
            // A terminus reached by one and not the other is itself a distinction.
            if here.is_some() != there.is_some() {
                collapsed.push(CollapsedPair {
                    left,
                    right,
                    distinguishing_word: word,
                    witness: None,
                    separated_by_terminus: true,
                });
                break;
            }
            let (Some(here_item), Some(there_item)) = (here, there) else {
                break;
            };
            if !word.is_empty() {
                if let Some(receiver) = receivers.iter().copied().find(|receiver| {
                    system.observation(here_item, *receiver)
                        != system.observation(there_item, *receiver)
                }) {
                    collapsed.push(CollapsedPair {
                        left,
                        right,
                        distinguishing_word: word,
                        witness: Some((
                            receiver,
                            system.observation(here_item, receiver),
                            system.observation(there_item, receiver),
                        )),
                        separated_by_terminus: false,
                    });
                    break;
                }
            }
            for input in &inputs {
                let next = (
                    system.successor(here_item, *input),
                    system.successor(there_item, *input),
                );
                if seen.insert(next) {
                    let mut extended = word.clone();
                    extended.push(*input);
                    frontier.push_back((next.0, next.1, extended));
                }
            }
        }
    }
    collapsed
}

/// A receiver family, ablated. Removing a receiver may only **coarsen** the compression — never
/// refine it — because a quotient identifies only pairs indistinguishable by every factored
/// receiver. H.0016's own transformations clause says so: *"enlarging R can refine or invalidate
/// the compression."* This is the monotonicity that makes a receiver's contribution measurable.
pub struct AblatedSystem<'a> {
    pub inner: &'a dyn ObservedSystem,
    pub without: ReceiverId,
}

impl ObservedSystem for AblatedSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.inner.items()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        self.inner
            .receivers()
            .into_iter()
            .filter(|receiver| *receiver != self.without)
            .collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        self.inner.inputs()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        self.inner.observation(item, receiver)
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.inner.successor(item, input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A cyclic counter on `n` items, advanced by one input, read by receivers `x mod k`.
    ///
    /// The answer is a theorem rather than an inspection, which is the point. Write `L = lcm(K)`.
    /// The one-shot reading identifies `x ~ y` exactly when `x ≡ y (mod L)`, and advancing preserves
    /// that congruence iff `L` divides `n` — otherwise the wrap at `n-1 -> 0` breaks it. So:
    ///
    /// ```text
    ///   L >= n  ->  the residues are already distinct on 0..n-1; the one-shot partition is
    ///               DISCRETE and exact with nothing collapsed to lose
    ///   L | n   ->  the congruence survives the wrap; exact, collapsed population EMPTY
    ///   else    ->  one-shot over-collapses, and the collapsed pairs are exhibitable
    /// ```
    ///
    /// **The `L >= n` clause is not a special case bolted on — it was missing from the first
    /// statement of this law and the sweep failed at `n=2, K={3}`.** The law as first written said
    /// exact iff `L | n`, which is false whenever the receiver family already separates everything;
    /// there is then no identified pair for conduct to refine. The test caught the derivation, not
    /// the code, which is the outcome a sweep over a parameterized family is for.
    ///
    /// All three branches are needed. Without the last the law returns zero and proves nothing about
    /// itself (`CLAUDE.md` §8); without the first two it could be refining indiscriminately.
    struct CyclicCounter {
        n: u64,
        moduli: Vec<u64>,
    }

    impl ObservedSystem for CyclicCounter {
        fn items(&self) -> Vec<ItemId> {
            (0..self.n).map(ItemId).collect()
        }
        fn receivers(&self) -> Vec<ReceiverId> {
            (0..self.moduli.len() as u64).map(ReceiverId).collect()
        }
        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0)]
        }
        fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
            Observation(item.0 % self.moduli[receiver.0 as usize])
        }
        fn successor(&self, item: ItemId, _input: InputId) -> Option<ItemId> {
            Some(ItemId((item.0 + 1) % self.n))
        }
    }

    fn lcm(values: &[u64]) -> u64 {
        fn gcd(a: u64, b: u64) -> u64 {
            if b == 0 { a } else { gcd(b, a % b) }
        }
        values.iter().fold(1, |acc, value| acc / gcd(acc, *value) * value)
    }

    #[test]
    fn the_quotient_is_exact_exactly_when_the_modulus_divides_the_cycle() {
        for n in 2..=24u64 {
            for moduli in [vec![2u64], vec![3], vec![2, 3], vec![4, 6]] {
                let system = CyclicCounter { n, moduli: moduli.clone() };
                let compression = compress(&system);
                let modulus = lcm(&moduli);
                let expected = modulus >= n || n % modulus == 0;
                assert_eq!(
                    compression.is_exact(),
                    expected,
                    "n={n} moduli={moduli:?}: lcm={modulus} expected={expected} but exact={} \
                     (one_shot {} blocks, conduct {} blocks)",
                    compression.is_exact(),
                    compression.one_shot.len(),
                    compression.conduct.len(),
                );
                if modulus >= n {
                    assert_eq!(
                        compression.one_shot.len(),
                        n as usize,
                        "n={n} moduli={moduli:?}: the one-shot partition must already be discrete"
                    );
                }
            }
        }
    }

    #[test]
    fn when_the_modulus_divides_nothing_is_collapsed_and_the_partition_is_the_residues() {
        let system = CyclicCounter { n: 12, moduli: vec![2, 3] };
        let compression = compress(&system);
        assert!(compression.is_exact());
        assert_eq!(compression.rounds, 0, "a stable partition needs no refinement");
        assert_eq!(
            compression.one_shot.len(),
            6,
            "lcm(2,3)=6 residues, and 6 divides 12"
        );
        assert_eq!(compression.conduct.len(), 6);
    }

    /// The case the module exists for. The one-shot reading says two items are the same; conduct
    /// says they are not; and the return names the shortest word that shows it.
    #[test]
    fn an_over_collapsed_pair_returns_the_shortest_word_that_separates_it() {
        let system = CyclicCounter { n: 3, moduli: vec![2] };
        let compression = compress(&system);

        assert_eq!(compression.one_shot.len(), 2, "even {{0,2}} and odd {{1}}");
        assert_eq!(compression.conduct.len(), 3, "the wrap separates 0 from 2");
        assert!(!compression.is_exact());
        assert_eq!(compression.refinement(), 1);

        assert_eq!(compression.collapsed.len(), 1);
        let pair = &compression.collapsed[0];
        assert_eq!((pair.left, pair.right), (ItemId(0), ItemId(2)));
        assert_eq!(
            pair.distinguishing_word.len(),
            1,
            "one step: 0 -> 1 is odd, 2 -> 0 is even"
        );
        let (_, left_seen, right_seen) = pair.witness.expect("a receiver sees the difference");
        assert_ne!(left_seen, right_seen);
    }

    #[test]
    fn the_shortest_word_length_grows_with_the_depth_of_the_distinction() {
        // n = 5 read only mod 2: {0,2,4} look alike, {1,3} look alike, and separating them takes
        // more than one step because the wrap is further away for some pairs than for others.
        let system = CyclicCounter { n: 5, moduli: vec![2] };
        let compression = compress(&system);
        assert!(!compression.is_exact());
        assert_eq!(compression.conduct.len(), 5, "every item becomes distinguishable");
        let longest = compression
            .collapsed
            .iter()
            .map(|pair| pair.distinguishing_word.len())
            .max()
            .expect("collapsed pairs exist");
        assert!(longest >= 2, "some pair needs more than one step, got {longest}");
        assert!(
            compression.rounds >= longest,
            "refinement rounds bound the longest shortest word: rounds={} longest={longest}",
            compression.rounds
        );
    }

    /// Two routes to the same distinction, one short and one long, so that "shortest" is a claim
    /// the material can actually refute.
    ///
    /// Items `0` and `1` read alike. Input `A` separates them after **two** steps; input `B`
    /// separates them after **four**, down a longer chain that is explored first by a depth-first
    /// frontier. A single-input system cannot test this at all — there is one chain and every
    /// search order walks it identically — and the first version of this module tested exactly
    /// that, so replacing the breadth-first frontier with a depth-first one changed nothing and
    /// passed. **Fourth instance in one day of a check whose material could not vary the property
    /// under test.**
    struct TwoRoutes;
    impl ObservedSystem for TwoRoutes {
        fn items(&self) -> Vec<ItemId> {
            (0..14).map(ItemId).collect()
        }
        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }
        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0), InputId(1)] // A then B, so a depth-first frontier takes B first
        }
        fn observation(&self, item: ItemId, _receiver: ReceiverId) -> Observation {
            match item.0 {
                6 | 12 => Observation(1),
                7 | 13 => Observation(2),
                _ => Observation(0),
            }
        }
        fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
            let short = input == InputId(0);
            Some(ItemId(match (item.0, short) {
                (0, true) => 2,
                (1, true) => 3,
                (2, true) => 6,
                (3, true) => 7,
                (0, false) => 4,
                (1, false) => 5,
                (4, false) => 8,
                (5, false) => 9,
                (8, false) => 10,
                (9, false) => 11,
                (10, false) => 12,
                (11, false) => 13,
                (other, _) => other, // every other pair rests where it is
            }))
        }
    }

    #[test]
    fn the_distinguishing_word_returned_is_the_shortest_one_and_not_merely_a_working_one() {
        let compression = compress(&TwoRoutes);
        let pair = compression
            .collapsed
            .iter()
            .find(|pair| (pair.left, pair.right) == (ItemId(0), ItemId(1)))
            .expect("0 and 1 read alike and conduct separates them");
        assert_eq!(
            pair.distinguishing_word,
            vec![InputId(0), InputId(0)],
            "the two-step route through A is shortest; the four-step route through B also works \
             and must not be what is returned"
        );
    }

    /// A terminus is a distinction. Two items that read alike but where one continues and the
    /// other stops are not the same item, and the return says so without inventing an observation.
    struct Terminating;
    impl ObservedSystem for Terminating {
        fn items(&self) -> Vec<ItemId> {
            (0..3).map(ItemId).collect()
        }
        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }
        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0)]
        }
        fn observation(&self, _item: ItemId, _receiver: ReceiverId) -> Observation {
            Observation(0)
        }
        fn successor(&self, item: ItemId, _input: InputId) -> Option<ItemId> {
            match item.0 {
                0 => Some(ItemId(1)),
                1 => Some(ItemId(1)),
                _ => None,
            }
        }
    }

    #[test]
    fn a_terminus_separates_items_that_every_receiver_reads_alike() {
        let compression = compress(&Terminating);
        assert_eq!(
            compression.one_shot.len(),
            1,
            "every receiver returns the same observation for all three"
        );
        assert!(!compression.is_exact());
        assert!(
            compression
                .collapsed
                .iter()
                .any(|pair| pair.separated_by_terminus),
            "the distinction must be reported as a terminus, not as a fabricated observation"
        );
        assert!(
            compression
                .collapsed
                .iter()
                .filter(|pair| pair.separated_by_terminus)
                .all(|pair| pair.witness.is_none()),
            "a terminus separation names no witnessing receiver because none saw a difference"
        );
    }

    /// Removing a receiver may only coarsen. H.0016's transformations clause: *"enlarging R can
    /// refine or invalidate the compression."* If ablation ever refined, the family would not be
    /// acting as a factorization and the whole construction would be wrong.
    #[test]
    fn ablating_a_receiver_only_coarsens_and_never_refines() {
        for n in 2..=18u64 {
            let system = CyclicCounter { n, moduli: vec![2, 3, 5] };
            let full = compress(&system);
            for receiver in system.receivers() {
                let ablated = AblatedSystem { inner: &system, without: receiver };
                let reduced = compress(&ablated);
                assert!(
                    reduced.conduct.len() <= full.conduct.len(),
                    "n={n}: ablating {receiver:?} refined {} -> {}",
                    full.conduct.len(),
                    reduced.conduct.len()
                );
                // Every pair the FULL family still identifies must also be identified by the
                // reduced one: fewer receivers can only merge more. The reverse does not hold.
                let reduced_pairs = reduced.conduct.identified_pairs();
                for pair in full.conduct.identified_pairs() {
                    assert!(
                        reduced_pairs.contains(&pair),
                        "n={n}: ablating {receiver:?} SPLIT the pair {pair:?}, which fewer                          receivers can never do"
                    );
                }
            }
        }
    }

    /// The ablation must be capable of actually changing something, or the control above is a law
    /// that returns zero.
    #[test]
    fn ablation_does_change_the_compression_somewhere() {
        let system = CyclicCounter { n: 12, moduli: vec![2, 3] };
        let full = compress(&system);
        let ablated = AblatedSystem { inner: &system, without: ReceiverId(1) };
        let reduced = compress(&ablated);
        assert_eq!(full.conduct.len(), 6);
        assert_eq!(reduced.conduct.len(), 2, "dropping mod 3 leaves only parity");
        assert!(reduced.conduct.len() < full.conduct.len());
    }
}
