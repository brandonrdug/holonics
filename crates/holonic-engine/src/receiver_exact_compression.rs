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

use crate::cuda_refine::{CudaRefineError, CudaRefineExecutor};

/// An item of the source population under compression.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ItemId(pub u64);

/// One declared future receiver.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverId(pub u64);

/// One admitted input that advances conduct.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct InputId(pub u64);

/// What a receiver returns from an item, exactly. An opaque exact token — never a magnitude.
///
/// **CORRECTED 2026-08-18.** This read *"so nothing here can be ordered, averaged, or thresholded"*
/// while the next line derives `Ord` and the field is `pub u64`, which the device path reads as a
/// raw key. The derive is **required**: `Partition::from_keys` groups by an observation signature
/// and needs a total order to do it, and `compress_on_device` needs a key. What is true, and is what
/// the sentence meant, is that **no law in this module reads an ordering between two observations as
/// a magnitude** — the order is a canonical arrangement, never a comparison of what two receivers
/// returned. A caller that subtracts, averages or thresholds these values has left the calculus.
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

    /// **The sparse face of the successor relation, optional and semantics-preserving.**
    ///
    /// A caller that already holds the transport as a sparse population may name, for one input,
    /// exactly the items that admit a continuation on it and where each continues. Returning
    /// `Some(pairs)` is an assertion the caller owes and the refinement relies on:
    ///
    /// ```text
    ///   for every (item, next) in pairs      successor(item, input) == Some(next)
    ///   for every item NOT named in pairs    successor(item, input) == None
    /// ```
    ///
    /// `None` — the default — means *ask [`ObservedSystem::successor`] item by item*, which is the
    /// dense reading and the only reading before 2026-08-20. Nothing about the returned partition
    /// changes: this face moves a round's cost from `|items| x |inputs|` to `|transitions|`, which
    /// is the difference between a whole atlas being readable and not.
    fn admitted(&self, _input: InputId) -> Option<Vec<(ItemId, ItemId)>> {
        None
    }
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

    /// **The same lookup, built once instead of scanned once per question.**
    ///
    /// [`Partition::block_of`] walks the block vector and asks each block whether it holds the item,
    /// so resolving every item costs `|items| x |blocks|` set lookups. Deed P0 measured that as one
    /// of the two things holding the whole-atlas reading out of reach. This builds the inverse map
    /// in one pass over the blocks and answers in `log |items|`; the answers are identical by
    /// construction, which the tests assert rather than assume.
    pub fn index(&self) -> BlockIndex {
        let mut of = BTreeMap::new();
        for (at, block) in self.blocks.iter().enumerate() {
            for item in block {
                of.insert(*item, at);
            }
        }
        BlockIndex { of }
    }

    /// Every item this partition holds, in ascending order — the canonical traversal order the
    /// collapsed population is exhibited in.
    pub fn items_in_order(&self) -> Vec<ItemId> {
        let mut items: Vec<ItemId> = self.blocks.iter().flatten().copied().collect();
        items.sort_unstable();
        items
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

/// The item-to-block inverse of a [`Partition`], built once.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BlockIndex {
    of: BTreeMap<ItemId, usize>,
}

impl BlockIndex {
    pub fn block_of(&self, item: ItemId) -> Option<usize> {
        self.of.get(&item).copied()
    }

    pub fn len(&self) -> usize {
        self.of.len()
    }

    pub fn is_empty(&self) -> bool {
        self.of.is_empty()
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
    /// **The memory order this quotient needs, read off the collapsed population.**
    ///
    /// A one-shot reading merges two items; conduct separates them, and the
    /// shortest word that does it is how far ahead the reading had to look. So
    /// the longest such word over the whole collapsed population is the depth at
    /// which every distinction this receiver family can make has been made.
    ///
    /// **That is a memory order, and it is the Markov order of the pair
    /// `(material, receiver family)` rather than of the material.** A process is
    /// not Markov or non-Markov by itself: it is Markov *relative to a declared
    /// state map*, and the state map here is the one-shot partition. The
    /// conduct partition is the coarsest map for which the future is determined
    /// by the block — which is the causal-state construction — and this figure
    /// says how much history that map had to absorb.
    ///
    /// `None` when nothing collapsed: the one-shot reading was already exact, so
    /// no history was needed at all and the reading is memoryless for this
    /// family. **That is a genuine zero and not a missing measurement**, which is
    /// why it is `None` rather than `0`.
    ///
    /// The figure is a **face**. The population it summarises —
    /// [`ReceiverExactCompression::collapsed`], every pair carrying its own word
    /// and the receiver that saw the difference — is the object, and a caller
    /// that reports this number without it has reported the shadow.
    pub fn memory_order(&self) -> Option<usize> {
        self.collapsed
            .iter()
            .map(|pair| pair.distinguishing_word.len())
            .max()
    }

    /// Whether every distinction this family makes is reachable within `order`
    /// symbols of history.
    ///
    /// The exact statement of *"is this Markov at order k"* for the declared
    /// receiver family, and it is decided by the population rather than assumed.
    pub fn is_markov_at(&self, order: usize) -> bool {
        self.memory_order().is_none_or(|needed| needed <= order)
    }

    /// The collapsed pairs that need more than `order` symbols to separate —
    /// **the non-Markovianity at that order, by name.**
    ///
    /// Exhibited rather than counted, because a pair that outruns the order is a
    /// statement about which two histories the state map could not tell apart,
    /// and that is the content.
    pub fn beyond_order(&self, order: usize) -> Vec<&CollapsedPair> {
        self.collapsed
            .iter()
            .filter(|pair| pair.distinguishing_word.len() > order)
            .collect()
    }

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

/// The refinement alone: the two partitions and the rounds, with no collapsed population exhibited.
///
/// Separated out 2026-08-20 because the two halves have wildly different costs and a caller may
/// genuinely want only the first. The refinement is `|transitions|` per round through the sparse
/// face; exhibiting the collapsed population is a breadth-first search **per pair**, and a
/// population of pairs is quadratic in a block. Reporting the partition reading and stating the
/// exhibition's aperture is a measurement; forcing the exhibition is not.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PartitionReading {
    /// `x ~_R y` — H.0016 exactly, one-shot.
    pub one_shot: Partition,
    /// The Nerode congruence of the declared family.
    pub conduct: Partition,
    /// Refinement rounds to stability.
    pub rounds: usize,
}

/// One synchronous Moore round, as a **sequence of exact intersections rather than one dense key**.
///
/// A round's key is the tuple `(current block, successor block per input)`, and grouping by a tuple
/// **is** the common refinement of grouping by each coordinate in turn. So the round can be taken
/// one input at a time, holding one label per item, instead of materialising the whole
/// `|items| x |inputs|` signature matrix — which at the whole atlas is 321,473,730 entries and
/// 2,571,789,840 octets in one allocation, the figure Deed P0 measured as the aperture.
///
/// A label is refreshed only where the successor **resolves to a block**. An input on which an item
/// terminates, or on which it continues to something outside the declared item population, leaves
/// the label where it was — which is exactly the dense reading's `None`, and is why an unclosed
/// scope behaves identically here.
fn refine_round(
    system: &dyn ObservedSystem,
    items: &[ItemId],
    inputs: &[InputId],
    current: &Partition,
    index: &BlockIndex,
) -> Partition {
    let mut labels: BTreeMap<ItemId, u64> = items
        .iter()
        .filter_map(|item| index.block_of(*item).map(|block| (*item, block as u64 + 1)))
        .collect();
    let mut next_label = current.len() as u64 + 1;
    let mut moved: Vec<(ItemId, u64)> = Vec::new();
    let mut fresh: BTreeMap<(u64, usize), u64> = BTreeMap::new();
    for input in inputs {
        fresh.clear();
        moved.clear();
        match system.admitted(*input) {
            Some(named) => {
                for (item, next) in named {
                    let (Some(block), Some(old)) =
                        (index.block_of(next), labels.get(&item).copied())
                    else {
                        continue;
                    };
                    let label = *fresh.entry((old, block)).or_insert_with(|| {
                        next_label += 1;
                        next_label - 1
                    });
                    moved.push((item, label));
                }
            }
            None => {
                for item in items {
                    let (Some(block), Some(old)) = (
                        system
                            .successor(*item, *input)
                            .and_then(|next| index.block_of(next)),
                        labels.get(item).copied(),
                    ) else {
                        continue;
                    };
                    let label = *fresh.entry((old, block)).or_insert_with(|| {
                        next_label += 1;
                        next_label - 1
                    });
                    moved.push((*item, label));
                }
            }
        }
        for (item, label) in moved.drain(..) {
            labels.insert(item, label);
        }
    }
    Partition::from_keys(labels)
}

/// Refine the one-shot partition until successor conduct is stable — Moore's algorithm.
///
/// Two items survive together only if, for every admitted input, their successors lie in the same
/// block *and* they agree on whether a successor exists at all.
pub fn refine(system: &dyn ObservedSystem) -> PartitionReading {
    let one_shot = one_shot_partition(system);
    let items = system.items();
    let inputs = system.inputs();

    let mut current = one_shot.clone();
    let mut rounds = 0usize;
    loop {
        let index = current.index();
        let refined = refine_round(system, &items, &inputs, &current, &index);
        if refined == current {
            break;
        }
        current = refined;
        rounds += 1;
    }
    PartitionReading {
        one_shot,
        conduct: current,
        rounds,
    }
}

/// The refinement **and** the complete collapsed population with its shortest separators.
pub fn compress(system: &dyn ObservedSystem) -> ReceiverExactCompression {
    let reading = refine(system);
    let collapsed = exhibit_collapsed(system, &reading.one_shot, &reading.conduct);
    ReceiverExactCompression {
        schema: "holonic-engine.receiver-exact-compression.v1".to_owned(),
        one_shot: reading.one_shot,
        conduct: reading.conduct,
        rounds: reading.rounds,
        collapsed,
    }
}

/// Enact the same stable receiver/history quotient through the resident card's material-free
/// `(current class, exact key)` law.
///
/// Receiver observations and successor addresses are the material keys. They cross without a
/// cpu-built block assignment. Each receiver and each input refines the standing partition in
/// turn; a complete input sweep which opens no class is the exact finite fixed point. Sequential
/// intersections may reach that point in a different number of physical launches than synchronous
/// Moore rounds, so the semantic `rounds` return is reconstructed from the exhibited shortest
/// distinguishing words rather than from launch chronology.
pub fn compress_on_device(
    system: &dyn ObservedSystem,
    executor: &mut CudaRefineExecutor,
) -> Result<ReceiverExactCompression, CudaRefineError> {
    let items = system.items();
    let locations = items
        .iter()
        .copied()
        .enumerate()
        .map(|(at, item)| (item, at))
        .collect::<BTreeMap<_, _>>();
    let mut classes = vec![1u32; items.len()];

    // H.0016 one-shot receiver equivalence. Successive exact intersections are the conjunction of
    // all receiver faces; receiver order can move dense class ordinals but cannot move the
    // partition.
    for receiver in system.receivers() {
        let keys = items
            .iter()
            .map(|item| system.observation(*item, receiver).0)
            .collect::<Vec<_>>();
        classes = executor.quotient_on_device(&classes, &keys)?.cell_class;
    }
    let one_shot = partition_from_device(&items, &classes);

    // Close the partition under every admitted successor. Terminus is identity zero; device class
    // identities begin at one, so absence cannot collide with a successor block.
    let inputs = system.inputs();
    loop {
        let before = classes.iter().copied().collect::<BTreeSet<_>>().len();
        for input in &inputs {
            let keys = items
                .iter()
                .map(|item| {
                    system
                        .successor(*item, *input)
                        .and_then(|successor| locations.get(&successor).copied())
                        .and_then(|at| classes.get(at).copied())
                        .map_or(0, u64::from)
                })
                .collect::<Vec<_>>();
            classes = executor.quotient_on_device(&classes, &keys)?.cell_class;
        }
        let after = classes.iter().copied().collect::<BTreeSet<_>>().len();
        if after == before {
            break;
        }
    }

    let conduct = partition_from_device(&items, &classes);
    let collapsed = exhibit_collapsed(system, &one_shot, &conduct);
    let rounds = collapsed
        .iter()
        .map(|pair| pair.distinguishing_word.len())
        .max()
        .unwrap_or(0);
    Ok(ReceiverExactCompression {
        schema: "holonic-engine.receiver-exact-compression.v1".to_owned(),
        one_shot,
        conduct,
        rounds,
        collapsed,
    })
}

fn partition_from_device(items: &[ItemId], quotient: &[u32]) -> Partition {
    Partition::from_keys(items.iter().copied().zip(quotient.iter().copied()))
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
    exhibit_collapsed_within(system, one_shot, conduct, None)
}

/// **How many pairs the one-shot reading holds together that the conduct partition separates.**
///
/// Counted from the block sizes rather than enumerated: within a one-shot block of `n` items whose
/// conduct sub-blocks have sizes `n_1..n_k`, the separated pairs number `(n^2 - sum n_i^2) / 2`.
/// Exact, and it costs one pass over the population instead of a quadratic enumeration.
///
/// **This is an upper bound on `collapsed.len()` and equals it exactly when the item population is
/// closed under the successor relation.** Where a declared scope is not closed, refinement reads a
/// successor that leaves the scope as an absence and separates on it, while the search for a
/// distinguishing word follows that successor out of the scope and may find no receiver difference
/// at all. The two readings then disagree, and the disagreement is a fact about the scope.
pub fn separated_pair_population(one_shot: &Partition, conduct: &Partition) -> u128 {
    let index = conduct.index();
    let mut total = 0u128;
    let mut sub: BTreeMap<usize, u128> = BTreeMap::new();
    for block in &one_shot.blocks {
        sub.clear();
        let mut size = 0u128;
        for item in block {
            size += 1;
            *sub.entry(index.block_of(*item).unwrap_or(usize::MAX))
                .or_default() += 1;
        }
        let within: u128 = sub.values().map(|count| count * count).sum();
        total += (size * size - within) / 2;
    }
    total
}

/// The collapsed population in canonical `(left, right)` order, optionally bounded.
///
/// `limit` is an **aperture**, not a sample: it takes the first `n` pairs of the canonical order the
/// unbounded call would return, so a bounded exhibition is a prefix of the complete one rather than
/// a selection from it.
pub fn exhibit_collapsed_within(
    system: &dyn ObservedSystem,
    one_shot: &Partition,
    conduct: &Partition,
    limit: Option<usize>,
) -> Vec<CollapsedPair> {
    let receivers = system.receivers();
    let inputs = system.inputs();
    let one_shot_index = one_shot.index();
    let conduct_index = conduct.index();
    let mut collapsed = Vec::new();

    // Ascending by `left`, then by `right` inside `left`'s one-shot block: the same order the pair
    // set gave, without materialising a set that is quadratic in a block.
    'population: for left in one_shot.items_in_order() {
        let Some(block) = one_shot_index
            .block_of(left)
            .and_then(|at| one_shot.blocks.get(at))
        else {
            continue;
        };
        for right in block.range((
            std::ops::Bound::Excluded(left),
            std::ops::Bound::Unbounded::<ItemId>,
        )) {
            let right = *right;
            if limit.is_some_and(|bound| collapsed.len() >= bound) {
                break 'population;
            }
            if conduct_index.block_of(left) == conduct_index.block_of(right) {
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
                // BOTH sides terminate on this input. That is not a distinction and it is not the end of
                // the search — the rest of the frontier may still separate them on another input.
                //
                // This read `break` until 2026-08-07, which abandoned the whole search and made
                // `is_exact()` return true while `refinement()` was nonzero: adding an input the system
                // admits could make the reported loss go from one pair to zero. No fixture in this
                // module could catch it, because none of them ever enqueues a both-terminate frontier
                // entry — the cyclic counter is total, and `TwoRoutes` rests where it is rather than
                // stopping.
                let (Some(here_item), Some(there_item)) = (here, there) else {
                    continue;
                };
                if !word.is_empty()
                    && let Some(receiver) = receivers.iter().copied().find(|receiver| {
                        system.observation(here_item, *receiver)
                            != system.observation(there_item, *receiver)
                    })
                {
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
        values
            .iter()
            .fold(1, |acc, value| acc / gcd(acc, *value) * value)
    }

    #[test]
    fn the_quotient_is_exact_exactly_when_the_modulus_divides_the_cycle() {
        for n in 2..=24u64 {
            for moduli in [vec![2u64], vec![3], vec![2, 3], vec![4, 6]] {
                let system = CyclicCounter {
                    n,
                    moduli: moduli.clone(),
                };
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
        let system = CyclicCounter {
            n: 12,
            moduli: vec![2, 3],
        };
        let compression = compress(&system);
        assert!(compression.is_exact());
        assert_eq!(
            compression.rounds, 0,
            "a stable partition needs no refinement"
        );
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
        let system = CyclicCounter {
            n: 3,
            moduli: vec![2],
        };
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

    /// **The memory order is the collapsed depth**, and it is a property of the
    /// pair `(material, receiver family)` rather than of the material.
    ///
    /// One counter read two ways: modulo two it needs history, modulo itself it
    /// needs none. The material is identical in both readings, so anything the
    /// order says is said about the *receiver*.
    #[test]
    fn the_memory_order_is_a_property_of_the_receiver_family_and_not_of_the_material() {
        let coarse = compress(&CyclicCounter {
            n: 5,
            moduli: vec![2],
        });
        let exact = compress(&CyclicCounter {
            n: 5,
            moduli: vec![5],
        });

        // The coarse family cannot tell the states apart at a glance and needs
        // history to do it; the order is exactly how much.
        assert!(!coarse.is_exact());
        let order = coarse.memory_order().expect("something collapsed");
        assert!(order >= 1);
        assert!(coarse.is_markov_at(order));
        assert!(!coarse.is_markov_at(order - 1));

        // The exact family separates everything one-shot: no history at all.
        assert!(exact.is_exact());
        assert_eq!(
            exact.memory_order(),
            None,
            "nothing collapsed, so no history was needed -- a genuine zero, returned as None \
             rather than as a figure that could be confused with an unmeasured one"
        );
        assert!(exact.is_markov_at(0));
    }

    /// The non-Markovianity at an order is **exhibited by name**, never counted.
    /// Every pair beyond the order carries the two histories the state map could
    /// not tell apart and the word that does it.
    #[test]
    fn the_pairs_beyond_an_order_are_returned_by_name_and_partition_the_population() {
        let compression = compress(&CyclicCounter {
            n: 5,
            moduli: vec![2],
        });
        let order = compression.memory_order().expect("something collapsed");
        assert!(compression.beyond_order(order).is_empty());

        let beyond = compression.beyond_order(0);
        assert_eq!(
            beyond.len(),
            compression.collapsed.len(),
            "every collapsed pair needs at least one symbol"
        );
        for pair in &beyond {
            assert!(!pair.distinguishing_word.is_empty());
            assert!(
                pair.witness.is_some(),
                "a pair beyond the order names its receiver"
            );
        }

        // And the split at an intermediate order is a genuine partition of the
        // population rather than all-or-nothing.
        if order > 1 {
            let split = compression.beyond_order(order - 1);
            assert!(!split.is_empty() && split.len() < compression.collapsed.len());
        }
    }

    #[test]
    fn the_shortest_word_length_grows_with_the_depth_of_the_distinction() {
        // n = 5 read only mod 2: {0,2,4} look alike, {1,3} look alike, and separating them takes
        // more than one step because the wrap is further away for some pairs than for others.
        let system = CyclicCounter {
            n: 5,
            moduli: vec![2],
        };
        let compression = compress(&system);
        assert!(!compression.is_exact());
        assert_eq!(
            compression.conduct.len(),
            5,
            "every item becomes distinguishable"
        );
        let longest = compression
            .collapsed
            .iter()
            .map(|pair| pair.distinguishing_word.len())
            .max()
            .expect("collapsed pairs exist");
        assert!(
            longest >= 2,
            "some pair needs more than one step, got {longest}"
        );
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

    /// Both sides terminating on one input must not end the search.
    ///
    /// Input `A` stops both `0` and `1`; input `B` sends them to items a receiver separates. The
    /// pair is genuinely collapsed and must be reported whether or not `A` is declared. Before the
    /// fix, declaring `A` alongside `B` silently dropped the pair and `is_exact()` returned true
    /// while `refinement()` stayed at 1 — a reported loss of zero on a system that loses something.
    struct BothStop;
    impl ObservedSystem for BothStop {
        fn items(&self) -> Vec<ItemId> {
            (0..4).map(ItemId).collect()
        }
        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }
        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0), InputId(1)]
        }
        fn observation(&self, item: ItemId, _receiver: ReceiverId) -> Observation {
            match item.0 {
                2 => Observation(1),
                3 => Observation(2),
                _ => Observation(0),
            }
        }
        fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
            match (item.0, input == InputId(0)) {
                (_, true) => None,
                (0, false) => Some(ItemId(2)),
                (1, false) => Some(ItemId(3)),
                _ => None,
            }
        }
    }

    #[test]
    fn a_both_terminating_input_does_not_end_the_search_for_a_distinguishing_word() {
        let compression = compress(&BothStop);
        assert!(
            !compression.is_exact(),
            "the pair (0,1) is separated by input B and must be reported"
        );
        assert_eq!(
            compression.refinement() > 0,
            !compression.is_exact(),
            "is_exact() and refinement() must never contradict each other"
        );
        let pair = compression
            .collapsed
            .iter()
            .find(|pair| (pair.left, pair.right) == (ItemId(0), ItemId(1)))
            .expect("the collapsed pair is exhibited, not silently dropped");
        assert_eq!(pair.distinguishing_word, vec![InputId(1)]);
        assert!(pair.witness.is_some());
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
            let system = CyclicCounter {
                n,
                moduli: vec![2, 3, 5],
            };
            let full = compress(&system);
            for receiver in system.receivers() {
                let ablated = AblatedSystem {
                    inner: &system,
                    without: receiver,
                };
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

    /// The indexed lookup and the scan answer the same question. Added with the index, 2026-08-20.
    #[test]
    fn the_indexed_block_lookup_agrees_with_the_scan_everywhere() {
        for n in 2..=18u64 {
            let system = CyclicCounter {
                n,
                moduli: vec![2, 3, 5],
            };
            let reading = refine(&system);
            for partition in [&reading.one_shot, &reading.conduct] {
                let index = partition.index();
                for item in system.items() {
                    assert_eq!(index.block_of(item), partition.block_of(item));
                }
                assert_eq!(index.len(), system.items().len());
                assert_eq!(partition.items_in_order(), system.items());
            }
        }
    }

    /// **The sparse successor face must not move the partition.** A system that names its admitted
    /// items per input and the same system read densely are the same system, and the whole value of
    /// the face is that this is checkable rather than argued.
    ///
    /// `TwoRoutes` is the fixture with a genuine branch structure and terminating rows, so both the
    /// "resolves to a block" and "keeps its label" arms are exercised.
    struct SparseTwoRoutes;
    impl ObservedSystem for SparseTwoRoutes {
        fn items(&self) -> Vec<ItemId> {
            TwoRoutes.items()
        }
        fn receivers(&self) -> Vec<ReceiverId> {
            TwoRoutes.receivers()
        }
        fn inputs(&self) -> Vec<InputId> {
            TwoRoutes.inputs()
        }
        fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
            TwoRoutes.observation(item, receiver)
        }
        fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
            TwoRoutes.successor(item, input)
        }
        fn admitted(&self, input: InputId) -> Option<Vec<(ItemId, ItemId)>> {
            Some(
                TwoRoutes
                    .items()
                    .into_iter()
                    .filter_map(|item| TwoRoutes.successor(item, input).map(|next| (item, next)))
                    .collect(),
            )
        }
    }

    /// The same, over a fixture whose rows genuinely terminate, so the arm that keeps a label is the
    /// one under test.
    struct SparseBothStop;
    impl ObservedSystem for SparseBothStop {
        fn items(&self) -> Vec<ItemId> {
            BothStop.items()
        }
        fn receivers(&self) -> Vec<ReceiverId> {
            BothStop.receivers()
        }
        fn inputs(&self) -> Vec<InputId> {
            BothStop.inputs()
        }
        fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
            BothStop.observation(item, receiver)
        }
        fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
            BothStop.successor(item, input)
        }
        fn admitted(&self, input: InputId) -> Option<Vec<(ItemId, ItemId)>> {
            Some(
                BothStop
                    .items()
                    .into_iter()
                    .filter_map(|item| BothStop.successor(item, input).map(|next| (item, next)))
                    .collect(),
            )
        }
    }

    #[test]
    fn the_sparse_successor_face_returns_the_same_compression_as_the_dense_reading() {
        let dense = compress(&TwoRoutes);
        let sparse = compress(&SparseTwoRoutes);
        assert_eq!(dense.one_shot, sparse.one_shot);
        assert_eq!(dense.conduct, sparse.conduct);
        assert_eq!(dense.rounds, sparse.rounds);
        assert_eq!(dense.collapsed, sparse.collapsed);
        assert!(
            !dense.collapsed.is_empty(),
            "the fixture must lose something"
        );

        let dense = compress(&BothStop);
        let sparse = compress(&SparseBothStop);
        assert_eq!(dense.one_shot, sparse.one_shot);
        assert_eq!(dense.conduct, sparse.conduct);
        assert_eq!(dense.rounds, sparse.rounds);
        assert_eq!(dense.collapsed, sparse.collapsed);
    }

    /// **On a population closed under the successor relation the round count IS the memory order.**
    ///
    /// Moore's round `k` separates exactly the pairs whose shortest distinguishing word has length
    /// `k`, so the last round that changed anything is the longest such word. This is what makes the
    /// whole-atlas memory order readable without a per-pair search — and it is stated as a condition
    /// rather than a fact, because Deed P0's declared scope is *not* closed and there the two
    /// readings disagree by construction.
    #[test]
    fn on_a_closed_population_the_rounds_are_the_memory_order() {
        for n in 2..=24u64 {
            for moduli in [vec![2u64], vec![3], vec![2, 3], vec![4, 6]] {
                let system = CyclicCounter { n, moduli };
                let compression = compress(&system);
                match compression.memory_order() {
                    None => assert_eq!(compression.rounds, 0),
                    Some(order) => assert_eq!(
                        compression.rounds, order,
                        "n={n}: rounds {} against memory order {order}",
                        compression.rounds
                    ),
                }
            }
        }
    }

    /// The counted separated population and the exhibited one agree on a closed system, and the
    /// bounded exhibition is a **prefix** of the complete one rather than a selection from it.
    #[test]
    fn the_counted_separated_population_matches_the_exhibited_one_and_the_bound_is_a_prefix() {
        let system = CyclicCounter {
            n: 5,
            moduli: vec![2],
        };
        let compression = compress(&system);
        assert_eq!(
            separated_pair_population(&compression.one_shot, &compression.conduct),
            compression.collapsed.len() as u128
        );
        for bound in 0..=compression.collapsed.len() {
            let bounded = exhibit_collapsed_within(
                &system,
                &compression.one_shot,
                &compression.conduct,
                Some(bound),
            );
            assert_eq!(bounded.len(), bound);
            assert_eq!(bounded.as_slice(), &compression.collapsed[..bound]);
        }
    }

    /// The ablation must be capable of actually changing something, or the control above is a law
    /// that returns zero.
    #[test]
    fn ablation_does_change_the_compression_somewhere() {
        let system = CyclicCounter {
            n: 12,
            moduli: vec![2, 3],
        };
        let full = compress(&system);
        let ablated = AblatedSystem {
            inner: &system,
            without: ReceiverId(1),
        };
        let reduced = compress(&ablated);
        assert_eq!(full.conduct.len(), 6);
        assert_eq!(
            reduced.conduct.len(),
            2,
            "dropping mod 3 leaves only parity"
        );
        assert!(reduced.conduct.len() < full.conduct.len());
    }
}
