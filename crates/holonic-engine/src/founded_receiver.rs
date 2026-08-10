//! A receiver founded at a junction, and the gyration between two founding orders.
//!
//! ## What was locked
//!
//! [`crate::receiver_exact_compression::ObservedSystem::receivers`] is consulted **once**, for the
//! one-shot partition; the refinement loop that follows touches only `items` and `inputs`. So the
//! partition refines and **the receiver population never grows**. A fixed panel returns exactly one
//! decomposition, and one decomposition cannot hold competing readings of the same material as live
//! alternatives — which is what a corpus actually presents. Brandon, 2026-08-09, on how a reading
//! decomposes: *"'t' is not always a conjunction token"* … *"in order to interpret me you must have
//! exposure to the potential variations in the way that the information I'm articulating can be
//! expressed; combinatorial potentials that are competitively selected."*
//!
//! The coupling is measured from the other side already: withholding a receiver axis **increases**
//! plurality. Because nothing founds a receiver, plurality can only be lost.
//!
//! ## The junction
//!
//! A [`CollapsedPair`] with `witness: None` is a pair **conduct separates and no declared receiver
//! saw**. The compression module's own fixture states it: *"a terminus separation names no
//! witnessing receiver because none saw a difference."* That is the declared panel exhausted at a
//! distinction the material carries, and exhaustion is a **FOUND**, not a report — the same
//! primitive as prime recognition, where trial transport against every founded axis and then
//! exhaustion founds a new axis which becomes later terrain.
//!
//! ```text
//!   compress                   -> conduct partition + collapsed pairs
//!   a pair with witness: None  -> THE JUNCTION
//!   found a receiver there     -> its reading is the item's own CONTINUATION APERTURE
//!   re-refine with the panel one wider
//!   repeat until no unwitnessed pair remains
//! ```
//!
//! **The founded reading is the material's, not an author's.** A terminus junction is a place where
//! one item continues under an input and the other does not, so the distinction the panel lacks is
//! *which inputs admit a continuation here* — the item's own aperture. [`continuation_aperture`]
//! reads exactly that and nothing else.
//!
//! **Termination is structural.** A founding is admitted only if it strictly refines the one-shot
//! partition, and the partition is over a finite population, so foundings are bounded by
//! `|items| − 1`. [`FoundedPanel::bound`] carries the bound and [`FoundedPanel::rounds`] what was
//! used.
//!
//! **And a founded receiver has two windings where a declared one has one.**
//! `observation(item, receiver)` is a single read — the receiver looks and returns a value; nothing
//! is conserved across it, which is why `the_measure_is_situated` had to prove Mayer–Vietoris
//! cannot express the two-body comparison. A founded receiver is defined **by a difference it
//! carries across a junction**, so the coupling is its definition rather than something added to it.
//!
//! ## The gyration
//!
//! Refinement commutes: refining by `a` then `b` is refining by `b` then `a`, because partition
//! joins commute. **Founding does not.** Junction `J₂` exists *only because* `a` was founded, so
//! `found(a)∘found(b)` and `found(b)∘found(a)` reach different panels.
//!
//! `papers/source/papers/knot-causal-topology/main.typ:314-332` names the object —
//! `gyr[a,b]` is *"a finite holonomy face of the noncommuting transports"* — and states its own
//! bound: *"It should not be installed as the universal law of every comparison complex. The general
//! object is connection and holonomy; the gyroparallelogram is one exact hyperbolic
//! specialization."* [`Gyration`] is that finite holonomy face and **not** its hyperbolic model:
//! two founding orders, one starting panel, the disagreement retained rather than resolved.
//!
//! Unlike the elaboration complex — where the same word was used over a structure carrying no
//! cochain, and the claim was struck the same day — there is a real transport here: the founding
//! order is the path, and the panel is what is transported along it.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use num_bigint::BigUint;
use num_traits::One;

use crate::receiver_exact_compression::{
    compress, CollapsedPair, InputId, ItemId, ObservedSystem, Observation, Partition, ReceiverId,
};

/// **Why an axis was founded.** Two pressures, and the second is the traffic law.
///
/// Founding on blindness alone is the four-fingers case: every axis founded the same way, each a
/// mode of freedom the others already have. Brandon, 2026-07-31, giving the other pressure:
/// *"It is stupid to try to serialize things generally through major pathways because they end up
/// becoming overcrowded and inaccessible because there is too much traffic, so what you would
/// normally do in engineering is just construct more dynamic pathways to navigate between."*
///
/// **Congestion founds an axis.** A block holding many items is an overloaded site: the declared
/// panel routes everything through one distinction, and the engineering answer is not a finer
/// version of that distinction but *another pathway*.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FoundingPressure {
    /// Conduct separates a pair and no receiver in the panel witnesses it.
    Blindness { left: ItemId, right: ItemId },
    /// A block of the one-shot partition carries more items than any other. The site is overloaded.
    Congestion { block: usize, occupancy: usize },
}

/// **What kind of axis was founded.** The species matters as much as the count.
///
/// Brandon, 2026-08-09: *"We literally have 5 fingers per hand, where 4 of the fingers have similar
/// modes of freedom, but the 5th is an opposable thumb that **exponentially increases the
/// combinatorial potentials** of what we can do with our hands."* Four axes of one species do not
/// multiply what a panel can do; an axis of a **different** species does. So the species is
/// retained, and [`FoundedPanel::species_founded`] returns how many distinct ones a run reached —
/// which is the non-naive reading of "more degrees of freedom".
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum AxisSpecies {
    /// Which admitted inputs offer a successor, read at the junction's own word. The distinction a
    /// terminus junction exhibits.
    ContinuationAperture,
    /// How far conduct carries from here before it stops — the length of the longest word this item
    /// admits, bounded by the population. A congested block is not blind; it is *undifferentiated*,
    /// and depth of reach differentiates it where aperture cannot.
    ConductReach,
}

/// A receiver founded at a junction the declared panel could not witness.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FoundedReceiver {
    /// The id minted for it, above every declared id in the starting panel.
    pub id: ReceiverId,
    /// Why it was founded.
    pub pressure: FoundingPressure,
    /// What kind of axis it is. Two of one species are four fingers; two species are a thumb.
    pub species: AxisSpecies,
    /// **The residue of this axis under the rest of the panel**, as a cardinality.
    ///
    /// For a receiver `r` in panel `R`, let `≡_r` be the equivalence it induces on items — the pairs
    /// it identifies. The residue is
    ///
    /// ```text
    ///   Res(r) = ( ⋂_{s ≠ r} ≡_s )  ∖  ≡_r
    /// ```
    ///
    /// the pairs **every other receiver identifies and this one separates**: what remains after
    /// quotienting by the rest. This is the residue-quotient sense the project already carries at
    /// `papers/source/mathematics/definitions/radix-residue-character-cell.typ`, not a metaphor.
    ///
    /// `Res(r) = ∅` iff `⋂_{s≠r} ≡_s ⊆ ≡_r`, iff **removing `r` does not move the partition** — the
    /// axis is redundant in the family. That is the exact statement, and it is what stops "more
    /// axes" from being monotone: an axis is not a gain because it exists, but because its residue
    /// is non-empty.
    pub residue: usize,
    /// The pair whose separation no declared receiver witnessed. This is the junction.
    pub junction: (ItemId, ItemId),
    /// The shortest input word after which conduct separated that pair.
    pub after: Vec<InputId>,
    /// What it reads, per item: the item's own continuation aperture, canonically encoded.
    pub reads: BTreeMap<ItemId, Observation>,
    /// How many blocks the partition gained when this receiver entered the panel. A founding that
    /// gained none is refused — see [`FoundingRefusal::FoundedNothing`].
    pub blocks_gained: usize,
}

/// Why a founding was refused. Refusals are returned, never silently skipped.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FoundingRefusal {
    /// The candidate reading does not separate the junction that provoked it. A receiver that
    /// cannot see the thing it was founded for is not that receiver.
    DoesNotSeparateItsJunction { left: ItemId, right: ItemId },
    /// The candidate reading separates nothing at all — the aperture is uniform over the population.
    FoundedNothing { left: ItemId, right: ItemId },
    /// The structural bound `|items| − 1` was reached with unwitnessed pairs still standing.
    BoundReached { remaining: usize },
    /// The declared junction is not standing against the prefix it was staged over: either the
    /// present panel already witnesses that pair, or the panel now separates it one-shot, or conduct
    /// never separated it at all.
    ///
    /// **This is the refusal `crate::interchange` reads as a failed rebase.** A staged occurrence
    /// that ceases to be a junction once another occurrence has been founded is not independent of
    /// it, and the front stays ordered.
    NotAStandingJunction { left: ItemId, right: ItemId },
    /// The founding gained no block against the prefix it was staged over. [`FoundedReceiver`]'s own
    /// `blocks_gained` documentation says a founding that gained none is refused; only
    /// [`found_at`] enforces it — [`found_to_exhaustion`] computes the gain and pushes regardless.
    GainedNoBlock { left: ItemId, right: ItemId },
}

/// The founding run to exhaustion, with everything it refused.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FoundedPanel {
    /// The panel the system declared.
    pub declared: Vec<ReceiverId>,
    /// What was founded, in the order it was founded.
    pub founded: Vec<FoundedReceiver>,
    /// Foundings performed.
    pub rounds: usize,
    /// The structural bound on foundings, `|items| − 1`.
    pub bound: usize,
    /// The one-shot partition **before** any founding.
    pub one_shot_before: Partition,
    /// The one-shot partition after the panel has grown. Founding acts here, not on conduct.
    pub one_shot_after: Partition,
    /// The conduct partition after the panel has grown. The Nerode congruence is an invariant of
    /// the material and **must not move** — founding sharpens what is *seen*, never what conduct
    /// *does*.
    pub conduct: Partition,
    /// Pairs conduct still separates that no receiver witnesses. Zero at exhaustion.
    pub unwitnessed_remaining: usize,
    /// Every refusal, in order.
    pub refused: Vec<FoundingRefusal>,
}

impl FoundedPanel {
    /// The junctions taken, in order — the path through the founding, which is what the gyration
    /// varies.
    pub fn order(&self) -> Vec<(ItemId, ItemId)> {
        self.founded.iter().map(|found| found.junction).collect()
    }

    /// Whether the panel reached exhaustion: every pair conduct separates now has a witness.
    pub const fn exhausted(&self) -> bool {
        self.unwitnessed_remaining == 0
    }

    /// How many **distinct axis species** the run founded. Four axes of one species are four
    /// fingers; two species are a thumb, and that is what multiplies what the panel can do.
    pub fn species_founded(&self) -> BTreeSet<AxisSpecies> {
        self.founded.iter().map(|found| found.species).collect()
    }

    /// Founded axes with **empty residue** — redundant in the family, since removing any of them
    /// leaves the partition unmoved.
    pub fn redundant(&self) -> Vec<&FoundedReceiver> {
        self.founded
            .iter()
            .filter(|found| found.residue == 0)
            .collect()
    }

    /// **The feedback: capacity is the residue.**
    ///
    /// `receiver_current`'s law is `service_rounds = ⌈co_present_branch_population / site_capacity⌉`
    /// and `passage_delay = characteristic_delay + (service_rounds − 1)`, so capacity **divides**
    /// demand: a wider site dilates less. Setting an axis's capacity to its residue closes the loop
    ///
    /// ```text
    ///   residue -> capacity -> service_rounds -> passage_delay -> what conducts -> residue
    /// ```
    ///
    /// and it is the exact form of *"the routes are cheap by design because that is something the
    /// brain did before this situation"*: a route is cheap **because it carried what nothing else
    /// carried**.
    ///
    /// **The `+ 1` is forced and it is meaningful.** `ExactReceiverCurrentLaw::set_site_capacity`
    /// refuses zero — `ceil_population_division` would divide by it — so an axis with empty residue
    /// takes capacity **1**, the minimum. It is not deleted; it becomes the **most congested** route,
    /// dilating maximally under any co-present demand. A redundant axis therefore changes what later
    /// current finds cheap without ever being removed by a chooser.
    pub fn capacities(&self) -> BTreeMap<ReceiverId, BigUint> {
        self.founded
            .iter()
            .map(|found| {
                (
                    found.id,
                    BigUint::from(found.residue) + BigUint::one(),
                )
            })
            .collect()
    }
}

/// The item's own continuation aperture: which admitted inputs offer a successor here.
///
/// Nothing is authored, ordered, or weighted — the encoding is a canonical bitset over the declared
/// input order, so two runs over one system agree bit for bit.
pub fn continuation_aperture(system: &dyn ObservedSystem, item: ItemId) -> Observation {
    let mut word = 0u64;
    for (place, input) in system.inputs().iter().enumerate().take(64) {
        if system.successor(item, *input).is_some() {
            word |= 1u64 << place;
        }
    }
    Observation(word)
}

/// **The founded reading, and it is LOCAL to its junction.**
///
/// The junction is not at `left` and `right`; it is at `left·w` and `right·w`, where `w` is the
/// shortest word after which conduct separated them. So the distinction the panel lacks lives
/// *there*, and a receiver founded to see it must look from there.
///
/// A global reading is what the first form of this organ used, and the consequence was measured:
/// **one founding closed all 318 junctions on the development**, because the same function founds
/// the same receiver at every junction and the second founding had nothing left to do. The gyration
/// was then non-trivial only in which junction was *recorded* as the provocation — it distinguished
/// provenance and not content. Reading at the word makes successive foundings genuinely different
/// receivers, which is what gives `gyr[a,b]` something to be a holonomy *of*.
///
/// Following the word may terminate early. That is not a failure to read: **where a path stops is a
/// distinction**, and it is encoded as the step it stopped at, disjoint from every aperture value.
pub fn aperture_after(
    system: &dyn ObservedSystem,
    item: ItemId,
    word: &[InputId],
) -> Observation {
    let mut here = item;
    for (step, input) in word.iter().enumerate() {
        match system.successor(here, *input) {
            Some(next) => here = next,
            // Terminated at `step`. Encoded above every aperture bitset so the two populations
            // cannot collide: the high bit marks a terminus, the rest names where.
            None => return Observation(1u64 << 63 | step as u64),
        }
    }
    continuation_aperture(system, here)
}

/// **The second axis species: how far conduct carries from here before it stops.**
///
/// A congested block is not blind — every receiver agrees about its members. It is
/// *undifferentiated*, and a finer version of the same aperture cannot differentiate it. Depth of
/// reach can: two items with identical apertures may still admit words of different length.
///
/// Bounded by the population, so the walk terminates: a cycle cannot extend the reach past the
/// number of items.
pub fn conduct_reach(system: &dyn ObservedSystem, item: ItemId) -> Observation {
    let bound = system.items().len();
    let inputs = system.inputs();
    let mut frontier = vec![item];
    let mut seen: BTreeSet<ItemId> = BTreeSet::from([item]);
    let mut reach = 0u64;
    while !frontier.is_empty() && (reach as usize) < bound {
        let mut next = Vec::new();
        for here in frontier {
            for input in &inputs {
                if let Some(there) = system.successor(here, *input)
                    && seen.insert(there)
                {
                    next.push(there);
                }
            }
        }
        if next.is_empty() {
            break;
        }
        frontier = next;
        reach += 1;
    }
    Observation(reach)
}

/// The reading for one axis species, at one junction word.
fn read_species(
    system: &dyn ObservedSystem,
    species: AxisSpecies,
    word: &[InputId],
) -> BTreeMap<ItemId, Observation> {
    system
        .items()
        .into_iter()
        .map(|item| {
            let read = match species {
                AxisSpecies::ContinuationAperture => aperture_after(system, item, word),
                AxisSpecies::ConductReach => conduct_reach(system, item),
            };
            (item, read)
        })
        .collect()
}

/// The most occupied block of a partition — the overloaded site.
fn congested_block(partition: &Partition) -> Option<(usize, usize)> {
    partition
        .blocks
        .iter()
        .enumerate()
        .max_by_key(|(_, block)| block.len())
        .map(|(index, block)| (index, block.len()))
}

/// A system whose panel is the declared one plus everything founded so far.
///
/// The item population, the input population and the successor law are the declared system's,
/// untouched. Only `receivers` and `observation` widen — which is exactly the claim: founding
/// changes what is **seen**, never what the material **does**.
pub struct WidenedSystem<'a> {
    pub declared: &'a dyn ObservedSystem,
    pub founded: &'a [FoundedReceiver],
}

impl ObservedSystem for WidenedSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.declared.items()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        let mut all = self.declared.receivers();
        all.extend(self.founded.iter().map(|found| found.id));
        all
    }

    fn inputs(&self) -> Vec<InputId> {
        self.declared.inputs()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        for found in self.founded {
            if found.id == receiver {
                return found.reads.get(&item).copied().unwrap_or(Observation(0));
            }
        }
        self.declared.observation(item, receiver)
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.declared.successor(item, input)
    }
}

/// The first pair conduct separates that no receiver in the present panel witnesses.
fn first_junction(collapsed: &[CollapsedPair]) -> Option<&CollapsedPair> {
    collapsed.iter().find(|pair| pair.witness.is_none())
}

/// Found receivers at junctions until the panel witnesses everything conduct separates.
///
/// `skip` is the junction order control: junctions whose pair appears in it are passed over on the
/// first sweep, which is how [`gyration`] takes a different path through the same material. It is
/// never a filter on the *result* — a skipped junction is revisited once the skip list is spent.
pub fn found_to_exhaustion(system: &dyn ObservedSystem, skip: &[(ItemId, ItemId)]) -> FoundedPanel {
    found_in_order(system, &[], skip)
}

/// **Found these junctions FIRST, then proceed canonically.**
///
/// The difference from a skip list is the whole content and it decides what a gyration can see.
/// Skipping a junction *removes* it and leaves every other junction in the same canonical scan
/// order, so two skip-perturbed orders differ by an **omission** and the permutation they induce on
/// the shared population is the identity — measured 0 of 190 on real corpus material by
/// `examples/the_junction_returns_a_group_element`. Preferring a junction **moves** it, so the two
/// orders differ by a genuine reordering and the gyration has a non-trivial group element to return.
///
/// This is what `Gyration`'s own claim was always about: `found(a)∘found(b)` against
/// `found(b)∘found(a)` is a statement about which is taken **first**, not about which is left out.
pub fn found_preferring(
    system: &dyn ObservedSystem,
    prefer: &[(ItemId, ItemId)],
) -> FoundedPanel {
    found_in_order(system, prefer, &[])
}

fn found_in_order(
    system: &dyn ObservedSystem,
    prefer: &[(ItemId, ItemId)],
    skip: &[(ItemId, ItemId)],
) -> FoundedPanel {
    let declared = system.receivers();
    let items = system.items();
    let bound = items.len().saturating_sub(1);
    let before = compress(system);

    let mut founded: Vec<FoundedReceiver> = Vec::new();
    let mut refused: Vec<FoundingRefusal> = Vec::new();
    let mut next_id = declared
        .iter()
        .map(|receiver| receiver.0)
        .max()
        .map_or(0u64, |top| top + 1);
    let mut deferred: BTreeSet<(ItemId, ItemId)> = skip.iter().copied().collect();
    let preferred: BTreeSet<(ItemId, ItemId)> = prefer.iter().copied().collect();

    loop {
        let widened = WidenedSystem {
            declared: system,
            founded: &founded,
        };
        let reading = compress(&widened);

        // Preferred junctions are taken first — that is what MOVES a junction rather than removing
        // it, and it is the only perturbation that can produce a reordering. Deferred junctions are
        // then passed over, and admitted once nothing else stands.
        let junction = reading
            .collapsed
            .iter()
            .find(|pair| pair.witness.is_none() && preferred.contains(&(pair.left, pair.right)))
            .or_else(|| {
                reading.collapsed.iter().find(|pair| {
                    pair.witness.is_none() && !deferred.contains(&(pair.left, pair.right))
                })
            })
            .or_else(|| first_junction(&reading.collapsed));
        let Some(pair) = junction else {
            // BLINDNESS IS EXHAUSTED. The other pressure remains: a block holding many items is an
            // overloaded site, and the traffic answer is another pathway rather than a finer
            // version of the same one. The axis founded here is a DIFFERENT SPECIES -- the thumb,
            // not a fifth finger -- because a congested block is undifferentiated rather than
            // blind, and a sharper aperture cannot differentiate it.
            let widened = WidenedSystem {
                declared: system,
                founded: &founded,
            };
            let settled = compress(&widened);

            if founded.len() < bound
                && let Some((block, occupancy)) = congested_block(&settled.one_shot)
                && occupancy > 1
            {
                let species = AxisSpecies::ConductReach;
                let reads = read_species(system, species, &[]);
                let distinct: BTreeSet<Observation> = reads.values().copied().collect();
                let gained = {
                    let mut trial = founded.clone();
                    trial.push(FoundedReceiver {
                        id: ReceiverId(next_id),
                        pressure: FoundingPressure::Congestion { block, occupancy },
                        species,
                        residue: 0,
                        junction: (ItemId(0), ItemId(0)),
                        after: Vec::new(),
                        reads: reads.clone(),
                        blocks_gained: 0,
                    });
                    let widened = WidenedSystem {
                        declared: system,
                        founded: &trial,
                    };
                    compress(&widened)
                        .one_shot
                        .len()
                        .saturating_sub(settled.one_shot.len())
                };
                if distinct.len() > 1 && gained > 0 {
                    founded.push(FoundedReceiver {
                        id: ReceiverId(next_id),
                        pressure: FoundingPressure::Congestion { block, occupancy },
                        species,
                        residue: 0,
                        junction: (ItemId(0), ItemId(0)),
                        after: Vec::new(),
                        reads,
                        blocks_gained: gained,
                    });
                    next_id += 1;
                    continue;
                }
                refused.push(FoundingRefusal::FoundedNothing {
                    left: ItemId(0),
                    right: ItemId(0),
                });
            }

            let widened = WidenedSystem {
                declared: system,
                founded: &founded,
            };
            let settled = compress(&widened);
            measure_residue(system, &mut founded);
            return FoundedPanel {
                declared,
                rounds: founded.len(),
                bound,
                one_shot_before: before.one_shot.clone(),
                one_shot_after: settled.one_shot,
                conduct: settled.conduct,
                unwitnessed_remaining: 0,
                founded,
                refused,
            };
        };
        deferred.remove(&(pair.left, pair.right));

        if founded.len() >= bound {
            let remaining = reading
                .collapsed
                .iter()
                .filter(|pair| pair.witness.is_none())
                .count();
            refused.push(FoundingRefusal::BoundReached { remaining });
            return FoundedPanel {
                declared,
                rounds: founded.len(),
                bound,
                one_shot_before: before.one_shot.clone(),
                one_shot_after: reading.one_shot,
                conduct: reading.conduct,
                unwitnessed_remaining: remaining,
                founded,
                refused,
            };
        }

        // The candidate reading, off the material and LOCAL to this junction's word.
        let pressure = FoundingPressure::Blindness {
            left: pair.left,
            right: pair.right,
        };
        let species = AxisSpecies::ContinuationAperture;
        let reads = read_species(system, species, &pair.distinguishing_word);

        // It must see the junction it was founded for, and it must found something.
        let left_read = reads.get(&pair.left).copied().unwrap_or(Observation(0));
        let right_read = reads.get(&pair.right).copied().unwrap_or(Observation(0));
        let distinct: BTreeSet<Observation> = reads.values().copied().collect();
        if distinct.len() < 2 {
            refused.push(FoundingRefusal::FoundedNothing {
                left: pair.left,
                right: pair.right,
            });
            return FoundedPanel {
                declared,
                rounds: founded.len(),
                bound,
                one_shot_before: before.one_shot.clone(),
                one_shot_after: reading.one_shot.clone(),
                conduct: reading.conduct.clone(),
                unwitnessed_remaining: reading
                    .collapsed
                    .iter()
                    .filter(|pair| pair.witness.is_none())
                    .count(),
                founded,
                refused,
            };
        }
        if left_read == right_read {
            // The aperture does not see this junction. Refuse it by name and stop, rather than
            // founding a receiver that cannot do the one thing it exists for.
            refused.push(FoundingRefusal::DoesNotSeparateItsJunction {
                left: pair.left,
                right: pair.right,
            });
            return FoundedPanel {
                declared,
                rounds: founded.len(),
                bound,
                one_shot_before: before.one_shot.clone(),
                one_shot_after: reading.one_shot.clone(),
                conduct: reading.conduct.clone(),
                unwitnessed_remaining: reading
                    .collapsed
                    .iter()
                    .filter(|pair| pair.witness.is_none())
                    .count(),
                founded,
                refused,
            };
        }

        let gained = {
            let candidate = FoundedReceiver {
                id: ReceiverId(next_id),
                pressure: pressure.clone(),
                species,
                residue: 0,
                junction: (pair.left, pair.right),
                after: pair.distinguishing_word.clone(),
                reads: reads.clone(),
                blocks_gained: 0,
            };
            let mut trial = founded.clone();
            trial.push(candidate);
            let widened = WidenedSystem {
                declared: system,
                founded: &trial,
            };
            compress(&widened).one_shot.len().saturating_sub(reading.one_shot.len())
        };

        founded.push(FoundedReceiver {
            id: ReceiverId(next_id),
            pressure,
            species,
            residue: 0,
            junction: (pair.left, pair.right),
            after: pair.distinguishing_word.clone(),
            reads,
            blocks_gained: gained,
        });
        next_id += 1;
    }
}

/// The next receiver id above every declared id and every id in the prefix. A mint ordinal, and
/// therefore an **absolute frame** in the sense of `CLAUDE.md` §0 lesson 2 — recorded so a caller
/// can see it move, never a coordinate a comparison may depend on.
fn next_receiver_id(system: &dyn ObservedSystem, prefix: &[FoundedReceiver]) -> ReceiverId {
    let top = system
        .receivers()
        .iter()
        .map(|receiver| receiver.0)
        .chain(prefix.iter().map(|found| found.id.0))
        .max();
    ReceiverId(top.map_or(0, |top| top + 1))
}

/// The junctions standing against a declared prefix: pairs the widened panel identifies one-shot,
/// conduct separates, and no receiver in that panel witnesses.
///
/// This is the population [`found_to_exhaustion`] walks one at a time. It is exposed because the
/// interchange question is *which* of these may be taken in either order, which needs the standing
/// population before and after a staged founding rather than only the run's own choice.
pub fn standing_junctions(
    system: &dyn ObservedSystem,
    prefix: &[FoundedReceiver],
) -> Vec<CollapsedPair> {
    let widened = WidenedSystem {
        declared: system,
        founded: prefix,
    };
    compress(&widened)
        .collapsed
        .into_iter()
        .filter(|pair| pair.witness.is_none())
        .collect()
}

/// **Found ONE receiver at a DECLARED junction, against a declared prefix.** The staged occurrence.
///
/// [`found_to_exhaustion`] chooses its own junctions and runs to a fixed point; that is a complete
/// order, not an occurrence. An interchange question needs an occurrence: *this* junction, over
/// *this* predecessor, so that the same two occurrences can be rebased in both orders and the
/// results compared. The admission rules are the ones `found_to_exhaustion` applies at a blindness
/// junction, unchanged, plus the two that only make sense when the junction is named by a caller:
/// the junction must actually be standing, and the founding must gain a block.
///
/// **The reading is the material's and the word is the panel's.** `reads` is
/// [`aperture_after`] over the *declared* system, so it does not depend on the prefix. The junction's
/// `after` word does — it comes from `compress` over the widened panel, and a wider panel can find a
/// witness earlier in the same breadth-first frontier. That is the whole coupling channel between
/// two staged occurrences, and it is why an interchange certificate must compare the word and the
/// reading rather than only the endpoint.
pub fn found_at(
    system: &dyn ObservedSystem,
    prefix: &[FoundedReceiver],
    junction: (ItemId, ItemId),
) -> Result<FoundedReceiver, FoundingRefusal> {
    let widened = WidenedSystem {
        declared: system,
        founded: prefix,
    };
    let reading = compress(&widened);
    let Some(pair) = reading
        .collapsed
        .iter()
        .find(|pair| pair.witness.is_none() && (pair.left, pair.right) == junction)
    else {
        return Err(FoundingRefusal::NotAStandingJunction {
            left: junction.0,
            right: junction.1,
        });
    };

    let species = AxisSpecies::ContinuationAperture;
    let reads = read_species(system, species, &pair.distinguishing_word);
    let distinct: BTreeSet<Observation> = reads.values().copied().collect();
    if distinct.len() < 2 {
        return Err(FoundingRefusal::FoundedNothing {
            left: pair.left,
            right: pair.right,
        });
    }
    if reads.get(&pair.left) == reads.get(&pair.right) {
        return Err(FoundingRefusal::DoesNotSeparateItsJunction {
            left: pair.left,
            right: pair.right,
        });
    }

    let candidate = FoundedReceiver {
        id: next_receiver_id(system, prefix),
        pressure: FoundingPressure::Blindness {
            left: pair.left,
            right: pair.right,
        },
        species,
        residue: 0,
        junction: (pair.left, pair.right),
        after: pair.distinguishing_word.clone(),
        reads,
        blocks_gained: 0,
    };
    let mut trial = prefix.to_vec();
    trial.push(candidate.clone());
    let gained = compress(&WidenedSystem {
        declared: system,
        founded: &trial,
    })
    .one_shot
    .len()
    .saturating_sub(reading.one_shot.len());
    if gained == 0 {
        return Err(FoundingRefusal::GainedNoBlock {
            left: pair.left,
            right: pair.right,
        });
    }

    Ok(FoundedReceiver {
        blocks_gained: gained,
        ..candidate
    })
}

/// Close a staged founding sequence into a [`FoundedPanel`], measuring residue over the settled
/// family.
///
/// [`found_to_exhaustion`] builds its panel on the way out; a staged sequence needs the same closure
/// so that the same organs read it — in particular [`FoundedPanel::capacities`], which is the
/// logical-resource face an interchange certificate has to compare.
pub fn panel_from_founded(
    system: &dyn ObservedSystem,
    mut founded: Vec<FoundedReceiver>,
    refused: Vec<FoundingRefusal>,
) -> FoundedPanel {
    let declared = system.receivers();
    let bound = system.items().len().saturating_sub(1);
    let before = compress(system);
    measure_residue(system, &mut founded);
    let settled = compress(&WidenedSystem {
        declared: system,
        founded: &founded,
    });
    let unwitnessed = settled
        .collapsed
        .iter()
        .filter(|pair| pair.witness.is_none())
        .count();
    FoundedPanel {
        declared,
        rounds: founded.len(),
        bound,
        one_shot_before: before.one_shot,
        one_shot_after: settled.one_shot,
        conduct: settled.conduct,
        unwitnessed_remaining: unwitnessed,
        founded,
        refused,
    }
}

/// The residue of each founded axis under the rest of the panel: `( ⋂_{s≠r} ≡_s ) ∖ ≡_r`.
///
/// Empty residue means the axis is redundant — removing it leaves the partition unmoved. This is
/// the measurement that makes the founded population non-monotone.
fn measure_residue(system: &dyn ObservedSystem, founded: &mut [FoundedReceiver]) {
    let items = system.items();
    let declared = system.receivers();
    let readings: Vec<BTreeMap<ItemId, Observation>> =
        founded.iter().map(|found| found.reads.clone()).collect();

    for (index, found) in founded.iter_mut().enumerate() {
        let mut unique = 0usize;
        for (place, left) in items.iter().enumerate() {
            for right in &items[place + 1..] {
                let mine = readings[index].get(left) != readings[index].get(right);
                if !mine {
                    continue;
                }
                let others_see = declared.iter().any(|receiver| {
                    system.observation(*left, *receiver) != system.observation(*right, *receiver)
                }) || readings.iter().enumerate().any(|(other, reading)| {
                    other != index && reading.get(left) != reading.get(right)
                });
                if !others_see {
                    unique += 1;
                }
            }
        }
        found.residue = unique;
    }
}

/// `gyr[a,b]` — the failure of two founding orders to commute.
///
/// Partition **joins** commute, so refining by two receivers in either order is the same. Founding
/// does not: a junction exists only relative to the panel standing when it is reached, so a
/// different first founding presents a different second junction.
///
/// What is returned is the finite holonomy face: two paths, one starting panel, and the
/// disagreement retained. `partitions_agree` is the endpoint; `founded_agree` is the path. **Equal
/// endpoints with different paths is exactly a holonomy** — and `CLAUDE.md`'s own law says equal
/// endpoints do not identify ordered paths.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Gyration {
    pub left_order: Vec<(ItemId, ItemId)>,
    pub right_order: Vec<(ItemId, ItemId)>,
    /// Both orders reached the same one-shot partition.
    pub partitions_agree: bool,
    /// Both orders reached the same conduct partition. This must hold: founding changes what is
    /// seen, never what the material does.
    pub conduct_agrees: bool,
    /// Both orders founded the same junctions in the same order.
    pub founded_agree: bool,
    /// The first place the two orders diverged, as `(step, left junction, right junction)`.
    pub divergence: Option<(usize, (ItemId, ItemId), (ItemId, ItemId))>,
    /// Junctions one order founded and the other never did — the gyration's own population.
    pub only_left: Vec<(ItemId, ItemId)>,
    pub only_right: Vec<(ItemId, ItemId)>,
}

impl Gyration {
    /// The holonomy: the two orders agree on where they arrived and disagree on how.
    pub const fn is_holonomy(&self) -> bool {
        self.partitions_agree && self.conduct_agrees && !self.founded_agree
    }

    /// The orbit is trivial — the two orders are one order, and the gauge measured nothing.
    pub const fn orbit_is_trivial(&self) -> bool {
        self.founded_agree
    }
}

/// **The gyration read as a group element, which is what this module's own bound asked for.**
///
/// The header quotes `papers/source/papers/knot-causal-topology/main.typ:314-332` naming the
/// object and stating its limit: *"The general object is **connection and holonomy**; the
/// gyroparallelogram is one exact hyperbolic specialization."* [`Gyration`] returns that holonomy as
/// three booleans and two lists — a flag. This returns it as an element of a group, and the group is
/// **read off the material rather than declared**.
///
/// ## The derivation, which authors nothing
///
/// Both orders found junctions and, when [`Gyration::is_holonomy`] holds, arrive at the same panel.
/// Out along one order and back along the other is therefore a **closed walk**. Over the junctions
/// **both** orders founded, the right order is a reordering of the left, and that reordering is a
/// permutation. It is the identity exactly when the two orders founded the shared population in the
/// same sequence.
///
/// ```text
///     shared = the junctions BOTH orders founded, in left order
///     π(i)   = the position, in the right order, of the junction the left order founded i-th
/// ```
///
/// Nothing is chosen: the population is the intersection, the ordering is each panel's own, and the
/// degree is `shared.len()` — read off, never authored.
///
/// ## Why this is worth having, in one line
///
/// `[S_n, S_n] = A_n`, so the abelianization of a symmetric group is **exactly the sign**. An
/// abelian holonomy on this material therefore carries **one bit** — even or odd. The group carries
/// the **cycle type**, which is the conjugacy class and is basepoint-free, as it must be: which
/// junction is founded "first" is a receiver-visible coordinate and promoting it into an invariant is
/// `CLAUDE.md` §0's fourth lesson.
///
/// > **The abelian reading keeps the sign and discards the turn.** `CLAUDE.md` §2b, on this body's
/// > own material: the discarded thing here is the cycle structure of the reordering.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GyrationHolonomy {
    /// The junctions both orders founded, in the left order. The walk is over exactly these.
    pub shared: Vec<(ItemId, ItemId)>,
    /// The reordering, as a group element over `shared.len()` points.
    pub permutation: crate::structure_group::GroupElement,
    /// Its conjugacy class in the symmetric group on `shared`. **The invariant.**
    pub class: crate::structure_group::GroupElement,
    /// The cycle type, ascending — the readable name of that class.
    pub cycle_type: Vec<usize>,
    /// The abelianized reading: `true` when the permutation is even. **This is the entire content an
    /// integer or `±` holonomy could have carried on this material.**
    pub is_even: bool,
    /// The walk closed carrying nothing: the two orders founded the shared population identically.
    pub is_trivial: bool,
    /// Junctions one order founded and the other never did. These are outside the shared walk and
    /// are retained rather than dropped, because a junction only one order reached is a real
    /// difference that no permutation of the intersection can express.
    pub unshared: usize,
}

/// Read a gyration as a group element. `None` when the two orders share no junction, so there is no
/// walk to take and the question is not posed.
pub fn gyration_holonomy(gyration: &Gyration) -> Option<GyrationHolonomy> {
    use crate::structure_group::GroupElement;

    let right_position: BTreeMap<(ItemId, ItemId), usize> = gyration
        .right_order
        .iter()
        .enumerate()
        .map(|(at, junction)| (*junction, at))
        .collect();
    // The shared population, in the LEFT order — the walk's own departure sequence.
    let shared: Vec<(ItemId, ItemId)> = gyration
        .left_order
        .iter()
        .filter(|junction| right_position.contains_key(*junction))
        .copied()
        .collect();
    if shared.is_empty() {
        return None;
    }
    // Rank the shared junctions by where the right order put them. Ranking rather than using the
    // raw right-order index is what makes this a permutation of `shared` and not of `right_order`.
    let mut by_right: Vec<usize> = (0..shared.len()).collect();
    by_right.sort_by_key(|at| right_position[&shared[*at]]);
    let mut permutation = vec![0u8; shared.len()];
    for (rank, from) in by_right.into_iter().enumerate() {
        permutation[from] = u8::try_from(rank).ok()?;
    }
    let element = GroupElement::Permutation(permutation.clone());
    let cycle_type = permutation_cycle_type(&permutation);

    // **The class is computed from the cycle type, and the symmetric group is never built.**
    //
    // Two permutations are conjugate in `S_n` exactly when their cycle types agree — a theorem, not
    // a search — so the class has a canonical representative: the cycles laid down consecutively in
    // ascending length. `structure_group::conjugacy_class` closes over the group's own elements,
    // which is right for the orders it was written against (`Q_8` at 8, `A_5` at 60) and is a cost
    // defect the moment a caller hands it a symmetric group. An earlier form of this function did
    // exactly that and the driver died at `S_19` — 19! elements, from a class the cycle type names
    // in linear time. `CLAUDE.md` §8: a cost law is a law, and an organ used past its declared
    // aperture is a defect even when it appears to return.
    let class = GroupElement::Permutation(canonical_class_representative(&cycle_type));
    // Parity from the cycle type: a k-cycle is odd exactly when k is even.
    let is_even = cycle_type.iter().filter(|length| **length % 2 == 0).count() % 2 == 0;

    Some(GyrationHolonomy {
        is_trivial: element.is_identity(),
        shared,
        permutation: element,
        class,
        cycle_type,
        is_even,
        unshared: gyration.only_left.len() + gyration.only_right.len(),
    })
}

/// The canonical member of the conjugacy class a cycle type names: the cycles laid down
/// consecutively, ascending. Two permutations of one degree are conjugate in `S_n` exactly when
/// their cycle types agree, so this is a complete invariant of the class and costs `O(n)`.
fn canonical_class_representative(cycle_type: &[usize]) -> Vec<u8> {
    let degree: usize = cycle_type.iter().sum();
    let mut representative = vec![0u8; degree];
    let mut at = 0usize;
    for length in cycle_type {
        for step in 0..*length {
            representative[at + step] = (at + (step + 1) % length) as u8;
        }
        at += length;
    }
    representative
}

/// The cycle type of a one-line permutation, ascending. Written here rather than borrowed because
/// `arithmetic_monodromy`'s is private to the quintic catalogue and returns `Vec<u32>` over a
/// different carrier; if a third caller appears, that is the moment to make one of them public
/// rather than to keep a third copy.
fn permutation_cycle_type(permutation: &[u8]) -> Vec<usize> {
    let mut visited = vec![false; permutation.len()];
    let mut lengths = Vec::new();
    for start in 0..permutation.len() {
        if visited[start] {
            continue;
        }
        let mut cursor = start;
        let mut length = 0usize;
        while !visited[cursor] {
            visited[cursor] = true;
            cursor = usize::from(permutation[cursor]);
            length += 1;
        }
        lengths.push(length);
    }
    lengths.sort_unstable();
    lengths
}

/// **The population an abelian holonomy collapses on this body's own gyrations.**
///
/// Pairs of readings that agree on parity — everything a `±` or integer holonomy carries — and
/// disagree on cycle type. This is `receiver_exact_compression`'s exact loss at the altitude of a
/// structure group, and it is the falsifier `crate::structure_group` declares: **a run returning an
/// empty population here has not shown the group doing anything**, and must say so rather than
/// presenting agreement as a result.
pub fn parity_collapsed_pairs(readings: &[GyrationHolonomy]) -> Vec<(usize, usize)> {
    let mut collapsed = Vec::new();
    for left in 0..readings.len() {
        for right in (left + 1)..readings.len() {
            // **Same degree, or the comparison is not a comparison.** Conjugacy is a relation
            // *within* one symmetric group, and parity is the sign character *of that group*. Two
            // readings over different shared populations live in different groups, so calling their
            // cycle types unequal says only that the walks had different lengths.
            //
            // The first form of this function omitted that guard and its driver reported a green
            // falsifier made entirely of identity permutations on 17, 18 and 19 points. `CLAUDE.md`
            // §8: a check whose material cannot vary the property under test is the same defect as a
            // check that cannot fail — this one wore a passing result while measuring length.
            if readings[left].shared.len() != readings[right].shared.len() {
                continue;
            }
            if readings[left].is_even == readings[right].is_even
                && readings[left].cycle_type != readings[right].cycle_type
            {
                collapsed.push((left, right));
            }
        }
    }
    collapsed
}

/// Run the founding twice, taking a different junction first, and return the gyration.
pub fn gyration(system: &dyn ObservedSystem) -> Gyration {
    let left = found_to_exhaustion(system, &[]);
    // Defer the junction the first order took first, so the second order must take another.
    let deferred: Vec<(ItemId, ItemId)> = left.founded.first().map(|f| f.junction).into_iter().collect();
    let right = found_to_exhaustion(system, &deferred);
    gyration_of(&left, &right)
}

/// The gyration between two founding orders already run. [`gyration`] is this over the two orders it
/// runs itself; a caller holding the panels — `crate::interchange` does — compares the same way
/// rather than re-running the founding.
pub fn gyration_of(left: &FoundedPanel, right: &FoundedPanel) -> Gyration {
    let left_order = left.order();
    let right_order = right.order();
    let divergence = left_order
        .iter()
        .zip(right_order.iter())
        .enumerate()
        .find(|(_, (a, b))| a != b)
        .map(|(step, (a, b))| (step, *a, *b));

    let left_set: BTreeSet<_> = left_order.iter().copied().collect();
    let right_set: BTreeSet<_> = right_order.iter().copied().collect();

    Gyration {
        partitions_agree: left.one_shot_after == right.one_shot_after,
        conduct_agrees: left.conduct == right.conduct,
        founded_agree: left_order == right_order,
        divergence,
        only_left: left_set.difference(&right_set).copied().collect(),
        only_right: right_set.difference(&left_set).copied().collect(),
        left_order,
        right_order,
    }
}

#[cfg(test)]
mod gyration_holonomy_tests {
    use super::*;

    fn junction(at: u64) -> (ItemId, ItemId) {
        (ItemId(at), ItemId(at + 100))
    }

    /// A gyration carrying two declared founding orders. The founding itself is exercised by the
    /// module's own tests; what is under test here is the **reading**.
    fn gyration_over(left: &[u64], right: &[u64]) -> Gyration {
        let left_order: Vec<_> = left.iter().copied().map(junction).collect();
        let right_order: Vec<_> = right.iter().copied().map(junction).collect();
        let left_set: BTreeSet<_> = left_order.iter().copied().collect();
        let right_set: BTreeSet<_> = right_order.iter().copied().collect();
        Gyration {
            divergence: left_order
                .iter()
                .zip(right_order.iter())
                .enumerate()
                .find(|(_, (a, b))| a != b)
                .map(|(step, (a, b))| (step, *a, *b)),
            only_left: left_set.difference(&right_set).copied().collect(),
            only_right: right_set.difference(&left_set).copied().collect(),
            founded_agree: left_order == right_order,
            partitions_agree: true,
            conduct_agrees: true,
            left_order,
            right_order,
        }
    }

    #[test]
    fn two_orders_that_founded_the_same_sequence_return_the_identity() {
        let reading = gyration_holonomy(&gyration_over(&[1, 2, 3], &[1, 2, 3])).expect("shares");
        assert!(reading.is_trivial);
        assert_eq!(reading.cycle_type, vec![1, 1, 1]);
        assert!(reading.is_even);
        assert_eq!(reading.unshared, 0);
    }

    #[test]
    fn a_reordering_returns_its_cycle_type_and_the_degree_is_read_off_the_shared_population() {
        // The right order swapped the last two. On two moved points that is a transposition.
        let reading = gyration_holonomy(&gyration_over(&[1, 2, 3], &[1, 3, 2])).expect("shares");
        assert!(!reading.is_trivial);
        assert_eq!(reading.shared.len(), 3, "the degree is the shared population");
        assert_eq!(reading.cycle_type, vec![1, 2]);
        assert!(!reading.is_even, "a transposition is odd");
    }

    #[test]
    fn junctions_only_one_order_founded_are_outside_the_walk_and_are_retained() {
        let reading = gyration_holonomy(&gyration_over(&[1, 2, 9], &[2, 1, 7])).expect("shares");
        assert_eq!(reading.shared, vec![junction(1), junction(2)]);
        assert_eq!(reading.unshared, 2, "9 and 7 are each founded by one order only");
        assert_eq!(reading.cycle_type, vec![2]);
    }

    #[test]
    fn orders_sharing_no_junction_pose_no_walk() {
        assert_eq!(gyration_holonomy(&gyration_over(&[1, 2], &[3, 4])), None);
    }

    /// **The falsifier, on gyrations.** `[S_n, S_n] = A_n`, so parity is the whole abelian reading.
    /// A 3-cycle and a double transposition are both **even** and are different classes, so an
    /// abelian holonomy calls them the same and the group does not.
    #[test]
    fn parity_collapses_two_readings_the_cycle_type_separates() {
        let three_cycle =
            gyration_holonomy(&gyration_over(&[1, 2, 3, 4], &[2, 3, 1, 4])).expect("shares");
        let double_transposition =
            gyration_holonomy(&gyration_over(&[1, 2, 3, 4], &[2, 1, 4, 3])).expect("shares");
        assert_eq!(three_cycle.cycle_type, vec![1, 3]);
        assert_eq!(double_transposition.cycle_type, vec![2, 2]);
        assert!(three_cycle.is_even && double_transposition.is_even);

        let collapsed = parity_collapsed_pairs(&[three_cycle, double_transposition]);
        assert_eq!(collapsed, vec![(0, 1)], "one bit cannot tell these apart");
    }

    /// **The control.** Readings of different parity are separated by the abelian reading too, so
    /// they are not in the collapsed population. Without this the test above would pass on an
    /// instrument that reported every pair.
    #[test]
    fn readings_of_different_parity_are_not_collapsed() {
        let transposition =
            gyration_holonomy(&gyration_over(&[1, 2, 3], &[2, 1, 3])).expect("shares");
        let three_cycle =
            gyration_holonomy(&gyration_over(&[1, 2, 3], &[2, 3, 1])).expect("shares");
        assert!(!transposition.is_even && three_cycle.is_even);
        assert!(parity_collapsed_pairs(&[transposition, three_cycle]).is_empty());
    }

    /// The conjugacy class is basepoint-free where the element is not — the same property
    /// `structure_group` proves on `Q_8`, holding on this material. Two gyrations that reorder
    /// different junctions by the same *shape* share a class and differ as elements.
    #[test]
    fn the_class_identifies_reorderings_of_the_same_shape_at_different_junctions() {
        let early = gyration_holonomy(&gyration_over(&[1, 2, 3], &[2, 1, 3])).expect("shares");
        let late = gyration_holonomy(&gyration_over(&[1, 2, 3], &[1, 3, 2])).expect("shares");
        assert_ne!(early.permutation, late.permutation, "different elements");
        assert_eq!(early.class, late.class, "one class");
        assert_eq!(early.cycle_type, late.cycle_type);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A system whose declared panel is blind to a terminus distinction.
    ///
    /// Items 0..4. Receiver 0 reads a parity that holds 0,2 together and 1,3 together. Input 0
    /// advances 0→2 and 1→3; item 2 continues under input 1 and item 3 does not. So conduct
    /// separates (0,1) at a terminus, and no declared receiver sees it: the junction.
    struct BlindPanel;

    impl ObservedSystem for BlindPanel {
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
            Observation(item.0 % 2)
        }
        fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
            match (item.0, input.0) {
                (0, 0) => Some(ItemId(2)),
                (1, 0) => Some(ItemId(3)),
                (2, 1) => Some(ItemId(2)),
                _ => None,
            }
        }
    }

    /// A system whose declared panel already witnesses everything. Founding must found nothing.
    struct SeeingPanel;

    impl ObservedSystem for SeeingPanel {
        fn items(&self) -> Vec<ItemId> {
            (0..3).map(ItemId).collect()
        }
        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }
        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0)]
        }
        fn observation(&self, item: ItemId, _receiver: ReceiverId) -> Observation {
            Observation(item.0)
        }
        fn successor(&self, item: ItemId, _input: InputId) -> Option<ItemId> {
            Some(ItemId((item.0 + 1) % 3))
        }
    }

    #[test]
    fn a_junction_is_a_pair_conduct_separates_and_no_receiver_witnesses() {
        let reading = compress(&BlindPanel);
        let blind: Vec<&CollapsedPair> = reading
            .collapsed
            .iter()
            .filter(|pair| pair.witness.is_none())
            .collect();
        assert!(
            !blind.is_empty(),
            "the fixture must actually present a junction, or every control below is vacuous"
        );
        assert!(blind.iter().all(|pair| pair.separated_by_terminus));
    }

    #[test]
    fn founding_closes_the_junction_it_was_founded_for() {
        let panel = found_to_exhaustion(&BlindPanel, &[]);
        assert!(panel.rounds > 0, "a junction stood and nothing was founded");
        assert!(
            panel.exhausted(),
            "founding must reach exhaustion: {} unwitnessed remain",
            panel.unwitnessed_remaining
        );
    }

    #[test]
    fn the_founded_reading_is_the_material_and_separates_something() {
        let panel = found_to_exhaustion(&BlindPanel, &[]);
        let found = &panel.founded[0];
        // The reading is the aperture AT THE JUNCTION'S OWN WORD, verbatim off the system. A
        // global reading founds the same receiver at every junction, so one founding closes them
        // all — measured on the development, 318 junctions closed by one receiver, and the gyration
        // then distinguished provenance rather than content.
        for item in BlindPanel.items() {
            assert_eq!(
                found.reads[&item],
                aperture_after(&BlindPanel, item, &found.after),
                "a founded reading is the material's, read from where the junction is"
            );
        }
        assert!(found.blocks_gained > 0, "a founding that founds nothing is refused");
    }

    #[test]
    fn founding_sharpens_what_is_seen_and_never_what_conduct_does() {
        let before = compress(&BlindPanel);
        let panel = found_to_exhaustion(&BlindPanel, &[]);
        assert_eq!(
            before.conduct, panel.conduct,
            "the Nerode congruence is an invariant of the material; founding may not move it"
        );
        assert!(
            panel.one_shot_after.len() > panel.one_shot_before.len(),
            "the panel grew, so the one-shot reading must be strictly finer"
        );
    }

    #[test]
    fn the_null_a_seeing_panel_founds_nothing() {
        let panel = found_to_exhaustion(&SeeingPanel, &[]);
        assert_eq!(
            panel.rounds, 0,
            "a panel that already witnesses everything must found nothing; \
             founding on a system with no junction would make the law unfalsifiable"
        );
        assert!(panel.exhausted());
        assert!(panel.founded.is_empty());
    }

    #[test]
    fn founding_is_bounded_by_the_population() {
        let panel = found_to_exhaustion(&BlindPanel, &[]);
        assert!(
            panel.rounds <= panel.bound,
            "each founding strictly refines a finite partition, so foundings are bounded by |items| - 1"
        );
        assert_eq!(panel.bound, BlindPanel.items().len() - 1);
    }

    #[test]
    fn a_receiver_that_cannot_see_its_own_junction_is_refused_by_name() {
        // Every item has the same aperture, so the founded reading separates nothing.
        struct UniformAperture;
        impl ObservedSystem for UniformAperture {
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
                (item.0 < 2).then(|| ItemId(item.0 + 1))
            }
        }
        let panel = found_to_exhaustion(&UniformAperture, &[]);
        // Either it founded nothing lawfully, or it refused by name. Never a silent skip.
        assert!(
            panel.exhausted() || !panel.refused.is_empty(),
            "an unwitnessed junction that cannot be founded must be REFUSED, not passed over"
        );
    }

    #[test]
    fn residue_is_empty_exactly_when_the_axis_is_redundant() {
        let panel = found_to_exhaustion(&BlindPanel, &[]);
        let items = BlindPanel.items();
        for found in &panel.founded {
            // Recompute the definition directly: pairs every OTHER receiver identifies and this
            // one separates. `( ⋂_{s≠r} ≡_s ) ∖ ≡_r`.
            let mut counted = 0usize;
            for (place, left) in items.iter().enumerate() {
                for right in &items[place + 1..] {
                    let mine = found.reads.get(left) != found.reads.get(right);
                    let others = BlindPanel.receivers().iter().any(|receiver| {
                        BlindPanel.observation(*left, *receiver)
                            != BlindPanel.observation(*right, *receiver)
                    }) || panel.founded.iter().any(|other| {
                        other.id != found.id && other.reads.get(left) != other.reads.get(right)
                    });
                    if mine && !others {
                        counted += 1;
                    }
                }
            }
            assert_eq!(found.residue, counted, "the residue is the definition, recomputed");
        }
    }

    #[test]
    fn capacity_is_the_residue_and_an_empty_residue_takes_the_minimum() {
        let panel = found_to_exhaustion(&BlindPanel, &[]);
        let capacities = panel.capacities();
        for found in &panel.founded {
            assert_eq!(
                capacities[&found.id],
                BigUint::from(found.residue) + BigUint::one(),
                "capacity is the residue; the +1 is forced by set_site_capacity refusing zero"
            );
            // An empty residue is not deleted -- it takes capacity 1, the MOST congested route,
            // so it dilates maximally under any co-present demand rather than being chosen against.
            if found.residue == 0 {
                assert_eq!(capacities[&found.id], BigUint::one());
            }
        }
    }

    #[test]
    fn found_at_takes_the_declared_junction_and_agrees_with_the_run_that_chose_it() {
        let standing = standing_junctions(&BlindPanel, &[]);
        assert!(!standing.is_empty(), "the fixture must present a junction");
        let junction = (standing[0].left, standing[0].right);
        let staged = found_at(&BlindPanel, &[], junction).expect("a standing junction founds");
        let run = found_to_exhaustion(&BlindPanel, &[]);
        // The run chose the same first junction, so the two must agree on everything that is not a
        // mint ordinal: the junction, the word it reads from, and what it returns for every item.
        assert_eq!(staged.junction, run.founded[0].junction);
        assert_eq!(staged.after, run.founded[0].after);
        assert_eq!(staged.reads, run.founded[0].reads);
    }

    #[test]
    fn found_at_refuses_a_junction_that_is_not_standing_by_name() {
        // A pair the declared panel already separates one-shot is not a junction.
        let refusal = found_at(&SeeingPanel, &[], (ItemId(0), ItemId(1)))
            .expect_err("a fully witnessing panel presents no junction");
        assert_eq!(
            refusal,
            FoundingRefusal::NotAStandingJunction {
                left: ItemId(0),
                right: ItemId(1)
            }
        );
    }

    /// `GainedNoBlock` is a **defence, not a measured refusal**, and this states why rather than
    /// leaving a branch that cannot fire.
    ///
    /// A blindness founding is admitted only after `DoesNotSeparateItsJunction` has passed, which
    /// means the reading separates a pair the present one-shot partition held in one block. Splitting
    /// a block strictly refines, so the block count must rise. The assertion below is that statement
    /// over the declared material: every junction that survives the separation check gains.
    #[test]
    fn separating_its_own_junction_implies_gaining_a_block() {
        for standing in standing_junctions(&BlindPanel, &[]) {
            match found_at(&BlindPanel, &[], (standing.left, standing.right)) {
                Ok(found) => assert!(
                    found.blocks_gained > 0,
                    "a founding that separated its junction must have split a block"
                ),
                Err(FoundingRefusal::GainedNoBlock { .. }) => panic!(
                    "GainedNoBlock fired, so the reasoning above is wrong and the branch is a \
                     measured refusal rather than a defence"
                ),
                Err(_) => {}
            }
        }
    }

    #[test]
    fn a_staged_panel_measures_its_residue_and_carries_its_capacities() {
        let standing = standing_junctions(&BlindPanel, &[]);
        let found = found_at(&BlindPanel, &[], (standing[0].left, standing[0].right))
            .expect("a standing junction founds");
        let id = found.id;
        let panel = panel_from_founded(&BlindPanel, vec![found], Vec::new());
        assert_eq!(panel.rounds, 1);
        let capacities = panel.capacities();
        assert_eq!(
            capacities[&id],
            BigUint::from(panel.founded[0].residue) + BigUint::one(),
            "capacity is the residue measured over the settled family, plus the forced one"
        );
        assert_eq!(panel.conduct, compress(&BlindPanel).conduct, "conduct is invariant");
    }

    #[test]
    fn the_gyration_returns_both_orders_and_says_when_the_orbit_is_trivial() {
        let gyr = gyration(&BlindPanel);
        // Conduct must agree under every order — this is the law, not the finding.
        assert!(
            gyr.conduct_agrees,
            "founding order may not move the Nerode congruence"
        );
        // The orbit may be trivial on this fixture, and if it is the reading must say so rather
        // than reporting an agreement as evidence.
        if gyr.orbit_is_trivial() {
            assert_eq!(gyr.divergence, None);
            assert!(gyr.only_left.is_empty() && gyr.only_right.is_empty());
        } else {
            assert!(gyr.divergence.is_some(), "a non-trivial orbit diverges somewhere");
        }
    }
}
