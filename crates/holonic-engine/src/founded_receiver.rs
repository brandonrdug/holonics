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
    /// **Silt.** How many pairs this axis separates that **no other receiver in the final panel
    /// separates**. Zero means the channel carries nothing of its own.
    ///
    /// Brandon, 2026-08-09: *"More joints != survival and propagation… The channel for water that
    /// has none flowing will experience nothing but the collection of debris, where the collection
    /// of debris changes the potential of how gradients of current can flow in the future."* A
    /// founded axis is not free and does not stay neutral: one that carries no unique current has
    /// silted, and [`FoundedPanel::silted`] returns them. This is what stops "more axes" from being
    /// monotone.
    pub unique_separations: usize,
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

    /// Founded axes carrying no current of their own — the silted channels.
    pub fn silted(&self) -> Vec<&FoundedReceiver> {
        self.founded
            .iter()
            .filter(|found| found.unique_separations == 0)
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
struct WidenedSystem<'a> {
    declared: &'a dyn ObservedSystem,
    founded: &'a [FoundedReceiver],
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

    loop {
        let widened = WidenedSystem {
            declared: system,
            founded: &founded,
        };
        let reading = compress(&widened);

        // Deferred junctions are passed over first, then admitted once nothing else stands.
        let junction = reading
            .collapsed
            .iter()
            .find(|pair| pair.witness.is_none() && !deferred.contains(&(pair.left, pair.right)))
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
                        unique_separations: 0,
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
                        unique_separations: 0,
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
            measure_silt(system, &mut founded);
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
                unique_separations: 0,
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
            unique_separations: 0,
            junction: (pair.left, pair.right),
            after: pair.distinguishing_word.clone(),
            reads,
            blocks_gained: gained,
        });
        next_id += 1;
    }
}

/// **Silt.** For each founded axis, how many pairs it separates that no other receiver separates.
///
/// A channel with no current of its own has collected debris. This is the measurement that makes
/// the founded population non-monotone: adding an axis is not automatically a gain, and an axis
/// that carries nothing unique is reported rather than counted.
fn measure_silt(system: &dyn ObservedSystem, founded: &mut [FoundedReceiver]) {
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
        found.unique_separations = unique;
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

/// Run the founding twice, taking a different junction first, and return the gyration.
pub fn gyration(system: &dyn ObservedSystem) -> Gyration {
    let left = found_to_exhaustion(system, &[]);
    // Defer the junction the first order took first, so the second order must take another.
    let deferred: Vec<(ItemId, ItemId)> = left.founded.first().map(|f| f.junction).into_iter().collect();
    let right = found_to_exhaustion(system, &deferred);

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
