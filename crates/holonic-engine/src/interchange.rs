//! The interchange certificate: two orders commute exactly when no receiver separates them.
//!
//! `blueprint/PURE_HOLONIC_ENGINE.md:170-174` specifies an `InterchangeCertificate` in prose and
//! **no code owns it**. Both halves exist: `founded_receiver::gyration` measures the failure of two
//! founding orders to commute, and `receiver_exact_compression` returns the shortest **separating
//! word** per collapsed pair. This module is the edge between them.
//!
//! ## What the certificate decides, and against which family
//!
//! Brandon, 2026-08-09: *"the receiver does not necessarily refer to an actively founding set of
//! leader arcs, it can refer to a previously founded region's perspectives."* So the receiver family
//! for *"may these two occurrences interchange"* is **not the live front**. It is what the
//! already-founded regions can distinguish.
//!
//! ```text
//!   two orders INTERCHANGE  <->  no receiver in that family has a distinguishing word for them
//! ```
//!
//! That is the Nerode partition of [`crate::receiver_exact_compression`] pointed at **orders**
//! instead of at items, and the refusal is a first-class return:
//! [`Interchange::Ordered`] carries the [`DistinguishingWord`] that refused it.
//!
//! ## Endpoint equality is NOT the certificate
//!
//! `canon/01_CAUSAL_CALCULUS.md:85-89` and
//! `research/records/2026-08-01_THE_HARDWARE_IS_A_RECEIVER_COVER_THE_CARD_MUST_CARRY_THE_CURRENT.md`
//! agree on the point and the second is RATIFIED: two events belong to the independence relation
//! only when their complete exact consequences commute, *"including lineage, radiation, obstruction,
//! and changed morphology"*, and *"a common label, collection, or lack of a visible edge does not
//! prove independence."* A certificate that compared only final states would be the defect
//! `2026-08-02_THE_HOST_FOREMAN...` convicts — *"Endpoint equality became stateful equivalence."*
//!
//! [`InterchangeCertificate::endpoint_only_verdict`] therefore computes what such a comparator
//! *would* have said and keeps it beside the real verdict, so the disagreement is legible rather
//! than argued. [`InterchangeCertificate::lineage_changed_the_verdict`] is true exactly when the two
//! differ, and it is true on `soma/formal`.
//!
//! ## Which coordinates are compared, and which are refused as frames
//!
//! | coordinate | compared? | why |
//! |---|---|---|
//! | conduct partition | **yes**, as law | founding sharpens what is seen, never what the material does |
//! | one-shot partition | yes | the endpoint |
//! | the equivalence on items, pair for pair | yes | block-set equality is the same statement, stated so a separating pair can be exhibited |
//! | the founded content — junction, species, word, reading | **yes** | the lineage; this is the test endpoint comparison lacks |
//! | capacity per axis, from [`crate::founded_receiver::FoundedPanel::capacities`] | yes | the blueprint's *"other successor … logical resources"* |
//! | `ReceiverId` | **no** | a mint ordinal. `CLAUDE.md` §0 lesson 2: no absolute frame in a lineage. Recorded in `minted` so a caller can watch it move under a comparison that must not depend on it |
//! | `blocks_gained` | **no** | a staging coordinate: what one founding gained *at the moment it was staged*, against a prefix that differs by construction. The combined gain is compared — it is the endpoint |
//! | the staged sequence itself | **no** | it is the variable |
//!
//! ## The three-or-more case
//!
//! `canon/01_CAUSAL_CALCULUS.md:88`: *"For three or more events, adjacent interchange must satisfy
//! the relevant braid/coherence diagrams; pairwise equal endpoints alone are insufficient."*
//! [`certify_pair`] returns [`Coherence::PairwiseOnly`] and names what a triple would require; it
//! does not claim a triple. [`certify_set`] discharges the obligation by **rebasing every
//! permutation of the caller's declared occurrence set** and requiring all of them to agree, which
//! is strictly stronger than pairwise. The set size is the caller's declaration, never a level
//! authored here.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;
use serde::{Deserialize, Serialize};

use crate::founded_receiver::{
    found_at, found_to_exhaustion, gyration_of, panel_from_founded, AxisSpecies, FoundedPanel,
    FoundedReceiver, FoundingRefusal, Gyration, WidenedSystem,
};
use crate::receiver_exact_compression::{
    compress, CollapsedPair, InputId, ItemId, ObservedSystem, Observation, Partition, ReceiverId,
};

/// One staged occurrence, named by the junction it founds a receiver at.
///
/// The **footprint** is the pair it must separate. `canon/01_CAUSAL_CALCULUS.md:85`: disjoint
/// read/write support is sufficient *"only when no hidden allocator, lineage mint, port, resource
/// state, or other owner is shared"* — and here the mint, the panel, and the junction population are
/// all shared, so disjointness of the footprints proves nothing on its own and this type carries no
/// independence claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct StagedFootprint {
    pub junction: (ItemId, ItemId),
}

impl StagedFootprint {
    pub const fn at(left: ItemId, right: ItemId) -> Self {
        Self {
            junction: (left, right),
        }
    }
}

/// One founded axis, keyed by **content** rather than by mint order.
///
/// A `ReceiverId` is the ordinal the panel happened to hand out, so two orders founding the same
/// axis mint different ids for it. Comparing ids would refuse every interchange and comparing
/// nothing but the endpoint would admit too many; the axis is the junction it was founded at, the
/// species of reading, the word it reads *from*, and what it returns for every item.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct FoundedAxis {
    pub junction: (ItemId, ItemId),
    pub species: AxisSpecies,
    pub after: Vec<InputId>,
    pub reads: BTreeMap<ItemId, Observation>,
}

impl FoundedAxis {
    pub fn of(found: &FoundedReceiver) -> Self {
        Self {
            junction: found.junction,
            species: found.species,
            after: found.after.clone(),
            reads: found.reads.clone(),
        }
    }
}

/// The predecessor the occurrences are staged over: one panel, named exactly.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Predecessor {
    pub declared: Vec<ReceiverId>,
    /// Axes already founded before staging — *"a previously founded region's perspectives"*.
    pub prefix: Vec<FoundedAxis>,
    pub one_shot: Partition,
    pub conduct: Partition,
    /// Junctions standing against this predecessor. A staged occurrence must be one of these.
    pub standing_junctions: Vec<(ItemId, ItemId)>,
}

/// One order, rebased over the predecessor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RebasedOrder {
    /// The junctions this order was asked to found, in order.
    pub staged: Vec<(ItemId, ItemId)>,
    /// The junctions it actually founded, in order. Shorter than `staged` when rebasing refused.
    pub founded: Vec<(ItemId, ItemId)>,
    /// The full receivers, retained so a separating pair can be traced back to the axis that saw it.
    pub receivers: Vec<FoundedReceiver>,
    /// The mint ordinals in staging order. **Recorded and never compared** — an absolute frame.
    ///
    /// Note that this sequence is `[first, second, …]` in *every* order, because the ordinal is
    /// handed out by position. What actually moves between orders is which **axis** received which
    /// ordinal, and that is [`RebasedOrder::mint_frame`].
    pub minted: Vec<ReceiverId>,
    /// Which mint ordinal each staged axis received. This is the frame the comparison must not
    /// depend on, exposed so a caller can watch it move while the verdict does not.
    pub mint_frame: BTreeMap<FoundedAxis, ReceiverId>,
    /// The staged part of the delta, content-keyed and therefore order-free by construction.
    pub delta: BTreeSet<FoundedAxis>,
    /// Where rebasing refused, if it did.
    pub refusal: Option<(usize, FoundingRefusal)>,
    pub one_shot: Partition,
    pub conduct: Partition,
    /// The equivalence on items, pair for pair.
    pub identified: BTreeSet<(ItemId, ItemId)>,
    /// The logical resource each axis carries, from `FoundedPanel::capacities`, re-keyed off the
    /// mint ordinal onto the axis content.
    pub capacities: Vec<(FoundedAxis, BigUint)>,
    /// What each founding gained **at the moment it was staged**. A staging coordinate: it is
    /// measured against a prefix that differs between orders by construction, so it is recorded and
    /// not compared. The *combined* gain is the endpoint and is compared.
    pub blocks_gained: Vec<usize>,
}

impl RebasedOrder {
    pub fn rebased(&self) -> bool {
        self.refusal.is_none()
    }

    /// The combined gain: one-shot blocks the whole order added to the predecessor. This is the
    /// order-free part of `blocks_gained`, and it is a function of the endpoint.
    pub fn combined_gain(&self, predecessor: &Partition) -> usize {
        self.one_shot.len().saturating_sub(predecessor.len())
    }
}

/// What refused an interchange, exhibited.
///
/// `CLAUDE.md` §9: *"a returned obstruction must itself be returned and inspected"*. Every species
/// below carries the material that refused, not a count of refusals.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DistinguishingWord {
    /// **A receiver founded by one order separates a pair another order's panel identifies.** The
    /// family has a word for the two orders, and the word is the one
    /// `receiver_exact_compression` returns for that pair under the panel that could not see it.
    ReceiverSeparates {
        pair: (ItemId, ItemId),
        separating_order: usize,
        identifying_order: usize,
        /// The mint ordinal of the axis that separated it, for provenance only.
        receiver: ReceiverId,
        axis: FoundedAxis,
        separating_observations: (Observation, Observation),
        /// The pair as `receiver_exact_compression` exhibits it under the identifying order:
        /// the shortest input word after which conduct separates it, and the receiver that finally
        /// sees the difference — or `None`, when conduct does not separate it there at all.
        collapsed_under_identifying_order: Option<CollapsedPair>,
    },
    /// **A staged occurrence stopped being a junction once another had been founded.** Rebasing is
    /// not lawful in this order, so the two occurrences are not independent and the front stays
    /// ordered. The blueprint's *"lawful rebasing in both orders"* failing is a refusal, not an
    /// error.
    RebaseRefused {
        order: usize,
        step: usize,
        junction: (ItemId, ItemId),
        refusal: FoundingRefusal,
        /// The receiver that witnesses the junction now, with what it returned for the two items
        /// and after which word — a distinguishing word for the pair, held by the panel the earlier
        /// founding produced.
        now_witnessed_by: Option<(ReceiverId, Observation, Observation, Vec<InputId>)>,
    },
    /// **Every order reached the same endpoint and the same equivalence, and founded different
    /// content.** Equal endpoints do not identify ordered paths.
    LineageDiverges {
        /// The first step at which two orders founded different junctions, if they are comparable
        /// step for step.
        step: Option<usize>,
        /// Per order, the axes only that order founded.
        only_in: Vec<(usize, Vec<FoundedAxis>)>,
    },
    /// Endpoint, equivalence and content all agree; a successor logical resource does not.
    ResourcesDiffer {
        orders: (usize, usize),
        axis: FoundedAxis,
        capacities: (BigUint, BigUint),
    },
    /// The conduct partition moved between orders. Founding may not do that
    /// (`founded_receiver.rs`: *"founding sharpens what is seen, never what conduct does"*). If this
    /// fires, the law is violated; the certificate reports it and refuses rather than grading it.
    ConductMoved { orders: (usize, usize) },
}

/// The verdict. Refusal is a first-class return.
///
/// `clippy::large_enum_variant` is allowed here deliberately: the refusal carries the material that
/// refused it — the pair, the axis, the collapsed pair with its word — and `CLAUDE.md` §9 requires a
/// returned obstruction to *be* returned rather than referenced. One verdict is constructed per
/// certificate, so the size is paid once and the artifact stays in hand.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Interchange {
    /// Every declared order rebased lawfully and no receiver in the family separates them.
    Interchangeable,
    /// The front remains ordered, and this is why.
    Ordered { because: DistinguishingWord },
}

/// How far the coherence obligation was discharged.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Coherence {
    /// Two occurrences were staged and both orders compared. **This is a pairwise claim only.**
    /// See [`Coherence::TRIPLE_REQUIRES`].
    PairwiseOnly,
    /// Every permutation of the declared occurrence set was rebased and compared — strictly stronger
    /// than pairwise, and what `canon/01_CAUSAL_CALCULUS.md:88` asks for on a declared set.
    AllOrders {
        occurrences: usize,
        orders_compared: usize,
        orders_lawful: usize,
        agreed: bool,
    },
}

impl Coherence {
    /// What a triple would require, named rather than assumed.
    pub const TRIPLE_REQUIRES: &'static str = "\
pairwise interchange does not compose. `canon/01_CAUSAL_CALCULUS.md:88`: for three or more events \
adjacent interchange must satisfy the relevant braid/coherence diagrams, and pairwise equal \
endpoints alone are insufficient. On a declared set {a,b,c} that is: all 6 orders rebase lawfully, \
all 6 reach one endpoint, one equivalence, one content-keyed delta and one capacity vector -- and \
the two adjacent-transposition routes from abc to cba agree, which all-6-agree implies. Use \
`certify_set` to take it; this certificate stages two occurrences and claims nothing about a third.";
}

/// The certificate. Every field the blueprint names, and the two comparisons kept apart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterchangeCertificate {
    pub schema: String,
    /// One predecessor.
    pub predecessor: Predecessor,
    /// The staged footprints.
    pub staged: Vec<StagedFootprint>,
    /// Lawful rebasing in every declared order — or the refusal.
    pub orders: Vec<RebasedOrder>,
    pub all_rebased: bool,
    /// Founding may not move the Nerode congruence. This is the law, not the finding.
    pub conduct_agrees: bool,
    /// Every order reached the same one-shot partition.
    pub endpoints_agree: bool,
    /// Every order induces the same equivalence on items, pair for pair.
    pub identified_agrees: bool,
    /// The canonical combined delta — `Some` exactly when every order founded the same content.
    pub combined_delta: Option<BTreeSet<FoundedAxis>>,
    /// Every order carries the same capacity per axis.
    pub capacities_agree: bool,
    /// The lineage test: content and resources both agree.
    pub lineage_agrees: bool,
    /// The mint ordinals differ across orders for the same axis. Recorded so the reader can see
    /// that the comparison did not depend on them.
    pub minted_ids_differ: bool,
    pub verdict: Interchange,
    pub coherence: Coherence,
    /// The gyration, when the orders were complete founding runs rather than staged occurrences.
    /// `Gyration::founded_agree` compares the ordered SEQUENCE, which is the wrong comparison for an
    /// interchange question — the sequence differing is the premise. `combined_delta` is the right
    /// one and the two disagree on real material.
    pub gyration: Option<Gyration>,
}

impl InterchangeCertificate {
    pub fn is_interchangeable(&self) -> bool {
        matches!(self.verdict, Interchange::Interchangeable)
    }

    /// **What a certificate comparing only final states would have returned.**
    ///
    /// Kept beside the real verdict so the convicted defect is legible rather than argued:
    /// `2026-08-02_THE_HOST_FOREMAN...`, *"Endpoint equality became stateful equivalence."*
    pub fn endpoint_only_verdict(&self) -> bool {
        self.all_rebased && self.conduct_agrees && self.endpoints_agree
    }

    /// True exactly when comparing lineage refused something endpoint comparison would have
    /// admitted, or admitted something it would have refused.
    pub fn lineage_changed_the_verdict(&self) -> bool {
        self.endpoint_only_verdict() != self.is_interchangeable()
    }

    /// The refusal, if there is one.
    pub fn because(&self) -> Option<&DistinguishingWord> {
        match &self.verdict {
            Interchange::Interchangeable => None,
            Interchange::Ordered { because } => Some(because),
        }
    }
}

// ---------------------------------------------------------------------------------------------
// staging
// ---------------------------------------------------------------------------------------------

/// Rebase one declared order over the predecessor, stopping at the first refusal.
fn rebase(
    system: &dyn ObservedSystem,
    prefix: &[FoundedReceiver],
    sequence: &[(ItemId, ItemId)],
) -> RebasedOrder {
    let mut standing: Vec<FoundedReceiver> = prefix.to_vec();
    let mut taken = Vec::new();
    let mut minted = Vec::new();
    let mut refusal = None;

    for (step, junction) in sequence.iter().enumerate() {
        match found_at(system, &standing, *junction) {
            Ok(found) => {
                minted.push(found.id);
                taken.push(found.junction);
                standing.push(found);
            }
            Err(err) => {
                refusal = Some((step, err));
                break;
            }
        }
    }

    let panel = panel_from_founded(system, standing, Vec::new());
    order_from_panel(&panel, prefix.len(), sequence.to_vec(), taken, minted, refusal)
}

/// Close a settled panel into a comparable order.
fn order_from_panel(
    panel: &FoundedPanel,
    prefix_len: usize,
    staged: Vec<(ItemId, ItemId)>,
    founded: Vec<(ItemId, ItemId)>,
    minted: Vec<ReceiverId>,
    refusal: Option<(usize, FoundingRefusal)>,
) -> RebasedOrder {
    let capacities_by_id = panel.capacities();
    let staged_axes = &panel.founded[prefix_len.min(panel.founded.len())..];
    let mut capacities: Vec<(FoundedAxis, BigUint)> = staged_axes
        .iter()
        .map(|found| {
            (
                FoundedAxis::of(found),
                capacities_by_id
                    .get(&found.id)
                    .cloned()
                    .unwrap_or_else(BigUint::default),
            )
        })
        .collect();
    capacities.sort();

    RebasedOrder {
        staged,
        founded,
        minted,
        mint_frame: staged_axes
            .iter()
            .map(|found| (FoundedAxis::of(found), found.id))
            .collect(),
        delta: staged_axes.iter().map(FoundedAxis::of).collect(),
        blocks_gained: staged_axes.iter().map(|found| found.blocks_gained).collect(),
        capacities,
        receivers: panel.founded.clone(),
        refusal,
        one_shot: panel.one_shot_after.clone(),
        conduct: panel.conduct.clone(),
        identified: panel.one_shot_after.identified_pairs(),
    }
}

fn predecessor_of(system: &dyn ObservedSystem, prefix: &[FoundedReceiver]) -> Predecessor {
    let widened = WidenedSystem {
        declared: system,
        founded: prefix,
    };
    let reading = compress(&widened);
    Predecessor {
        declared: system.receivers(),
        prefix: prefix.iter().map(FoundedAxis::of).collect(),
        standing_junctions: reading
            .collapsed
            .iter()
            .filter(|pair| pair.witness.is_none())
            .map(|pair| (pair.left, pair.right))
            .collect(),
        one_shot: reading.one_shot,
        conduct: reading.conduct,
    }
}

/// Every permutation of a declared population, in lexicographic order of the original indices.
fn permutations<T: Clone>(items: &[T]) -> Vec<Vec<T>> {
    if items.is_empty() {
        return vec![Vec::new()];
    }
    let mut all = Vec::new();
    for index in 0..items.len() {
        let mut rest = items.to_vec();
        let head = rest.remove(index);
        for tail in permutations(&rest) {
            let mut one = Vec::with_capacity(items.len());
            one.push(head.clone());
            one.extend(tail);
            all.push(one);
        }
    }
    all
}

// ---------------------------------------------------------------------------------------------
// the certificate
// ---------------------------------------------------------------------------------------------

/// **Certify whether two staged occurrences may interchange over one predecessor.**
///
/// Rebases `[a, b]` and `[b, a]`, compares endpoint, equivalence, content and resources, and returns
/// [`Coherence::PairwiseOnly`]. It claims nothing about a third occurrence.
pub fn certify_pair(
    system: &dyn ObservedSystem,
    prefix: &[FoundedReceiver],
    a: StagedFootprint,
    b: StagedFootprint,
) -> InterchangeCertificate {
    let orders = vec![
        rebase(system, prefix, &[a.junction, b.junction]),
        rebase(system, prefix, &[b.junction, a.junction]),
    ];
    assemble(
        system,
        prefix,
        vec![a, b],
        orders,
        Coherence::PairwiseOnly,
        None,
    )
}

/// **Certify a declared occurrence SET, over every permutation of it.**
///
/// This discharges the three-or-more obligation on the declared set rather than inferring it from
/// pairs: `n!` orders are rebased and all are required to agree. The set is the caller's; nothing
/// here bounds it.
pub fn certify_set(
    system: &dyn ObservedSystem,
    prefix: &[FoundedReceiver],
    staged: &[StagedFootprint],
) -> InterchangeCertificate {
    let sequences = permutations(
        &staged
            .iter()
            .map(|footprint| footprint.junction)
            .collect::<Vec<_>>(),
    );
    let orders: Vec<RebasedOrder> = sequences
        .iter()
        .map(|sequence| rebase(system, prefix, sequence))
        .collect();
    let lawful = orders.iter().filter(|order| order.rebased()).count();
    let coherence = Coherence::AllOrders {
        occurrences: staged.len(),
        orders_compared: orders.len(),
        orders_lawful: lawful,
        agreed: false,
    };
    let certificate = assemble(system, prefix, staged.to_vec(), orders, coherence, None);
    let agreed = certificate.is_interchangeable();
    InterchangeCertificate {
        coherence: match certificate.coherence {
            Coherence::AllOrders {
                occurrences,
                orders_compared,
                orders_lawful,
                ..
            } => Coherence::AllOrders {
                occurrences,
                orders_compared,
                orders_lawful,
                agreed,
            },
            other => other,
        },
        ..certificate
    }
}

/// **Certify the two COMPLETE founding orders `gyration` runs**, rather than two staged occurrences.
///
/// `found_to_exhaustion` chooses its own junctions; deferring the first one it took forces the other
/// order to choose differently. The two runs may then found different *sets* of axes, which is what
/// makes this the interesting instance: on real material both orders reach the same partition by
/// different junctions, and a certificate that stopped at the endpoint would admit an interchange
/// the lineage refuses.
pub fn certify_founding_orders(system: &dyn ObservedSystem) -> InterchangeCertificate {
    let left = found_to_exhaustion(system, &[]);
    let deferred: Vec<(ItemId, ItemId)> = left
        .founded
        .first()
        .map(|found| found.junction)
        .into_iter()
        .collect();
    let right = found_to_exhaustion(system, &deferred);
    let gyration = gyration_of(&left, &right);

    let orders = vec![
        order_from_panel(
            &left,
            0,
            left.order(),
            left.order(),
            left.founded.iter().map(|found| found.id).collect(),
            None,
        ),
        order_from_panel(
            &right,
            0,
            right.order(),
            right.order(),
            right.founded.iter().map(|found| found.id).collect(),
            None,
        ),
    ];
    let staged: Vec<StagedFootprint> = left
        .order()
        .into_iter()
        .map(|junction| StagedFootprint { junction })
        .collect();
    assemble(
        system,
        &[],
        staged,
        orders,
        Coherence::PairwiseOnly,
        Some(gyration),
    )
}

/// The comparison. Everything above assembles orders; this decides.
fn assemble(
    system: &dyn ObservedSystem,
    prefix: &[FoundedReceiver],
    staged: Vec<StagedFootprint>,
    orders: Vec<RebasedOrder>,
    coherence: Coherence,
    gyration: Option<Gyration>,
) -> InterchangeCertificate {
    let predecessor = predecessor_of(system, prefix);

    let all_rebased = orders.iter().all(RebasedOrder::rebased);
    let conduct_agrees = orders.windows(2).all(|pair| pair[0].conduct == pair[1].conduct);
    let endpoints_agree = orders
        .windows(2)
        .all(|pair| pair[0].one_shot == pair[1].one_shot);
    let identified_agrees = orders
        .windows(2)
        .all(|pair| pair[0].identified == pair[1].identified);
    let deltas_agree = orders.windows(2).all(|pair| pair[0].delta == pair[1].delta);
    let capacities_agree = orders
        .windows(2)
        .all(|pair| pair[0].capacities == pair[1].capacities);
    let lineage_agrees = deltas_agree && capacities_agree;
    let combined_delta = deltas_agree.then(|| orders[0].delta.clone());

    let frames: BTreeSet<Vec<(FoundedAxis, ReceiverId)>> = orders
        .iter()
        .map(|order| {
            order
                .mint_frame
                .iter()
                .map(|(axis, id)| (axis.clone(), *id))
                .collect()
        })
        .collect();
    let minted_ids_differ = frames.len() > 1;

    let verdict = decide(
        system,
        prefix,
        &orders,
        all_rebased,
        conduct_agrees,
        identified_agrees,
        deltas_agree,
        capacities_agree,
    );

    InterchangeCertificate {
        schema: "holonic-engine.interchange-certificate.v1".to_owned(),
        predecessor,
        staged,
        orders,
        all_rebased,
        conduct_agrees,
        endpoints_agree,
        identified_agrees,
        combined_delta,
        capacities_agree,
        lineage_agrees,
        minted_ids_differ,
        verdict,
        coherence,
        gyration,
    }
}

#[allow(clippy::too_many_arguments)]
fn decide(
    system: &dyn ObservedSystem,
    prefix: &[FoundedReceiver],
    orders: &[RebasedOrder],
    all_rebased: bool,
    conduct_agrees: bool,
    identified_agrees: bool,
    deltas_agree: bool,
    capacities_agree: bool,
) -> Interchange {
    // 1. Lawful rebasing in both orders. The blueprint asks for it first, and it is the refusal that
    //    actually fires on coupled junctions: the second occurrence stopped being a junction.
    if !all_rebased {
        let (order, (step, refusal)) = orders
            .iter()
            .enumerate()
            .find_map(|(index, order)| order.refusal.clone().map(|found| (index, found)))
            .expect("all_rebased is false, so some order refused");
        let junction = orders[order].staged[step];
        return Interchange::Ordered {
            because: DistinguishingWord::RebaseRefused {
                order,
                step,
                junction,
                refusal,
                now_witnessed_by: witness_for(system, &orders[order], junction),
            },
        };
    }

    // 2. Conduct is invariant under founding. If it moved, the law did, and that outranks a verdict.
    if !conduct_agrees {
        let orders_pair = orders
            .iter()
            .enumerate()
            .flat_map(|(i, left)| {
                orders
                    .iter()
                    .enumerate()
                    .skip(i + 1)
                    .filter(move |(_, right)| left.conduct != right.conduct)
                    .map(move |(j, _)| (i, j))
            })
            .next()
            .expect("conduct disagrees somewhere");
        return Interchange::Ordered {
            because: DistinguishingWord::ConductMoved {
                orders: orders_pair,
            },
        };
    }

    // 3. Does any receiver in the family have a distinguishing word for the orders? A pair one order
    //    separates and another identifies is exactly that, and it is Nerode pointed at orders.
    if !identified_agrees
        && let Some(word) = separating_pair(system, prefix, orders)
    {
        return Interchange::Ordered { because: word };
    }

    // 4. Equal endpoints do not identify ordered paths. Compare the content.
    if !deltas_agree {
        let mut only_in = Vec::new();
        for (index, order) in orders.iter().enumerate() {
            let elsewhere: BTreeSet<&FoundedAxis> = orders
                .iter()
                .enumerate()
                .filter(|(other, _)| *other != index)
                .flat_map(|(_, other)| other.delta.iter())
                .collect();
            let mine: Vec<FoundedAxis> = order
                .delta
                .iter()
                .filter(|axis| !elsewhere.contains(axis))
                .cloned()
                .collect();
            if !mine.is_empty() {
                only_in.push((index, mine));
            }
        }
        // The first step at which two orders took different junctions. Stated between the first two
        // orders only: for more than two, `only_in` carries the full population and a single
        // "first divergence" would be a reading of one pair reported as a property of the set.
        let step = orders.get(1).and_then(|second| {
            orders[0]
                .founded
                .iter()
                .zip(second.founded.iter())
                .position(|(left, right)| left != right)
        });
        return Interchange::Ordered {
            because: DistinguishingWord::LineageDiverges { step, only_in },
        };
    }

    // 5. The successor's other logical resources.
    if !capacities_agree {
        for (i, left) in orders.iter().enumerate() {
            for (j, right) in orders.iter().enumerate().skip(i + 1) {
                for ((axis, mine), (_, theirs)) in left.capacities.iter().zip(right.capacities.iter())
                {
                    if mine != theirs {
                        return Interchange::Ordered {
                            because: DistinguishingWord::ResourcesDiffer {
                                orders: (i, j),
                                axis: axis.clone(),
                                capacities: (mine.clone(), theirs.clone()),
                            },
                        };
                    }
                }
            }
        }
    }

    Interchange::Interchangeable
}

/// The receiver that witnesses a junction now, after an earlier founding — the panel's own
/// distinguishing word for the pair that stopped being blind.
fn witness_for(
    system: &dyn ObservedSystem,
    order: &RebasedOrder,
    junction: (ItemId, ItemId),
) -> Option<(ReceiverId, Observation, Observation, Vec<InputId>)> {
    let widened = WidenedSystem {
        declared: system,
        founded: &order.receivers,
    };
    let reading = compress(&widened);
    // Either conduct still separates it and a receiver now sees the difference …
    if let Some(pair) = reading
        .collapsed
        .iter()
        .find(|pair| (pair.left, pair.right) == junction)
        && let Some((receiver, left, right)) = pair.witness
    {
        return Some((receiver, left, right, pair.distinguishing_word.clone()));
    }
    // … or the panel now separates the two items one-shot, with the empty word.
    order
        .receivers
        .iter()
        .find(|found| found.reads.get(&junction.0) != found.reads.get(&junction.1))
        .map(|found| {
            (
                found.id,
                found.reads.get(&junction.0).copied().unwrap_or(Observation(0)),
                found.reads.get(&junction.1).copied().unwrap_or(Observation(0)),
                Vec::new(),
            )
        })
}

/// The first pair one order separates that another identifies, with the axis that saw it and the
/// word `receiver_exact_compression` returns for it under the panel that did not.
fn separating_pair(
    system: &dyn ObservedSystem,
    prefix: &[FoundedReceiver],
    orders: &[RebasedOrder],
) -> Option<DistinguishingWord> {
    for (identifying, blind) in orders.iter().enumerate() {
        for (separating, sharp) in orders.iter().enumerate() {
            if identifying == separating {
                continue;
            }
            // Every pair one order separates and this one identifies, not merely the first — a
            // `?` here would abandon the whole search on one pair with no founded separator and
            // report "no distinguishing word" for a family that has several.
            for pair in blind.identified.difference(&sharp.identified).copied() {
                let Some(axis) = sharp.receivers[prefix.len().min(sharp.receivers.len())..]
                    .iter()
                    .find(|found| found.reads.get(&pair.0) != found.reads.get(&pair.1))
                else {
                    continue;
                };
                let widened = WidenedSystem {
                    declared: system,
                    founded: &blind.receivers,
                };
                let collapsed = compress(&widened)
                    .collapsed
                    .into_iter()
                    .find(|collapsed| (collapsed.left, collapsed.right) == pair);
                return Some(DistinguishingWord::ReceiverSeparates {
                    pair,
                    separating_order: separating,
                    identifying_order: identifying,
                    receiver: axis.id,
                    axis: FoundedAxis::of(axis),
                    separating_observations: (
                        axis.reads.get(&pair.0).copied().unwrap_or(Observation(0)),
                        axis.reads.get(&pair.1).copied().unwrap_or(Observation(0)),
                    ),
                    collapsed_under_identifying_order: collapsed,
                });
            }
        }
    }
    None
}

/// **The declared material this organ is falsified against.**
///
/// Both fixtures live outside `#[cfg(test)]` on purpose: the unit tests and
/// `examples/the_front_is_ordered_until_a_certificate_unorders_it.rs` must run the **same** material,
/// or the two reconciliations are of two different things — `canon/THE_CONTAMINANT_PROTOCOL.md` §2.3.
/// Neither is a production organ; each is a declared system whose junctions are known by
/// construction to be independent, or known by construction not to be.
///
/// `CLAUDE.md` §8: a certificate that admits everything has measured nothing, and so has one that
/// refuses everything. These are the two inputs on which it must return opposite verdicts.
pub mod declared_material {
    use super::{InputId, ItemId, ObservedSystem, Observation, ReceiverId};

    /// **Two gadgets that never meet — the junctions ARE independent.**
    ///
    /// Gadget A conducts only under input `0`, gadget B only under input `1`. The reading founded at
    /// A's junction is `aperture_after(·, [0,0])`, which terminates at step `0` on every one of B's
    /// items and therefore returns the same observation for all of them; symmetrically for B. So
    /// neither founding witnesses, separates, or shortens the other's junction, and both orders must
    /// reach the same panel by the same content.
    ///
    /// ```text
    ///   A:  0 --0--> 2 --0--> 2        B:  4 --1--> 6 --1--> 6
    ///       1 --0--> 3 --0--> stop         5 --1--> 7 --1--> stop
    ///   the declared receiver reads {0,1}=10 {2,3}=20 {4,5}=30 {6,7}=40 — blind to both junctions
    /// ```
    pub struct TwoGadgets;

    impl ObservedSystem for TwoGadgets {
        fn items(&self) -> Vec<ItemId> {
            (0..8).map(ItemId).collect()
        }
        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }
        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0), InputId(1)]
        }
        fn observation(&self, item: ItemId, _receiver: ReceiverId) -> Observation {
            Observation(match item.0 {
                0 | 1 => 10,
                2 | 3 => 20,
                4 | 5 => 30,
                _ => 40,
            })
        }
        fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
            match (item.0, input.0) {
                (0, 0) => Some(ItemId(2)),
                (1, 0) => Some(ItemId(3)),
                (2, 0) => Some(ItemId(2)),
                (4, 1) => Some(ItemId(6)),
                (5, 1) => Some(ItemId(7)),
                (6, 1) => Some(ItemId(6)),
                _ => None,
            }
        }
    }

    /// **Two junctions that are NOT independent — and the coupling is not visible in the
    /// footprints.**
    ///
    /// `(0,1)` and `(0,2)` are both standing junctions over the bare panel. Founding at `(0,1)`
    /// reads `aperture_after(·, [1])`, which separates `3` from `4` — items neither junction names.
    /// The breadth-first search for `(0,2)`'s distinguishing word walks straight through `(3,4)`, so
    /// once that axis stands the pair is **witnessed** and `(0,2)` is no longer a junction.
    ///
    /// This is `canon/01_CAUSAL_CALCULUS.md:85` in one fixture: the two footprints share no item,
    /// and disjoint support proves nothing because the panel, the junction population and the mint
    /// are shared.
    ///
    /// ```text
    ///   0 --0--> 3   0 --1--> 5      3 --0--> 6   3 --1--> 7
    ///   1 --0--> 3                   4 --0--> 6
    ///   2 --0--> 4   2 --1--> 5      5,6,7 stop
    ///   the declared receiver reads {0,1,2}=0 {3,4}=1 {5,6,7}=2
    /// ```
    pub struct CoupledJunctions;

    impl ObservedSystem for CoupledJunctions {
        fn items(&self) -> Vec<ItemId> {
            (0..8).map(ItemId).collect()
        }
        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }
        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0), InputId(1)]
        }
        fn observation(&self, item: ItemId, _receiver: ReceiverId) -> Observation {
            Observation(match item.0 {
                0..=2 => 0,
                3 | 4 => 1,
                _ => 2,
            })
        }
        fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
            match (item.0, input.0) {
                (0, 0) => Some(ItemId(3)),
                (0, 1) => Some(ItemId(5)),
                (1, 0) => Some(ItemId(3)),
                (2, 0) => Some(ItemId(4)),
                (2, 1) => Some(ItemId(5)),
                (3, 0) => Some(ItemId(6)),
                (3, 1) => Some(ItemId(7)),
                (4, 0) => Some(ItemId(6)),
                _ => None,
            }
        }
    }

    /// **Three gadgets that never meet — the material a triple can be certified on.**
    ///
    /// [`TwoGadgets`] with a third arm, on a third input, so that `certify_set` has a declared set of
    /// three whose `3! = 6` orders are all lawful. Without it the all-orders path would only ever be
    /// exercised on a refusal, and a coherence check that has never returned agreement has not been
    /// shown to be able to.
    ///
    /// Each gadget conducts under exactly one input, so a reading founded at one gadget's junction
    /// terminates at step `0` on every item of the other two and returns the same observation for all
    /// of them.
    ///
    /// ```text
    ///   A (input 0):  0 --> 6 --> 6      B (input 1):  2 --> 8 --> 8      C (input 2):  4 --> 10 --> 10
    ///                 1 --> 7 --> stop                 3 --> 9 --> stop                 5 --> 11 --> stop
    /// ```
    pub struct ThreeGadgets;

    impl ObservedSystem for ThreeGadgets {
        fn items(&self) -> Vec<ItemId> {
            (0..12).map(ItemId).collect()
        }
        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }
        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0), InputId(1), InputId(2)]
        }
        fn observation(&self, item: ItemId, _receiver: ReceiverId) -> Observation {
            Observation(10 * (item.0 / 2 + 1))
        }
        fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
            match (item.0, input.0) {
                (0, 0) => Some(ItemId(6)),
                (1, 0) => Some(ItemId(7)),
                (6, 0) => Some(ItemId(6)),
                (2, 1) => Some(ItemId(8)),
                (3, 1) => Some(ItemId(9)),
                (8, 1) => Some(ItemId(8)),
                (4, 2) => Some(ItemId(10)),
                (5, 2) => Some(ItemId(11)),
                (10, 2) => Some(ItemId(10)),
                _ => None,
            }
        }
    }

    /// **Same endpoint, different path — the case endpoint comparison gets wrong.**
    ///
    /// [`CoupledJunctions`] without item `4`'s successor. The two complete founding orders reach
    /// **one partition** and get there by founding different axes: one takes the blindness junction
    /// `(0,1)` and then a congestion axis, the other takes `(0,2)` and then `(0,1)`. A certificate
    /// that stopped at the endpoint would admit an interchange the lineage refuses, which is the
    /// defect `2026-08-02_THE_HOST_FOREMAN...` convicts, reproduced on eight items so it does not
    /// depend on the filesystem.
    ///
    /// This is the same shape `soma/formal` returns — there the divergence is
    /// `Compression|Programme` against `Compression|Route`.
    pub struct SameEndpointDifferentPath;

    impl ObservedSystem for SameEndpointDifferentPath {
        fn items(&self) -> Vec<ItemId> {
            (0..8).map(ItemId).collect()
        }
        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }
        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0), InputId(1)]
        }
        fn observation(&self, item: ItemId, _receiver: ReceiverId) -> Observation {
            Observation(match item.0 {
                0..=2 => 0,
                3 | 4 => 1,
                _ => 2,
            })
        }
        fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
            match (item.0, input.0) {
                (0, 0) => Some(ItemId(3)),
                (0, 1) => Some(ItemId(5)),
                (1, 0) => Some(ItemId(3)),
                (2, 0) => Some(ItemId(4)),
                (2, 1) => Some(ItemId(5)),
                (3, 0) => Some(ItemId(6)),
                (3, 1) => Some(ItemId(7)),
                _ => None,
            }
        }
    }
}

/// The junctions standing over a bare panel, as pairs.
pub fn bare_junctions(system: &dyn ObservedSystem) -> Vec<(ItemId, ItemId)> {
    crate::founded_receiver::standing_junctions(system, &[])
        .into_iter()
        .map(|pair| (pair.left, pair.right))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::declared_material::{
        CoupledJunctions, SameEndpointDifferentPath, ThreeGadgets, TwoGadgets,
    };
    use super::*;

    fn junctions(system: &dyn ObservedSystem) -> Vec<(ItemId, ItemId)> {
        bare_junctions(system)
    }

    #[test]
    fn independent_junctions_interchange_and_the_certificate_admits() {
        let standing = junctions(&TwoGadgets);
        assert!(
            standing.contains(&(ItemId(0), ItemId(1))) && standing.contains(&(ItemId(4), ItemId(5))),
            "the fixture must present both junctions or the admission is vacuous: {standing:?}"
        );
        let certificate = certify_pair(
            &TwoGadgets,
            &[],
            StagedFootprint::at(ItemId(0), ItemId(1)),
            StagedFootprint::at(ItemId(4), ItemId(5)),
        );
        assert!(certificate.all_rebased, "both orders must rebase lawfully");
        assert!(certificate.conduct_agrees);
        assert!(certificate.endpoints_agree);
        assert!(certificate.identified_agrees);
        assert!(certificate.lineage_agrees);
        assert_eq!(
            certificate.verdict,
            Interchange::Interchangeable,
            "refused: {:?}",
            certificate.because()
        );
        assert!(certificate.combined_delta.is_some());
        assert_eq!(certificate.coherence, Coherence::PairwiseOnly);
    }

    /// The comparison must not depend on the mint ordinal, and on this fixture it demonstrably
    /// cannot: the two orders hand the same axis different ids and the certificate still admits.
    #[test]
    fn the_mint_ordinal_moves_and_the_verdict_does_not() {
        let certificate = certify_pair(
            &TwoGadgets,
            &[],
            StagedFootprint::at(ItemId(0), ItemId(1)),
            StagedFootprint::at(ItemId(4), ItemId(5)),
        );
        assert!(
            certificate.minted_ids_differ,
            "the two orders must mint different ids for the same axis, or this control is vacuous"
        );
        assert!(certificate.is_interchangeable());
        // And the content-keyed delta is bit-identical across the two orders.
        assert_eq!(certificate.orders[0].delta, certificate.orders[1].delta);
        assert_ne!(
            certificate.orders[0].mint_frame, certificate.orders[1].mint_frame,
            "the same axis must receive different ordinals under the two orders"
        );
    }

    #[test]
    fn coupled_junctions_are_refused_and_the_refusal_exhibits_its_witness() {
        let standing = junctions(&CoupledJunctions);
        assert!(
            standing.contains(&(ItemId(0), ItemId(1))) && standing.contains(&(ItemId(0), ItemId(2))),
            "both staged junctions must stand over the bare panel: {standing:?}"
        );
        let certificate = certify_pair(
            &CoupledJunctions,
            &[],
            StagedFootprint::at(ItemId(0), ItemId(1)),
            StagedFootprint::at(ItemId(0), ItemId(2)),
        );
        assert!(!certificate.all_rebased);
        match certificate.because() {
            Some(DistinguishingWord::RebaseRefused {
                refusal,
                now_witnessed_by,
                ..
            }) => {
                assert!(matches!(
                    refusal,
                    FoundingRefusal::NotAStandingJunction { .. }
                ));
                let (_, left, right, _) = now_witnessed_by
                    .as_ref()
                    .expect("the panel that closed the junction must exhibit what now sees it");
                assert_ne!(left, right, "a witness returns two different observations");
            }
            other => panic!("expected a rebase refusal, got {other:?}"),
        }
    }

    /// The null for the whole thing: a certificate that refuses everything has measured nothing, and
    /// one that admits everything has measured nothing either. Both fixtures run through the same
    /// organ and return opposite verdicts.
    #[test]
    fn the_organ_returns_both_verdicts_on_the_same_code_path() {
        let admitted = certify_pair(
            &TwoGadgets,
            &[],
            StagedFootprint::at(ItemId(0), ItemId(1)),
            StagedFootprint::at(ItemId(4), ItemId(5)),
        );
        let refused = certify_pair(
            &CoupledJunctions,
            &[],
            StagedFootprint::at(ItemId(0), ItemId(1)),
            StagedFootprint::at(ItemId(0), ItemId(2)),
        );
        assert!(admitted.is_interchangeable());
        assert!(!refused.is_interchangeable());
    }

    /// Sequential execution adds no causal edge: staging `(a,b)` and staging `(b,a)` are the same
    /// question and must return the same verdict.
    #[test]
    fn the_certificate_is_symmetric_in_the_staged_pair() {
        for (system, a, b) in [
            (
                &TwoGadgets as &dyn ObservedSystem,
                (ItemId(0), ItemId(1)),
                (ItemId(4), ItemId(5)),
            ),
            (
                &CoupledJunctions as &dyn ObservedSystem,
                (ItemId(0), ItemId(1)),
                (ItemId(0), ItemId(2)),
            ),
        ] {
            let forward = certify_pair(
                system,
                &[],
                StagedFootprint::at(a.0, a.1),
                StagedFootprint::at(b.0, b.1),
            );
            let backward = certify_pair(
                system,
                &[],
                StagedFootprint::at(b.0, b.1),
                StagedFootprint::at(a.0, a.1),
            );
            assert_eq!(
                forward.is_interchangeable(),
                backward.is_interchangeable(),
                "staging order changed the verdict"
            );
        }
    }

    /// `certify_set` rebases every permutation. On the independent pair it must agree; the
    /// coherence return says how many orders were compared rather than implying a triple.
    #[test]
    fn a_declared_set_is_certified_over_every_permutation() {
        let certificate = certify_set(
            &TwoGadgets,
            &[],
            &[
                StagedFootprint::at(ItemId(0), ItemId(1)),
                StagedFootprint::at(ItemId(4), ItemId(5)),
            ],
        );
        match certificate.coherence {
            Coherence::AllOrders {
                occurrences,
                orders_compared,
                orders_lawful,
                agreed,
            } => {
                assert_eq!(occurrences, 2);
                assert_eq!(orders_compared, 2, "2! orders");
                assert_eq!(orders_lawful, 2);
                assert!(agreed);
            }
            other => panic!("expected AllOrders, got {other:?}"),
        }
        assert!(certificate.is_interchangeable());
    }

    /// The three-or-more case, taken rather than inferred: `3! = 6` orders, all lawful, all agreeing.
    /// A coherence check that has only ever returned a refusal has not been shown to be able to
    /// admit.
    #[test]
    fn a_declared_triple_agrees_over_all_six_orders() {
        let staged = [
            StagedFootprint::at(ItemId(0), ItemId(1)),
            StagedFootprint::at(ItemId(2), ItemId(3)),
            StagedFootprint::at(ItemId(4), ItemId(5)),
        ];
        let standing = junctions(&ThreeGadgets);
        for footprint in &staged {
            assert!(
                standing.contains(&footprint.junction),
                "{:?} must stand over the bare panel: {standing:?}",
                footprint.junction
            );
        }
        let certificate = certify_set(&ThreeGadgets, &[], &staged);
        match certificate.coherence {
            Coherence::AllOrders {
                occurrences,
                orders_compared,
                orders_lawful,
                agreed,
            } => {
                assert_eq!(occurrences, 3);
                assert_eq!(orders_compared, 6, "3! orders");
                assert_eq!(orders_lawful, 6, "every order must rebase, or the triple is vacuous");
                assert!(agreed, "refused: {:?}", certificate.because());
            }
            other => panic!("expected AllOrders, got {other:?}"),
        }
        assert!(certificate.is_interchangeable());
        assert!(certificate.combined_delta.is_some());
    }

    /// **The receiver family is a previously founded region's perspectives**, so the certificate has
    /// to run over a non-empty prefix. Founding at one gadget's junction first and then certifying
    /// the other two over that panel must still admit — and the predecessor must record the prefix
    /// rather than pretending the panel is bare.
    #[test]
    fn a_certificate_stages_over_an_already_founded_prefix() {
        let prefix = vec![
            crate::founded_receiver::found_at(&ThreeGadgets, &[], (ItemId(0), ItemId(1)))
                .expect("the first gadget's junction stands over the bare panel"),
        ];
        let certificate = certify_pair(
            &ThreeGadgets,
            &prefix,
            StagedFootprint::at(ItemId(2), ItemId(3)),
            StagedFootprint::at(ItemId(4), ItemId(5)),
        );
        assert_eq!(
            certificate.predecessor.prefix.len(),
            1,
            "the predecessor must name what was already founded"
        );
        assert!(
            certificate.all_rebased,
            "the two remaining junctions must still stand over the founded prefix"
        );
        assert!(certificate.is_interchangeable(), "{:?}", certificate.because());
        // The delta is the STAGED part only — the prefix is the predecessor, not the delta.
        assert_eq!(certificate.orders[0].delta.len(), 2);
    }

    #[test]
    fn a_pair_certificate_never_claims_a_triple() {
        let certificate = certify_pair(
            &TwoGadgets,
            &[],
            StagedFootprint::at(ItemId(0), ItemId(1)),
            StagedFootprint::at(ItemId(4), ItemId(5)),
        );
        assert_eq!(certificate.coherence, Coherence::PairwiseOnly);
        assert!(Coherence::TRIPLE_REQUIRES.contains("braid"));
    }

    /// Permutation enumeration is over the caller's declared set and is complete.
    #[test]
    fn every_permutation_is_enumerated_and_none_is_repeated() {
        for population in 0..5usize {
            let items: Vec<usize> = (0..population).collect();
            let all = permutations(&items);
            let factorial: usize = (1..=population).product::<usize>().max(1);
            assert_eq!(all.len(), factorial, "population {population}");
            let distinct: BTreeSet<Vec<usize>> = all.into_iter().collect();
            assert_eq!(distinct.len(), factorial);
        }
    }

    /// The whole-order form on coupled material: the two runs found different SETS, and here they
    /// also reach different endpoints, so the family has a genuine separating pair.
    #[test]
    fn different_founding_orders_can_be_separated_by_a_receiver_with_a_word() {
        let certificate = certify_founding_orders(&CoupledJunctions);
        let gyration = certificate
            .gyration
            .as_ref()
            .expect("the whole-order form carries its gyration");
        assert!(
            gyration.conduct_agrees,
            "founding order may not move the Nerode congruence"
        );
        assert!(
            !gyration.orbit_is_trivial(),
            "the two orders must actually differ, or this control is vacuous"
        );
        assert!(!certificate.is_interchangeable());
        match certificate.because() {
            Some(DistinguishingWord::ReceiverSeparates {
                collapsed_under_identifying_order,
                separating_observations,
                ..
            }) => {
                assert_ne!(separating_observations.0, separating_observations.1);
                let collapsed = collapsed_under_identifying_order
                    .as_ref()
                    .expect("conduct separates the pair under the blind order, so a word exists");
                assert!(
                    !collapsed.distinguishing_word.is_empty(),
                    "an empty word is the one-shot reading, which identified this pair"
                );
            }
            other => panic!("expected a receiver separation, got {other:?}"),
        }
    }

    /// **The finding this module exists to make legible**, and it does not need the filesystem:
    /// the two orders reach one partition by different content, endpoint comparison admits, and the
    /// certificate refuses.
    #[test]
    fn equal_endpoints_do_not_identify_ordered_paths() {
        let certificate = certify_founding_orders(&SameEndpointDifferentPath);
        assert!(
            certificate.conduct_agrees,
            "founding order may not move the Nerode congruence"
        );
        assert!(
            certificate.endpoints_agree && certificate.identified_agrees,
            "the fixture must reach ONE endpoint, or the finding is not about lineage: {} vs {}",
            certificate.orders[0].one_shot.len(),
            certificate.orders[1].one_shot.len()
        );
        assert!(
            certificate.endpoint_only_verdict(),
            "an endpoint-only comparator must ADMIT here — that is the defect being exhibited"
        );
        assert!(
            !certificate.is_interchangeable(),
            "the certificate must refuse on lineage"
        );
        assert!(certificate.lineage_changed_the_verdict());
        match certificate.because() {
            Some(DistinguishingWord::LineageDiverges { only_in, .. }) => {
                assert!(
                    !only_in.is_empty(),
                    "the divergence must exhibit the axes only one order founded"
                );
            }
            other => panic!("expected a lineage divergence, got {other:?}"),
        }
    }

    /// The two comparators are computed and reported separately in every case, and on independent
    /// material they agree — so `lineage_changed_the_verdict` is not a constant.
    #[test]
    fn the_two_comparators_agree_where_the_junctions_are_independent() {
        let certificate = certify_pair(
            &TwoGadgets,
            &[],
            StagedFootprint::at(ItemId(0), ItemId(1)),
            StagedFootprint::at(ItemId(4), ItemId(5)),
        );
        assert!(certificate.endpoint_only_verdict());
        assert!(certificate.is_interchangeable());
        assert!(!certificate.lineage_changed_the_verdict());
    }
}

// -------------------------------------------------------------------------------------------------
// The price of an order, and whether the receiver family can read what it paid for
// -------------------------------------------------------------------------------------------------

/// **What it costs to carry an order over `n` items, in bits, exactly.**
///
/// There are `n!` orderings, so distinguishing one costs `⌈log₂(n!)⌉` bits. Computed over `BigUint`
/// with no float and no Stirling approximation: the factorial is built exactly and its bit length is
/// read off, corrected downward when the factorial is itself a power of two.
///
/// # Why this is the right quantity and where it comes from
///
/// Devillers and Gandoin, *Geometric compression for progressive transmission* (`arXiv:cs/9909018`),
/// invert the standard mesh coder: they **discard the topology**, spend the vertex-order entropy on
/// the coordinates, and reconstruct the topology afterward. Their result, verbatim: *"the gain is
/// `log₂ n − 2.402` per point… which corresponds exactly to the **order information** over the
/// points… the algorithm **saves the encoding of the order information**."*
///
/// **So an order is not free, and this says what it costs.** `CLAUDE.md` §0's fourth lesson and the
/// ratified *"apparatus completion order never enters semantic lineage"* were correctness statements;
/// this is the same statement with a price on it. A front that carries host arrival order into a
/// returned population and whose receiver family cannot read that order has **paid `⌈log₂(n!)⌉` bits
/// for nothing** — and that is a measured overpayment, not a suspicion.
///
/// The Stirling reading, for scale only and never used in a computation here: `log₂(n!) ≈ n log₂ n`,
/// which is Devillers–Gandoin's `n log₂ n` gain.
pub fn order_price_bits(population: usize) -> u64 {
    if population < 2 {
        return 0;
    }
    let mut factorial = num_bigint::BigUint::from(1u32);
    for factor in 2..=population {
        factorial *= num_bigint::BigUint::from(factor);
    }
    let bits = factorial.bits();
    // `⌈log₂ x⌉` is `bits` unless `x` is exactly a power of two, where it is `bits - 1`.
    if factorial.count_ones() == 1 {
        bits.saturating_sub(1)
    } else {
        bits
    }
}

/// **An order's price beside the verdict on whether anything can read it.**
///
/// The two halves are kept separate on purpose. The price is arithmetic and is always correct; the
/// verdict is a measurement against a **declared receiver family**, and a different family may read
/// what this one cannot. Reporting the price alone would imply a waste that has not been established;
/// reporting the verdict alone leaves the correctness statement without a magnitude.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderPrice {
    /// How many items the order ranges over.
    pub population: usize,
    /// `⌈log₂(n!)⌉` — the exact cost of distinguishing one ordering.
    pub bits: u64,
    /// True when the declared receiver family has **no** distinguishing word for the two orders, so
    /// the bits above buy nothing that family can read.
    pub unreadable_by_the_declared_family: bool,
}

impl OrderPrice {
    /// The bits paid and not readable. Zero when the order is load-bearing.
    pub fn overpayment(&self) -> u64 {
        if self.unreadable_by_the_declared_family {
            self.bits
        } else {
            0
        }
    }

    pub fn written(&self) -> String {
        format!(
            "{} item(s) · order costs {} bits · {}",
            self.population,
            self.bits,
            if self.unreadable_by_the_declared_family {
                "UNREADABLE by the declared family — paid for nothing"
            } else {
                "readable — the order is load-bearing"
            }
        )
    }
}

impl InterchangeCertificate {
    /// Price the order this certificate ruled on.
    ///
    /// `Interchange::Unordered` means no receiver in the declared family separates the two orders, so
    /// the order's bits are unreadable **by that family**. `Interchange::Ordered` carries the
    /// distinguishing word, so the order is load-bearing and the price is earned.
    pub fn order_price(&self, population: usize) -> OrderPrice {
        OrderPrice {
            population,
            bits: order_price_bits(population),
            unreadable_by_the_declared_family: self.is_interchangeable(),
        }
    }
}

#[cfg(test)]
mod order_price_tests {
    use super::*;

    /// `⌈log₂(n!)⌉`, checked against hand values. No float, no Stirling.
    #[test]
    fn the_order_price_is_the_exact_bits_to_index_a_permutation() {
        assert_eq!(order_price_bits(0), 0);
        assert_eq!(order_price_bits(1), 0);
        assert_eq!(order_price_bits(2), 1); // 2! = 2, a power of two
        assert_eq!(order_price_bits(3), 3); // 3! = 6 → ⌈log₂6⌉ = 3
        assert_eq!(order_price_bits(4), 5); // 4! = 24 → ⌈log₂24⌉ = 5
        assert_eq!(order_price_bits(5), 7); // 5! = 120 → ⌈log₂120⌉ = 7
        assert_eq!(order_price_bits(8), 16); // 8! = 40320 → ⌈log₂⌉ = 16
    }

    /// It grows like `n log₂ n`, which is Devillers–Gandoin's gain. Checked as a bound rather than
    /// asserted as an identity, because Stirling is an asymptotic and this carrier is exact.
    #[test]
    fn the_price_is_bounded_by_n_log_n_and_grows_superlinearly() {
        for population in [4usize, 8, 16, 32, 64] {
            let bits = order_price_bits(population);
            let n = population as u64;
            let log2n = (u64::BITS - (n - 1).leading_zeros()) as u64;
            assert!(bits <= n * log2n, "n = {population}: {bits} > {n}·{log2n}");
            assert!(bits > n, "n = {population}: the price must exceed n bits");
        }
    }
}
