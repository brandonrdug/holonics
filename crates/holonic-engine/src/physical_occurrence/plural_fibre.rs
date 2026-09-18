//! **B5 — plural fibres and separator sets.** Several predictors, seeds and environments produce a
//! population of faces over one candidate; this is the n-way fibre and the *complete* separator
//! structure over it.
//!
//! [definition] This file is part of the [`crate::physical_occurrence`] owner and adds no second
//! carrier. Its population is built from that owner's [`SituatedFamily`], and its two entry points
//! [`PluralFibre::from_vertical`] and [`PluralFibre::from_horizontal`] compose the two families
//! that owner already has. It owns item **B5** of
//! `docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`.
//!
//! # Why a third family exists beside the two that already do
//!
//! [definition] [`VerticalFamily`] refuses two members at the same environment value;
//! [`HorizontalFamily`] refuses two members at different environment values. **Neither admits the
//! B5 population**, which is several predictors and seeds *and* several environments over one
//! candidate — two Protenix seeds at one environment beside a designed structure at another. The
//! concretely absent type is a population indexed by nothing but the occurrence, constrained only
//! to be about one object at one receiver. That is [`PluralFibre`], and it is the join of the two
//! indices restricted to a single object.
//!
//! # The receiver
//!
//! [definition] The receiver `R` this fibre is read at is **one contact family at one aperture**:
//! the addressed pairs of a [`SituatedFamily`] together with the [`DistanceAperture`] its classes
//! were taken against. [`PluralFibre::over_one_candidate`] refuses members at different apertures,
//! because two readings at two apertures are two receivers and separation at one says nothing at
//! the other.
//!
//! # The central law: agreement narrows the fibre and does not prove realization
//!
//! [proved-derived] Unanimity of a family on `R` gives **`R`-indistinguishability of its members**
//! and never equality of sources.
//!
//! 1. [`PluralFibre::separator_between`] returns the *complete* set of contacts at which two
//!    members read different **decided** classes — not the first one, and not a shortest witness.
//!    Two members are `R`-distinguishable exactly when that set is nonempty
//!    ([`PluralFibre::indistinguishable`]).
//! 2. [`PluralFibre::unanimity`] returns the members no contact separates, and
//!    [`UnanimityReceipt::realization_proof`] is `None` **by type**: [`RealizationProof`] is an
//!    uninhabited enum, so no code path in this owner can turn agreement into a claim that two
//!    occurrences are one source.
//! 3. [`PluralFibre::adjoin`] is monotone: adding a member can only shrink or preserve the
//!    unanimous set ([`FibrePartition::unanimous`]), never enlarge it.
//! 4. One separating contact refutes a proposed merge: [`PluralFibre::refutes_merge`] returns the
//!    contact and the two decided classes, which is the exact analogue of
//!    `continuing_tower::Transition::separating_residuals`.
//!
//! # Open readings are carried, never counted
//!
//! [definition] A contact that any member reads [`ContactClass::Open`] is
//! [`ContactRole::OpenCarrying`] in the family partition: it is counted as neither agreement nor
//! separation there, exactly as `physical_constraint_grading` keeps the open class plural. At the
//! *pairwise* separator the same rule applies to the two members concerned — a contact either of
//! them reads open never enters their separator set — and that is the honest scope of the rule.
//!
//! [definition] **A finding worth naming: openness is a property of a reading at a member, not a
//! global veto on a contact.** A contact one member leaves open may still be decided differently by
//! two other members, and it then separates *them*. Such a contact therefore can appear in a
//! minimum separating receiver while appearing in no separator set of any pair that reads it open.
//! Discarding it wholesale would throw away a real distinction; counting it as agreement or
//! separation where it is open would resolve an undecided reading. Both are refused here.
//!
//! # The minimal separating sets
//!
//! [definition] A receiver that distinguishes every member of the fibre is exactly a **hitting
//! set** of the pairwise separator sets, and the smallest such receiver is a minimum hitting set.
//! Minimum hitting set is NP-hard in general, so [`PluralFibre::minimal_separating_sets`] takes a
//! declared [`HittingSetBound`] and bounds its **whole** search before allocating or recursing.
//! The search is iterative deepening: it restarts once per cardinality `c = 1..=depth`, so its
//! work is not one depth-`depth` tree but the **sum over the rounds**,
//! `Σ_{c=1}^{depth} Σ_{i=0}^{c} b^i`, at branching factor `b`. That sum is what is computed as a
//! `BigUint` and compared against the declared ceiling — a single `Σ_{i≤depth} b^i` undercounts
//! the real work, at `b = 1` by a factor of about `depth/2` — and a declaration above the ceiling
//! is [`FibreRefusal::HittingSetSearchTooWide`] rather than a search that cannot finish. Within
//! the bound the answer is exact and complete: *every* minimum-cardinality hitting set is returned,
//! never a representative chosen out of a plural family.
//!
//! Two returns are not hitting sets at all and are named rather than encoded as an empty answer:
//! [`MinimalSeparation::Unseparable`] when some member pair has an empty separator set — no
//! receiver built from these contacts distinguishes them, which is the fibre staying plural — and
//! [`FibreRefusal::NoSeparatingSetWithinCardinality`] when the declared depth was too shallow.
//!
//! # The paired Lean owner
//!
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/PhysicalOccurrence.lean`, section
//! **B5**, namespace `Soma.Holonics.Foundation.PhysicalOccurrence`.
//!
//! | Lean declaration | Rust owner |
//! |---|---|
//! | `separatesB`, `separatorSet`, `separatesB_of_open` | [`PluralFibre::separator_between`] |
//! | `mem_separatorSet_iff` | [`PairwiseSeparator::separating`] carrying the complete set |
//! | `separatorSet_eq_nil_iff_indistinguishable` | [`PluralFibre::indistinguishable`] |
//! | `separatesB_irrefl` | a member never separates from itself |
//! | `unanimousAt`, `unanimous` | [`FibrePartition::unanimous`] |
//! | `unanimous_antitone` | [`PluralFibre::adjoin`] and the monotonicity test |
//! | `Source`, `preimageFibre` | [`PluralFibre`] itself, whose members are the retained sources |
//! | `agreement_does_not_prove_realization` | [`RealizationProof`], uninhabited |
//! | `fibre_stays_plural` | [`UnanimityReceipt::indistinguishable_pairs`] |
//! | `one_separating_contact_refutes_the_merge` | [`PluralFibre::refutes_merge`] |
//! | `Hits`, `SeparatesAll`, `hittingSet_separates_all` | [`PluralFibre::separates_every_pair`] |
//! | `Indistinguishable`, `indistinguishableB_iff`, `indistinguishableB_refl` | [`PluralFibre::indistinguishable`] |
//! | `MinimumHittingSet`, `minimum_hittingSet_separates_all`, `minimum_no_smaller` | [`MinimalSeparation::Minimum`] |
//! | `no_hittingSet_of_empty_separator_set` | [`MinimalSeparation::Unseparable`] |
//! | `fibre_contract` | the whole B5 contract |

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;
use num_traits::{One, Zero};
use serde::Serialize;

use thiserror::Error;

use super::{HorizontalFamily, ObjectKinship, OccurrenceId, SituatedFamily, VerticalFamily};
use crate::physical_constraint_complex::{ContactClass, DistanceAperture};

// ---------------------------------------------------------------------------------------------
// The decided class
// ---------------------------------------------------------------------------------------------

/// A **decided** reading: the two classes the exact interval law resolves.
///
/// [definition] [`ContactClass::Open`] is deliberately not a value of this type. A separator is a
/// disagreement between two *decided* readings; an undecided reading is carried in
/// [`PairwiseSeparator::open_carrying`] and is never promoted into a decision by this owner.
///
/// Lean counterpart: the `separatesB` guard that refuses `ContactClass.openContact` on either side.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum DecidedClass {
    /// The exact interval's upper bound is at or below the aperture.
    Formed,
    /// The exact interval's lower bound is strictly above it.
    Excluded,
}

impl DecidedClass {
    /// The decided class of a reading, or `None` for an open one.
    pub const fn of(class: ContactClass) -> Option<Self> {
        match class {
            ContactClass::Inside => Some(Self::Formed),
            ContactClass::Outside => Some(Self::Excluded),
            ContactClass::Open => None,
        }
    }

    /// A short name for receipts.
    pub const fn label(self) -> &'static str {
        match self {
            Self::Formed => "formed",
            Self::Excluded => "excluded",
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The n-way fibre
// ---------------------------------------------------------------------------------------------

/// **The population of faces over one candidate.** Several predictors, seeds and environments.
///
/// [definition] Every member is about the same object, addresses the same pairs in the same order,
/// and was classified against the same aperture. Members may repeat an environment (two seeds of
/// one predictor) and may differ in environment (a designed structure beside a prediction); the
/// occurrence identity is what must not repeat.
///
/// `Deserialize` is deliberately not derived. This is a founded population, re-founded through
/// [`PluralFibre::over_one_candidate`] and never remounted past its checks.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PluralFibre {
    /// The schema this fibre serializes under.
    pub schema: String,
    object: ObjectKinship,
    members: Vec<SituatedFamily>,
}

impl PluralFibre {
    /// The schema stamp.
    pub const SCHEMA: &'static str = "holonic-engine.plural-occurrence-fibre.v1";

    /// **Found the fibre over one candidate.**
    ///
    /// Refuses a population of fewer than two members, a member about a different object, a member
    /// addressing a different pair population or order, a member read at a different aperture, and
    /// a repeated occurrence identity.
    pub fn over_one_candidate(members: Vec<SituatedFamily>) -> Result<Self, FibreRefusal> {
        if members.len() < 2 {
            return Err(FibreRefusal::NotPlural {
                members: members.len(),
            });
        }
        let first = &members[0];
        let object = first.kinship();
        let aperture = first.aperture.clone();
        let mut seen: BTreeSet<OccurrenceId> = BTreeSet::new();
        for member in &members {
            if member.kinship() != object {
                return Err(FibreRefusal::ObjectDiffersInTheFibre {
                    occurrence: member.occurrence,
                });
            }
            if member.aperture != aperture {
                return Err(FibreRefusal::ApertureDiffersInTheFibre {
                    occurrence: member.occurrence,
                    declared: aperture.lineage.clone(),
                    presented: member.aperture.lineage.clone(),
                });
            }
            if member.readings.len() != first.readings.len() {
                return Err(FibreRefusal::PairPopulationDisagrees {
                    left: first.occurrence,
                    right: member.occurrence,
                    left_pairs: first.readings.len(),
                    right_pairs: member.readings.len(),
                });
            }
            for (a, b) in first.readings.iter().zip(&member.readings) {
                if a.pair != b.pair {
                    return Err(FibreRefusal::PairOrderDisagrees {
                        left: first.occurrence,
                        right: member.occurrence,
                        left_pair: a.pair,
                        right_pair: b.pair,
                    });
                }
            }
            if !seen.insert(member.occurrence) {
                return Err(FibreRefusal::OccurrenceRepeatedInTheFibre {
                    occurrence: member.occurrence,
                });
            }
        }
        Ok(Self {
            schema: Self::SCHEMA.to_owned(),
            object,
            members,
        })
    }

    /// The fibre of a [`VerticalFamily`]: one object, several environments.
    ///
    /// [definition] This is a composition, not a second constructor. The vertical family already
    /// guarantees one object and distinct environments; the fibre adds the receiver checks — one
    /// aperture and one addressed pair population — that separation needs and the family does not.
    pub fn from_vertical(family: &VerticalFamily) -> Result<Self, FibreRefusal> {
        Self::over_one_candidate(family.members().to_vec())
    }

    /// The fibre of a [`HorizontalFamily`], which is lawful exactly when that family happens to be
    /// about one object.
    ///
    /// [definition] A horizontal family is the *design population* and its members may be about
    /// different objects. When they are, the return is
    /// [`FibreRefusal::ObjectDiffersInTheFibre`] naming the member: a fibre is over one candidate,
    /// and a population of several candidates is not narrowed by agreement between them.
    pub fn from_horizontal(family: &HorizontalFamily) -> Result<Self, FibreRefusal> {
        Self::over_one_candidate(family.members().to_vec())
    }

    /// The members, in declaration order.
    pub fn members(&self) -> &[SituatedFamily] {
        &self.members
    }

    /// The object every member is a face of. Established by the constructor, so no clone-then-
    /// mutate path can make it disagree with the members.
    pub const fn object(&self) -> &ObjectKinship {
        &self.object
    }

    /// How many faces stand over the candidate.
    pub fn len(&self) -> usize {
        self.members.len()
    }

    /// Never true: [`PluralFibre::over_one_candidate`] refuses a population of fewer than two.
    pub fn is_empty(&self) -> bool {
        self.members.is_empty()
    }

    /// The receiver this fibre is read at.
    pub fn aperture(&self) -> &DistanceAperture {
        &self.members[0].aperture
    }

    /// How many contacts the receiver addresses.
    pub fn contacts(&self) -> usize {
        self.members[0].readings.len()
    }

    /// The addressed contacts, in the order every member carries them.
    pub fn addressed(&self) -> Vec<(u32, u32)> {
        self.members[0]
            .readings
            .iter()
            .map(|reading| reading.pair)
            .collect()
    }

    /// The occurrence identities, in declaration order.
    pub fn occurrences(&self) -> Vec<OccurrenceId> {
        self.members
            .iter()
            .map(|member| member.occurrence)
            .collect()
    }

    /// **Adjoin one more face to the fibre.** Every check of
    /// [`PluralFibre::over_one_candidate`] is applied to the enlarged population.
    ///
    /// [proved-derived] The unanimous set is antitone under this operation: adding a member can
    /// only shrink or preserve [`FibrePartition::unanimous`], never enlarge it. Lean counterpart:
    /// `unanimous_antitone`.
    pub fn adjoin(&self, member: SituatedFamily) -> Result<Self, FibreRefusal> {
        let mut members = self.members.clone();
        members.push(member);
        Self::over_one_candidate(members)
    }

    // -----------------------------------------------------------------------------------------
    // The separator sets
    // -----------------------------------------------------------------------------------------

    /// **The complete separator set of one ordered index pair of members.**
    ///
    /// Every contact at which the two read *different decided* classes is returned, in addressed
    /// order. A contact either member reads [`ContactClass::Open`] is carried in
    /// [`PairwiseSeparator::open_carrying`] and never counted on either side.
    ///
    /// Lean counterpart: `separatorSet`, with `mem_separatorSet_iff`.
    pub fn separator_between(&self, left: usize, right: usize) -> Result<PairwiseSeparator, FibreRefusal> {
        let left_member = self
            .members
            .get(left)
            .ok_or(FibreRefusal::MemberIndexAbsent { at: left })?;
        let right_member = self
            .members
            .get(right)
            .ok_or(FibreRefusal::MemberIndexAbsent { at: right })?;
        let mut separating = Vec::new();
        let mut open_carrying = Vec::new();
        let mut agreeing = 0_usize;
        for (a, b) in left_member.readings.iter().zip(&right_member.readings) {
            match (DecidedClass::of(a.class), DecidedClass::of(b.class)) {
                (Some(left_class), Some(right_class)) => {
                    if left_class == right_class {
                        agreeing += 1;
                    } else {
                        separating.push(SeparatingContact {
                            pair: a.pair,
                            left: left_class,
                            right: right_class,
                        });
                    }
                }
                _ => open_carrying.push(a.pair),
            }
        }
        Ok(PairwiseSeparator {
            schema: "holonic-engine.pairwise-separator-set.v1".to_owned(),
            left: left_member.occurrence,
            right: right_member.occurrence,
            agreeing,
            separating,
            open_carrying,
        })
    }

    /// Every unordered pair of members, with its complete separator set. `n(n-1)/2` entries in
    /// lexicographic index order.
    pub fn pairwise_separators(&self) -> Result<Vec<PairwiseSeparator>, FibreRefusal> {
        let mut out = Vec::with_capacity(self.members.len() * self.members.len().saturating_sub(1) / 2);
        for left in 0..self.members.len() {
            for right in (left + 1)..self.members.len() {
                out.push(self.separator_between(left, right)?);
            }
        }
        Ok(out)
    }

    /// **Two members are `R`-indistinguishable exactly when their separator set is empty.**
    ///
    /// [definition] A `true` return is a fact about this receiver and never about the sources:
    /// it says the two faces cannot be told apart here, not that they are one occurrence. This is
    /// the contact-receiver instance of `receiver_atlas::ReceiverAtlas::indistinguishable`, whose
    /// Lean law `indistinguishable_of_refinement` says a richer receiver may reopen it.
    ///
    /// Lean counterpart: `separatorSet_eq_nil_iff_indistinguishable`.
    pub fn indistinguishable(&self, left: usize, right: usize) -> Result<bool, FibreRefusal> {
        Ok(self.separator_between(left, right)?.separating.is_empty())
    }

    /// **One separating contact refutes a proposed merge**, returned with the two decided classes
    /// that refute it. `None` exactly when the two members are indistinguishable here.
    ///
    /// Lean counterpart: `one_separating_contact_refutes_the_merge`.
    pub fn refutes_merge(
        &self,
        left: usize,
        right: usize,
    ) -> Result<Option<SeparatingContact>, FibreRefusal> {
        Ok(self
            .separator_between(left, right)?
            .separating
            .into_iter()
            .next())
    }

    // -----------------------------------------------------------------------------------------
    // The partition of contacts
    // -----------------------------------------------------------------------------------------

    /// **The partition of every addressed contact into the four roles.**
    ///
    /// [proved-derived] The four classes are disjoint and exhaust the addressed population. Open
    /// takes precedence: a contact any member reads [`ContactClass::Open`] is
    /// [`ContactRole::OpenCarrying`] whatever the other members read, so an undecided reading is
    /// never counted as agreement and never counted as separation.
    pub fn partition(&self) -> FibrePartition {
        let mut unanimously_formed = Vec::new();
        let mut unanimously_excluded = Vec::new();
        let mut separating = Vec::new();
        let mut open_carrying = Vec::new();
        for (at, reading) in self.members[0].readings.iter().enumerate() {
            let pair = reading.pair;
            let mut open_at = Vec::new();
            let mut decided: BTreeSet<DecidedClass> = BTreeSet::new();
            for member in &self.members {
                match DecidedClass::of(member.readings[at].class) {
                    Some(class) => {
                        decided.insert(class);
                    }
                    None => open_at.push(member.occurrence),
                }
            }
            if !open_at.is_empty() {
                open_carrying.push(pair);
            } else if decided.len() > 1 {
                separating.push(pair);
            } else if decided.contains(&DecidedClass::Formed) {
                unanimously_formed.push(pair);
            } else {
                unanimously_excluded.push(pair);
            }
        }
        FibrePartition {
            schema: "holonic-engine.fibre-contact-partition.v1".to_owned(),
            members: self.occurrences(),
            contacts: self.members[0].readings.len(),
            unanimously_formed,
            unanimously_excluded,
            separating,
            open_carrying,
        }
    }

    /// The role of one addressed contact, with the members placed.
    pub fn role_of(&self, pair: (u32, u32)) -> Result<ContactRole, FibreRefusal> {
        let at = self.members[0]
            .readings
            .iter()
            .position(|reading| reading.pair == pair)
            .ok_or(FibreRefusal::ContactNotAddressed { pair })?;
        let mut open_at = Vec::new();
        let mut formed_at = Vec::new();
        let mut excluded_at = Vec::new();
        for member in &self.members {
            match DecidedClass::of(member.readings[at].class) {
                Some(DecidedClass::Formed) => formed_at.push(member.occurrence),
                Some(DecidedClass::Excluded) => excluded_at.push(member.occurrence),
                None => open_at.push(member.occurrence),
            }
        }
        Ok(if !open_at.is_empty() {
            ContactRole::OpenCarrying {
                pair,
                open_at,
                formed_at,
                excluded_at,
            }
        } else if !formed_at.is_empty() && !excluded_at.is_empty() {
            ContactRole::Separating {
                pair,
                formed_at,
                excluded_at,
            }
        } else if formed_at.is_empty() {
            ContactRole::UnanimouslyExcluded { pair }
        } else {
            ContactRole::UnanimouslyFormed { pair }
        })
    }

    // -----------------------------------------------------------------------------------------
    // Unanimity, and what it does not buy
    // -----------------------------------------------------------------------------------------

    /// **The unanimity receipt: what agreement across the whole fibre actually establishes.**
    ///
    /// [proved-derived] It establishes `R`-indistinguishability of the named member pairs and
    /// nothing else. [`UnanimityReceipt::realization_proof`] is `None` for every fibre at every
    /// receiver because [`RealizationProof`] has no values.
    ///
    /// Lean counterpart: `fibre_stays_plural` together with `agreement_does_not_prove_realization`.
    pub fn unanimity(&self) -> Result<UnanimityReceipt, FibreRefusal> {
        let partition = self.partition();
        let mut indistinguishable_pairs = Vec::new();
        for left in 0..self.members.len() {
            for right in (left + 1)..self.members.len() {
                if self.indistinguishable(left, right)? {
                    indistinguishable_pairs
                        .push((self.members[left].occurrence, self.members[right].occurrence));
                }
            }
        }
        Ok(UnanimityReceipt {
            schema: "holonic-engine.fibre-unanimity-receipt.v1".to_owned(),
            members: self.occurrences(),
            unanimous_contacts: partition.unanimous().len(),
            separating_contacts: partition.separating.len(),
            open_carrying_contacts: partition.open_carrying.len(),
            indistinguishable_pairs,
        })
    }

    // -----------------------------------------------------------------------------------------
    // The minimal separating sets
    // -----------------------------------------------------------------------------------------

    /// **Does this declared receiver distinguish every member of the fibre?**
    ///
    /// A receiver is a list of addressed contacts. It separates the fibre exactly when every
    /// member pair has one of those contacts in its separator set — that is, exactly when it is a
    /// hitting set.
    ///
    /// Lean counterpart: `hittingSet_separates_all`.
    pub fn separates_every_pair(&self, receiver: &[(u32, u32)]) -> Result<bool, FibreRefusal> {
        let chosen: BTreeSet<(u32, u32)> = receiver.iter().copied().collect();
        for separator in self.pairwise_separators()? {
            if !separator
                .separating
                .iter()
                .any(|contact| chosen.contains(&contact.pair))
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// **Every minimum-cardinality receiver that distinguishes all members**, computed exactly
    /// under a declared bound.
    ///
    /// [definition] The construction is iterative deepening over a bounded branching search: for
    /// each cardinality `c = 1..=depth` in turn, pick a member pair no chosen contact separates yet
    /// and branch on the contacts of its separator set to depth `c`. **The work is therefore the
    /// sum over the rounds**, `Σ_{c=1}^{depth} Σ_{i=0}^{c} b^i`, and that whole sum — not one
    /// depth-`depth` tree — is what `search_tree_nodes` computes as a `BigUint` before any
    /// allocation or recursion. A sum above the declared ceiling is
    /// [`FibreRefusal::HittingSetSearchTooWide`] — never a truncated search and never a heuristic.
    ///
    /// The depth is `min(declared cardinality, number of member pairs)`, because a hitting set
    /// never needs more than one contact per pair, so the search depth is derived from the fibre
    /// and bounded above by the declaration rather than taken from it.
    ///
    /// Lean counterpart: `MinimumHittingSet`, with `minimum_hittingSet_separates_all`,
    /// `minimum_no_smaller` and `no_hittingSet_of_empty_separator_set`.
    pub fn minimal_separating_sets(
        &self,
        bound: &HittingSetBound,
    ) -> Result<MinimalSeparation, FibreRefusal> {
        let separators = self.pairwise_separators()?;
        // A member pair no contact separates makes the whole family unseparable at this receiver.
        // It is named rather than silently dropped from the search.
        for separator in &separators {
            if separator.separating.is_empty() {
                return Ok(MinimalSeparation::Unseparable {
                    left: separator.left,
                    right: separator.right,
                    open_carrying: separator.open_carrying.len(),
                });
            }
        }
        let sets: Vec<BTreeSet<(u32, u32)>> = separators
            .iter()
            .map(|separator| separator.contacts())
            .collect();
        let branching = sets.iter().map(BTreeSet::len).max().unwrap_or(0);
        // `sets` is nonempty (n >= 2 members give at least one pair) and every set is nonempty,
        // so a hitting set of size at most `sets.len()` exists; nothing deeper can be minimum.
        let depth = bound.max_cardinality.min(sets.len());
        // The whole search is bounded, not one of its rounds: the loop below restarts the branching
        // search once per cardinality, so the node count that must fit under the ceiling is the sum
        // over `c = 1..=depth`.
        let (nodes, rounds_counted) = search_tree_nodes(branching, depth, &bound.max_search_nodes);
        if nodes > bound.max_search_nodes {
            return Err(FibreRefusal::HittingSetSearchTooWide {
                branching,
                depth,
                worst_case_nodes: nodes,
                rounds_counted,
                declared_ceiling: bound.max_search_nodes.clone(),
                ground: bound.ground.clone(),
            });
        }
        for cardinality in 1..=depth {
            let mut found: BTreeSet<Vec<(u32, u32)>> = BTreeSet::new();
            let mut chosen: Vec<(u32, u32)> = Vec::with_capacity(cardinality);
            collect_hitting_sets(&sets, cardinality, &mut chosen, &mut found);
            if !found.is_empty() {
                return Ok(MinimalSeparation::Minimum {
                    cardinality,
                    sets: found.into_iter().collect(),
                });
            }
        }
        Err(FibreRefusal::NoSeparatingSetWithinCardinality {
            declared: bound.max_cardinality,
            searched: depth,
            pairs: sets.len(),
        })
    }
}

/// **The exact worst-case node count of the whole bounded search**, summed over its rounds.
///
/// [implemented-exact] `PluralFibre::minimal_separating_sets` is iterative deepening: it runs one
/// bounded branching search per cardinality `c = 1..=depth`, and the round at cardinality `c`
/// visits at most `N(c) = Σ_{i=0}^{c} branching^i` nodes. The work of the call is therefore
/// `Σ_{c=1}^{depth} N(c)`, and that is what this returns. Bounding only `N(depth)` undercounts the
/// real work — at `branching = 1` it counts `depth + 1` nodes where the search visits
/// `depth·(depth+3)/2`, which is an undercount by a factor of about `depth/2`.
///
/// `BigUint` throughout, so no term can wrap and the comparison against a declared ceiling is exact
/// at any width.
///
/// Returns `(total, rounds)`. `rounds == depth` means the sum is complete. `rounds < depth` means
/// the running total passed `ceiling` at round `rounds` and the later rounds were not summed: the
/// true total is then strictly greater than `total`, which is everything the guard needs, and it
/// keeps the guard's own arithmetic bounded by the ceiling the caller declared rather than by a
/// tower of powers no one asked for.
fn search_tree_nodes(branching: usize, depth: usize, ceiling: &BigUint) -> (BigUint, usize) {
    let base = BigUint::from(branching);
    // `nodes` is N(c) and `power` is branching^c, both carried from the previous round.
    let mut nodes = BigUint::one();
    let mut power = BigUint::one();
    let mut total = BigUint::zero();
    let mut rounds = 0_usize;
    for _ in 0..depth {
        power *= &base;
        nodes += &power;
        total += &nodes;
        rounds += 1;
        if &total > ceiling {
            break;
        }
    }
    (total, rounds)
}

/// Collect every hitting set of size **exactly at most** `cardinality` that the branching search
/// reaches. Complete for minimum hitting sets: every element of a minimum hitting set hits some
/// set uncovered at the moment it is chosen, so branching on an uncovered set's elements reaches
/// all of them.
fn collect_hitting_sets(
    sets: &[BTreeSet<(u32, u32)>],
    cardinality: usize,
    chosen: &mut Vec<(u32, u32)>,
    found: &mut BTreeSet<Vec<(u32, u32)>>,
) {
    let uncovered = sets
        .iter()
        .find(|set| !set.iter().any(|contact| chosen.contains(contact)));
    let Some(uncovered) = uncovered else {
        let mut witness = chosen.clone();
        witness.sort_unstable();
        found.insert(witness);
        return;
    };
    if chosen.len() == cardinality {
        return;
    }
    for contact in uncovered {
        chosen.push(*contact);
        collect_hitting_sets(sets, cardinality, chosen, found);
        chosen.pop();
    }
}

// ---------------------------------------------------------------------------------------------
// The separator carriers
// ---------------------------------------------------------------------------------------------

/// One addressed contact at which two members read different decided classes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct SeparatingContact {
    /// The addressed pair.
    pub pair: (u32, u32),
    /// What the left member decided there.
    pub left: DecidedClass,
    /// What the right member decided there.
    pub right: DecidedClass,
}

/// **The complete separator set between two members of the fibre.**
///
/// [definition] `Deserialize` is not derived: this is a derived receipt, recomputed from the fibre
/// and never remounted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PairwiseSeparator {
    /// The schema this separator set serializes under.
    pub schema: String,
    /// The left member.
    pub left: OccurrenceId,
    /// The right member.
    pub right: OccurrenceId,
    /// How many contacts the two decided the same way.
    pub agreeing: usize,
    /// **Every** contact at which the two decided differently, in addressed order.
    pub separating: Vec<SeparatingContact>,
    /// Contacts at which either member's reading is open. Carried, never counted as agreeing and
    /// never counted as separating.
    pub open_carrying: Vec<(u32, u32)>,
}

impl PairwiseSeparator {
    /// Whether no contact separates the two members at this receiver.
    pub fn is_empty(&self) -> bool {
        self.separating.is_empty()
    }

    /// The separating contacts as a set.
    pub fn contacts(&self) -> BTreeSet<(u32, u32)> {
        self.separating
            .iter()
            .map(|contact| contact.pair)
            .collect()
    }
}

/// The role one addressed contact plays across the whole fibre.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum ContactRole {
    /// Every member decided it formed.
    UnanimouslyFormed {
        /// The addressed pair.
        pair: (u32, u32),
    },
    /// Every member decided it excluded.
    UnanimouslyExcluded {
        /// The addressed pair.
        pair: (u32, u32),
    },
    /// Members decided it differently. This contact separates at least one member pair.
    Separating {
        /// The addressed pair.
        pair: (u32, u32),
        /// Where it read formed.
        formed_at: Vec<OccurrenceId>,
        /// Where it read excluded.
        excluded_at: Vec<OccurrenceId>,
    },
    /// At least one member left it undecided. Never counted as agreeing or separating.
    OpenCarrying {
        /// The addressed pair.
        pair: (u32, u32),
        /// Where the reading is open.
        open_at: Vec<OccurrenceId>,
        /// Where it read formed.
        formed_at: Vec<OccurrenceId>,
        /// Where it read excluded.
        excluded_at: Vec<OccurrenceId>,
    },
}

impl ContactRole {
    /// A short name for receipts.
    pub const fn label(&self) -> &'static str {
        match self {
            Self::UnanimouslyFormed { .. } => "unanimously-formed",
            Self::UnanimouslyExcluded { .. } => "unanimously-excluded",
            Self::Separating { .. } => "separating",
            Self::OpenCarrying { .. } => "open-carrying",
        }
    }
}

/// **The partition of the addressed contacts by their role across the fibre.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FibrePartition {
    /// The schema this partition serializes under.
    pub schema: String,
    /// The members it is a partition across.
    pub members: Vec<OccurrenceId>,
    /// How many contacts the receiver addresses.
    pub contacts: usize,
    /// Contacts every member decided formed.
    pub unanimously_formed: Vec<(u32, u32)>,
    /// Contacts every member decided excluded.
    pub unanimously_excluded: Vec<(u32, u32)>,
    /// Contacts the members decided differently.
    pub separating: Vec<(u32, u32)>,
    /// Contacts at least one member left undecided.
    pub open_carrying: Vec<(u32, u32)>,
}

impl FibrePartition {
    /// The unanimous set: the contacts every member decided the same way.
    ///
    /// Lean counterpart: `unanimous`, with `unanimous_antitone`.
    pub fn unanimous(&self) -> BTreeSet<(u32, u32)> {
        self.unanimously_formed
            .iter()
            .chain(&self.unanimously_excluded)
            .copied()
            .collect()
    }

    /// **The four roles are disjoint and exhaust the addressed contacts.** Checked rather than
    /// asserted, so a future role cannot be added without this returning `false`.
    pub fn is_a_partition(&self) -> bool {
        let mut all: BTreeSet<(u32, u32)> = BTreeSet::new();
        let mut counted = 0_usize;
        for group in [
            &self.unanimously_formed,
            &self.unanimously_excluded,
            &self.separating,
            &self.open_carrying,
        ] {
            counted += group.len();
            for pair in group {
                all.insert(*pair);
            }
        }
        counted == self.contacts && all.len() == self.contacts
    }
}

// ---------------------------------------------------------------------------------------------
// Unanimity: what it establishes, and what it cannot
// ---------------------------------------------------------------------------------------------

/// **A proof that two occurrences are one realized source.**
///
/// [definition] This enum has **no constructors**. Nothing in this owner — no amount of agreement
/// across any number of predictors, seeds and environments — produces a value of it. Agreement at a
/// receiver is `R`-indistinguishability and never identity of sources, and that statement is a fact
/// about this type rather than a rule someone must remember.
///
/// Lean counterpart: `agreement_does_not_prove_realization`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RealizationProof {}

/// What unanimity across the fibre establishes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UnanimityReceipt {
    /// The schema this receipt serializes under.
    pub schema: String,
    /// The members it is a statement about.
    pub members: Vec<OccurrenceId>,
    /// How many contacts every member decided the same way.
    pub unanimous_contacts: usize,
    /// How many contacts the members decided differently.
    pub separating_contacts: usize,
    /// How many contacts at least one member left undecided.
    pub open_carrying_contacts: usize,
    /// **The member pairs no contact separates.** These are indistinguishable at this receiver, so
    /// the preimage fibre over them stays plural.
    pub indistinguishable_pairs: Vec<(OccurrenceId, OccurrenceId)>,
}

impl UnanimityReceipt {
    /// **Always `None`.** [`RealizationProof`] is uninhabited, so agreement cannot become a claim
    /// that two occurrences are one source through any path in this owner.
    pub const fn realization_proof(&self) -> Option<RealizationProof> {
        None
    }

    /// Whether the fibre is still plural at this receiver: at least one member pair is
    /// indistinguishable.
    pub fn stays_plural(&self) -> bool {
        !self.indistinguishable_pairs.is_empty()
    }
}

// ---------------------------------------------------------------------------------------------
// The declared bound on the minimum hitting set search
// ---------------------------------------------------------------------------------------------

/// **A declared bound on the exact minimum-hitting-set search.**
///
/// [definition] Minimum hitting set is NP-hard, so the bound is not decoration: it is the declared
/// receiver aperture of the search. The fields are private and [`HittingSetBound::declare`] refuses
/// a zero ceiling, a zero cardinality and an unstated ground. `Deserialize` is not derived — a
/// remount would be a second constructor bypassing those checks.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HittingSetBound {
    max_cardinality: usize,
    max_search_nodes: BigUint,
    ground: String,
}

impl HittingSetBound {
    /// Declare the bound. Refuses a zero cardinality, a zero node ceiling and an unstated ground.
    pub fn declare(
        max_cardinality: usize,
        max_search_nodes: impl Into<BigUint>,
        ground: impl Into<String>,
    ) -> Result<Self, FibreRefusal> {
        let ground = ground.into();
        let max_search_nodes = max_search_nodes.into();
        if ground.trim().is_empty() {
            return Err(FibreRefusal::HittingSetGroundNotStated);
        }
        if max_cardinality == 0 || max_search_nodes.is_zero() {
            return Err(FibreRefusal::HittingSetBoundIsZero {
                max_cardinality,
                max_search_nodes,
            });
        }
        Ok(Self {
            max_cardinality,
            max_search_nodes,
            ground,
        })
    }

    /// The greatest receiver size the search will consider.
    pub const fn max_cardinality(&self) -> usize {
        self.max_cardinality
    }

    /// The greatest number of search-tree nodes admitted.
    pub const fn max_search_nodes(&self) -> &BigUint {
        &self.max_search_nodes
    }

    /// The ground the bound was declared on.
    pub fn ground(&self) -> &str {
        &self.ground
    }
}

/// **What the minimum separating receiver is.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum MinimalSeparation {
    /// Two members have an empty separator set. No receiver built from these contacts
    /// distinguishes them, so the fibre stays plural however many contacts are read.
    Unseparable {
        /// One of the two members.
        left: OccurrenceId,
        /// The other.
        right: OccurrenceId,
        /// How many contacts between them carry an open reading and are therefore not candidates.
        open_carrying: usize,
    },
    /// Every minimum-cardinality receiver that distinguishes all members, complete at that size.
    Minimum {
        /// The minimum size.
        cardinality: usize,
        /// Every receiver of that size, sorted. Never a representative.
        sets: Vec<Vec<(u32, u32)>>,
    },
}

impl MinimalSeparation {
    /// The minimum cardinality, when the fibre is separable at all.
    pub const fn cardinality(&self) -> Option<usize> {
        match self {
            Self::Minimum { cardinality, .. } => Some(*cardinality),
            Self::Unseparable { .. } => None,
        }
    }

    /// How many distinct minimum receivers were found.
    pub fn witnesses(&self) -> usize {
        match self {
            Self::Minimum { sets, .. } => sets.len(),
            Self::Unseparable { .. } => 0,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// A reading of the fibre as a table, for receipts
// ---------------------------------------------------------------------------------------------

/// The role of every addressed contact, as a map. Useful for a receipt; the partition is the
/// structure.
pub fn role_table(fibre: &PluralFibre) -> BTreeMap<(u32, u32), &'static str> {
    let partition = fibre.partition();
    let mut table = BTreeMap::new();
    for pair in &partition.unanimously_formed {
        table.insert(*pair, "unanimously-formed");
    }
    for pair in &partition.unanimously_excluded {
        table.insert(*pair, "unanimously-excluded");
    }
    for pair in &partition.separating {
        table.insert(*pair, "separating");
    }
    for pair in &partition.open_carrying {
        table.insert(*pair, "open-carrying");
    }
    table
}

// ---------------------------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------------------------

/// Why a fibre, a separator set or a minimum-hitting-set search refused.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum FibreRefusal {
    /// A fibre was founded over fewer than two faces.
    #[error(
        "a fibre over {members} face(s) is not a plural fibre; separation between members is not \
         a question one face can be asked"
    )]
    NotPlural {
        /// How many faces were offered.
        members: usize,
    },
    /// A member is a face of a different object.
    #[error(
        "occurrence {occurrence:?} is a face of a different object; a fibre stands over one \
         candidate and agreement between two candidates narrows nothing"
    )]
    ObjectDiffersInTheFibre {
        /// The offending member.
        occurrence: OccurrenceId,
    },
    /// A member was classified against a different aperture, so it is a reading at another
    /// receiver.
    #[error(
        "occurrence {occurrence:?} was read against {presented:?} while the fibre's receiver is \
         {declared:?}; two apertures are two receivers and separation at one says nothing at the \
         other"
    )]
    ApertureDiffersInTheFibre {
        /// The offending member.
        occurrence: OccurrenceId,
        /// The fibre's declared aperture lineage.
        declared: String,
        /// The member's own.
        presented: String,
    },
    /// An occurrence identity appears twice.
    #[error("occurrence {occurrence:?} appears twice; a fibre's members are distinct occurrences")]
    OccurrenceRepeatedInTheFibre {
        /// The repeated identity.
        occurrence: OccurrenceId,
    },
    /// Two members address different numbers of contacts.
    #[error("occurrences {left:?} and {right:?} address {left_pairs} and {right_pairs} contacts")]
    PairPopulationDisagrees {
        /// The first member.
        left: OccurrenceId,
        /// The second.
        right: OccurrenceId,
        /// How many the first addresses.
        left_pairs: usize,
        /// How many the second addresses.
        right_pairs: usize,
    },
    /// Two members address the contacts in a different order.
    #[error(
        "occurrences {left:?} and {right:?} are not in the same contact order: {left_pair:?} \
         against {right_pair:?}"
    )]
    PairOrderDisagrees {
        /// The first member.
        left: OccurrenceId,
        /// The second.
        right: OccurrenceId,
        /// The first member's contact.
        left_pair: (u32, u32),
        /// The second member's contact.
        right_pair: (u32, u32),
    },
    /// A member index was asked for that the fibre does not carry.
    #[error("the fibre carries no member at index {at}")]
    MemberIndexAbsent {
        /// The index asked for.
        at: usize,
    },
    /// A contact was asked for that the receiver does not address.
    #[error("the receiver does not address the contact {pair:?}")]
    ContactNotAddressed {
        /// The contact asked for.
        pair: (u32, u32),
    },
    /// A hitting-set bound carried no ground.
    #[error("a bound on an NP-hard search needs a stated ground; an empty one is a magic number")]
    HittingSetGroundNotStated,
    /// A hitting-set bound admitted nothing.
    #[error(
        "the declared bound admits no search at all: cardinality {max_cardinality}, node ceiling \
         {max_search_nodes}"
    )]
    HittingSetBoundIsZero {
        /// The declared cardinality.
        max_cardinality: usize,
        /// The declared node ceiling.
        max_search_nodes: BigUint,
    },
    /// The exact worst-case node count of the whole iterative-deepening search exceeds the
    /// declared ceiling.
    #[error(
        "the exact minimum-hitting-set search over branching {branching} restarts once per \
         cardinality 1..={depth} and visits at least {worst_case_nodes} nodes over its first \
         {rounds_counted} round(s), above the declared ceiling {declared_ceiling} ({ground}). \
         Minimum hitting set is NP-hard; this owner refuses rather than approximating"
    )]
    HittingSetSearchTooWide {
        /// The largest separator set's size.
        branching: usize,
        /// The search depth actually needed, which is the number of cardinality rounds.
        depth: usize,
        /// The exact worst-case node count summed over the first `rounds_counted` rounds. When
        /// `rounds_counted == depth` this is the complete count `Σ_{c=1}^{depth} Σ_{i=0}^{c} b^i`;
        /// when it is smaller the true count is strictly larger than this.
        worst_case_nodes: BigUint,
        /// How many of the `depth` cardinality rounds `worst_case_nodes` covers.
        rounds_counted: usize,
        /// The declared ceiling.
        declared_ceiling: BigUint,
        /// The ground the ceiling was declared on.
        ground: String,
    },
    /// No receiver of the declared size separates every member pair.
    #[error(
        "no receiver of {searched} or fewer contacts separates all {pairs} member pairs; the \
         declared cardinality was {declared}"
    )]
    NoSeparatingSetWithinCardinality {
        /// The declared cardinality.
        declared: usize,
        /// The depth actually searched.
        searched: usize,
        /// How many member pairs had to be separated.
        pairs: usize,
    },
}

#[cfg(test)]
#[path = "plural_fibre/tests.rs"]
mod tests;
