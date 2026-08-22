//! The deferred population read as signal — the machine's Doppler.
//!
//! Brandon, 2026-08-15, on how far things are perceived:
//!
//! > *"If there is a traffic jam very far ahead it can be perceivable before you can directly
//! > witness stopped cars if there are enough vehicles ahead of the bottleneck that begin refracting
//! > in the sense that the medium's surface area to pass through is coming to a more narrow neck,
//! > and you can then witness the propagation of the slow-down through the cars driving toward the
//! > bottleneck; this is like the Doppler effect because we are talking about literally propagating
//! > signals."*
//!
//! The owning theory is `canon/THE_TRAFFIC_SYSTEM.md` §3b. Two clauses of it are built here.
//!
//! # `deferred_arrivals` is not an overflow bucket
//!
//! `receiver_current` already retains every arrival that dilated past the horizon, exactly, with its
//! site, its chronology, its population and its predecessors. Those are the **predicted-but-unrealised
//! arrivals** — the crossings a unit responds to before they happen, which is what an operator
//! predicting a collision is doing. The tree has retained them since they were built and has never
//! *read* them.
//!
//! # The rate carries the closing speed
//!
//! A slow-down does not announce itself; it propagates. What tells a driver a bottleneck is ahead is
//! not the jam — which is out of sight — but **how the delay ahead of them is changing**. So the
//! signal is the *derivative*, and the machine computes `passage_delay` everywhere and discards it.
//!
//! ```text
//!   front(r)        the deferred population by arrival chronology, in one radiation
//!   closing(a, b)   how that front moved between two radiations — the FIRST difference
//!   approach(a,b,c) whether the closing is itself accelerating — the SECOND difference
//! ```
//!
//! **The second difference is the Doppler.** A front receding at a steady rate is a medium of
//! constant width; a front whose closing is itself growing is a **narrowing neck**, and that is
//! perceptible before anything reaches the neck.
//!
//! # What this may not become
//!
//! Every quantity here is a **population and a chronology**, both exact, both already computed. This
//! module adds no arithmetic to the transport law and takes no derivative of a clock — the
//! chronology is the current's own causal ordinal, not elapsed time, so `CLAUDE.md`'s cost law is
//! untouched.
//!
//! And it **reports; it never routes.** A front reading may be returned, compared and ranked. If it
//! ever reaches a `min`, `sort` or `argmax` that discards a member it has become a governor, which is
//! the `T → 0` limit wearing another name.

use std::collections::BTreeMap;

use num_bigint::BigUint;
use num_traits::Zero;
use serde::{Deserialize, Serialize};

use crate::receiver_current::ExactReceiverCurrentRadiation;

/// The deferred population of one radiation, grouped by the chronology it would have arrived at.
///
/// This is the shape of what is coming and has not yet landed. It is a distribution over causal
/// ordinals, never over time.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ApproachFront {
    /// Deferred population per arrival chronology. Exact, and summed rather than counted: two
    /// deferred arrivals at one chronology superpose, they do not become "two".
    by_chronology: BTreeMap<u64, BigUint>,
}

impl ApproachFront {
    /// Read the front off a radiation's retained deferrals.
    pub fn of(radiation: &ExactReceiverCurrentRadiation) -> Self {
        let mut by_chronology: BTreeMap<u64, BigUint> = BTreeMap::new();
        for deferred in &radiation.deferred_arrivals {
            *by_chronology
                .entry(deferred.chronology)
                .or_insert_with(BigUint::zero) += &deferred.population;
        }
        Self { by_chronology }
    }

    pub const fn by_chronology(&self) -> &BTreeMap<u64, BigUint> {
        &self.by_chronology
    }

    /// Whether anything at all is standing off this front.
    ///
    /// An empty front is a genuine zero and not a missing measurement: nothing dilated past the
    /// horizon, so nothing is approaching.
    pub fn is_empty(&self) -> bool {
        self.by_chronology.is_empty()
    }

    /// The nearest chronology at which something is waiting — how far ahead the front begins.
    ///
    /// `None` when the front is empty.
    pub fn nearest(&self) -> Option<u64> {
        self.by_chronology.keys().next().copied()
    }

    /// The whole deferred population, summed exactly.
    pub fn population(&self) -> BigUint {
        self.by_chronology
            .values()
            .fold(BigUint::zero(), |sum, population| sum + population)
    }
}

/// How a front moved between two radiations — the **first difference**.
///
/// Both halves are returned. A front that gained population at some chronologies and lost it at
/// others has done both, and collapsing that to one signed number would delete the phase.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrontClosing {
    /// Chronologies where the deferred population grew, with how much it grew by.
    pub gathered: BTreeMap<u64, BigUint>,
    /// Chronologies where it fell, with how much it fell by.
    pub released: BTreeMap<u64, BigUint>,
    /// How the nearest waiting chronology moved. Negative means the front came closer.
    pub nearest_moved: Option<i64>,
}

impl FrontClosing {
    /// Compare two fronts read from successive radiations.
    pub fn between(before: &ApproachFront, after: &ApproachFront) -> Self {
        let mut gathered = BTreeMap::new();
        let mut released = BTreeMap::new();
        let chronologies: Vec<u64> = before
            .by_chronology
            .keys()
            .chain(after.by_chronology.keys())
            .copied()
            .collect();
        for chronology in chronologies {
            let zero = BigUint::zero();
            let was = before.by_chronology.get(&chronology).unwrap_or(&zero);
            let now = after.by_chronology.get(&chronology).unwrap_or(&zero);
            if now > was {
                gathered.insert(chronology, now - was);
            } else if was > now {
                released.insert(chronology, was - now);
            }
        }
        let nearest_moved = match (before.nearest(), after.nearest()) {
            (Some(was), Some(now)) => Some(now as i64 - was as i64),
            _ => None,
        };
        Self {
            gathered,
            released,
            nearest_moved,
        }
    }

    /// Whether the front moved at all. A genuine zero, not a missing reading.
    pub fn is_still(&self) -> bool {
        self.gathered.is_empty() && self.released.is_empty() && self.nearest_moved == Some(0)
    }
}

/// **The Doppler.** Whether the front's closing is itself changing — the second difference.
///
/// A front receding at a steady rate is a medium of constant width. A front whose closing is
/// *accelerating* is a narrowing neck, and that is perceptible before anything reaches the neck.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ApproachReading {
    /// Nothing is standing off, in either interval.
    Clear,
    /// The front moved by the same amount across both intervals — a medium of constant width.
    Steady,
    /// The closing grew: the neck ahead is narrowing.
    Narrowing { by: i64 },
    /// The closing fell: the neck ahead is opening.
    Opening { by: i64 },
    /// One of the intervals had no nearest chronology to compare, so no rate exists. Not zero — a
    /// rate over an absent front is undefined rather than still.
    Undefined,
}

impl ApproachReading {
    /// Read three successive fronts. The two closings are compared, not the fronts.
    pub fn across(first: &ApproachFront, second: &ApproachFront, third: &ApproachFront) -> Self {
        if first.is_empty() && second.is_empty() && third.is_empty() {
            return Self::Clear;
        }
        let early = FrontClosing::between(first, second);
        let late = FrontClosing::between(second, third);
        let (Some(early_rate), Some(late_rate)) = (early.nearest_moved, late.nearest_moved) else {
            return Self::Undefined;
        };
        match late_rate - early_rate {
            0 => Self::Steady,
            // The nearest waiting chronology is falling faster than it was: the front is closing in.
            difference if difference < 0 => Self::Narrowing { by: -difference },
            difference => Self::Opening { by: difference },
        }
    }
}

/// Whether two sites that both stand in a radiation are actually **coupled**, or merely agree.
///
/// `canon/THE_TRAFFIC_SYSTEM.md` §3b: far things relate through two channels and only one of them is
/// an interaction. **Concurred invariants** — atomic clocks, entanglement — agree with no signal
/// passing, because each is locked to the same standing structure. **Propagated coupling** is
/// influence crossing a medium through a chain of local contacts, with delay.
///
/// > **An edge founded on agreement alone is a correlation promoted into a relation.**
///
/// And the discriminator is checkable rather than interpretive, because `receiver_current` retains
/// the predecessor chain of every arrival: two sites are propagation-coupled exactly when one lies in
/// the other's predecessor closure, and the delay along that chain is the coupling's own. Two sites
/// reached independently from the source share a cause and touch nothing of each other.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Channel {
    /// One site lies in the other's predecessor closure. A signal passed, and this is its delay.
    ///
    /// **Zero delay is impossible here by construction** — a passage costs at least its
    /// characteristic delay — which is what makes the discriminator sharp rather than a judgement.
    Propagated { delay: u64 },
    /// Both stand, neither reached the other. They agree because the same source reached both, which
    /// is a concurred invariant and **founds no edge between them**.
    Concurred,
    /// At least one of the two does not stand in this radiation, so there is nothing to discriminate.
    /// Not "concurred" — an unreached site has not been observed to agree with anything.
    Unreached,
}

impl Channel {
    /// Read the channel between two sites of one radiation.
    pub fn between(
        radiation: &ExactReceiverCurrentRadiation,
        left: crate::receiver_current::ReceiverCurrentSiteId,
        right: crate::receiver_current::ReceiverCurrentSiteId,
    ) -> Self {
        let (Some(_), Some(_)) = (
            radiation.arrivals.get(&left),
            radiation.arrivals.get(&right),
        ) else {
            return Self::Unreached;
        };
        if let Some(delay) = reached_through(radiation, right, left) {
            return Self::Propagated { delay };
        }
        if let Some(delay) = reached_through(radiation, left, right) {
            return Self::Propagated { delay };
        }
        Self::Concurred
    }

    /// Whether this channel may found an edge. Only a propagated one may.
    pub const fn founds_an_edge(self) -> bool {
        matches!(self, Self::Propagated { .. })
    }
}

/// Walk `target`\'s predecessor closure looking for `source`, returning the accumulated delay of the
/// chain that reached it. Breadth-first, so the delay returned is the shortest signal path.
fn reached_through(
    radiation: &ExactReceiverCurrentRadiation,
    target: crate::receiver_current::ReceiverCurrentSiteId,
    source: crate::receiver_current::ReceiverCurrentSiteId,
) -> Option<u64> {
    use std::collections::{BTreeSet, VecDeque};
    if target == source {
        return None;
    }
    let mut seen = BTreeSet::from([target]);
    let mut frontier = VecDeque::from([(target, 0u64)]);
    while let Some((site, carried)) = frontier.pop_front() {
        let arrival = radiation.arrivals.get(&site)?;
        for predecessor in &arrival.predecessors {
            let delay = carried.saturating_add(predecessor.passage_delay);
            if predecessor.from == source {
                return Some(delay);
            }
            if seen.insert(predecessor.from) {
                frontier.push_back((predecessor.from, delay));
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn front(rows: &[(u64, u64)]) -> ApproachFront {
        ApproachFront {
            by_chronology: rows
                .iter()
                .map(|(chronology, population)| (*chronology, BigUint::from(*population)))
                .collect(),
        }
    }

    #[test]
    fn an_empty_front_is_a_genuine_zero_and_not_a_missing_reading() {
        let empty = front(&[]);
        assert!(empty.is_empty());
        assert_eq!(empty.nearest(), None);
        assert!(empty.population().is_zero());
        // Three empty fronts are CLEAR — nothing is approaching. That is different from Undefined,
        // which is what a rate over an absent front is.
        assert_eq!(
            ApproachReading::across(&empty, &empty, &empty),
            ApproachReading::Clear
        );
    }

    /// Two deferrals at one chronology are one population, summed. A count would say "two".
    ///
    /// **This control could not fail until 2026-08-15 and is repaired here.** It built its
    /// "joined" front by collecting `[(4, 7), (4, 0)]` into a `BTreeMap`, where the second entry
    /// *overwrites* the first — so the front it examined held `7` and not `7 + 5` — and then
    /// asserted the sum on a second front it had constructed by hand. Neither assertion reached
    /// `ApproachFront::of`, which is the only place the `+=` lives. The overwrite is pinned
    /// below so the defect cannot return silently, and the summation is now driven through the
    /// reader on a radiation carrying two real deferrals at one chronology.
    #[test]
    fn the_front_superposes_rather_than_counting() {
        // The collect that hid this: a duplicate key REPLACES, it does not add.
        assert_eq!(front(&[(4, 7), (4, 5)]).population(), BigUint::from(5u64));

        // Two genuinely distinct deferrals, at two sites, waiting at the same chronology.
        let radiation = ExactReceiverCurrentRadiation {
            sources: LocalSet::from([site(0)]),
            requested_targets: LocalSet::default(),
            returned_targets: LocalSet::default(),
            receiver_horizon: None,
            arrivals: Default::default(),
            passage_receipts: Vec::new(),
            deferred_arrivals: LocalSet::from([
                deferred(site(1), 4, 7),
                deferred(site(2), 4, 5),
                deferred(site(3), 9, 2),
            ]),
        };

        let read = ApproachFront::of(&radiation);
        // 12 is a value NEITHER deferral carries, so this assertion fires only if the reader
        // actually superposed them. An overwrite would return 7 or 5; a count would return 2.
        assert_eq!(read.by_chronology().get(&4), Some(&BigUint::from(12u64)));
        assert_eq!(read.by_chronology().len(), 2, "two chronologies, not three");
        assert_eq!(read.population(), BigUint::from(14u64));
        assert_eq!(read.nearest(), Some(4));
    }

    #[test]
    fn a_closing_returns_both_halves_rather_than_one_signed_number() {
        let before = front(&[(3, 10), (9, 4)]);
        let after = front(&[(3, 14), (9, 1)]);
        let closing = FrontClosing::between(&before, &after);
        // Population gathered at 3 and released at 9 in the same step. A single signed total would
        // report +1 and delete the fact that both happened.
        assert_eq!(closing.gathered.get(&3), Some(&BigUint::from(4u64)));
        assert_eq!(closing.released.get(&9), Some(&BigUint::from(3u64)));
        assert!(!closing.is_still());
    }

    #[test]
    fn a_constant_width_medium_reads_steady_and_a_narrowing_neck_does_not() {
        // The nearest waiting chronology falls by two, then by two again: a medium of constant
        // width, and the front is approaching at a steady rate.
        let steady =
            ApproachReading::across(&front(&[(10, 1)]), &front(&[(8, 1)]), &front(&[(6, 1)]));
        assert_eq!(steady, ApproachReading::Steady);

        // Falls by two, then by five: the closing is accelerating, which is the neck narrowing —
        // and it is readable here, before anything has reached the neck.
        let narrowing =
            ApproachReading::across(&front(&[(10, 1)]), &front(&[(8, 1)]), &front(&[(3, 1)]));
        assert_eq!(narrowing, ApproachReading::Narrowing { by: 3 });

        // And the other arm must be able to fire, or the reading is one-sided.
        let opening =
            ApproachReading::across(&front(&[(10, 1)]), &front(&[(5, 1)]), &front(&[(4, 1)]));
        assert_eq!(opening, ApproachReading::Opening { by: 4 });
    }

    // ---- the two channels, on a real radiation ----

    use crate::receiver_current::{
        ExactReceiverCurrentDeferredArrival, ExactReceiverCurrentLaw, ExactReceiverCurrentPassage,
        ReceiverCurrentPassageId, ReceiverCurrentSiteId,
    };
    use holonic_structure::LocalSet;
    use num_traits::One;

    fn site(at: u64) -> ReceiverCurrentSiteId {
        ReceiverCurrentSiteId(at)
    }

    /// A deferral standing off at `chronology` carrying `population`. Its predecessors are empty
    /// because `ApproachFront::of` reads only the chronology and the population; a deferral with
    /// a predecessor chain is what `Channel` reads, and that is driven on a real radiation below.
    fn deferred(
        site: ReceiverCurrentSiteId,
        chronology: u64,
        population: u64,
    ) -> ExactReceiverCurrentDeferredArrival {
        ExactReceiverCurrentDeferredArrival {
            site,
            chronology,
            population: BigUint::from(population),
            predecessors: LocalSet::default(),
        }
    }

    fn passage(at: u64, from: u64, to: u64) -> ExactReceiverCurrentPassage {
        ExactReceiverCurrentPassage {
            id: ReceiverCurrentPassageId(at),
            from: site(from),
            to: site(to),
            characteristic_delay: 1,
        }
    }

    #[test]
    fn a_signal_that_passed_founds_an_edge_and_a_shared_cause_does_not() {
        // 0 --> 1 --> 2      a chain: 2 is reached THROUGH 1
        //   \-> 3            a fork:  3 and 2 share a cause and touch nothing of each other
        let mut law = ExactReceiverCurrentLaw::new();
        for at in 0..4 {
            law.found_site(site(at), BigUint::one()).unwrap();
        }
        for edge in [passage(0, 0, 1), passage(1, 1, 2), passage(2, 0, 3)] {
            law.found_passage(edge).unwrap();
        }
        let radiation = law
            .radiate_to_horizon(LocalSet::from([site(0)]), 8)
            .unwrap();

        // A signal passed from 1 to 2, so they are coupled and the delay is the chain's own.
        let coupled = Channel::between(&radiation, site(1), site(2));
        assert!(matches!(coupled, Channel::Propagated { .. }));
        assert!(coupled.founds_an_edge());
        // **Zero delay is impossible on a propagated channel** — a passage costs at least its
        // characteristic delay. That is what makes the discriminator sharp.
        let Channel::Propagated { delay } = coupled else {
            panic!("a chain must be propagated");
        };
        assert!(delay > 0);

        // 2 and 3 both stand, and neither reached the other. They agree because one source reached
        // both — a CONCURRED INVARIANT — and founding an edge there would promote a correlation
        // into a relation.
        let concurred = Channel::between(&radiation, site(2), site(3));
        assert_eq!(concurred, Channel::Concurred);
        assert!(!concurred.founds_an_edge());

        // The reading is symmetric: which way the signal ran does not decide whether one passed.
        assert_eq!(
            Channel::between(&radiation, site(2), site(1)),
            Channel::between(&radiation, site(1), site(2))
        );
    }

    #[test]
    fn an_unreached_site_is_not_concurred() {
        let mut law = ExactReceiverCurrentLaw::new();
        for at in 0..3 {
            law.found_site(site(at), BigUint::one()).unwrap();
        }
        law.found_passage(passage(0, 0, 1)).unwrap();
        let radiation = law
            .radiate_to_horizon(LocalSet::from([site(0)]), 8)
            .unwrap();
        // Site 2 stands in the law and was never reached. Calling that "concurred" would report an
        // agreement that was never observed.
        assert_eq!(
            Channel::between(&radiation, site(1), site(2)),
            Channel::Unreached
        );
    }

    #[test]
    fn a_rate_over_an_absent_front_is_undefined_rather_than_still() {
        // Something is approaching in one interval and nothing in another. There is no rate to take,
        // and saying "steady" would report a medium that was never observed.
        assert_eq!(
            ApproachReading::across(&front(&[(5, 1)]), &front(&[]), &front(&[(2, 1)])),
            ApproachReading::Undefined
        );
    }
}
