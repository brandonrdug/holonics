//! Placement, which is not returned until a realizer paid for it.
//!
//! `CLAUDE.md` §2: *"**Do not build modal placement and supported lifting as two organs.** Derive
//! placement from realization. A returned placement that no realizer paid for has smuggled an
//! absolute frame into the engine; that is the half-rank razor firing at the level of
//! architecture."* And: *"**FOUND pays curvature; RIDE is cheap because the terrain already paid.**
//! Realization pays; placement rides."*
//!
//! `receiver_exact_compression` and `supported_realizers` were built as two organs with placement
//! returning first and support auditing it afterwards — the architecture that consequence forbids.
//! This is the composition, and it is the entry point. Neither of those modules should be called
//! directly to decide what stands.
//!
//! ```text
//!   conduct class with a realizer  ->  STANDING
//!   conduct class with none        ->  OPEN, and never a class
//! ```
//!
//! ## Founding and coarsening are different discharges and the reading says which
//!
//! A support obstruction can be discharged two ways: found a realizer that reaches the class, or
//! remove a receiver so the class stops being distinguished. Both leave a clean matrix, and
//! comparing two readings by their obstruction alone cannot tell them apart. So a reading carries
//! the **receiver extent** and the **class extent** it was taken at, and `discharge` names which
//! happened.
//!
//! Neither is forbidden. Coarsening is the correct move when the classes were manufactured by a
//! receiver reporting an absolute coordinate — H.0016's own transformations clause says enlarging
//! the family can *invalidate* a compression. What is forbidden is not being able to tell.

use std::collections::BTreeSet;

use num_bigint::BigInt;
use serde::{Deserialize, Serialize};

use crate::receiver_exact_compression::{
    compress, ItemId, ObservedSystem, ReceiverExactCompression,
};
use crate::supported_realizers::{decide_support, Realization, RealizerId, RealizerSupport};

/// A class a realizer paid for.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StandingClass {
    pub class: usize,
    pub members: BTreeSet<ItemId>,
    /// The realizers that reach it. Never empty — that is the invariant this type exists for.
    pub realizers: Vec<RealizerId>,
}

/// A class the receivers distinguish and nothing reaches. OPEN, never standing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpenClass {
    pub class: usize,
    pub members: BTreeSet<ItemId>,
    /// Present when something reaches it only in multiple: supported rationally, not integrally.
    pub reached_only_in_multiple: Option<BigInt>,
}

/// What placement returns.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Placement {
    pub schema: String,
    pub standing: Vec<StandingClass>,
    pub open: Vec<OpenClass>,
    /// The aperture this reading was taken at. Carried so that a later reading can be compared
    /// against it and the kind of discharge named.
    pub receiver_extent: usize,
    pub class_extent: usize,
    pub compression: ReceiverExactCompression,
    pub support: RealizerSupport,
}

impl Placement {
    /// Every distinguished class was paid for.
    pub fn closed(&self) -> bool {
        self.open.is_empty()
    }

    /// The invariant §2 demands: nothing stands that no realizer reached.
    pub fn every_standing_class_was_paid_for(&self) -> bool {
        self.standing
            .iter()
            .all(|class| !class.realizers.is_empty())
    }
}

/// How a later reading discharged what an earlier one left open.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Discharge {
    /// The receiver family shrank, so classes stopped being distinguished. Lawful, and never to be
    /// confused with production.
    Coarsened,
    /// The realizer population grew and reached what was open. This is the FOUND that pays.
    Founded,
    /// Both moved. Reported rather than guessed at.
    Both,
    /// Nothing was open, or nothing changed.
    Nothing,
}

/// Name the kind of discharge between two readings. Without this, founding and coarsening are
/// indistinguishable by their returns, which they are.
pub fn discharge(before: &Placement, after: &Placement) -> Discharge {
    if before.open.is_empty() || after.open.len() >= before.open.len() {
        return Discharge::Nothing;
    }
    let coarsened = after.receiver_extent < before.receiver_extent
        || after.class_extent < before.class_extent;
    let founded = after.support.realizer_extent > before.support.realizer_extent;
    match (coarsened, founded) {
        (true, true) => Discharge::Both,
        (true, false) => Discharge::Coarsened,
        (false, true) => Discharge::Founded,
        (false, false) => Discharge::Nothing,
    }
}

/// Decide placement: refine to the conduct classes, then return only what a realizer paid for.
///
/// `reaches` is asked, per realizer, which items its production lands on. Landing on an item places
/// the realizer in that item's conduct class.
pub fn place(
    system: &dyn ObservedSystem,
    realizers: &[RealizerId],
    mut reaches: impl FnMut(RealizerId) -> Vec<ItemId>,
) -> Placement {
    let compression = compress(system);
    let class_extent = compression.conduct.len();

    let mut realizations: Vec<Realization> = Vec::with_capacity(realizers.len());
    let mut reached_by: Vec<Vec<RealizerId>> = vec![Vec::new(); class_extent];
    for realizer in realizers {
        let mut landings = std::collections::BTreeMap::new();
        for item in reaches(*realizer) {
            if let Some(class) = compression.conduct.block_of(item) {
                *landings.entry(class).or_insert_with(|| BigInt::from(0)) += 1;
                if !reached_by[class].contains(realizer) {
                    reached_by[class].push(*realizer);
                }
            }
        }
        realizations.push(Realization {
            realizer: *realizer,
            landings,
        });
    }

    let support = decide_support(&realizations, class_extent);
    let torsion = support.torsion_obstruction();

    let mut standing = Vec::new();
    let mut open = Vec::new();
    for (class, members) in compression.conduct.blocks.iter().enumerate() {
        if reached_by[class].is_empty() {
            open.push(OpenClass {
                class,
                members: members.clone(),
                reached_only_in_multiple: None,
            });
            continue;
        }
        // Reached, but every landing a proper multiple: rationally supported, integrally not.
        let only_multiple = realizations
            .iter()
            .filter_map(|realization| realization.landings.get(&class))
            .fold(None::<BigInt>, |accumulated, count| {
                Some(match accumulated {
                    None => count.clone(),
                    Some(previous) => gcd(&previous, count),
                })
            })
            .filter(|shared| *shared > BigInt::from(1))
            .filter(|shared| torsion.contains(shared));
        if let Some(factor) = only_multiple {
            open.push(OpenClass {
                class,
                members: members.clone(),
                reached_only_in_multiple: Some(factor),
            });
            continue;
        }
        standing.push(StandingClass {
            class,
            members: members.clone(),
            realizers: reached_by[class].clone(),
        });
    }

    Placement {
        schema: "holonic-engine.placement.v1".to_owned(),
        receiver_extent: system.receivers().len(),
        class_extent,
        standing,
        open,
        compression,
        support,
    }
}

fn gcd(left: &BigInt, right: &BigInt) -> BigInt {
    let mut a = left.clone();
    let mut b = right.clone();
    while b != BigInt::from(0) {
        let next = a % &b;
        a = b;
        b = next;
    }
    if a < BigInt::from(0) { -a } else { a }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::receiver_exact_compression::{InputId, Observation, ReceiverId};

    /// Four items in four conduct classes, one input, receivers reading the item directly.
    struct Four {
        receivers: usize,
    }
    impl ObservedSystem for Four {
        fn items(&self) -> Vec<ItemId> {
            (0..4).map(ItemId).collect()
        }
        fn receivers(&self) -> Vec<ReceiverId> {
            (0..self.receivers as u64).map(ReceiverId).collect()
        }
        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0)]
        }
        fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
            // Receiver 0 separates everything; receiver 1 only sees parity.
            if receiver.0 == 0 {
                Observation(item.0)
            } else {
                Observation(item.0 % 2)
            }
        }
        fn successor(&self, item: ItemId, _input: InputId) -> Option<ItemId> {
            Some(item)
        }
    }

    #[test]
    fn a_class_no_realizer_reaches_is_open_and_never_standing() {
        let system = Four { receivers: 1 };
        let placed = place(&system, &[RealizerId(0), RealizerId(1)], |realizer| {
            vec![ItemId(realizer.0)]
        });
        assert_eq!(placed.standing.len(), 2);
        assert_eq!(placed.open.len(), 2);
        assert!(!placed.closed());
        assert!(placed.every_standing_class_was_paid_for());
        for open in &placed.open {
            assert!(
                placed.standing.iter().all(|standing| standing.class != open.class),
                "an OPEN class must never also stand"
            );
        }
    }

    #[test]
    fn founding_a_realizer_closes_it_and_is_named_as_founding() {
        let system = Four { receivers: 1 };
        let before = place(&system, &[RealizerId(0), RealizerId(1)], |realizer| {
            vec![ItemId(realizer.0)]
        });
        let after = place(
            &system,
            &[RealizerId(0), RealizerId(1), RealizerId(2), RealizerId(3)],
            |realizer| vec![ItemId(realizer.0)],
        );
        assert!(after.closed());
        assert_eq!(discharge(&before, &after), Discharge::Founded);
    }

    /// The same obstruction discharged by removing a receiver. The returns are otherwise
    /// indistinguishable from founding, which is exactly why the reading carries its aperture.
    #[test]
    fn coarsening_closes_it_too_and_is_named_as_coarsening() {
        let before = place(&Four { receivers: 1 }, &[RealizerId(0), RealizerId(1)], |r| {
            vec![ItemId(r.0)]
        });
        // Receiver 1 sees only parity, so items 0,2 and 1,3 merge into two classes, both reached.
        let after = place(&Four { receivers: 0 }, &[RealizerId(0), RealizerId(1)], |r| {
            vec![ItemId(r.0)]
        });
        assert!(before.open.len() > after.open.len(), "the obstruction was discharged");
        assert_eq!(discharge(&before, &after), Discharge::Coarsened);
        assert_ne!(
            discharge(&before, &after),
            Discharge::Founded,
            "coarsening must never read as production"
        );
    }

    /// A class reached only in multiple is OPEN, not standing. Rational support is not integral
    /// support, and placement takes the integral question.
    #[test]
    fn a_class_reached_only_in_multiple_does_not_stand() {
        struct One;
        impl ObservedSystem for One {
            fn items(&self) -> Vec<ItemId> {
                vec![ItemId(0)]
            }
            fn receivers(&self) -> Vec<ReceiverId> {
                vec![ReceiverId(0)]
            }
            fn inputs(&self) -> Vec<InputId> {
                vec![InputId(0)]
            }
            fn observation(&self, _: ItemId, _: ReceiverId) -> Observation {
                Observation(0)
            }
            fn successor(&self, item: ItemId, _: InputId) -> Option<ItemId> {
                Some(item)
            }
        }
        let placed = place(&One, &[RealizerId(0)], |_| vec![ItemId(0), ItemId(0)]);
        assert!(placed.standing.is_empty(), "a doubled reach does not pay");
        assert_eq!(placed.open.len(), 1);
        assert_eq!(
            placed.open[0].reached_only_in_multiple,
            Some(BigInt::from(2))
        );
    }

    #[test]
    fn nothing_produced_leaves_every_class_open() {
        let placed = place(&Four { receivers: 1 }, &[], |_| Vec::new());
        assert!(placed.standing.is_empty());
        assert_eq!(placed.open.len(), 4);
        assert!(!placed.closed());
        assert!(placed.every_standing_class_was_paid_for());
    }
}
