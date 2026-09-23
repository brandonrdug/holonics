//! Atomic causal succession for an exact world law.
//!
//! [definition] **The event chart of motion** (plan phase 16,
//! `docs/plans/THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md`). An [`ExactEventLaw`] is the
//! Holon's motion charted by discrete occurrences: its standing is the configuration of a core
//! [`HolonState`], and the world's commit counts the events committed to it
//! ([`CausalWorld::state`]). An event is the effort a receiver supplies at the Holon's external
//! ports; the radiation of a successor is the flow the Holon returns at those ports. Every law's
//! refusals are one family [`EventRefusal<K>`]: the refusals every law shares (a repeated
//! occurrence, a malformed standing, a law/standing mismatch, a carrier overflow) and the law's
//! own kinds `K`. [`EventStanding<S>`] is the standing shape the laws repeat: a schema, the
//! admitted occurrences and the law's own quotient `S`.
//!
//! [definition] Retention law (`Foundation/Standing.lean::StandingLaw`,
//! `Foundation/Standing.lean::standingLaw_exists_iff_future_factors`): a standing retains only
//! what the law's future reads. An audit of the admitted testimony is returned per event in the
//! radiation and is not kept in the standing; a history-free standing reached by two histories is
//! one standing (`Foundation/Standing.lean::two_histories_leave_one_standing`).

use std::fmt;

use holonic_structure::CausalMembrane;
use serde::{Deserialize, Serialize};

pub use holonic_core::holon::HolonState;

use crate::{LogicalResourceReceipt, PhysicalResourceReceipt};

mod scaffold;

pub use scaffold::{AdmittedEvents, EventQuotient, EventRefusal, EventStanding, RefusalKind};
pub(crate) use scaffold::{event_refusal_from, event_standing_wire};

pub trait ExactEventLaw {
    type Standing: Clone + PartialEq + Eq;
    type Event;
    type Radiation;
    type Error;

    /// Derive a complete successor from one immutable predecessor.
    ///
    /// Implementations must not expose a partially changed standing body.
    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error>;
}

/// A complete successor: the next configuration and the flow the event returns at the Holon's
/// external ports (`radiation`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EventSuccessor<S, R> {
    pub standing_after: S,
    pub radiation: Vec<R>,
    pub logical_resources: Option<LogicalResourceReceipt>,
    pub physical_resources: Option<PhysicalResourceReceipt>,
}

impl<S, R> EventSuccessor<S, R> {
    /// The external-port flow of this successor.
    pub fn port_flow(&self) -> &[R] {
        &self.radiation
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransitionReceipt<R> {
    pub schema: String,
    pub ordinal: u64,
    pub radiation: Vec<R>,
    pub logical_resources: Option<LogicalResourceReceipt>,
    pub physical_resources: Option<PhysicalResourceReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ThroughTransitionError<LawError, CrossError> {
    Law(LawError),
    Cross(CrossError),
    OrdinalExtent,
}

impl<LawError: fmt::Display, CrossError: fmt::Display> fmt::Display
    for ThroughTransitionError<LawError, CrossError>
{
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Law(error) => write!(formatter, "the exact law refused the event: {error}"),
            Self::Cross(error) => write!(formatter, "the receiving membrane refused: {error}"),
            Self::OrdinalExtent => formatter.write_str("the causal-world ordinal was exhausted"),
        }
    }
}

impl<LawError, CrossError> std::error::Error for ThroughTransitionError<LawError, CrossError>
where
    LawError: std::error::Error + 'static,
    CrossError: std::error::Error + 'static,
{
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CausalWorldRestError {
    ZeroNextOrdinal,
}

impl fmt::Display for CausalWorldRestError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroNextOrdinal => {
                formatter.write_str("a causal-world rest cannot have successor ordinal zero")
            }
        }
    }
}

impl std::error::Error for CausalWorldRestError {}

/// A law and its current point: the standing is the configuration of a core [`HolonState`] whose
/// commit is the number of events committed; the next transition ordinal is `commit + 1`.
#[derive(Clone, Debug)]
pub struct CausalWorld<L: ExactEventLaw> {
    law: L,
    state: HolonState<L::Standing>,
}

impl<L: ExactEventLaw> CausalWorld<L> {
    pub fn new(law: L, standing: L::Standing) -> Self {
        Self {
            law,
            state: HolonState::at(standing, 0),
        }
    }

    pub fn standing(&self) -> &L::Standing {
        &self.state.configuration
    }

    /// The current point on the Holon: the standing and the committed-event count.
    pub fn state(&self) -> &HolonState<L::Standing> {
        &self.state
    }

    pub fn next_ordinal(&self) -> u64 {
        self.state.commit + 1
    }

    /// Remount a separately persisted typed standing and its exact transition horizon.
    ///
    /// The application owns the standing's native persistence format. This restores only the
    /// world's administrative successor ordinal and does not introduce a universal standing
    /// serializer.
    pub fn from_rest(
        law: L,
        standing: L::Standing,
        next_ordinal: u64,
    ) -> Result<Self, CausalWorldRestError> {
        if next_ordinal == 0 {
            return Err(CausalWorldRestError::ZeroNextOrdinal);
        }
        Ok(Self::from_state(
            law,
            HolonState::at(standing, next_ordinal - 1),
        ))
    }

    /// Remount a world at a core point: its standing and committed-event count.
    pub fn from_state(law: L, state: HolonState<L::Standing>) -> Self {
        Self { law, state }
    }

    /// Borrow the exact transition law which owns this world's succession.
    ///
    /// This exposes constitutive incidence for read-only source factoring; it
    /// does not allow callers to bypass the world's atomic `receive` mouth.
    pub fn law(&self) -> &L {
        &self.law
    }

    pub fn receive(
        &mut self,
        event: &L::Event,
    ) -> Result<TransitionReceipt<L::Radiation>, L::Error> {
        let successor = self.law.enact(&self.state.configuration, event)?;
        let ordinal = self.next_ordinal();
        self.state = HolonState::at(successor.standing_after, ordinal);
        Ok(TransitionReceipt {
            schema: "holonic-engine.transition-receipt.v1".to_owned(),
            ordinal,
            radiation: successor.radiation,
            logical_resources: successor.logical_resources,
            physical_resources: successor.physical_resources,
        })
    }

    /// Carry one typed law successor through another membrane before either standing commits.
    ///
    /// The crossing borrows the immutable predecessor and complete proposed successor. If either
    /// the law or crossing refuses, this world remains unchanged. Once the crossing succeeds, no
    /// fallible work remains here: the typed successor and its ordinal commit together. This is
    /// the joining seam for a reference law and a continuing live-current body; serialization and
    /// a universal payload enum are deliberately absent.
    pub fn receive_through<X, CrossError>(
        &mut self,
        event: &L::Event,
        cross: impl FnOnce(
            &L::Standing,
            &EventSuccessor<L::Standing, L::Radiation>,
        ) -> Result<X, CrossError>,
    ) -> Result<(TransitionReceipt<L::Radiation>, X), ThroughTransitionError<L::Error, CrossError>>
    {
        let ordinal = self
            .state
            .commit
            .checked_add(1)
            .ok_or(ThroughTransitionError::OrdinalExtent)?;
        ordinal
            .checked_add(1)
            .ok_or(ThroughTransitionError::OrdinalExtent)?;
        let successor = self
            .law
            .enact(&self.state.configuration, event)
            .map_err(ThroughTransitionError::Law)?;
        let crossed =
            cross(&self.state.configuration, &successor).map_err(ThroughTransitionError::Cross)?;
        self.state = HolonState::at(successor.standing_after, ordinal);
        Ok((
            TransitionReceipt {
                schema: "holonic-engine.transition-receipt.v1".to_owned(),
                ordinal,
                radiation: successor.radiation,
                logical_resources: successor.logical_resources,
                physical_resources: successor.physical_resources,
            },
            crossed,
        ))
    }
}

/// Exact reference laws and the live Soma current machine share this typed receiving contract.
/// The associated occurrence preserves the law's own event morphology; no universal token, byte
/// packet, or scalar adapter is inserted between the world and its receiver.
impl<L: ExactEventLaw> CausalMembrane for CausalWorld<L> {
    type Standing = L::Standing;
    type Occurrence<'a>
        = &'a L::Event
    where
        Self: 'a,
        L::Event: 'a;
    type Return = TransitionReceipt<L::Radiation>;
    type Error = L::Error;

    fn standing(&self) -> &Self::Standing {
        CausalWorld::standing(self)
    }

    fn receive_occurrence<'a>(
        &mut self,
        occurrence: Self::Occurrence<'a>,
    ) -> Result<Self::Return, Self::Error>
    where
        Self: 'a,
    {
        self.receive(occurrence)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug)]
    struct AddUnlessNegative;

    impl ExactEventLaw for AddUnlessNegative {
        type Standing = i64;
        type Event = i64;
        type Radiation = i64;
        type Error = &'static str;

        fn enact(
            &self,
            standing_before: &Self::Standing,
            event: &Self::Event,
        ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
            if *event < 0 {
                return Err("refused");
            }
            Ok(EventSuccessor {
                standing_after: standing_before + event,
                radiation: vec![*event],
                logical_resources: None,
                physical_resources: None,
            })
        }
    }

    #[test]
    fn refusal_does_not_create_a_false_partial_successor() {
        let mut world = CausalWorld::new(AddUnlessNegative, 3);
        assert_eq!(world.receive(&-2), Err("refused"));
        assert_eq!(*world.standing(), 3);
        assert_eq!(world.receive(&2).unwrap().ordinal, 1);
        assert_eq!(*world.standing(), 5);
    }

    #[test]
    fn crossing_refusal_discards_the_complete_typed_successor() {
        let mut world = CausalWorld::new(AddUnlessNegative, 3);
        let refusal = world.receive_through(&2, |before, successor| {
            assert_eq!(*before, 3);
            assert_eq!(successor.standing_after, 5);
            Err::<(), _>("cross refused")
        });
        assert_eq!(refusal, Err(ThroughTransitionError::Cross("cross refused")));
        assert_eq!(*world.standing(), 3);
        assert_eq!(world.receive(&1).unwrap().ordinal, 1);
    }

    #[test]
    fn the_world_is_a_core_point_whose_commit_counts_committed_events() {
        let mut world = CausalWorld::new(AddUnlessNegative, 3);
        assert_eq!(world.state(), &HolonState::at(3, 0));
        let receipt = world.receive(&4).unwrap();
        assert_eq!(receipt.ordinal, 1);
        assert_eq!(world.state(), &HolonState::at(7, 1));
        assert!(world.receive(&-1).is_err());
        assert_eq!(world.state().commit, 1);
        let remounted = CausalWorld::from_state(AddUnlessNegative, world.state().clone());
        assert_eq!(remounted.next_ordinal(), 2);
        let successor = AddUnlessNegative.enact(&7, &1).unwrap();
        assert_eq!(successor.port_flow(), &[1]);
    }

    #[test]
    fn typed_rest_restores_the_successor_horizon_without_a_common_wire() {
        let mut world = CausalWorld::new(AddUnlessNegative, 5);
        assert_eq!(world.receive(&2).unwrap().ordinal, 1);
        let standing = *world.standing();
        let next = world.next_ordinal();
        let mut remounted = CausalWorld::from_rest(AddUnlessNegative, standing, next).unwrap();
        assert_eq!(remounted.receive(&3).unwrap().ordinal, 2);
        assert_eq!(*remounted.standing(), 10);
        assert_eq!(
            CausalWorld::from_rest(AddUnlessNegative, 0, 0).unwrap_err(),
            CausalWorldRestError::ZeroNextOrdinal
        );
    }
}
