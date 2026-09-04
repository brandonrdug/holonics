//! Explicit interaction patterns between exposed occurrence ports.
//!
//! Independent juxtaposition does not imply contact.  An interaction pattern
//! names the exact ports, boundary species, hand, and temporal relation which
//! make two otherwise available occurrences participate in one construction.

use relational_geometry::ReceiverId;
use serde::{Deserialize, Serialize};

use crate::{BoundaryId, EventId};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct InteractionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum PortHand {
    Input,
    Output,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OccurrencePort {
    pub event: EventId,
    pub hand: PortHand,
    pub ordinal: usize,
}

impl OccurrencePort {
    pub fn input(event: EventId, ordinal: usize) -> Self {
        Self {
            event,
            hand: PortHand::Input,
            ordinal,
        }
    }

    pub fn output(event: EventId, ordinal: usize) -> Self {
        Self {
            event,
            hand: PortHand::Output,
            ordinal,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum InteractionTemporality {
    /// The emitted boundary becomes input to a genuinely later occurrence.
    CarriesPrecedence,
    /// Both ports participate in one same-predecessor event.
    CoPresent,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InteractionBond {
    pub source: OccurrencePort,
    pub target: OccurrencePort,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InteractionPattern {
    pub id: InteractionId,
    pub name: String,
    pub boundary: BoundaryId,
    pub temporality: InteractionTemporality,
    pub bonds: Vec<InteractionBond>,
    /// A receiver is named only when the interaction is specifically
    /// receiver-local. `None` is not an absolute receiver.
    pub receiver_scope: Option<ReceiverId>,
}

impl InteractionPattern {
    pub fn new(
        name: impl Into<String>,
        boundary: BoundaryId,
        temporality: InteractionTemporality,
        bonds: Vec<InteractionBond>,
    ) -> Self {
        Self {
            id: InteractionId(0),
            name: name.into(),
            boundary,
            temporality,
            bonds,
            receiver_scope: None,
        }
    }

    pub fn within_receiver(mut self, receiver: ReceiverId) -> Self {
        self.receiver_scope = Some(receiver);
        self
    }
}
