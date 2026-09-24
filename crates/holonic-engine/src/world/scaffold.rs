//! **The scaffolding every exact event law shares** (plan phase 16).
//!
//! [definition] The twenty-six `ExactEventLaw` modules keep their own laws; what they repeated
//! around those laws is stated once here:
//!
//! * [`EventRefusal<K>`] — one refusal family per law. The four refusals every law repeated
//!   (`RepeatedEvent`, `MalformedStanding`, `LawStandingMismatch`, `CarrierOverflow`) are shared;
//!   the law's own refusals are its kinds `K`, reached through [`EventRefusal::Law`]. Each module
//!   keeps its public error name as an alias, `type XError = EventRefusal<XRefusal>`, so the shared
//!   variants keep their paths (`XError::RepeatedEvent(event)`). There is deliberately no blanket
//!   `From<K>`: a shared refusal returned by the scaffold then converts by identity alone, and a
//!   law kind's `#[from]` sources are routed by [`event_refusal_from!`].
//! * [`EventStanding<S>`] — the standing shape the laws repeated: a schema, the occurrences already
//!   admitted (a repeated occurrence is refused) and the law's own quotient `S`, reached by
//!   `Deref`. The admitted-occurrence set is what the law's future reads to refuse a repetition;
//!   it is kept, and it is the only occurrence-indexed statistic the scaffold keeps.
//! * [`AdmittedEvents`] — the admission check on that set, for standings that keep it inline.
//!
//! [definition] A module adopting [`EventStanding<S>`] owns its wire through
//! [`event_standing_wire!`]: a borrowed record with the old struct name and field order for
//! writing, and an owned record for reading that accepts (and drops, or reduces to the sufficient
//! statistic) the retired archive fields. New rests omit the archives; old rests still decode.

use std::collections::BTreeSet;
use std::fmt;
use std::ops::{Deref, DerefMut};

use crate::EventId;

/// The law's name in the shared refusal messages.
pub trait RefusalKind {
    /// A short law name, for example `"bit-causal"`.
    const LAW: &'static str;
}

/// [definition] **One refusal family per law.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EventRefusal<K> {
    /// The occurrence was already admitted to this standing.
    RepeatedEvent(EventId),
    /// The standing does not satisfy its own invariants.
    MalformedStanding,
    /// The law and the standing were declared with different parameters.
    LawStandingMismatch,
    /// An exact finite carrier overflowed.
    CarrierOverflow,
    /// A refusal of this law's own mathematics.
    Law(K),
}

impl<K> EventRefusal<K> {
    /// The law's own refusal, if this is one.
    pub fn law(&self) -> Option<&K> {
        match self {
            Self::Law(kind) => Some(kind),
            _ => None,
        }
    }
}

impl<K: RefusalKind + fmt::Display> fmt::Display for EventRefusal<K> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RepeatedEvent(event) => {
                write!(
                    formatter,
                    "{} occurrence {event:?} was already admitted",
                    K::LAW
                )
            }
            Self::MalformedStanding => write!(formatter, "the {} standing is malformed", K::LAW),
            Self::LawStandingMismatch => {
                write!(formatter, "the {} law and standing disagree", K::LAW)
            }
            Self::CarrierOverflow => {
                write!(formatter, "a {} exact carrier overflowed", K::LAW)
            }
            Self::Law(kind) => fmt::Display::fmt(kind, formatter),
        }
    }
}

impl<K: RefusalKind + std::error::Error + 'static> std::error::Error for EventRefusal<K> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Law(kind) => kind.source(),
            _ => None,
        }
    }
}

/// Route `?` from a law kind's `#[from]` sources into the law's refusal family.
macro_rules! event_refusal_from {
    ($kind:ty : $($source:ty),+ $(,)?) => {
        $(
            impl From<$source> for $crate::world::EventRefusal<$kind> {
                fn from(source: $source) -> Self {
                    Self::Law(<$kind>::from(source))
                }
            }
        )+
    };
}
pub(crate) use event_refusal_from;

/// The admission check on a set of admitted occurrences.
pub trait AdmittedEvents {
    /// Refuse an occurrence that was already admitted.
    fn refuse_repeated<K>(&self, event: EventId) -> Result<(), EventRefusal<K>>;
    /// Admit an occurrence, refusing a repetition.
    fn admit<K>(&mut self, event: EventId) -> Result<(), EventRefusal<K>>;
}

impl AdmittedEvents for BTreeSet<EventId> {
    fn refuse_repeated<K>(&self, event: EventId) -> Result<(), EventRefusal<K>> {
        if self.contains(&event) {
            return Err(EventRefusal::RepeatedEvent(event));
        }
        Ok(())
    }

    fn admit<K>(&mut self, event: EventId) -> Result<(), EventRefusal<K>> {
        if !self.insert(event) {
            return Err(EventRefusal::RepeatedEvent(event));
        }
        Ok(())
    }
}

/// A law's own quotient names its law's refusal kinds, so the scaffold's shared refusals are
/// already in the law's family.
pub trait EventQuotient {
    type Refusal;
}

/// [definition] **The repeated standing shape**: a schema, the admitted occurrences and the law's
/// own quotient. The quotient is reached through `Deref`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EventStanding<S> {
    pub schema: String,
    pub(crate) used_events: BTreeSet<EventId>,
    pub(crate) body: S,
}

impl<S> EventStanding<S> {
    /// A standing that has admitted no occurrence.
    pub fn founded(schema: impl Into<String>, body: S) -> Self {
        Self {
            schema: schema.into(),
            used_events: BTreeSet::new(),
            body,
        }
    }

    pub(crate) fn from_parts(schema: String, used_events: BTreeSet<EventId>, body: S) -> Self {
        Self {
            schema,
            used_events,
            body,
        }
    }

    /// The occurrences already admitted.
    pub fn used_events(&self) -> &BTreeSet<EventId> {
        &self.used_events
    }

    /// The law's own quotient.
    pub fn quotient(&self) -> &S {
        &self.body
    }

    /// The admitted occurrences beside the mutable quotient (disjoint borrows through the
    /// scaffold).
    pub(crate) fn split_mut(&mut self) -> (&BTreeSet<EventId>, &mut S) {
        (&self.used_events, &mut self.body)
    }
}

impl<S: EventQuotient> EventStanding<S> {
    /// Refuse a repeated occurrence.
    pub fn refuse_repeated(&self, event: EventId) -> Result<(), EventRefusal<S::Refusal>> {
        self.used_events.refuse_repeated(event)
    }

    /// Refuse a schema other than the declared one.
    pub fn check_schema(&self, schema: &str) -> Result<(), EventRefusal<S::Refusal>> {
        if self.schema != schema {
            return Err(EventRefusal::MalformedStanding);
        }
        Ok(())
    }
}

impl<S> Deref for EventStanding<S> {
    type Target = S;

    fn deref(&self) -> &S {
        &self.body
    }
}

impl<S> DerefMut for EventStanding<S> {
    fn deref_mut(&mut self) -> &mut S {
        &mut self.body
    }
}

/// Serialize and deserialize an [`EventStanding`] through a module's wire records:
/// `$write<'a>` borrows (`From<&'a EventStanding<$body>>`), `$read` owns (`Into<EventStanding<$body>>`).
macro_rules! event_standing_wire {
    ($body:ty, $write:ident, $read:ty) => {
        impl serde::Serialize for $crate::world::EventStanding<$body> {
            fn serialize<Ser: serde::Serializer>(
                &self,
                serializer: Ser,
            ) -> Result<Ser::Ok, Ser::Error> {
                serde::Serialize::serialize(&$write::from(self), serializer)
            }
        }

        impl<'de> serde::Deserialize<'de> for $crate::world::EventStanding<$body> {
            fn deserialize<De: serde::Deserializer<'de>>(
                deserializer: De,
            ) -> Result<Self, De::Error> {
                <$read as serde::Deserialize<'de>>::deserialize(deserializer).map(Into::into)
            }
        }
    };
}
pub(crate) use event_standing_wire;

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
    enum ToyRefusal {}

    impl RefusalKind for ToyRefusal {
        const LAW: &'static str = "toy";
    }

    type ToyError = EventRefusal<ToyRefusal>;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct ToyQuotient(u8);

    impl EventQuotient for ToyQuotient {
        type Refusal = ToyRefusal;
    }

    #[test]
    fn admission_refuses_a_repeated_occurrence_and_keeps_the_set() {
        let mut standing = EventStanding::founded("toy.v1", ToyQuotient(5));
        assert_eq!(standing.0, 5);
        standing
            .used_events
            .admit::<ToyRefusal>(EventId(1))
            .unwrap();
        assert_eq!(
            standing.refuse_repeated(EventId(1)),
            Err(ToyError::RepeatedEvent(EventId(1)))
        );
        assert_eq!(
            standing.used_events.admit::<ToyRefusal>(EventId(1)),
            Err(ToyError::RepeatedEvent(EventId(1)))
        );
        assert_eq!(standing.used_events().len(), 1);
        assert_eq!(
            standing.check_schema("toy.v2"),
            Err(ToyError::MalformedStanding)
        );
        standing.0 += 1;
        assert_eq!(standing.quotient(), &ToyQuotient(6));
    }
}
