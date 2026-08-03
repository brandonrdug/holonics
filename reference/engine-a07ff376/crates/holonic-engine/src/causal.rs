//! Algorithms as unfolded causal diagrams.
//!
//! A loop in an algorithm is represented by distinct event occurrences.
//! The law may recur; the occurrence does not.  This keeps logical chronology
//! separate from a cyclic standing data structure.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct EventId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EventOccurrence {
    pub id: EventId,
    /// The recurring transformation law.  It is not the identity of this
    /// particular occurrence.
    pub law: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalDiagram {
    pub schema: String,
    pub events: BTreeMap<EventId, EventOccurrence>,
    /// `before -> after` precedence. Co-present events have no edge merely
    /// because an executor happens to enumerate them.
    pub precedence: BTreeSet<(EventId, EventId)>,
    next_event: u64,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum DiagramError {
    #[error("event {0:?} is absent")]
    MissingEvent(EventId),
    #[error("an event cannot precede itself")]
    ReflexivePrecedence,
    #[error("the unfolded event diagram contains a causal cycle")]
    CausalCycle,
}

impl Default for CausalDiagram {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.causal-diagram.v1".to_owned(),
            events: BTreeMap::new(),
            precedence: BTreeSet::new(),
            next_event: 1,
        }
    }
}

impl CausalDiagram {
    pub fn add_event(&mut self, law: impl Into<String>) -> EventId {
        let id = EventId(self.next_event);
        self.next_event += 1;
        self.events.insert(
            id,
            EventOccurrence {
                id,
                law: law.into(),
            },
        );
        id
    }

    pub fn precedes(&mut self, before: EventId, after: EventId) -> Result<(), DiagramError> {
        if before == after {
            return Err(DiagramError::ReflexivePrecedence);
        }
        if !self.events.contains_key(&before) {
            return Err(DiagramError::MissingEvent(before));
        }
        if !self.events.contains_key(&after) {
            return Err(DiagramError::MissingEvent(after));
        }
        self.precedence.insert((before, after));
        if self.layers().is_err() {
            self.precedence.remove(&(before, after));
            return Err(DiagramError::CausalCycle);
        }
        Ok(())
    }

    /// Exact co-present layers induced only by declared precedence.
    ///
    /// Each result member is an antichain. The executor may serialize a layer
    /// physically, but that serialization does not become logical causality.
    pub fn layers(&self) -> Result<Vec<Vec<EventId>>, DiagramError> {
        let mut incoming = self
            .events
            .keys()
            .copied()
            .map(|id| (id, 0_usize))
            .collect::<BTreeMap<_, _>>();
        let mut outgoing = BTreeMap::<EventId, Vec<EventId>>::new();
        for (before, after) in &self.precedence {
            if !self.events.contains_key(before) {
                return Err(DiagramError::MissingEvent(*before));
            }
            if !self.events.contains_key(after) {
                return Err(DiagramError::MissingEvent(*after));
            }
            *incoming.get_mut(after).expect("event presence was checked") += 1;
            outgoing.entry(*before).or_default().push(*after);
        }

        let mut ready = incoming
            .iter()
            .filter_map(|(id, degree)| (*degree == 0).then_some(*id))
            .collect::<VecDeque<_>>();
        let mut visited = 0_usize;
        let mut layers = Vec::new();
        while !ready.is_empty() {
            let mut layer = ready.drain(..).collect::<Vec<_>>();
            layer.sort();
            visited += layer.len();
            for id in &layer {
                if let Some(next) = outgoing.get(id) {
                    for successor in next {
                        let degree = incoming
                            .get_mut(successor)
                            .expect("event presence was checked");
                        *degree -= 1;
                        if *degree == 0 {
                            ready.push_back(*successor);
                        }
                    }
                }
            }
            layers.push(layer);
        }
        if visited != self.events.len() {
            return Err(DiagramError::CausalCycle);
        }
        Ok(layers)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn co_present_events_remain_one_layer() {
        let mut diagram = CausalDiagram::default();
        let source = diagram.add_event("source");
        let left = diagram.add_event("left");
        let right = diagram.add_event("right");
        let return_event = diagram.add_event("return");
        diagram.precedes(source, left).unwrap();
        diagram.precedes(source, right).unwrap();
        diagram.precedes(left, return_event).unwrap();
        diagram.precedes(right, return_event).unwrap();

        assert_eq!(
            diagram.layers().unwrap(),
            vec![vec![source], vec![left, right], vec![return_event]]
        );
    }

    #[test]
    fn unfolded_chronology_refuses_a_cycle() {
        let mut diagram = CausalDiagram::default();
        let first = diagram.add_event("same recurring law");
        let second = diagram.add_event("same recurring law");
        diagram.precedes(first, second).unwrap();
        assert_eq!(
            diagram.precedes(second, first),
            Err(DiagramError::CausalCycle)
        );
    }
}
