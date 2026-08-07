//! Structured parameter and resource lifecycles.
//!
//! A parameter is not presumed copyable merely because its Rust carrier can
//! be cloned.  Copy, retention, and departure are separate laws of the
//! parameter's role in the active construction.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ParameterId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CopyLaw {
    /// The parameter carries a declared diagonal and may be copied.
    Shared,
    /// This occurrence has no lawful diagonal.
    Singular,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RetentionLaw {
    Persistent,
    EventLocal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DepartureLaw {
    MayDepart,
    MustReturn,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParameterLifecycle {
    pub copy: CopyLaw,
    pub retention: RetentionLaw,
    pub departure: DepartureLaw,
}

impl ParameterLifecycle {
    pub const REUSABLE_LAW: Self = Self {
        copy: CopyLaw::Shared,
        retention: RetentionLaw::Persistent,
        departure: DepartureLaw::MayDepart,
    };

    pub const SINGULAR_EVENT: Self = Self {
        copy: CopyLaw::Singular,
        retention: RetentionLaw::EventLocal,
        departure: DepartureLaw::MayDepart,
    };

    pub const BORROWED_RESOURCE: Self = Self {
        copy: CopyLaw::Singular,
        retention: RetentionLaw::EventLocal,
        departure: DepartureLaw::MustReturn,
    };
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParameterEntry<T> {
    pub id: ParameterId,
    pub name: String,
    pub value: T,
    pub lifecycle: ParameterLifecycle,
    /// A copied parameter remains related to the parameter whose declared
    /// diagonal produced it.
    pub copied_from: Option<ParameterId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParameterEcology<T> {
    pub schema: String,
    entries: BTreeMap<ParameterId, ParameterEntry<T>>,
    next_id: u64,
}

impl<T> Default for ParameterEcology<T> {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.parameter-ecology.v1".to_owned(),
            entries: BTreeMap::new(),
            next_id: 1,
        }
    }
}

impl<T> ParameterEcology<T> {
    pub fn introduce(
        &mut self,
        name: impl Into<String>,
        value: T,
        lifecycle: ParameterLifecycle,
    ) -> ParameterId {
        let id = ParameterId(self.next_id);
        self.next_id += 1;
        self.entries.insert(
            id,
            ParameterEntry {
                id,
                name: name.into(),
                value,
                lifecycle,
                copied_from: None,
            },
        );
        id
    }

    pub fn get(&self, id: ParameterId) -> Result<&ParameterEntry<T>, ParameterError> {
        self.entries.get(&id).ok_or(ParameterError::Missing(id))
    }

    pub fn get_mut(&mut self, id: ParameterId) -> Result<&mut ParameterEntry<T>, ParameterError> {
        self.entries.get_mut(&id).ok_or(ParameterError::Missing(id))
    }

    pub fn active(&self) -> impl Iterator<Item = &ParameterEntry<T>> {
        self.entries.values()
    }

    pub fn depart(&mut self, id: ParameterId) -> Result<ParameterEntry<T>, ParameterError> {
        let entry = self.get(id)?;
        if entry.lifecycle.departure == DepartureLaw::MustReturn {
            return Err(ParameterError::MustReturn(id));
        }
        Ok(self
            .entries
            .remove(&id)
            .expect("parameter presence was checked"))
    }

    /// Close one event-local aperture.
    ///
    /// Persistent parameters remain. Event-local parameters which may depart
    /// leave the active ecology. A borrowed resource must be explicitly
    /// returned before this boundary can close.
    pub fn close_event(&mut self) -> Result<Vec<ParameterId>, ParameterError> {
        if let Some(id) = self.entries.values().find_map(|entry| {
            (entry.lifecycle.retention == RetentionLaw::EventLocal
                && entry.lifecycle.departure == DepartureLaw::MustReturn)
                .then_some(entry.id)
        }) {
            return Err(ParameterError::UnreturnedBorrow(id));
        }
        let departing = self
            .entries
            .values()
            .filter_map(|entry| {
                (entry.lifecycle.retention == RetentionLaw::EventLocal).then_some(entry.id)
            })
            .collect::<Vec<_>>();
        for id in &departing {
            self.entries.remove(id);
        }
        Ok(departing)
    }

    pub fn return_borrow(&mut self, id: ParameterId) -> Result<ParameterEntry<T>, ParameterError> {
        let entry = self.get(id)?;
        if entry.lifecycle.departure != DepartureLaw::MustReturn {
            return Err(ParameterError::NotBorrowed(id));
        }
        Ok(self
            .entries
            .remove(&id)
            .expect("parameter presence was checked"))
    }
}

impl<T: Clone> ParameterEcology<T> {
    pub fn copy_parameter(&mut self, id: ParameterId) -> Result<ParameterId, ParameterError> {
        let source = self.get(id)?;
        if source.lifecycle.copy != CopyLaw::Shared {
            return Err(ParameterError::CopyRefused(id));
        }
        let copied = source.clone();
        let copy_id = ParameterId(self.next_id);
        self.next_id += 1;
        self.entries.insert(
            copy_id,
            ParameterEntry {
                id: copy_id,
                name: copied.name,
                value: copied.value,
                lifecycle: copied.lifecycle,
                copied_from: Some(id),
            },
        );
        Ok(copy_id)
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ParameterError {
    #[error("parameter {0:?} is absent")]
    Missing(ParameterId),
    #[error("parameter {0:?} has no declared copy law")]
    CopyRefused(ParameterId),
    #[error("parameter {0:?} is borrowed and must return rather than depart")]
    MustReturn(ParameterId),
    #[error("parameter {0:?} is not a borrowed resource")]
    NotBorrowed(ParameterId),
    #[error("borrowed parameter {0:?} has not returned at the event boundary")]
    UnreturnedBorrow(ParameterId),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_cloneable_carrier_cannot_bypass_a_singular_copy_law() {
        let mut ecology = ParameterEcology::default();
        let event = ecology.introduce(
            "one occurrence",
            String::from("cloneable carrier"),
            ParameterLifecycle::SINGULAR_EVENT,
        );
        assert_eq!(
            ecology.copy_parameter(event),
            Err(ParameterError::CopyRefused(event))
        );
        assert_eq!(ecology.close_event().unwrap(), vec![event]);
    }

    #[test]
    fn a_borrowed_resource_must_return_before_the_event_closes() {
        let mut ecology = ParameterEcology::default();
        let resource = ecology.introduce(
            "receiver aperture",
            7_u8,
            ParameterLifecycle::BORROWED_RESOURCE,
        );
        assert_eq!(
            ecology.close_event(),
            Err(ParameterError::UnreturnedBorrow(resource))
        );
        ecology.return_borrow(resource).unwrap();
        assert!(ecology.close_event().unwrap().is_empty());
    }
}
