//! Source-neutral native anatomical incidence.
//!
//! This rest begins after exterior realization descent has ended.  It retains only the native
//! class population, the receiver-visible emitted address of each class, and exact predecessor /
//! successor incidence.  Occurrence coordinates, coefficient nodes, inherited carrier classes,
//! separators, realization addresses, apparatus testimony, and reconstruction maps belong to the
//! separately sealed exterior witness.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::receiver_history_compression::NativeStateId;

pub const NATIVE_ANATOMY_SCHEMA: &str = "holonic-engine.native-anatomy-rest.v1";

/// One native anatomical class and its complete local incidence at the admitted aperture.
/// Equal emitted addresses do not identify classes; their incidence and native addresses remain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAnatomyClass {
    pub native: NativeStateId,
    pub emitted_native_address: u32,
    pub predecessor_classes: BTreeSet<NativeStateId>,
    pub successor_classes: BTreeSet<NativeStateId>,
}

/// The independently mountable native anatomical core.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAnatomyRest {
    pub schema: String,
    pub native_population: Vec<NativeStateId>,
    pub classes: Vec<NativeAnatomyClass>,
}

impl NativeAnatomyRest {
    pub fn new(
        native_population: Vec<NativeStateId>,
        classes: Vec<NativeAnatomyClass>,
    ) -> Result<Self, NativeAnatomyRefusal> {
        let rest = Self {
            schema: NATIVE_ANATOMY_SCHEMA.to_owned(),
            native_population,
            classes,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, NativeAnatomyRefusal> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| NativeAnatomyRefusal::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeAnatomyRefusal> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| NativeAnatomyRefusal::Wire(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), NativeAnatomyRefusal> {
        if self.schema != NATIVE_ANATOMY_SCHEMA {
            return Err(NativeAnatomyRefusal::Schema(self.schema.clone()));
        }
        let population = self
            .native_population
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        if population.is_empty()
            || population.len() != self.native_population.len()
            || self.classes.len() != population.len()
        {
            return Err(NativeAnatomyRefusal::NativePopulation);
        }

        let mut classes = BTreeMap::new();
        for class in &self.classes {
            if !population.contains(&class.native)
                || !class.predecessor_classes.is_subset(&population)
                || !class.successor_classes.is_subset(&population)
                || classes.insert(class.native, class).is_some()
            {
                return Err(NativeAnatomyRefusal::Class(class.native));
            }
        }
        if classes.keys().copied().collect::<BTreeSet<_>>() != population {
            return Err(NativeAnatomyRefusal::NativePopulation);
        }
        for class in &self.classes {
            for predecessor in &class.predecessor_classes {
                if !classes[predecessor]
                    .successor_classes
                    .contains(&class.native)
                {
                    return Err(NativeAnatomyRefusal::Incidence {
                        from: *predecessor,
                        to: class.native,
                    });
                }
            }
            for successor in &class.successor_classes {
                if !classes[successor]
                    .predecessor_classes
                    .contains(&class.native)
                {
                    return Err(NativeAnatomyRefusal::Incidence {
                        from: class.native,
                        to: *successor,
                    });
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum NativeAnatomyRefusal {
    #[error("native anatomy wire refused: {0}")]
    Wire(String),
    #[error("unknown native anatomy schema {0}")]
    Schema(String),
    #[error("the native anatomy population is empty, repeated, or does not equal its classes")]
    NativePopulation,
    #[error("native anatomy class {0:?} is repeated or leaves the native population")]
    Class(NativeStateId),
    #[error("native anatomy incidence {from:?} -> {to:?} is not reciprocal")]
    Incidence {
        from: NativeStateId,
        to: NativeStateId,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rest() -> NativeAnatomyRest {
        NativeAnatomyRest::new(
            vec![NativeStateId(0), NativeStateId(1)],
            vec![
                NativeAnatomyClass {
                    native: NativeStateId(0),
                    emitted_native_address: 7,
                    predecessor_classes: BTreeSet::from([NativeStateId(1)]),
                    successor_classes: BTreeSet::from([NativeStateId(1)]),
                },
                NativeAnatomyClass {
                    native: NativeStateId(1),
                    emitted_native_address: 7,
                    predecessor_classes: BTreeSet::from([NativeStateId(0)]),
                    successor_classes: BTreeSet::from([NativeStateId(0)]),
                },
            ],
        )
        .expect("native anatomy")
    }

    #[test]
    fn native_anatomy_round_trips_without_ancestry_fields() {
        let rest = rest();
        let bytes = rest.canonical_bytes().expect("wire");
        let remounted = NativeAnatomyRest::read(&bytes).expect("remount");
        assert_eq!(remounted, rest);
        let wire = String::from_utf8(bytes).expect("json").to_ascii_lowercase();
        for forbidden in [
            "phoenix",
            "soulkiller",
            "foreign",
            "source",
            "coefficient",
            "realization",
            "separator",
            "witness",
            "apparatus",
            "device",
            "surface",
        ] {
            assert!(
                !wire.contains(forbidden),
                "native wire contains {forbidden}"
            );
        }
    }

    #[test]
    fn equal_receiver_addresses_do_not_identify_native_classes() {
        let rest = rest();
        assert_eq!(rest.classes[0].emitted_native_address, 7);
        assert_eq!(rest.classes[1].emitted_native_address, 7);
        assert_ne!(rest.classes[0].native, rest.classes[1].native);
    }

    #[test]
    fn one_sided_incidence_is_refused() {
        let mut rest = rest();
        rest.classes[1].predecessor_classes.clear();
        assert!(matches!(
            rest.validate(),
            Err(NativeAnatomyRefusal::Incidence { .. })
        ));
    }
}
