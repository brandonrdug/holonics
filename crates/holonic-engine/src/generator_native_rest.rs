//! Source-detached execution of a finite generator-native ecology.
//!
//! [`crate::receiver_history_compression`] returns the quotient map, complete fibres and commuting
//! squares which justify this rest.  Those source witnesses belong to the exterior decoder.  The
//! reusable body below retains only the native population, factored receiver images and total
//! generator transports.  It therefore cannot choose a source representative or silently invert a
//! quotient.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::receiver_exact_compression::{InputId, Observation, ReceiverId};
use crate::receiver_history_compression::{NativeStateId, NativeTransport, ReceiverFactor};

pub const GENERATOR_NATIVE_REST_SCHEMA: &str = "holonics.m3.generator-native-rest.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeGenerator {
    pub generator: InputId,
    pub transport: Vec<NativeTransport>,
}

/// The complete native action and its declared receiver image.
///
/// No source population, quotient assignment, reconstruction fibre, foreign tensor or path is
/// representable in this type.  Those objects remain in separately addressed evidence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorNativeRest {
    pub schema: String,
    pub native_population: Vec<NativeStateId>,
    pub receiver_factors: Vec<ReceiverFactor>,
    pub generators: Vec<NativeGenerator>,
}

impl GeneratorNativeRest {
    pub fn new(
        native_population: Vec<NativeStateId>,
        receiver_factors: Vec<ReceiverFactor>,
        generators: Vec<NativeGenerator>,
    ) -> Result<Self, GeneratorNativeRestError> {
        let rest = Self {
            schema: GENERATOR_NATIVE_REST_SCHEMA.to_owned(),
            native_population,
            receiver_factors,
            generators,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, GeneratorNativeRestError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| GeneratorNativeRestError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, GeneratorNativeRestError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| GeneratorNativeRestError::Wire(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), GeneratorNativeRestError> {
        if self.schema != GENERATOR_NATIVE_REST_SCHEMA {
            return Err(GeneratorNativeRestError::Schema(self.schema.clone()));
        }
        let population = self
            .native_population
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        if population.is_empty() || population.len() != self.native_population.len() {
            return Err(GeneratorNativeRestError::NativePopulation);
        }

        let mut receiver_keys = BTreeSet::new();
        for factor in &self.receiver_factors {
            if !population.contains(&factor.native)
                || !receiver_keys.insert((factor.native, factor.receiver))
            {
                return Err(GeneratorNativeRestError::ReceiverFactor {
                    native: factor.native,
                    receiver: factor.receiver,
                });
            }
        }

        let mut generator_ids = BTreeSet::new();
        for generator in &self.generators {
            if !generator_ids.insert(generator.generator) {
                return Err(GeneratorNativeRestError::DuplicateGenerator(
                    generator.generator,
                ));
            }
            let mut domain = BTreeSet::new();
            for edge in &generator.transport {
                if !population.contains(&edge.from)
                    || !population.contains(&edge.to)
                    || !domain.insert(edge.from)
                {
                    return Err(GeneratorNativeRestError::GeneratorTransport {
                        generator: generator.generator,
                        state: edge.from,
                    });
                }
            }
            if domain != population {
                return Err(GeneratorNativeRestError::PartialGenerator(
                    generator.generator,
                ));
            }
        }
        Ok(())
    }

    pub fn conduct_word(
        &self,
        mut state: NativeStateId,
        word: &[InputId],
    ) -> Result<NativeStateId, GeneratorNativeRestError> {
        if !self.native_population.contains(&state) {
            return Err(GeneratorNativeRestError::UnknownState(state));
        }
        for generator in word {
            let action = self
                .generators
                .iter()
                .find(|action| action.generator == *generator)
                .ok_or(GeneratorNativeRestError::UnknownGenerator(*generator))?;
            state = action
                .transport
                .iter()
                .find(|edge| edge.from == state)
                .map(|edge| edge.to)
                .ok_or(GeneratorNativeRestError::PartialGenerator(*generator))?;
        }
        Ok(state)
    }

    pub fn decode(
        &self,
        state: NativeStateId,
        receiver: ReceiverId,
    ) -> Result<Observation, GeneratorNativeRestError> {
        self.receiver_factors
            .iter()
            .find(|factor| factor.native == state && factor.receiver == receiver)
            .map(|factor| factor.observation)
            .ok_or(GeneratorNativeRestError::ReceiverOutsideImage {
                native: state,
                receiver,
            })
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum GeneratorNativeRestError {
    #[error("generator-native wire refused: {0}")]
    Wire(String),
    #[error("unknown generator-native schema {0}")]
    Schema(String),
    #[error("the native population is empty or repeats an identity")]
    NativePopulation,
    #[error("receiver {receiver:?} is repeated or lies outside native state {native:?}")]
    ReceiverFactor {
        native: NativeStateId,
        receiver: ReceiverId,
    },
    #[error("generator {0:?} is repeated")]
    DuplicateGenerator(InputId),
    #[error("generator {generator:?} has an invalid or repeated edge from {state:?}")]
    GeneratorTransport {
        generator: InputId,
        state: NativeStateId,
    },
    #[error("generator {0:?} is not total on the native population")]
    PartialGenerator(InputId),
    #[error("native state {0:?} is outside this rest")]
    UnknownState(NativeStateId),
    #[error("generator {0:?} is outside this rest")]
    UnknownGenerator(InputId),
    #[error("receiver {receiver:?} is outside native state {native:?}'s declared image")]
    ReceiverOutsideImage {
        native: NativeStateId,
        receiver: ReceiverId,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rest() -> GeneratorNativeRest {
        GeneratorNativeRest::new(
            vec![NativeStateId(0), NativeStateId(1)],
            vec![
                ReceiverFactor {
                    native: NativeStateId(0),
                    receiver: ReceiverId(0),
                    observation: Observation(4),
                },
                ReceiverFactor {
                    native: NativeStateId(1),
                    receiver: ReceiverId(0),
                    observation: Observation(7),
                },
            ],
            vec![NativeGenerator {
                generator: InputId(0),
                transport: vec![
                    NativeTransport {
                        from: NativeStateId(0),
                        to: NativeStateId(1),
                    },
                    NativeTransport {
                        from: NativeStateId(1),
                        to: NativeStateId(1),
                    },
                ],
            }],
        )
        .expect("rest")
    }

    #[test]
    fn source_detached_rest_round_trips_and_conducts() {
        let rest = rest();
        let bytes = rest.canonical_bytes().expect("bytes");
        let mounted = GeneratorNativeRest::read(&bytes).expect("mount");
        assert_eq!(mounted, rest);
        let end = mounted
            .conduct_word(NativeStateId(0), &[InputId(0), InputId(0)])
            .expect("conduct");
        assert_eq!(end, NativeStateId(1));
        assert_eq!(
            mounted.decode(end, ReceiverId(0)).expect("decode"),
            Observation(7)
        );
    }

    #[test]
    fn a_partial_generator_cannot_become_a_rest() {
        let refusal = GeneratorNativeRest::new(
            vec![NativeStateId(0), NativeStateId(1)],
            Vec::new(),
            vec![NativeGenerator {
                generator: InputId(0),
                transport: vec![NativeTransport {
                    from: NativeStateId(0),
                    to: NativeStateId(1),
                }],
            }],
        )
        .expect_err("partial");
        assert_eq!(
            refusal,
            GeneratorNativeRestError::PartialGenerator(InputId(0))
        );
    }
}
