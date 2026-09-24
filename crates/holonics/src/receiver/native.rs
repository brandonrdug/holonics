//! Canonical receiver and native-action carriers.
//!
//! The finite quotient is discovered by the engine's source-qualified compression machinery.
//! This module owns only receiver identifiers and the state, transport, and receiver-factor
//! carriers shared by that discovery and its native realization, together with the validated
//! source-detached native generator action. Lean peer:
//! `ElementaryHolonics.Foundation.ReceiverHistoryCompression`, whose naturality theorem proves
//! that the quotient commutes with every ordered generator word. Quotient assignments, source
//! fibres, shortest separators, and source-qualified witnesses remain in the engine.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// One declared receiver in a compression or native receipt.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverId(pub u64);

/// One admitted generator/input that advances conduct.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct InputId(pub u64);

/// What a receiver returns from an item, exactly. An opaque exact token — never a magnitude.
///
/// It derives `Ord` because partition construction groups by observation signatures and the device
/// path uses the key. No law here reads that order as a magnitude: it is a canonical arrangement,
/// never a comparison of what two receivers returned. Subtracting, averaging, or thresholding these
/// values leaves the receiver calculus.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Observation(pub u64);

/// One state of the native quotient. Its ordinal is only the canonical address of a conduct block;
/// no arithmetic or semantic ordering is read from it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct NativeStateId(pub u64);

/// One edge in an induced native generator transport.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeTransport {
    pub from: NativeStateId,
    pub to: NativeStateId,
}

/// The receiver factor `rhoBar_j : Q -> Face` at one native state.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverFactor {
    pub native: NativeStateId,
    pub receiver: ReceiverId,
    pub observation: Observation,
}

pub const GENERATOR_NATIVE_REST_SCHEMA: &str = "holonics.m3.generator-native-rest.v1";

/// One generator in a source-detached finite native action.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeGenerator {
    pub generator: InputId,
    pub transport: Vec<NativeTransport>,
}

/// The complete native action and its declared receiver image.
///
/// This rest stores the induced action and receiver image only. Source populations, quotient
/// assignments, source representatives, reconstruction fibres, shortest separators, foreign
/// tensors and source paths remain outside this representation in the engine's discovery evidence.
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
