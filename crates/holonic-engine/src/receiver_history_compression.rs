//! The finite transport ecology induced by a receiver/history quotient.
//!
//! [`crate::receiver_exact_compression`] finds the coarsest partition which no declared receiver
//! and admitted successor history can separate.  This owner returns the consequence that turns
//! that partition into a native codec rather than a class list:
//!
//! ```text
//!                         T_i
//!                    X --------> X
//!                    |            |
//!                  q |            | q
//!                    v            v
//!                    Q --------> Q
//!                         U_i
//! ```
//!
//! Every square is checked on the complete source population.  Ordered-word exactness is then an
//! executable induction over those squares, not a replay campaign.  Decoding opens only the
//! declared receiver image and returns the complete source fibre; it never chooses an inverse of a
//! non-injective quotient.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::receiver_exact_compression::{
    CollapsedPair, InputId, ItemId, Observation, ObservedSystem, ReceiverExactCompression,
    ReceiverId,
};

/// One state of the native quotient.  Its ordinal is only the canonical address of a conduct
/// block; no arithmetic or semantic ordering is read from it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct NativeStateId(pub u64);

/// The quotient map `q : X -> Q`, exhibited at every source occurrence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuotientAssignment {
    pub source: ItemId,
    pub native: NativeStateId,
}

/// One complete source fibre of `q`.  This is what an exterior decoder must retain instead of
/// silently choosing a source occurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReconstructionFibre {
    pub native: NativeStateId,
    pub sources: BTreeSet<ItemId>,
}

/// One entry of a source generator `T_i`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceTransport {
    pub from: ItemId,
    pub to: ItemId,
}

/// One entry of the induced native generator `U_i`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeTransport {
    pub from: NativeStateId,
    pub to: NativeStateId,
}

/// A complete commuting generator square.  `source` and `native` are total functions over their
/// respective declared populations; construction refuses a terminus rather than hiding it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratorSquare {
    pub generator: InputId,
    pub source: Vec<SourceTransport>,
    pub native: Vec<NativeTransport>,
}

/// The factor `rhoBar_j : Q -> Face` for one native state and receiver.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverFactor {
    pub native: NativeStateId,
    pub receiver: ReceiverId,
    pub observation: Observation,
}

/// Exact semantic work used to found the native rest.  These are populations of exact relation
/// reads, not elapsed-time estimates.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverHistoryWork {
    pub quotient_assignments: u64,
    pub receiver_factor_reads: u64,
    pub source_transport_reads: u64,
    pub native_transport_entries: u64,
    pub generator_square_checks: u64,
}

/// The executable result of decoding one native state at one declared receiver.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecodedReceiverImage {
    pub native: NativeStateId,
    pub receiver: ReceiverId,
    pub observation: Observation,
    pub reconstruction_fibre: BTreeSet<ItemId>,
}

/// An executable witness of `q(T_w x) = U_w(q x)` for one arbitrary ordered word.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrderedWordConsequence {
    pub source_start: ItemId,
    pub native_start: NativeStateId,
    pub word: Vec<InputId>,
    pub source_end: ItemId,
    pub encoded_source_end: NativeStateId,
    pub native_end: NativeStateId,
}

impl OrderedWordConsequence {
    pub fn commutes(&self) -> bool {
        self.encoded_source_end == self.native_end
    }
}

/// The complete finite native action founded by a receiver/history quotient.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverHistoryCompression {
    pub schema: String,
    pub source_population: Vec<ItemId>,
    pub native_population: Vec<NativeStateId>,
    pub quotient: Vec<QuotientAssignment>,
    pub receiver_factors: Vec<ReceiverFactor>,
    pub generators: Vec<GeneratorSquare>,
    pub reconstruction_fibres: Vec<ReconstructionFibre>,
    /// Pairs a present-only quotient would have collapsed, with their first separating word.
    pub first_separators: Vec<CollapsedPair>,
    pub construction_work: ReceiverHistoryWork,
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ReceiverHistoryRefusal {
    #[error("receiver-history wire refused: {0}")]
    Wire(String),
    #[error("the source population is empty or repeats an identity")]
    SourcePopulation,
    #[error("the native population is empty or repeats an identity")]
    NativePopulation,
    #[error("source item {0:?} occurs in no conduct fibre")]
    SourceOutsideQuotient(ItemId),
    #[error("source item {0:?} occurs in more than one conduct fibre")]
    SourceOccursInPluralFibres(ItemId),
    #[error("conduct fibre {0:?} is empty")]
    EmptyFibre(NativeStateId),
    #[error("receiver {receiver:?} does not factor on native state {native:?}")]
    ReceiverDoesNotFactor {
        native: NativeStateId,
        receiver: ReceiverId,
    },
    #[error(
        "generator {generator:?} terminates at source item {source_item:?}; M3 requires a total typed transport"
    )]
    SourceTransportTerminates {
        generator: InputId,
        source_item: ItemId,
    },
    #[error(
        "generator {generator:?} leaves the declared source population from {source_item:?} to {target:?}"
    )]
    SourceTransportLeavesPopulation {
        generator: InputId,
        source_item: ItemId,
        target: ItemId,
    },
    #[error("generator {generator:?} does not induce one native successor on fibre {native:?}")]
    GeneratorDoesNotDescend {
        generator: InputId,
        native: NativeStateId,
    },
    #[error("generator square {generator:?} fails at source item {source_item:?}")]
    GeneratorSquareDoesNotCommute {
        generator: InputId,
        source_item: ItemId,
    },
    #[error("source item {0:?} is not in the quotient map")]
    UnknownSource(ItemId),
    #[error("native state {0:?} is not in the quotient")]
    UnknownNative(NativeStateId),
    #[error("generator {0:?} is not in the native action")]
    UnknownGenerator(InputId),
    #[error("receiver {receiver:?} is not declared on native state {native:?}")]
    UnknownReceiverFactor {
        native: NativeStateId,
        receiver: ReceiverId,
    },
    #[error("receiver factors do not form one complete declared family on native state {0:?}")]
    ReceiverFactorPopulation(NativeStateId),
    #[error("generator {0:?} is repeated")]
    DuplicateGenerator(InputId),
    #[error("the exact construction-work receipt disagrees with the validated relation population")]
    ConstructionWork,
    #[error("a shortest separator is malformed or leaves the declared passage")]
    Separator,
}

impl ReceiverHistoryCompression {
    /// Reopen a serialized compression and rederive every structural law it claims.
    pub fn read(bytes: &[u8]) -> Result<Self, ReceiverHistoryRefusal> {
        let compression: Self = serde_json::from_slice(bytes)
            .map_err(|error| ReceiverHistoryRefusal::Wire(error.to_string()))?;
        compression.validate()?;
        Ok(compression)
    }

    /// Validate the complete finite passage without consulting the source system which founded it.
    ///
    /// This is deliberately stronger than a schema check.  It reopens the quotient partition,
    /// complete reconstruction fibres, receiver-factor family, total source/native generators,
    /// every local naturality square, shortest-separator addresses and exact structural-work
    /// population.  The observations themselves remain opaque exact faces.
    pub fn validate(&self) -> Result<(), ReceiverHistoryRefusal> {
        if self.schema != "holonic-engine.receiver-history-compression.v1" {
            return Err(ReceiverHistoryRefusal::Wire(format!(
                "unknown schema {}",
                self.schema
            )));
        }
        let mut source_set = BTreeSet::new();
        for source in &self.source_population {
            source_set.insert(*source);
        }
        if source_set.is_empty() || source_set.len() != self.source_population.len() {
            return Err(ReceiverHistoryRefusal::SourcePopulation);
        }
        let mut native_set = BTreeSet::new();
        for native in &self.native_population {
            native_set.insert(*native);
        }
        if native_set.is_empty() || native_set.len() != self.native_population.len() {
            return Err(ReceiverHistoryRefusal::NativePopulation);
        }

        let mut encoded = BTreeMap::<ItemId, NativeStateId>::new();
        for assignment in &self.quotient {
            if !source_set.contains(&assignment.source)
                || !native_set.contains(&assignment.native)
                || encoded
                    .insert(assignment.source, assignment.native)
                    .is_some()
            {
                return Err(ReceiverHistoryRefusal::SourceOccursInPluralFibres(
                    assignment.source,
                ));
            }
        }
        for source in &source_set {
            if !encoded.contains_key(source) {
                return Err(ReceiverHistoryRefusal::SourceOutsideQuotient(*source));
            }
        }

        let mut fibre_by_native = BTreeMap::<NativeStateId, &BTreeSet<ItemId>>::new();
        let mut fibre_union = BTreeSet::new();
        for fibre in &self.reconstruction_fibres {
            if !native_set.contains(&fibre.native)
                || fibre.sources.is_empty()
                || fibre_by_native
                    .insert(fibre.native, &fibre.sources)
                    .is_some()
            {
                return Err(ReceiverHistoryRefusal::EmptyFibre(fibre.native));
            }
            for source in &fibre.sources {
                if !source_set.contains(source)
                    || !fibre_union.insert(*source)
                    || encoded.get(source) != Some(&fibre.native)
                {
                    return Err(ReceiverHistoryRefusal::SourceOccursInPluralFibres(*source));
                }
            }
        }
        if fibre_by_native.len() != native_set.len()
            || native_set
                .iter()
                .any(|native| !fibre_by_native.contains_key(native))
            || fibre_union != source_set
        {
            return Err(ReceiverHistoryRefusal::NativePopulation);
        }

        let mut receiver_set = BTreeSet::new();
        for factor in &self.receiver_factors {
            receiver_set.insert(factor.receiver);
        }
        let mut factor_keys = BTreeSet::new();
        let mut receivers_by_native = BTreeMap::<NativeStateId, BTreeSet<ReceiverId>>::new();
        for factor in &self.receiver_factors {
            if !native_set.contains(&factor.native)
                || !factor_keys.insert((factor.native, factor.receiver))
            {
                return Err(ReceiverHistoryRefusal::UnknownReceiverFactor {
                    native: factor.native,
                    receiver: factor.receiver,
                });
            }
            receivers_by_native
                .entry(factor.native)
                .or_default()
                .insert(factor.receiver);
        }
        for native in &native_set {
            if receivers_by_native.get(native) != Some(&receiver_set) {
                return Err(ReceiverHistoryRefusal::ReceiverFactorPopulation(*native));
            }
        }

        let mut generator_ids = BTreeSet::new();
        for square in &self.generators {
            if !generator_ids.insert(square.generator) {
                return Err(ReceiverHistoryRefusal::DuplicateGenerator(square.generator));
            }
            let mut source_map = BTreeMap::new();
            for edge in &square.source {
                if !source_set.contains(&edge.from)
                    || !source_set.contains(&edge.to)
                    || source_map.insert(edge.from, edge.to).is_some()
                {
                    return Err(ReceiverHistoryRefusal::SourceTransportLeavesPopulation {
                        generator: square.generator,
                        source_item: edge.from,
                        target: edge.to,
                    });
                }
            }
            if source_map.len() != source_set.len()
                || source_set
                    .iter()
                    .any(|source| !source_map.contains_key(source))
            {
                let missing = source_set
                    .iter()
                    .find(|source| !source_map.contains_key(source))
                    .copied()
                    .unwrap_or(ItemId(0));
                return Err(ReceiverHistoryRefusal::SourceTransportTerminates {
                    generator: square.generator,
                    source_item: missing,
                });
            }

            let mut native_map = BTreeMap::new();
            for edge in &square.native {
                if !native_set.contains(&edge.from)
                    || !native_set.contains(&edge.to)
                    || native_map.insert(edge.from, edge.to).is_some()
                {
                    return Err(ReceiverHistoryRefusal::GeneratorDoesNotDescend {
                        generator: square.generator,
                        native: edge.from,
                    });
                }
            }
            if native_map.len() != native_set.len()
                || native_set
                    .iter()
                    .any(|native| !native_map.contains_key(native))
            {
                let missing = native_set
                    .iter()
                    .find(|native| !native_map.contains_key(native))
                    .copied()
                    .unwrap_or(NativeStateId(0));
                return Err(ReceiverHistoryRefusal::GeneratorDoesNotDescend {
                    generator: square.generator,
                    native: missing,
                });
            }
            for (source, target) in source_map {
                if encoded[&target] != native_map[&encoded[&source]] {
                    return Err(ReceiverHistoryRefusal::GeneratorSquareDoesNotCommute {
                        generator: square.generator,
                        source_item: source,
                    });
                }
            }
        }

        for separator in &self.first_separators {
            if separator.left == separator.right
                || !source_set.contains(&separator.left)
                || !source_set.contains(&separator.right)
                || separator.distinguishing_word.is_empty()
                || separator
                    .distinguishing_word
                    .iter()
                    .any(|generator| !generator_ids.contains(generator))
                || separator.witness.is_some_and(|(receiver, left, right)| {
                    !receiver_set.contains(&receiver) || left == right
                })
                || (!separator.separated_by_terminus && separator.witness.is_none())
            {
                return Err(ReceiverHistoryRefusal::Separator);
            }
        }

        let source_count = self.source_population.len() as u64;
        let native_count = self.native_population.len() as u64;
        let generator_count = self.generators.len() as u64;
        let receiver_count = receiver_set.len() as u64;
        let expected = ReceiverHistoryWork {
            quotient_assignments: source_count,
            receiver_factor_reads: source_count * receiver_count,
            source_transport_reads: source_count * generator_count,
            native_transport_entries: native_count * generator_count,
            generator_square_checks: source_count * generator_count,
        };
        if self.construction_work != expected {
            return Err(ReceiverHistoryRefusal::ConstructionWork);
        }
        Ok(())
    }

    /// Found the native action from an already-computed stable receiver/history partition.
    pub fn found(
        system: &dyn ObservedSystem,
        exact: &ReceiverExactCompression,
    ) -> Result<Self, ReceiverHistoryRefusal> {
        let mut source_population = system.items();
        source_population.sort_unstable();
        source_population.dedup();
        let source_set = source_population.iter().copied().collect::<BTreeSet<_>>();

        let mut quotient = Vec::with_capacity(source_population.len());
        let mut reconstruction_fibres = Vec::with_capacity(exact.conduct.blocks.len());
        let mut encoded = BTreeMap::<ItemId, NativeStateId>::new();
        for (at, sources) in exact.conduct.blocks.iter().enumerate() {
            let native = NativeStateId(at as u64);
            if sources.is_empty() {
                return Err(ReceiverHistoryRefusal::EmptyFibre(native));
            }
            for source in sources {
                if encoded.insert(*source, native).is_some() {
                    return Err(ReceiverHistoryRefusal::SourceOccursInPluralFibres(*source));
                }
                quotient.push(QuotientAssignment {
                    source: *source,
                    native,
                });
            }
            reconstruction_fibres.push(ReconstructionFibre {
                native,
                sources: sources.clone(),
            });
        }
        for source in &source_population {
            if !encoded.contains_key(source) {
                return Err(ReceiverHistoryRefusal::SourceOutsideQuotient(*source));
            }
        }
        quotient.sort_by_key(|assignment| assignment.source);
        let native_population = reconstruction_fibres
            .iter()
            .map(|fibre| fibre.native)
            .collect::<Vec<_>>();

        let receivers = system.receivers();
        let mut receiver_factors = Vec::with_capacity(native_population.len() * receivers.len());
        let mut receiver_factor_reads = 0u64;
        for fibre in &reconstruction_fibres {
            for receiver in &receivers {
                let mut readings = fibre.sources.iter().map(|source| {
                    receiver_factor_reads += 1;
                    system.observation(*source, *receiver)
                });
                let first = readings
                    .next()
                    .ok_or(ReceiverHistoryRefusal::EmptyFibre(fibre.native))?;
                if readings.any(|reading| reading != first) {
                    return Err(ReceiverHistoryRefusal::ReceiverDoesNotFactor {
                        native: fibre.native,
                        receiver: *receiver,
                    });
                }
                receiver_factors.push(ReceiverFactor {
                    native: fibre.native,
                    receiver: *receiver,
                    observation: first,
                });
            }
        }

        let mut generators = Vec::with_capacity(system.inputs().len());
        let mut source_transport_reads = 0u64;
        let mut native_transport_entries = 0u64;
        let mut generator_square_checks = 0u64;
        for generator in system.inputs() {
            let mut source = Vec::with_capacity(source_population.len());
            for from in &source_population {
                source_transport_reads += 1;
                let to = system.successor(*from, generator).ok_or(
                    ReceiverHistoryRefusal::SourceTransportTerminates {
                        generator,
                        source_item: *from,
                    },
                )?;
                if !source_set.contains(&to) {
                    return Err(ReceiverHistoryRefusal::SourceTransportLeavesPopulation {
                        generator,
                        source_item: *from,
                        target: to,
                    });
                }
                source.push(SourceTransport { from: *from, to });
            }

            let source_map = source
                .iter()
                .map(|edge| (edge.from, edge.to))
                .collect::<BTreeMap<_, _>>();
            let mut native = Vec::with_capacity(native_population.len());
            for fibre in &reconstruction_fibres {
                let targets = fibre
                    .sources
                    .iter()
                    .filter_map(|member| source_map.get(member))
                    .filter_map(|target| encoded.get(target))
                    .copied()
                    .collect::<BTreeSet<_>>();
                if targets.len() != 1 {
                    return Err(ReceiverHistoryRefusal::GeneratorDoesNotDescend {
                        generator,
                        native: fibre.native,
                    });
                }
                native_transport_entries += 1;
                native.push(NativeTransport {
                    from: fibre.native,
                    to: *targets.iter().next().expect("one target was established"),
                });
            }
            let native_map = native
                .iter()
                .map(|edge| (edge.from, edge.to))
                .collect::<BTreeMap<_, _>>();
            for edge in &source {
                generator_square_checks += 1;
                let left = encoded[&edge.to];
                let right = native_map[&encoded[&edge.from]];
                if left != right {
                    return Err(ReceiverHistoryRefusal::GeneratorSquareDoesNotCommute {
                        generator,
                        source_item: edge.from,
                    });
                }
            }
            generators.push(GeneratorSquare {
                generator,
                source,
                native,
            });
        }

        let compression = Self {
            schema: "holonic-engine.receiver-history-compression.v1".to_owned(),
            source_population,
            native_population,
            quotient,
            receiver_factors,
            generators,
            reconstruction_fibres,
            first_separators: exact.collapsed.clone(),
            construction_work: ReceiverHistoryWork {
                quotient_assignments: encoded.len() as u64,
                receiver_factor_reads,
                source_transport_reads,
                native_transport_entries,
                generator_square_checks,
            },
        };
        compression.validate()?;
        Ok(compression)
    }

    pub fn encode(&self, source: ItemId) -> Result<NativeStateId, ReceiverHistoryRefusal> {
        self.quotient
            .binary_search_by_key(&source, |assignment| assignment.source)
            .ok()
            .and_then(|at| self.quotient.get(at))
            .map(|assignment| assignment.native)
            .ok_or(ReceiverHistoryRefusal::UnknownSource(source))
    }

    /// Decode exactly the declared receiver image and reopen the complete source fibre.
    pub fn decode(
        &self,
        native: NativeStateId,
        receiver: ReceiverId,
    ) -> Result<DecodedReceiverImage, ReceiverHistoryRefusal> {
        let observation = self
            .receiver_factors
            .iter()
            .find(|factor| factor.native == native && factor.receiver == receiver)
            .map(|factor| factor.observation)
            .ok_or(ReceiverHistoryRefusal::UnknownReceiverFactor { native, receiver })?;
        let reconstruction_fibre = self
            .reconstruction_fibres
            .iter()
            .find(|fibre| fibre.native == native)
            .map(|fibre| fibre.sources.clone())
            .ok_or(ReceiverHistoryRefusal::UnknownNative(native))?;
        Ok(DecodedReceiverImage {
            native,
            receiver,
            observation,
            reconstruction_fibre,
        })
    }

    fn source_step(
        &self,
        source: ItemId,
        generator: InputId,
    ) -> Result<ItemId, ReceiverHistoryRefusal> {
        self.generators
            .iter()
            .find(|square| square.generator == generator)
            .ok_or(ReceiverHistoryRefusal::UnknownGenerator(generator))?
            .source
            .iter()
            .find(|edge| edge.from == source)
            .map(|edge| edge.to)
            .ok_or(ReceiverHistoryRefusal::UnknownSource(source))
    }

    pub fn native_step(
        &self,
        native: NativeStateId,
        generator: InputId,
    ) -> Result<NativeStateId, ReceiverHistoryRefusal> {
        self.generators
            .iter()
            .find(|square| square.generator == generator)
            .ok_or(ReceiverHistoryRefusal::UnknownGenerator(generator))?
            .native
            .iter()
            .find(|edge| edge.from == native)
            .map(|edge| edge.to)
            .ok_or(ReceiverHistoryRefusal::UnknownNative(native))
    }

    /// Derive the ordered-word square by composing the already-checked generator squares.
    pub fn ordered_word_consequence(
        &self,
        source_start: ItemId,
        word: &[InputId],
    ) -> Result<OrderedWordConsequence, ReceiverHistoryRefusal> {
        let native_start = self.encode(source_start)?;
        let mut source_end = source_start;
        let mut native_end = native_start;
        for generator in word {
            source_end = self.source_step(source_end, *generator)?;
            native_end = self.native_step(native_end, *generator)?;
        }
        let encoded_source_end = self.encode(source_end)?;
        Ok(OrderedWordConsequence {
            source_start,
            native_start,
            word: word.to_vec(),
            source_end,
            encoded_source_end,
            native_end,
        })
    }

    /// Conduct an arbitrary ordered word natively and decode its declared endpoint image.
    pub fn decode_after_word(
        &self,
        native_start: NativeStateId,
        word: &[InputId],
        receiver: ReceiverId,
    ) -> Result<DecodedReceiverImage, ReceiverHistoryRefusal> {
        let mut native = native_start;
        for generator in word {
            native = self.native_step(native, *generator)?;
        }
        self.decode(native, receiver)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::receiver_exact_compression::compress;

    struct PairedCycle;

    impl ObservedSystem for PairedCycle {
        fn items(&self) -> Vec<ItemId> {
            (0..8).map(ItemId).collect()
        }

        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }

        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0), InputId(1)]
        }

        fn observation(&self, item: ItemId, _: ReceiverId) -> Observation {
            Observation(item.0 % 2)
        }

        fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
            Some(match input.0 {
                0 => ItemId((item.0 + 2) % 8),
                _ => ItemId(7 - item.0),
            })
        }
    }

    #[test]
    fn generator_squares_found_every_ordered_word_and_decoder_reopens_the_fibre() {
        let system = PairedCycle;
        let exact = compress(&system);
        let native = ReceiverHistoryCompression::found(&system, &exact).expect("stable quotient");
        assert!(native.native_population.len() < native.source_population.len());
        for source in &native.source_population {
            for word in [
                vec![],
                vec![InputId(0)],
                vec![InputId(1), InputId(0), InputId(1), InputId(0)],
            ] {
                assert!(
                    native
                        .ordered_word_consequence(*source, &word)
                        .expect("declared word")
                        .commutes()
                );
            }
        }
        let decoded = native
            .decode(native.encode(ItemId(0)).expect("encoded"), ReceiverId(0))
            .expect("declared image");
        assert_eq!(decoded.observation, Observation(0));
        assert!(decoded.reconstruction_fibre.len() > 1);
    }

    struct Terminates;

    impl ObservedSystem for Terminates {
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
        fn successor(&self, _: ItemId, _: InputId) -> Option<ItemId> {
            None
        }
    }

    #[test]
    fn a_partial_successor_cannot_pose_as_the_total_m3_transport_square() {
        let system = Terminates;
        let exact = compress(&system);
        assert!(matches!(
            ReceiverHistoryCompression::found(&system, &exact),
            Err(ReceiverHistoryRefusal::SourceTransportTerminates { .. })
        ));
    }
}
