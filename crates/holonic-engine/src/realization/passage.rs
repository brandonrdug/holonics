//! Addressed realization passages over existing exact owners.
//!
//! This module is the missing join between four owners which already stand:
//! receiver-history compression supplies the finite quotient, generator squares, decoder and
//! fibres; the generator-native rest supplies source-detached conduct; cross-chart supplies exact
//! defects and their serial chain law; addressed exterior occurrences supply lineage and typed
//! boundaries.  The result is a receipt over those owners, never a second copy of their bodies.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::cross_chart::{ChainLawReading, CrossChartDefect};
use crate::generator_native_rest::GeneratorNativeRest;
use crate::receiver_exact_compression::{InputId, ItemId, Observation, ReceiverId};
use crate::receiver_history_compression::{
    DecodedReceiverImage, NativeStateId, OrderedWordConsequence, ReceiverHistoryCompression,
    ReceiverHistoryRefusal,
};

pub const REALIZATION_PASSAGE_SCHEMA: &str = "holonics.i0.realization-passage.v1";

/// Content identity of one exterior artifact occurrence.  A filesystem path is lineage and is
/// intentionally absent from identity.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactOccurrence {
    pub sha256: String,
    pub octets: u64,
}

impl ArtifactOccurrence {
    pub fn measure(bytes: &[u8]) -> Self {
        Self {
            sha256: format!("{:x}", Sha256::digest(bytes)),
            octets: bytes.len() as u64,
        }
    }

    pub fn validate(&self) -> Result<(), RealizationPassageRefusal> {
        if self.sha256.len() != 64 || !self.sha256.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(RealizationPassageRefusal::ArtifactIdentity);
        }
        Ok(())
    }
}

/// One boundary port on an addressed physical realization reference.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TypedBoundaryReference {
    pub port: String,
    pub carrier: String,
    pub hand: BoundaryHand,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum BoundaryHand {
    Entering,
    Emitting,
}

/// The exterior reference to one physical realization.  Its live incidence and morphology remain
/// owned by `body`; this record binds their populations and apparatus testimony without cloning
/// either.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PhysicalRealizationReference {
    pub body: ArtifactOccurrence,
    pub state_population: u64,
    pub generator_population: u64,
    pub receiver_population: u64,
    pub typed_ports: Vec<TypedBoundaryReference>,
    pub apparatus: ArtifactOccurrence,
    pub source_detached: bool,
    pub open_exterior: Vec<String>,
}

impl PhysicalRealizationReference {
    fn validate(&self) -> Result<(), RealizationPassageRefusal> {
        self.body.validate()?;
        self.apparatus.validate()?;
        if self.state_population == 0
            || self.typed_ports.is_empty()
            || self
                .typed_ports
                .iter()
                .any(|port| port.port.is_empty() || port.carrier.is_empty())
            || self.typed_ports.iter().collect::<BTreeSet<_>>().len() != self.typed_ports.len()
        {
            return Err(RealizationPassageRefusal::PhysicalRealization);
        }
        Ok(())
    }
}

/// One carrying occurrence.  Equal source and target faces do not identify two entries: the
/// occurrence and predecessor lineage remain explicit.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedPassageOccurrence {
    pub occurrence: String,
    pub predecessor: Option<String>,
    pub source_boundary: String,
    pub target_boundary: String,
}

/// A finite same-endpoint control.  The endpoints are one receiver face; the occurrence
/// population is not.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SameEndpointDistinctLineage {
    pub source_boundary: String,
    pub target_boundary: String,
    pub occurrences: Vec<String>,
}

impl SameEndpointDistinctLineage {
    pub fn validate(&self) -> Result<(), RealizationPassageRefusal> {
        if self.source_boundary.is_empty()
            || self.target_boundary.is_empty()
            || self.occurrences.len() < 2
            || self.occurrences.iter().any(String::is_empty)
            || self.occurrences.iter().collect::<BTreeSet<_>>().len() != self.occurrences.len()
        {
            return Err(RealizationPassageRefusal::EndpointLineageControl);
        }
        Ok(())
    }
}

/// One executable word square already derived from the complete local generator population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WordClosureReading {
    pub consequence: OrderedWordConsequence,
    pub rested_native_end: NativeStateId,
    pub receiver_images: Vec<DecodedReceiverImage>,
}

/// The complete decoder is retained in the addressed evidence artifact.  This receipt proves the
/// covered populations without copying the fibre body into a second product.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DecoderAndFibreReceipt {
    pub evidence: ArtifactOccurrence,
    pub source_population: u64,
    pub native_population: u64,
    pub reconstruction_fibre_population: u64,
    pub receiver_factor_population: u64,
    pub every_source_occurs_once: bool,
    pub every_declared_image_decodes: bool,
}

/// A present receiver identifies the pair, while the named shortest ordered word reopens it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StaticEqualityReopening {
    pub left: ItemId,
    pub right: ItemId,
    pub present_images: Vec<(ReceiverId, Observation)>,
    pub shortest_word: Vec<InputId>,
    pub separating_receiver: ReceiverId,
    pub left_future: Observation,
    pub right_future: Observation,
}

/// The additive cross-chart chain law over actual exact matrices, with one lawful square and one
/// noncommuting control retained rather than thresholded.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LinearPassageChainReceipt {
    pub first: CrossChartDefect,
    pub second: CrossChartDefect,
    pub composite: CrossChartDefect,
    pub chain: ChainLawReading,
}

impl LinearPassageChainReceipt {
    pub fn validate(&self) -> Result<(), RealizationPassageRefusal> {
        if !self.first.is_zero
            || self.second.is_zero
            || !self.chain.operator_identity_holds
            || self
                .chain
                .residual
                .entries()
                .iter()
                .any(|entry| !num_traits::Zero::is_zero(entry))
            || self
                .chain
                .vector_checks
                .iter()
                .any(|reading| !reading.holds)
        {
            return Err(RealizationPassageRefusal::ChainDefectLaw);
        }
        Ok(())
    }
}

/// Addressed evidence that the A3 continuation is a distinct realization passage rather than a
/// renamed endpoint.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ContinuationPassageReference {
    pub input_occurrences: ArtifactOccurrence,
    pub cultivation_complex: ArtifactOccurrence,
    pub grade: ArtifactOccurrence,
    pub predecessor_body_sha256: String,
    pub successor_continuation_sha256: String,
    pub unchanged_predecessor_and_distinct_successor: bool,
    pub source_detached_successor_remount: bool,
    pub targeted_ablation_restored_predecessor: bool,
    pub no_retained_exchange_lookup: bool,
}

impl ContinuationPassageReference {
    fn validate(&self) -> Result<(), RealizationPassageRefusal> {
        self.input_occurrences.validate()?;
        self.cultivation_complex.validate()?;
        self.grade.validate()?;
        if self.predecessor_body_sha256.len() != 64
            || self.successor_continuation_sha256.len() != 64
            || self.predecessor_body_sha256 == self.successor_continuation_sha256
            || !self.unchanged_predecessor_and_distinct_successor
            || !self.source_detached_successor_remount
            || !self.targeted_ablation_restored_predecessor
            || !self.no_retained_exchange_lookup
        {
            return Err(RealizationPassageRefusal::Continuation);
        }
        Ok(())
    }
}

/// Exact work belonging to the I0 join itself.  It counts relation reads and artifact reads; it is
/// not elapsed time and it does not replay the source deeds.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RealizationPassageWork {
    pub artifact_octets_read: u64,
    pub quotient_assignments_checked: u64,
    pub fibre_members_checked: u64,
    pub receiver_images_checked: u64,
    pub source_generator_edges_checked: u64,
    pub native_generator_edges_checked: u64,
    pub ordered_word_steps_checked: u64,
}

/// One apparatus receipt may be reused only when the exact producing artifacts are addressed and
/// no new device claim is made.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReusedApparatusReceipt {
    pub source: ArtifactOccurrence,
    pub native: ArtifactOccurrence,
    pub continuation: ArtifactOccurrence,
    pub unchanged_addressed_receipts_reused: bool,
    pub new_device_deed_claimed: bool,
}

/// The addressed product receipt.  Large owner payloads remain behind their content identities.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiverHistoryRealizationPassage {
    pub schema: String,
    pub source: PhysicalRealizationReference,
    pub target: PhysicalRealizationReference,
    pub occurrences: Vec<AddressedPassageOccurrence>,
    pub local_generator_square_population: u64,
    pub every_ordered_word_follows_by_composition: bool,
    pub checked_words: Vec<WordClosureReading>,
    pub decoder: DecoderAndFibreReceipt,
    pub static_reopening: StaticEqualityReopening,
    pub same_endpoint_distinct_lineage: SameEndpointDistinctLineage,
    pub chain_defect: LinearPassageChainReceipt,
    pub continuation: ContinuationPassageReference,
    pub exact_work: RealizationPassageWork,
    pub apparatus: ReusedApparatusReceipt,
    pub open_exterior: Vec<String>,
}

impl ReceiverHistoryRealizationPassage {
    #[allow(clippy::too_many_arguments)]
    pub fn bind(
        source: PhysicalRealizationReference,
        target: PhysicalRealizationReference,
        occurrences: Vec<AddressedPassageOccurrence>,
        compression_evidence: ArtifactOccurrence,
        history: &ReceiverHistoryCompression,
        rest: &GeneratorNativeRest,
        word_requests: &[(ItemId, Vec<InputId>)],
        same_endpoint_distinct_lineage: SameEndpointDistinctLineage,
        chain_defect: LinearPassageChainReceipt,
        continuation: ContinuationPassageReference,
        apparatus: ReusedApparatusReceipt,
        artifact_octets_read: u64,
        open_exterior: Vec<String>,
    ) -> Result<Self, RealizationPassageRefusal> {
        source.validate()?;
        target.validate()?;
        compression_evidence.validate()?;
        history.validate()?;
        rest.validate()
            .map_err(|error| RealizationPassageRefusal::NativeRest(error.to_string()))?;
        same_endpoint_distinct_lineage.validate()?;
        chain_defect.validate()?;
        continuation.validate()?;
        validate_occurrences(&occurrences)?;
        validate_apparatus(&apparatus)?;

        if source.state_population != history.source_population.len() as u64
            || target.state_population != history.native_population.len() as u64
            || source.generator_population != history.generators.len() as u64
            || target.generator_population != rest.generators.len() as u64
            || source.receiver_population
                != history
                    .receiver_factors
                    .iter()
                    .map(|factor| factor.receiver)
                    .collect::<BTreeSet<_>>()
                    .len() as u64
            || target.receiver_population != source.receiver_population
        {
            return Err(RealizationPassageRefusal::PhysicalRealization);
        }
        validate_native_projection(history, rest)?;

        let receiver_ids = history
            .receiver_factors
            .iter()
            .map(|factor| factor.receiver)
            .collect::<BTreeSet<_>>();
        let mut every_declared_image_decodes = true;
        for fibre in &history.reconstruction_fibres {
            for receiver in &receiver_ids {
                let image = history.decode(fibre.native, *receiver)?;
                let rested = rest
                    .decode(fibre.native, *receiver)
                    .map_err(|error| RealizationPassageRefusal::NativeRest(error.to_string()))?;
                every_declared_image_decodes &=
                    image.observation == rested && image.reconstruction_fibre == fibre.sources;
            }
        }
        if !every_declared_image_decodes {
            return Err(RealizationPassageRefusal::Decoder);
        }

        let mut checked_words = Vec::with_capacity(word_requests.len());
        let mut ordered_word_steps_checked = 0u64;
        for (source_start, word) in word_requests {
            let consequence = history.ordered_word_consequence(*source_start, word)?;
            if !consequence.commutes() {
                return Err(RealizationPassageRefusal::OrderedWord);
            }
            let rested_native_end = rest
                .conduct_word(consequence.native_start, word)
                .map_err(|error| RealizationPassageRefusal::NativeRest(error.to_string()))?;
            if rested_native_end != consequence.native_end {
                return Err(RealizationPassageRefusal::OrderedWord);
            }
            let mut receiver_images = Vec::with_capacity(receiver_ids.len());
            for receiver in &receiver_ids {
                let image = history.decode(consequence.native_end, *receiver)?;
                if rest
                    .decode(consequence.native_end, *receiver)
                    .map_err(|error| RealizationPassageRefusal::NativeRest(error.to_string()))?
                    != image.observation
                {
                    return Err(RealizationPassageRefusal::Decoder);
                }
                receiver_images.push(image);
            }
            ordered_word_steps_checked += word.len() as u64;
            checked_words.push(WordClosureReading {
                consequence,
                rested_native_end,
                receiver_images,
            });
        }
        let static_reopening = static_reopening(history, rest, &receiver_ids)?;

        let source_generator_edges_checked = history
            .generators
            .iter()
            .map(|square| square.source.len() as u64)
            .sum();
        let native_generator_edges_checked = history
            .generators
            .iter()
            .map(|square| square.native.len() as u64)
            .sum();
        let exact_work = RealizationPassageWork {
            artifact_octets_read,
            quotient_assignments_checked: history.quotient.len() as u64,
            fibre_members_checked: history
                .reconstruction_fibres
                .iter()
                .map(|fibre| fibre.sources.len() as u64)
                .sum(),
            receiver_images_checked: history.receiver_factors.len() as u64,
            source_generator_edges_checked,
            native_generator_edges_checked,
            ordered_word_steps_checked,
        };

        Ok(Self {
            schema: REALIZATION_PASSAGE_SCHEMA.to_owned(),
            source,
            target,
            occurrences,
            local_generator_square_population: history.construction_work.generator_square_checks,
            every_ordered_word_follows_by_composition: true,
            checked_words,
            decoder: DecoderAndFibreReceipt {
                evidence: compression_evidence,
                source_population: history.source_population.len() as u64,
                native_population: history.native_population.len() as u64,
                reconstruction_fibre_population: history.reconstruction_fibres.len() as u64,
                receiver_factor_population: history.receiver_factors.len() as u64,
                every_source_occurs_once: true,
                every_declared_image_decodes,
            },
            static_reopening,
            same_endpoint_distinct_lineage,
            chain_defect,
            continuation,
            exact_work,
            apparatus,
            open_exterior,
        })
    }
}

fn validate_occurrences(
    occurrences: &[AddressedPassageOccurrence],
) -> Result<(), RealizationPassageRefusal> {
    if occurrences.is_empty()
        || occurrences.iter().any(|occurrence| {
            occurrence.occurrence.is_empty()
                || occurrence.source_boundary.is_empty()
                || occurrence.target_boundary.is_empty()
        })
        || occurrences
            .iter()
            .map(|occurrence| &occurrence.occurrence)
            .collect::<BTreeSet<_>>()
            .len()
            != occurrences.len()
    {
        return Err(RealizationPassageRefusal::OccurrenceLineage);
    }
    Ok(())
}

fn validate_apparatus(apparatus: &ReusedApparatusReceipt) -> Result<(), RealizationPassageRefusal> {
    apparatus.source.validate()?;
    apparatus.native.validate()?;
    apparatus.continuation.validate()?;
    if !apparatus.unchanged_addressed_receipts_reused || apparatus.new_device_deed_claimed {
        return Err(RealizationPassageRefusal::Apparatus);
    }
    Ok(())
}

fn validate_native_projection(
    history: &ReceiverHistoryCompression,
    rest: &GeneratorNativeRest,
) -> Result<(), RealizationPassageRefusal> {
    if history.native_population != rest.native_population
        || history.receiver_factors != rest.receiver_factors
    {
        return Err(RealizationPassageRefusal::NativeProjection);
    }
    if history.generators.len() != rest.generators.len()
        || history
            .generators
            .iter()
            .zip(&rest.generators)
            .any(|(square, native)| {
                square.generator != native.generator || square.native != native.transport
            })
    {
        return Err(RealizationPassageRefusal::NativeProjection);
    }
    Ok(())
}

fn static_reopening(
    history: &ReceiverHistoryCompression,
    rest: &GeneratorNativeRest,
    receiver_ids: &BTreeSet<ReceiverId>,
) -> Result<StaticEqualityReopening, RealizationPassageRefusal> {
    let separator = history
        .first_separators
        .iter()
        .filter(|separator| !separator.separated_by_terminus)
        .min_by_key(|separator| {
            (
                separator.distinguishing_word.len(),
                separator.left,
                separator.right,
            )
        })
        .ok_or(RealizationPassageRefusal::StaticReopening)?;
    let (separating_receiver, expected_left, expected_right) = separator
        .witness
        .ok_or(RealizationPassageRefusal::StaticReopening)?;
    let left_native = history.encode(separator.left)?;
    let right_native = history.encode(separator.right)?;
    if left_native == right_native {
        return Err(RealizationPassageRefusal::StaticReopening);
    }
    let mut present_images = Vec::with_capacity(receiver_ids.len());
    for receiver in receiver_ids {
        let left = rest
            .decode(left_native, *receiver)
            .map_err(|error| RealizationPassageRefusal::NativeRest(error.to_string()))?;
        let right = rest
            .decode(right_native, *receiver)
            .map_err(|error| RealizationPassageRefusal::NativeRest(error.to_string()))?;
        if left != right {
            return Err(RealizationPassageRefusal::StaticReopening);
        }
        present_images.push((*receiver, left));
    }
    let left_end = history
        .ordered_word_consequence(separator.left, &separator.distinguishing_word)?
        .native_end;
    let right_end = history
        .ordered_word_consequence(separator.right, &separator.distinguishing_word)?
        .native_end;
    let left_future = rest
        .decode(left_end, separating_receiver)
        .map_err(|error| RealizationPassageRefusal::NativeRest(error.to_string()))?;
    let right_future = rest
        .decode(right_end, separating_receiver)
        .map_err(|error| RealizationPassageRefusal::NativeRest(error.to_string()))?;
    if left_future == right_future || left_future != expected_left || right_future != expected_right
    {
        return Err(RealizationPassageRefusal::StaticReopening);
    }
    Ok(StaticEqualityReopening {
        left: separator.left,
        right: separator.right,
        present_images,
        shortest_word: separator.distinguishing_word.clone(),
        separating_receiver,
        left_future,
        right_future,
    })
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum RealizationPassageRefusal {
    #[error("an exterior artifact identity is malformed")]
    ArtifactIdentity,
    #[error("the physical realization reference is incomplete")]
    PhysicalRealization,
    #[error("the addressed occurrence population is empty, repeated or untyped")]
    OccurrenceLineage,
    #[error("equal endpoints were substituted for distinct occurrence lineage")]
    EndpointLineageControl,
    #[error("the exact cross-chart chain law or its noncommuting control failed")]
    ChainDefectLaw,
    #[error(
        "the continuation reference did not retain predecessor, successor, remount and ablation"
    )]
    Continuation,
    #[error("the native rest refused: {0}")]
    NativeRest(String),
    #[error(
        "the generator-native rest is not the exact projection of the receiver-history passage"
    )]
    NativeProjection,
    #[error("an arbitrary ordered word failed to commute")]
    OrderedWord,
    #[error("the complete decoder or reconstruction fibre failed")]
    Decoder,
    #[error("no present-equal pair reopened under its shortest admitted history")]
    StaticReopening,
    #[error("the reused apparatus testimony is missing or claims a new device deed")]
    Apparatus,
    #[error("receiver-history passage refused: {0}")]
    ReceiverHistory(String),
}

impl From<ReceiverHistoryRefusal> for RealizationPassageRefusal {
    fn from(error: ReceiverHistoryRefusal) -> Self {
        Self::ReceiverHistory(error.to_string())
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;
    use relational_geometry::Rat;

    use super::*;
    use crate::cross_chart::chain_law;
    use crate::exact_linear::ExactRatMatrix;
    use crate::generator_native_rest::NativeGenerator;
    use crate::receiver_exact_compression::{ObservedSystem, compress};

    struct ExchangeBits;

    impl ObservedSystem for ExchangeBits {
        fn items(&self) -> Vec<ItemId> {
            (0..4).map(ItemId).collect()
        }

        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }

        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0)]
        }

        fn observation(&self, item: ItemId, _: ReceiverId) -> Observation {
            Observation(item.0 / 2)
        }

        fn successor(&self, item: ItemId, _: InputId) -> Option<ItemId> {
            let left = item.0 / 2;
            let right = item.0 % 2;
            Some(ItemId(2 * right + left))
        }
    }

    fn artifact(seed: char) -> ArtifactOccurrence {
        ArtifactOccurrence {
            sha256: seed.to_string().repeat(64),
            octets: 1,
        }
    }

    fn physical(
        seed: char,
        states: usize,
        generators: usize,
        receivers: usize,
        detached: bool,
    ) -> PhysicalRealizationReference {
        PhysicalRealizationReference {
            body: artifact(seed),
            state_population: states as u64,
            generator_population: generators as u64,
            receiver_population: receivers as u64,
            typed_ports: vec![
                TypedBoundaryReference {
                    port: "enter".to_owned(),
                    carrier: "state".to_owned(),
                    hand: BoundaryHand::Entering,
                },
                TypedBoundaryReference {
                    port: "emit".to_owned(),
                    carrier: "state".to_owned(),
                    hand: BoundaryHand::Emitting,
                },
            ],
            apparatus: artifact('a'),
            source_detached: detached,
            open_exterior: vec!["unasked receivers".to_owned()],
        }
    }

    fn matrix(value: i64) -> ExactRatMatrix {
        ExactRatMatrix::new(vec![vec![Rat::from_integer(BigInt::from(value))]])
            .expect("one-cell matrix")
    }

    fn chain() -> LinearPassageChainReceipt {
        let identity = matrix(1);
        let two = matrix(2);
        let three = matrix(3);
        let material = vec![("one".to_owned(), vec![Rat::from_integer(BigInt::from(1))])];
        let (first, second, composite, reading) = chain_law(
            &identity, &identity, &three, &two, &two, &identity, &identity, &material,
        )
        .expect("exact chain");
        LinearPassageChainReceipt {
            first,
            second,
            composite,
            chain: reading,
        }
    }

    #[test]
    fn the_addressed_passage_reopens_static_equality_and_keeps_lineage() {
        let system = ExchangeBits;
        let exact = compress(&system);
        let history = ReceiverHistoryCompression::found(&system, &exact).expect("history");
        let rest = GeneratorNativeRest::new(
            history.native_population.clone(),
            history.receiver_factors.clone(),
            history
                .generators
                .iter()
                .map(|square| NativeGenerator {
                    generator: square.generator,
                    transport: square.native.clone(),
                })
                .collect(),
        )
        .expect("rest");
        let evidence = artifact('e');
        let continuation = ContinuationPassageReference {
            input_occurrences: artifact('1'),
            cultivation_complex: artifact('2'),
            grade: artifact('3'),
            predecessor_body_sha256: "4".repeat(64),
            successor_continuation_sha256: "5".repeat(64),
            unchanged_predecessor_and_distinct_successor: true,
            source_detached_successor_remount: true,
            targeted_ablation_restored_predecessor: true,
            no_retained_exchange_lookup: true,
        };
        let passage = ReceiverHistoryRealizationPassage::bind(
            physical('6', 4, 1, 1, false),
            physical('7', 4, 1, 1, true),
            vec![AddressedPassageOccurrence {
                occurrence: "carrying-occurrence".to_owned(),
                predecessor: None,
                source_boundary: "source".to_owned(),
                target_boundary: "native".to_owned(),
            }],
            evidence,
            &history,
            &rest,
            &[(ItemId(0), vec![InputId(0), InputId(0)])],
            SameEndpointDistinctLineage {
                source_boundary: "same-source".to_owned(),
                target_boundary: "same-target".to_owned(),
                occurrences: vec!["left".to_owned(), "right".to_owned()],
            },
            chain(),
            continuation,
            ReusedApparatusReceipt {
                source: artifact('8'),
                native: artifact('9'),
                continuation: artifact('a'),
                unchanged_addressed_receipts_reused: true,
                new_device_deed_claimed: false,
            },
            3,
            vec!["other receiver families".to_owned()],
        )
        .expect("passage");
        assert!(passage.every_ordered_word_follows_by_composition);
        assert_eq!(passage.static_reopening.shortest_word, vec![InputId(0)]);
        assert_ne!(
            passage.static_reopening.left_future,
            passage.static_reopening.right_future
        );
        assert_eq!(passage.same_endpoint_distinct_lineage.occurrences.len(), 2);
        assert!(passage.chain_defect.first.is_zero);
        assert!(!passage.chain_defect.second.is_zero);
    }

    #[test]
    fn a_deserialized_square_with_a_foreign_target_refuses() {
        let system = ExchangeBits;
        let exact = compress(&system);
        let mut history = ReceiverHistoryCompression::found(&system, &exact).expect("history");
        history.generators[0].native[0].to = NativeStateId(99);
        assert!(matches!(
            history.validate(),
            Err(ReceiverHistoryRefusal::GeneratorDoesNotDescend { .. })
        ));
    }
}
