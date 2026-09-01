//! Complete-exchange ingress as a dependent product passage over the K3 native ecology.
//!
//! The 2,224 exchange occurrences do not collapse into K3's six native cells.  Before any later
//! return is admitted, each history-only occurrence is paired with every ordinary K3 ingress
//! section and those addressed sections conduct through the one owned ecology.  The returned
//! receiver-history quotient enters only after that plural candidate has been sealed.  The result
//! retains both factors, every quotient fibre and every generator square; source ordinals and
//! observation ordinals remain exterior chart coordinates and never select a K3 route.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::{
    ported_operation::{OperationSpecies, PortedOperationComplex, SourceTestimony},
    receiver_exact_compression::{ItemId, Observation, ReceiverId},
    receiver_history_compression::{NativeStateId, ReceiverFactor, ReceiverHistoryCompression},
    EventId, OccurrencePort,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::receiver_history::{CausalSectionAddress, ReceiverHistoryCongruence};

use super::{
    NativeConductConsequence, NativeConductPassage, NativeEcologyError, NativeEcologyRest,
    NativeSectionAddress,
};

pub const HISTORY_ONLY_EXCHANGE_FRONT_SCHEMA: &str = "soma-life.history-only-exchange-front.v1";
pub const SEALED_NATIVE_CANDIDATE_FRONT_SCHEMA: &str = "soma-life.sealed-native-candidate-front.v1";
pub const COMPLETE_EXCHANGE_NATIVE_REALIZATION_SCHEMA: &str =
    "soma-life.complete-exchange-native-realization-passage.v1";

/// The only exchange faces visible while a candidate is being emitted.
///
/// `source` is an apparatus coordinate used to join the later quotient.  It is not a state,
/// coefficient, route, or identity.  Response occurrences, returned surfaces, family addresses
/// that include a response, and later-return fields are unrepresentable here.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HistoryOnlyExchangeOccurrence {
    pub source: ItemId,
    pub prompt_occurrence: String,
    pub history_occurrences: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HistoryOnlyExchangeFront {
    pub schema: String,
    pub occurrences: Vec<HistoryOnlyExchangeOccurrence>,
}

impl HistoryOnlyExchangeFront {
    pub fn project(sections: &[CausalSectionAddress]) -> Result<Self, String> {
        let occurrences = sections
            .iter()
            .map(|section| HistoryOnlyExchangeOccurrence {
                source: ItemId(section.source_item),
                prompt_occurrence: section.prompt_occurrence.clone(),
                history_occurrences: section.history_occurrences.clone(),
            })
            .collect::<Vec<_>>();
        let front = Self {
            schema: HISTORY_ONLY_EXCHANGE_FRONT_SCHEMA.to_owned(),
            occurrences,
        };
        front.validate()?;
        Ok(front)
    }

    pub fn validate(&self) -> Result<(), String> {
        let mut sources = BTreeSet::new();
        if self.schema != HISTORY_ONLY_EXCHANGE_FRONT_SCHEMA
            || self.occurrences.is_empty()
            || self.occurrences.iter().any(|occurrence| {
                occurrence.prompt_occurrence.is_empty()
                    || occurrence.history_occurrences.iter().any(String::is_empty)
                    || !sources.insert(occurrence.source)
            })
        {
            return Err("the history-only exchange front is incomplete or repeats a source".into());
        }
        Ok(())
    }
}

/// One factor of a plural candidate.  Literal equality is equality of this complete structure,
/// not equality of its observation or digest testimony.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCandidateProductState {
    pub seed_section: NativeSectionAddress,
    pub entering_native: NativeStateId,
    pub emitting_native: NativeStateId,
    pub receiver: ReceiverId,
    pub observation: Observation,
    pub candidate_occurrence_sha256: String,
}

/// One history paired with the complete K3 ingress potential before any later-return face exists.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SealedNativeCandidateSection {
    pub history: HistoryOnlyExchangeOccurrence,
    pub product_states: Vec<NativeCandidateProductState>,
    pub seal_sha256: String,
}

/// The common K3 conduct is retained once.  Per-history members own only their local product
/// address and never clone the continuing ecology.
#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SealedNativeCandidateFront {
    pub schema: String,
    pub predecessor_rest_wire_sha256: String,
    pub ingress_template: Vec<NativeConductPassage>,
    pub sections: Vec<SealedNativeCandidateSection>,
    pub open_exterior: Vec<String>,
}

impl SealedNativeCandidateFront {
    pub fn seal(
        rest: &NativeEcologyRest,
        history: HistoryOnlyExchangeFront,
    ) -> Result<Self, NativeEcologyError> {
        history
            .validate()
            .map_err(NativeEcologyError::Realization)?;
        rest.validate()?;
        let receiver = *rest
            .realization
            .receiver_family
            .iter()
            .next()
            .ok_or_else(|| NativeEcologyError::Realization("empty K3 receiver family".into()))?;
        let mut ingress_template = Vec::with_capacity(rest.realization.ingress_sections.len());
        for address in &rest.realization.ingress_sections {
            match rest.conduct(address, receiver)? {
                NativeConductConsequence::Returned(passage) => ingress_template.push(passage),
                NativeConductConsequence::Insufficient(insufficiency) => {
                    return Err(NativeEcologyError::Conduct(format!(
                        "an admitted K3 ingress returned {insufficiency:?}"
                    )));
                }
            }
        }
        if ingress_template.is_empty() {
            return Err(NativeEcologyError::Realization(
                "the K3 predecessor returned no ingress potential".into(),
            ));
        }
        ingress_template.sort_by(|left, right| left.section.address.cmp(&right.section.address));
        let sections = history
            .occurrences
            .into_iter()
            .map(|history| seal_section(history, &ingress_template))
            .collect::<Result<Vec<_>, _>>()?;
        let front = Self {
            schema: SEALED_NATIVE_CANDIDATE_FRONT_SCHEMA.to_owned(),
            predecessor_rest_wire_sha256: rest.wire_sha256()?,
            ingress_template,
            sections,
            open_exterior: vec![
                "later exchange returns are sealed outside this candidate front".to_owned(),
                "candidate and returned receiver families remain distinct until the returned defect passage"
                    .to_owned(),
            ],
        };
        front.validate()?;
        Ok(front)
    }

    pub fn validate(&self) -> Result<(), NativeEcologyError> {
        if self.schema != SEALED_NATIVE_CANDIDATE_FRONT_SCHEMA
            || !is_digest(&self.predecessor_rest_wire_sha256)
            || self.ingress_template.is_empty()
            || self.sections.is_empty()
            || self.open_exterior.is_empty()
            || self.open_exterior.iter().any(String::is_empty)
        {
            return Err(NativeEcologyError::Realization(
                "the sealed native candidate front is malformed".into(),
            ));
        }
        let template = template_states(&self.ingress_template)?;
        let mut sources = BTreeSet::new();
        for section in &self.sections {
            if !sources.insert(section.history.source)
                || section.product_states.len() != template.len()
                || section
                    .product_states
                    .iter()
                    .zip(&template)
                    .any(|(actual, expected)| {
                        actual.seed_section != expected.seed_section
                            || actual.entering_native != expected.entering_native
                            || actual.emitting_native != expected.emitting_native
                            || actual.receiver != expected.receiver
                            || actual.observation != expected.observation
                            || actual.candidate_occurrence_sha256
                                != candidate_occurrence(&section.history, expected)
                    })
                || section.seal_sha256 != section_seal(&section.history, &section.product_states)?
            {
                return Err(NativeEcologyError::Realization(
                    "a candidate section does not reconstruct from history-only material and K3 conduct"
                        .into(),
                ));
            }
        }
        Ok(())
    }
}

/// The genuinely later receiver faces of one source occurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnedExchangeSection {
    pub source: ItemId,
    pub native: NativeStateId,
    pub family_occurrence: String,
    pub response_occurrences: Vec<String>,
    pub later_return_occurrence: Option<String>,
    pub receiver_faces: Vec<ReceiverFactor>,
    pub candidate_event: EventId,
    pub return_event: EventId,
}

/// A total addressed span from the sealed plural K3 candidate to the complete receiver-history
/// realization.  Neither factor is flattened into the other.
#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CompleteExchangeNativeRealizationPassage {
    pub schema: String,
    pub candidate: SealedNativeCandidateFront,
    pub native: ReceiverHistoryCompression,
    pub returned: Vec<ReturnedExchangeSection>,
    pub chronology: PortedOperationComplex,
    pub open_exterior: Vec<String>,
}

impl CompleteExchangeNativeRealizationPassage {
    pub fn found(
        candidate: SealedNativeCandidateFront,
        congruence: ReceiverHistoryCongruence,
    ) -> Result<Self, String> {
        candidate.validate().map_err(|error| error.to_string())?;
        congruence.validate()?;
        let candidate_by_source = candidate
            .sections
            .iter()
            .map(|section| (section.history.source, section))
            .collect::<BTreeMap<_, _>>();
        let section_by_source = congruence
            .sections
            .iter()
            .map(|section| (ItemId(section.source_item), section))
            .collect::<BTreeMap<_, _>>();
        if candidate_by_source.len() != congruence.sections.len()
            || candidate_by_source.keys().copied().collect::<BTreeSet<_>>()
                != section_by_source.keys().copied().collect::<BTreeSet<_>>()
        {
            return Err(
                "the sealed candidate and returned population do not share one total source span"
                    .into(),
            );
        }

        let mut chronology =
            PortedOperationComplex::new("complete-exchange-candidate-precedes-return");
        let history_boundary = chronology.port("history-only-native-product");
        let emission_boundary = chronology.port("sealed-native-candidate");
        let return_boundary = chronology.port("genuinely-later-receiver-return");
        let candidate_law = chronology
            .bind_operation(
                "emit-sealed-native-candidate",
                OperationSpecies::Transport,
                vec![history_boundary],
                vec![emission_boundary],
                Some("native-ecology-rest".to_owned()),
                vec![SourceTestimony::RestedImplementation {
                    symbol: "NativeEcologyRest::conduct".to_owned(),
                }],
            )
            .map_err(|error| error.to_string())?;
        let return_law = chronology
            .bind_operation(
                "admit-genuinely-later-return",
                OperationSpecies::Construction,
                vec![emission_boundary],
                vec![return_boundary],
                Some("complete-exchange-native-realization".to_owned()),
                vec![SourceTestimony::RestedImplementation {
                    symbol: "ReceiverHistoryCompression::decode_after_word".to_owned(),
                }],
            )
            .map_err(|error| error.to_string())?;

        let receiver_family = congruence
            .native
            .receiver_factors
            .iter()
            .map(|factor| factor.receiver)
            .collect::<BTreeSet<_>>();
        let generators = congruence
            .native
            .generators
            .iter()
            .map(|square| square.generator)
            .collect::<Vec<_>>();
        let mut returned = Vec::with_capacity(congruence.sections.len());
        for source in &congruence.native.source_population {
            let section = section_by_source[source];
            let candidate_event = chronology
                .occur(candidate_law)
                .map_err(|error| error.to_string())?;
            let return_event = chronology
                .occur(return_law)
                .map_err(|error| error.to_string())?;
            chronology
                .carries_precedence(
                    format!(
                        "candidate-return/{}",
                        candidate_by_source[source].seal_sha256
                    ),
                    emission_boundary,
                    OccurrencePort::output(candidate_event, 0),
                    OccurrencePort::input(return_event, 0),
                )
                .map_err(|error| error.to_string())?;
            for generator in &generators {
                let consequence = congruence
                    .native
                    .ordered_word_consequence(*source, &[*generator])
                    .map_err(|error| error.to_string())?;
                if !consequence.commutes() {
                    return Err(format!(
                        "generator {:?} failed the source/native square at {:?}",
                        generator, source
                    ));
                }
            }
            let native = congruence
                .native
                .encode(*source)
                .map_err(|error| error.to_string())?;
            let receiver_faces = receiver_family
                .iter()
                .map(|receiver| {
                    congruence
                        .native
                        .decode_after_word(native, &[], *receiver)
                        .map(|decoded| ReceiverFactor {
                            native,
                            receiver: *receiver,
                            observation: decoded.observation,
                        })
                        .map_err(|error| error.to_string())
                })
                .collect::<Result<Vec<_>, _>>()?;
            returned.push(ReturnedExchangeSection {
                source: *source,
                native,
                family_occurrence: section.family_occurrence.clone(),
                response_occurrences: section.response_occurrences.clone(),
                later_return_occurrence: section.later_return_occurrence.clone(),
                receiver_faces,
                candidate_event,
                return_event,
            });
        }
        let passage = Self {
            schema: COMPLETE_EXCHANGE_NATIVE_REALIZATION_SCHEMA.to_owned(),
            candidate,
            native: congruence.native,
            returned,
            chronology,
            open_exterior: vec![
                "receiver/history families outside the complete exchange aperture remain open"
                    .to_owned(),
                "the returned defect has not yet been deposited as morphology".to_owned(),
            ],
        };
        passage.validate()?;
        Ok(passage)
    }

    pub fn validate(&self) -> Result<(), String> {
        self.candidate
            .validate()
            .map_err(|error| error.to_string())?;
        self.native.validate().map_err(|error| error.to_string())?;
        if self.schema != COMPLETE_EXCHANGE_NATIVE_REALIZATION_SCHEMA
            || self.returned.len() != self.native.source_population.len()
            || self.open_exterior.is_empty()
            || self.open_exterior.iter().any(String::is_empty)
            || self
                .chronology
                .dependency_span()
                .map_err(|error| error.to_string())?
                != 2
        {
            return Err("the complete-exchange realization passage is malformed".into());
        }
        let candidate_sources = self
            .candidate
            .sections
            .iter()
            .map(|section| section.history.source)
            .collect::<BTreeSet<_>>();
        let returned_sources = self
            .returned
            .iter()
            .map(|section| section.source)
            .collect::<BTreeSet<_>>();
        let native_sources = self.native.source_population.iter().copied().collect();
        let receiver_family = self
            .native
            .receiver_factors
            .iter()
            .map(|factor| factor.receiver)
            .collect::<BTreeSet<_>>();
        if candidate_sources != returned_sources || returned_sources != native_sources {
            return Err("the candidate/return/native source span is not total".into());
        }
        for returned in &self.returned {
            if returned.native
                != self
                    .native
                    .encode(returned.source)
                    .map_err(|error| error.to_string())?
                || returned.candidate_event == returned.return_event
                || returned.receiver_faces.len() != receiver_family.len()
                || returned.receiver_faces.iter().any(|factor| {
                    factor.native != returned.native
                        || !receiver_family.contains(&factor.receiver)
                        || self
                            .native
                            .decode_after_word(returned.native, &[], factor.receiver)
                            .map_or(true, |decoded| {
                                decoded.native != factor.native
                                    || decoded.receiver != factor.receiver
                                    || decoded.observation != factor.observation
                            })
                })
            {
                return Err("one returned section breaks the dependent source/native span".into());
            }
        }
        for source in &self.native.source_population {
            for square in &self.native.generators {
                if !self
                    .native
                    .ordered_word_consequence(*source, &[square.generator])
                    .map_err(|error| error.to_string())?
                    .commutes()
                {
                    return Err("a generator naturality square failed after realization".into());
                }
            }
        }
        Ok(())
    }
}

fn seal_section(
    history: HistoryOnlyExchangeOccurrence,
    template: &[NativeConductPassage],
) -> Result<SealedNativeCandidateSection, NativeEcologyError> {
    let mut product_states = template_states(template)?;
    for state in &mut product_states {
        state.candidate_occurrence_sha256 = candidate_occurrence(&history, state);
    }
    let seal_sha256 = section_seal(&history, &product_states)?;
    Ok(SealedNativeCandidateSection {
        history,
        product_states,
        seal_sha256,
    })
}

fn template_states(
    template: &[NativeConductPassage],
) -> Result<Vec<NativeCandidateProductState>, NativeEcologyError> {
    template
        .iter()
        .map(|passage| {
            if passage.source_fallback_permitted {
                return Err(NativeEcologyError::Conduct(
                    "the candidate template permits a foreign fallback".into(),
                ));
            }
            Ok(NativeCandidateProductState {
                seed_section: passage.section.address.clone(),
                entering_native: passage.section.entering_native,
                emitting_native: passage.section.emitting_native,
                receiver: passage.section.receiver,
                observation: passage.section.observation,
                candidate_occurrence_sha256: String::new(),
            })
        })
        .collect()
}

fn candidate_occurrence(
    history: &HistoryOnlyExchangeOccurrence,
    state: &NativeCandidateProductState,
) -> String {
    digest_json(&(
        "complete-exchange-native-product-occurrence/v1",
        history,
        &state.seed_section,
        state.entering_native,
        state.emitting_native,
        state.receiver,
        state.observation,
    ))
    .expect("serializable candidate occurrence")
}

fn section_seal(
    history: &HistoryOnlyExchangeOccurrence,
    states: &[NativeCandidateProductState],
) -> Result<String, NativeEcologyError> {
    digest_json(&("sealed-native-candidate-section/v1", history, states))
        .map_err(NativeEcologyError::Wire)
}

fn digest_json(value: &impl Serialize) -> Result<String, String> {
    let bytes = serde_json::to_vec(value).map_err(|error| error.to_string())?;
    Ok(Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

use holonic_engine::is_sha256_digest as is_digest;

#[cfg(test)]
mod tests {
    use super::*;

    fn section() -> CausalSectionAddress {
        CausalSectionAddress {
            source_item: 7,
            family_occurrence: "return-aware-family-a".into(),
            predecessor_family_address: "predecessor-a".into(),
            prompt_occurrence: "prompt".into(),
            history_occurrences: vec!["history/0".into(), "history/1".into()],
            response_occurrences: vec!["response/a".into()],
            later_return_occurrence: Some("later/a".into()),
            returned_surface_sha256: format!("{:064x}", 1),
        }
    }

    #[test]
    fn later_return_mutation_cannot_change_the_history_only_candidate_aperture() {
        let left = section();
        let mut right = left.clone();
        right.family_occurrence = "return-aware-family-b".into();
        right.response_occurrences = vec!["response/b".into(), "response/c".into()];
        right.later_return_occurrence = Some("later/b".into());
        right.returned_surface_sha256 = format!("{:064x}", 2);
        assert_eq!(
            HistoryOnlyExchangeFront::project(&[left]).unwrap(),
            HistoryOnlyExchangeFront::project(&[right]).unwrap()
        );
    }
}
