//! Source-neutral text material and its continuing sparse conditioning ecology.
//!
//! Codex rollouts, Codex history, Claude Code sessions, Claude history, and already parsed
//! documents are different world containers.  They cross this membrane as the same kind of
//! linguistic occurrence while their container, byte range, role, chronology, parentage, identity
//! species, and exact surface remain inspectable lineage.  Container syntax, tools, hidden
//! reasoning, generated control wrappers, and attachments do not become language merely because
//! they share a JSON record with it.
//!
//! **Every coordinate this membrane retains is read out of the container, never off the cpu.**
//! A container is addressed by its own name in whatever store holds it, an occurrence identity is
//! founded from that address plus the record ordinal and byte range, and a conversation is the
//! container's declared session — never a message identity.  The two defects that law exists to
//! close were both measured on the sealed corpus of 2026-08-11: 46,745 occurrence identities
//! carrying this machine's home directory, so the corpus content address was a function of one
//! filesystem; and 11,266 of 11,282 rollout witnesses carrying their own message identity as a
//! conversation, so the largest container in the body entered with its chronology deleted.
//!
//! The conditioned atlas is not a detached search service.  Every admitted occurrence changes
//! its token population, ordered transports, local sections, feature incidence, and recurrence.
//! A receiver question restricts that standing to a finite local star; a generated answer may be
//! admitted through the same membrane and therefore changes later conduct.

mod import;
mod resident;

use import::{import_parallel, merge_occurrence, parse_document};
use resident::extent_u32;
pub use resident::{
    CudaResidentTextMaterialAtlas, CudaResidentTextMaterialNativeRest,
    CudaResidentTextMaterialRestRefusal, TextMaterialCudaContactAttempt,
    TextMaterialCudaContactReceipt, TextMaterialCudaMountRefusal,
    TextMaterialCudaRestrictionReceipt, TextMaterialRestrictionError,
};

use std::{
    collections::{BTreeMap, BTreeSet},
    io::Read,
    ops::Range,
    path::{Path, PathBuf},
};

use holonic_structure::{LocalRelations, LocalSequence, LocalSet};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    causal_language::lexical_tokens,
    laboratory_language::{
        text_features, LaboratoryDeferredSection, LaboratoryResearchLeader,
        LaboratoryReturnedSection, LaboratorySourceKind, LaboratoryWorldReturn, LeaderAdmission,
    },
    morphological_language::MorphologicalLanguagePassage,
    text_material_cuda::{
        TextMaterialFeatureHeadUpdate, TextMaterialResidentDelta, TextMaterialResidentImage,
        TextMaterialResidentShape,
    },
};
use soma_abi::text_restrict_cuda as text_cuda;

type TextMaterialMap<Key, Value> = BTreeMap<Key, Value>;
type TextMaterialSet<Member> = BTreeSet<Member>;
type TextMaterialVector<Member> = Vec<Member>;

const TEXT_USER_RECEIVER: u64 = 40_000_000;
const TEXT_ASSISTANT_PROCESS_RECEIVER: u64 = 40_000_001;
const TEXT_ASSISTANT_FINAL_RECEIVER: u64 = 40_000_002;
const TEXT_DOCUMENT_RECEIVER: u64 = 40_000_003;
const TEXT_EMANATED_RECEIVER: u64 = 40_000_004;
/// `v5` because the occurrence identity law changed on 2026-08-11 and a `v4` rest is not the same
/// body under a new name: every founded identity in a `v4` rest carries the absolute cpu path it
/// was read at, so it is a lineage in an absolute frame. Refusing it at the schema is the point.
const REST_SCHEMA: &str = "life.exact-text-material-atlas.v5";
const CORPUS_SCHEMA: &str = "life.exact-text-material-corpus.v3";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum TextMaterialSourceKind {
    CodexRollout,
    CodexHistory,
    ClaudeCode,
    ClaudeHistory,
    ParsedDocument,
    SelfEmanated,
}

/// Which owner supplied an occurrence identity.
///
/// Provider identity and a membrane-founded record coordinate are different testimony.  An absent
/// provider identity never deletes the occurrence and never promotes the membrane coordinate into
/// a provider claim; the witness carries which species it is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum TextMaterialIdentitySpecies {
    ProviderSupplied,
    FoundedFromContainerRecordRange,
    DeclaredDocument,
    SelfEmanated,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum TextMaterialRole {
    Human,
    Assistant,
    Document,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum TextMaterialPhase {
    Received,
    Commentary,
    FinalAnswer,
    Response,
    Document,
    Emanated,
    Other(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TextMaterialError {
    Io(String),
    Json(String),
    EmptySource,
    EmptyText,
    InvalidRest,
    CarrierExtent,
    WorkerPanicked,
    /// Two distinct containers of one source kind presented one container address.
    ///
    /// The membrane will not disambiguate them by reaching back to the cpu path, because that is
    /// the absolute frame this identity law exists to remove. The ambiguity is returned instead.
    ContainerAddressCollision(String),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TextMaterialWitness {
    pub source_kind: TextMaterialSourceKind,
    pub identity_species: TextMaterialIdentitySpecies,
    /// The container's own address — its name in whatever store holds it — and never the cpu
    /// path it was mounted from. A witness is retained testimony; folding the filesystem into it
    /// makes the whole sealed body a function of one machine.
    pub container: String,
    pub conversation: String,
    pub raw_record: u64,
    pub raw_start: u64,
    pub raw_end: u64,
    pub timestamp: String,
    pub native_parent: Option<String>,
    pub sidechain: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TextMaterialOccurrence {
    /// Version-specific identity. Equal native identities with different surfaces remain plural.
    pub identity: String,
    pub native_identity: String,
    pub surface_sha256: String,
    pub ordinal: u64,
    pub role: TextMaterialRole,
    pub phase: TextMaterialPhase,
    pub text: String,
    pub witnesses: BTreeSet<TextMaterialWitness>,
    pub caused_by: BTreeSet<String>,
}

impl TextMaterialOccurrence {
    pub const fn receiver(&self) -> u64 {
        match (&self.role, &self.phase) {
            (TextMaterialRole::Human, _) => TEXT_USER_RECEIVER,
            (TextMaterialRole::Assistant, TextMaterialPhase::FinalAnswer) => {
                TEXT_ASSISTANT_FINAL_RECEIVER
            }
            (TextMaterialRole::Assistant, TextMaterialPhase::Emanated) => TEXT_EMANATED_RECEIVER,
            (TextMaterialRole::Assistant, _) => TEXT_ASSISTANT_PROCESS_RECEIVER,
            (TextMaterialRole::Document, _) => TEXT_DOCUMENT_RECEIVER,
        }
    }

    pub fn passage(&self) -> MorphologicalLanguagePassage {
        MorphologicalLanguagePassage::new(
            self.identity.clone(),
            format!(
                "text-material/{}/{}",
                role_name(self.role),
                phase_name(&self.phase)
            ),
            self.receiver(),
            self.text.clone(),
        )
    }

    fn first_witness(&self) -> Option<&TextMaterialWitness> {
        self.witnesses.iter().min_by(|left, right| {
            (
                empty_last(&left.timestamp),
                left.source_kind,
                left.conversation.as_str(),
                left.raw_record,
                left.container.as_str(),
            )
                .cmp(&(
                    empty_last(&right.timestamp),
                    right.source_kind,
                    right.conversation.as_str(),
                    right.raw_record,
                    right.container.as_str(),
                ))
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TextMaterialContainerReceipt {
    pub source_kind: TextMaterialSourceKind,
    pub source: String,
    pub conversation: String,
    pub raw_extent: u64,
    pub raw_sha256: String,
    pub complete_records: u64,
    pub visible_occurrences: usize,
    pub founded_identity_occurrences: usize,
    pub excluded_control_occurrences: usize,
    pub partial_tail_bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TextMaterialCorpusReceipt {
    pub schema: String,
    pub containers: usize,
    pub raw_bytes: u64,
    pub raw_container_sha256: String,
    pub witnessed_occurrences: usize,
    pub unique_occurrences: usize,
    pub human_occurrences: usize,
    pub assistant_occurrences: usize,
    pub document_occurrences: usize,
    pub codex_witnesses: usize,
    pub codex_history_witnesses: usize,
    pub claude_witnesses: usize,
    pub claude_history_witnesses: usize,
    pub document_witnesses: usize,
    pub self_emanated_witnesses: usize,
    pub founded_identity_witnesses: usize,
    pub exact_duplicate_witnesses: usize,
    pub native_version_fibers: usize,
    pub excluded_control_occurrences: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExactTextMaterialCorpus {
    occurrences: LocalSequence<TextMaterialOccurrence>,
    containers: LocalSequence<TextMaterialContainerReceipt>,
    receipt: TextMaterialCorpusReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TextMaterialInput {
    CodexRollout(PathBuf),
    CodexHistory(PathBuf),
    ClaudeCode(PathBuf),
    ClaudeHistory(PathBuf),
}

impl TextMaterialInput {
    pub fn path(&self) -> &Path {
        match self {
            Self::CodexRollout(path)
            | Self::CodexHistory(path)
            | Self::ClaudeCode(path)
            | Self::ClaudeHistory(path) => path,
        }
    }

    pub const fn source_kind(&self) -> TextMaterialSourceKind {
        match self {
            Self::CodexRollout(_) => TextMaterialSourceKind::CodexRollout,
            Self::CodexHistory(_) => TextMaterialSourceKind::CodexHistory,
            Self::ClaudeCode(_) => TextMaterialSourceKind::ClaudeCode,
            Self::ClaudeHistory(_) => TextMaterialSourceKind::ClaudeHistory,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParsedTextDocument {
    pub identity: String,
    pub source: String,
    pub sections: Vec<String>,
}

impl ExactTextMaterialCorpus {
    pub fn import(
        mut inputs: Vec<TextMaterialInput>,
        documents: &[ParsedTextDocument],
        thread_budget: usize,
    ) -> Result<Self, TextMaterialError> {
        inputs.sort_by(|left, right| {
            (left.source_kind(), left.path()).cmp(&(right.source_kind(), right.path()))
        });
        inputs.dedup();
        let parsed = import_parallel(&inputs, thread_budget.max(1))?;
        let mut containers = LocalSequence::with_capacity(parsed.len() + documents.len());
        let mut witnessed_occurrences = 0usize;
        let mut excluded_control_occurrences = 0usize;
        let mut versions = BTreeMap::<String, TextMaterialOccurrence>::new();
        for container in parsed {
            witnessed_occurrences = witnessed_occurrences
                .checked_add(container.occurrences.len())
                .ok_or(TextMaterialError::CarrierExtent)?;
            excluded_control_occurrences = excluded_control_occurrences
                .checked_add(container.receipt.excluded_control_occurrences)
                .ok_or(TextMaterialError::CarrierExtent)?;
            for occurrence in container.occurrences {
                merge_occurrence(&mut versions, occurrence)?;
            }
            containers.push(container.receipt);
        }
        for document in documents {
            let parsed = parse_document(document)?;
            witnessed_occurrences = witnessed_occurrences
                .checked_add(parsed.occurrences.len())
                .ok_or(TextMaterialError::CarrierExtent)?;
            for occurrence in parsed.occurrences {
                merge_occurrence(&mut versions, occurrence)?;
            }
            containers.push(parsed.receipt);
        }
        if versions.is_empty() {
            return Err(TextMaterialError::EmptySource);
        }

        let mut occurrences = versions.into_values().collect::<LocalSequence<_>>();
        occurrences.sort_by(|left, right| {
            let left_witness = left.first_witness();
            let right_witness = right.first_witness();
            (
                left_witness.map(|witness| empty_last(&witness.timestamp)),
                left_witness.map(|witness| witness.source_kind),
                left_witness.map(|witness| witness.conversation.as_str()),
                left_witness.map(|witness| witness.raw_record),
                left.identity.as_str(),
            )
                .cmp(&(
                    right_witness.map(|witness| empty_last(&witness.timestamp)),
                    right_witness.map(|witness| witness.source_kind),
                    right_witness.map(|witness| witness.conversation.as_str()),
                    right_witness.map(|witness| witness.raw_record),
                    right.identity.as_str(),
                ))
        });
        for (ordinal, occurrence) in occurrences.iter_mut().enumerate() {
            occurrence.ordinal =
                u64::try_from(ordinal).map_err(|_| TextMaterialError::CarrierExtent)?;
        }
        containers.sort_by(|left, right| {
            (left.source_kind, left.source.as_str())
                .cmp(&(right.source_kind, right.source.as_str()))
        });
        // A container address must separate the containers it addresses. Two of one kind under one
        // address is an ambiguity, and the membrane returns it rather than reaching back to the
        // cpu path that used to separate them.
        for pair in containers.windows(2) {
            if (pair[0].source_kind, pair[0].source.as_str())
                == (pair[1].source_kind, pair[1].source.as_str())
            {
                return Err(TextMaterialError::ContainerAddressCollision(format!(
                    "{:?} presents two containers addressed {}",
                    pair[0].source_kind, pair[0].source
                )));
            }
        }

        let mut container_hash = Sha256::new();
        let mut raw_bytes = 0u64;
        let mut codex_witnesses = 0usize;
        let mut codex_history_witnesses = 0usize;
        let mut claude_witnesses = 0usize;
        let mut claude_history_witnesses = 0usize;
        let mut document_witnesses = 0usize;
        let mut self_emanated_witnesses = 0usize;
        let mut founded_identity_witnesses = 0usize;
        for container in &containers {
            raw_bytes = raw_bytes
                .checked_add(container.raw_extent)
                .ok_or(TextMaterialError::CarrierExtent)?;
            container_hash.update([source_kind_tag(container.source_kind)]);
            container_hash.update(container.source.as_bytes());
            container_hash.update([0]);
            container_hash.update(container.raw_sha256.as_bytes());
        }
        for occurrence in &occurrences {
            for witness in &occurrence.witnesses {
                match witness.source_kind {
                    TextMaterialSourceKind::CodexRollout => codex_witnesses += 1,
                    TextMaterialSourceKind::CodexHistory => codex_history_witnesses += 1,
                    TextMaterialSourceKind::ClaudeCode => claude_witnesses += 1,
                    TextMaterialSourceKind::ClaudeHistory => claude_history_witnesses += 1,
                    TextMaterialSourceKind::ParsedDocument => document_witnesses += 1,
                    TextMaterialSourceKind::SelfEmanated => self_emanated_witnesses += 1,
                }
                if witness.identity_species
                    == TextMaterialIdentitySpecies::FoundedFromContainerRecordRange
                {
                    founded_identity_witnesses += 1;
                }
            }
        }
        let exact_witnesses = codex_witnesses
            .checked_add(codex_history_witnesses)
            .and_then(|count| count.checked_add(claude_witnesses))
            .and_then(|count| count.checked_add(claude_history_witnesses))
            .and_then(|count| count.checked_add(document_witnesses))
            .and_then(|count| count.checked_add(self_emanated_witnesses))
            .ok_or(TextMaterialError::CarrierExtent)?;
        let mut native_versions = BTreeMap::<&str, usize>::new();
        for occurrence in &occurrences {
            *native_versions
                .entry(occurrence.native_identity.as_str())
                .or_default() += 1;
        }
        let receipt = TextMaterialCorpusReceipt {
            schema: CORPUS_SCHEMA.to_owned(),
            containers: containers.len(),
            raw_bytes,
            raw_container_sha256: hex_digest(&container_hash.finalize()),
            witnessed_occurrences,
            unique_occurrences: occurrences.len(),
            human_occurrences: occurrences
                .iter()
                .filter(|occurrence| occurrence.role == TextMaterialRole::Human)
                .count(),
            assistant_occurrences: occurrences
                .iter()
                .filter(|occurrence| occurrence.role == TextMaterialRole::Assistant)
                .count(),
            document_occurrences: occurrences
                .iter()
                .filter(|occurrence| occurrence.role == TextMaterialRole::Document)
                .count(),
            codex_witnesses,
            codex_history_witnesses,
            claude_witnesses,
            claude_history_witnesses,
            document_witnesses,
            self_emanated_witnesses,
            founded_identity_witnesses,
            exact_duplicate_witnesses: exact_witnesses.saturating_sub(occurrences.len()),
            native_version_fibers: native_versions.values().filter(|count| **count > 1).count(),
            excluded_control_occurrences,
        };
        Ok(Self {
            occurrences,
            containers,
            receipt,
        })
    }

    pub fn occurrences(&self) -> &[TextMaterialOccurrence] {
        &self.occurrences
    }

    pub fn containers(&self) -> &[TextMaterialContainerReceipt] {
        &self.containers
    }

    pub const fn receipt(&self) -> &TextMaterialCorpusReceipt {
        &self.receipt
    }

    pub fn passages(&self) -> Vec<MorphologicalLanguagePassage> {
        self.occurrences
            .iter()
            .map(TextMaterialOccurrence::passage)
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct TextMaterialSection {
    occurrence_at: u32,
    local_at: u32,
    range: Range<usize>,
    /// Interned active face section. Sorted exact identifiers replace repeated owned strings.
    feature_ids: LocalSequence<u32>,
    token_path: LocalSequence<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct TextMaterialTransportPopulation {
    source: u32,
    target: u32,
    population: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TextMaterialAtlasReceipt {
    pub schema: String,
    pub conditioned_occurrences: usize,
    pub conditioned_sections: usize,
    pub surface_bytes: u64,
    pub token_occurrences: u64,
    pub distinct_tokens: usize,
    pub distinct_transports: usize,
    pub transport_occurrences: u64,
    pub indexed_features: usize,
    pub recurrent_tokens: usize,
    pub recurrent_transports: usize,
    pub source_kinds: LocalSet<TextMaterialSourceKind>,
}

/// Complete text standing plus its sparse local receiver atlas.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExactTextMaterialAtlas {
    schema: String,
    corpus: ExactTextMaterialCorpus,
    sections: LocalSequence<TextMaterialSection>,
    feature_catalogue: LocalSequence<String>,
    feature_lookup: LocalRelations<String, u32>,
    compact_feature_incidence: LocalSequence<LocalSequence<u32>>,
    token_catalogue: LocalSequence<String>,
    token_lookup: LocalRelations<String, u32>,
    token_population: LocalSequence<u64>,
    transport_population: LocalSequence<TextMaterialTransportPopulation>,
    receipt: TextMaterialAtlasReceipt,
}

impl ExactTextMaterialAtlas {
    pub fn condition(corpus: ExactTextMaterialCorpus) -> Result<Self, TextMaterialError> {
        let mut atlas = Self {
            schema: REST_SCHEMA.to_owned(),
            corpus,
            sections: LocalSequence::new(),
            feature_catalogue: LocalSequence::new(),
            feature_lookup: LocalRelations::new(),
            compact_feature_incidence: LocalSequence::new(),
            token_catalogue: LocalSequence::new(),
            token_lookup: LocalRelations::new(),
            token_population: LocalSequence::new(),
            transport_population: LocalSequence::new(),
            receipt: TextMaterialAtlasReceipt {
                schema: "life.exact-text-material-atlas-receipt.v1".to_owned(),
                conditioned_occurrences: 0,
                conditioned_sections: 0,
                surface_bytes: 0,
                token_occurrences: 0,
                distinct_tokens: 0,
                distinct_transports: 0,
                transport_occurrences: 0,
                indexed_features: 0,
                recurrent_tokens: 0,
                recurrent_transports: 0,
                source_kinds: Default::default(),
            },
        };
        atlas.rebuild_conditioned_morphology()?;
        Ok(atlas)
    }

    pub const fn corpus(&self) -> &ExactTextMaterialCorpus {
        &self.corpus
    }

    pub const fn receipt(&self) -> &TextMaterialAtlasReceipt {
        &self.receipt
    }

    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, TextMaterialError> {
        serde_json::to_vec(self).map_err(|error| TextMaterialError::Json(error.to_string()))
    }

    pub fn from_native_bytes(bytes: &[u8]) -> Result<Self, TextMaterialError> {
        Self::from_native_reader(bytes)
    }

    /// Mount a native rest from a bounded input membrane. Unlike `fs::read` followed by
    /// `from_native_bytes`, this does not retain a second complete file-sized cpu allocation
    /// beside the formed ecology.
    pub fn from_native_reader(reader: impl Read) -> Result<Self, TextMaterialError> {
        let atlas: Self = serde_json::from_reader(reader)
            .map_err(|error| TextMaterialError::Json(error.to_string()))?;
        if atlas.schema != REST_SCHEMA {
            return Err(TextMaterialError::InvalidRest);
        }
        atlas.validate()?;
        Ok(atlas)
    }

    /// Return one exact local star of the already conditioned text body.
    pub fn enact(&self, leader: &LaboratoryResearchLeader) -> LaboratoryWorldReturn {
        let (leader_features, query_transports) = self.restriction_coordinates(leader);
        // The handle population the card materializes is an APPARATUS extent — how many rows the
        // return buffer holds — and never an admission. Admission is the junction, applied to the
        // returned sections in `finish_restriction`. Before 2026-08-15 `leader.aperture` did both
        // jobs at once, which is how a device buffer size came to decide what a leader could see.
        let (source_handles, complete_population) =
            self.bounded_source_handles(&leader_features, self.sections.len().max(1));
        let feature_mask_words = text_cuda::mask_words(leader_features.len());
        let transport_mask_words = text_cuda::mask_words(query_transports.len());
        let output_row_words = text_cuda::RETURN_MASK_AT
            .saturating_add(feature_mask_words)
            .saturating_add(transport_mask_words);
        let output_words = text_cuda::RETURN_HEADER_WORDS
            .saturating_add(source_handles.len().saturating_mul(output_row_words));
        let mut output = vec![0u32; output_words];
        output[text_cuda::RETURN_COMPLETE_POPULATION] =
            u32::try_from(complete_population).unwrap_or(u32::MAX);
        output[text_cuda::RETURN_HANDLE_POPULATION] =
            u32::try_from(source_handles.len()).unwrap_or(u32::MAX);
        for (handle_at, section_at) in source_handles.iter().copied().enumerate() {
            let Some(section) = usize::try_from(section_at)
                .ok()
                .and_then(|at| self.sections.get(at))
            else {
                continue;
            };
            let output_at = text_cuda::RETURN_HEADER_WORDS
                .saturating_add(handle_at.saturating_mul(output_row_words));
            output[output_at + text_cuda::RETURN_SECTION_HANDLE] = section_at;
            let mask_at = output_at + text_cuda::RETURN_MASK_AT;
            for (query_at, feature) in leader_features.iter().copied().enumerate() {
                if section.feature_ids.binary_search(&feature).is_ok() {
                    output[mask_at + query_at / u32::BITS as usize] |=
                        1u32 << (query_at % u32::BITS as usize);
                }
            }
            for (query_at, transport) in query_transports.iter().copied().enumerate() {
                if section
                    .token_path
                    .windows(2)
                    .any(|pair| (pair[0], pair[1]) == transport)
                {
                    output[mask_at + feature_mask_words + query_at / u32::BITS as usize] |=
                        1u32 << (query_at % u32::BITS as usize);
                }
            }
        }
        self.finish_restriction(
            leader,
            &leader_features,
            feature_mask_words,
            transport_mask_words,
            &output,
        )
    }
    fn restriction_coordinates(
        &self,
        leader: &LaboratoryResearchLeader,
    ) -> (LocalSequence<u32>, LocalSequence<(u32, u32)>) {
        let mut leader_features = LocalSequence::with_capacity(leader.region.len());
        for feature in &leader.region {
            if let Some(identity) = self.feature_lookup.get(feature).copied() {
                leader_features.push(identity);
            }
        }
        leader_features.sort_unstable();
        leader_features.dedup();

        let query_tokens = lexical_tokens(&leader.question);
        let mut known_tokens = LocalSequence::with_capacity(query_tokens.len());
        for token in query_tokens {
            if let Some(identity) = self.token_lookup.get(&token).copied() {
                known_tokens.push(identity);
            }
        }
        let mut query_transports =
            LocalSequence::with_capacity(known_tokens.len().saturating_sub(1));
        for pair in known_tokens.windows(2) {
            query_transports.push((pair[0], pair[1]));
        }
        query_transports.sort_unstable();
        query_transports.dedup();
        (leader_features, query_transports)
    }

    fn resident_image(&self) -> Result<TextMaterialResidentImage, TextMaterialRestrictionError> {
        let mut feature_words = 0usize;
        let mut token_words = 0usize;
        for section in &self.sections {
            feature_words = feature_words
                .checked_add(section.feature_ids.len())
                .ok_or(TextMaterialRestrictionError::CarrierExtent)?;
            token_words = token_words
                .checked_add(section.token_path.len())
                .ok_or(TextMaterialRestrictionError::CarrierExtent)?;
        }
        let mut section_rows = LocalSequence::with_capacity(
            self.sections
                .len()
                .checked_mul(text_cuda::SECTION_ROW_WORDS)
                .ok_or(TextMaterialRestrictionError::CarrierExtent)?,
        );
        let mut section_features = LocalSequence::with_capacity(feature_words);
        let mut section_tokens = LocalSequence::with_capacity(token_words);
        let mut feature_heads = LocalSequence::with_capacity(self.feature_catalogue.len());
        feature_heads.resize_with(self.feature_catalogue.len(), || text_cuda::OPEN_LINK);
        let mut feature_nodes = LocalSequence::with_capacity(
            feature_words
                .checked_mul(text_cuda::FEATURE_NODE_WORDS)
                .ok_or(TextMaterialRestrictionError::CarrierExtent)?,
        );
        for (section_at, section) in self.sections.iter().enumerate() {
            section_rows.extend_from_slice(&[
                extent_u32(section_features.len())?,
                extent_u32(section.feature_ids.len())?,
                extent_u32(section_tokens.len())?,
                extent_u32(section.token_path.len())?,
            ]);
            section_features.extend_from_slice(&section.feature_ids);
            section_tokens.extend_from_slice(&section.token_path);
            let section_at = extent_u32(section_at)?;
            for feature in &section.feature_ids {
                let feature_at = usize::try_from(*feature)
                    .map_err(|_| TextMaterialRestrictionError::CarrierExtent)?;
                let prior = *feature_heads
                    .get(feature_at)
                    .ok_or(TextMaterialRestrictionError::CarrierExtent)?;
                let node = extent_u32(feature_nodes.len() / text_cuda::FEATURE_NODE_WORDS)?;
                feature_nodes.extend_from_slice(&[section_at, prior]);
                *feature_heads
                    .get_mut(feature_at)
                    .ok_or(TextMaterialRestrictionError::CarrierExtent)? = node;
            }
        }
        Ok(TextMaterialResidentImage {
            shape: TextMaterialResidentShape {
                occurrences: self.corpus.occurrences.len(),
                sections: self.sections.len(),
                features: self.feature_catalogue.len(),
                tokens: self.token_catalogue.len(),
                section_feature_words: feature_words,
                section_token_words: token_words,
                feature_nodes: feature_words,
            },
            section_rows,
            section_features,
            section_tokens,
            feature_heads,
            feature_nodes,
        })
    }

    fn resident_delta(
        &self,
        from: TextMaterialResidentShape,
        head_shadow: &[u32],
    ) -> Result<TextMaterialResidentDelta, TextMaterialRestrictionError> {
        if from.occurrences > self.corpus.occurrences.len()
            || from.sections > self.sections.len()
            || from.features > self.feature_catalogue.len()
            || from.tokens > self.token_catalogue.len()
            || from.feature_nodes != from.section_feature_words
            || head_shadow.len() != from.features
        {
            return Err(TextMaterialRestrictionError::CarrierExtent);
        }
        let appended_sections = self.sections.len() - from.sections;
        let mut section_rows = LocalSequence::with_capacity(
            appended_sections
                .checked_mul(text_cuda::SECTION_ROW_WORDS)
                .ok_or(TextMaterialRestrictionError::CarrierExtent)?,
        );
        let mut section_features = LocalSequence::new();
        let mut section_tokens = LocalSequence::new();
        let mut feature_nodes = LocalSequence::new();
        let mut head_updates = LocalRelations::<u32, u32>::new();
        for section_at in from.sections..self.sections.len() {
            let section = self
                .sections
                .get(section_at)
                .ok_or(TextMaterialRestrictionError::CarrierExtent)?;
            let feature_at = from
                .section_feature_words
                .checked_add(section_features.len())
                .ok_or(TextMaterialRestrictionError::CarrierExtent)?;
            let token_at = from
                .section_token_words
                .checked_add(section_tokens.len())
                .ok_or(TextMaterialRestrictionError::CarrierExtent)?;
            section_rows.extend_from_slice(&[
                extent_u32(feature_at)?,
                extent_u32(section.feature_ids.len())?,
                extent_u32(token_at)?,
                extent_u32(section.token_path.len())?,
            ]);
            section_features.extend_from_slice(&section.feature_ids);
            section_tokens.extend_from_slice(&section.token_path);
            for feature in &section.feature_ids {
                let feature_at = usize::try_from(*feature)
                    .map_err(|_| TextMaterialRestrictionError::CarrierExtent)?;
                let prior = if let Some(head) = head_updates.get(feature).copied() {
                    head
                } else if feature_at < head_shadow.len() {
                    head_shadow[feature_at]
                } else {
                    text_cuda::OPEN_LINK
                };
                let node = from
                    .feature_nodes
                    .checked_add(feature_nodes.len() / text_cuda::FEATURE_NODE_WORDS)
                    .ok_or(TextMaterialRestrictionError::CarrierExtent)?;
                let node = extent_u32(node)?;
                feature_nodes.extend_from_slice(&[extent_u32(section_at)?, prior]);
                head_updates
                    .try_insert(*feature, node)
                    .map_err(|_| TextMaterialRestrictionError::CarrierExtent)?;
            }
        }
        let mut updates = LocalSequence::with_capacity(head_updates.len());
        for (feature, head) in head_updates.iter() {
            updates.push(TextMaterialFeatureHeadUpdate {
                feature: *feature,
                head: *head,
            });
        }
        let section_feature_words = from
            .section_feature_words
            .checked_add(section_features.len())
            .ok_or(TextMaterialRestrictionError::CarrierExtent)?;
        let section_token_words = from
            .section_token_words
            .checked_add(section_tokens.len())
            .ok_or(TextMaterialRestrictionError::CarrierExtent)?;
        Ok(TextMaterialResidentDelta {
            from,
            to: TextMaterialResidentShape {
                occurrences: self.corpus.occurrences.len(),
                sections: self.sections.len(),
                features: self.feature_catalogue.len(),
                tokens: self.token_catalogue.len(),
                section_feature_words,
                section_token_words,
                feature_nodes: section_feature_words,
            },
            section_rows,
            section_features,
            section_tokens,
            feature_nodes,
            head_updates: updates,
        })
    }

    fn bounded_source_handles(
        &self,
        leader_features: &[u32],
        aperture: usize,
    ) -> (LocalSequence<u32>, usize) {
        let mut cursors = LocalSequence::with_capacity(leader_features.len());
        for feature in leader_features {
            let extent = usize::try_from(*feature)
                .ok()
                .and_then(|at| self.compact_feature_incidence.get(at))
                .map_or(0, |incidence| incidence.len());
            cursors.push(extent);
        }
        let aperture = aperture.max(1).min(self.sections.len());
        let mut handles = LocalSequence::with_capacity(aperture);
        let mut complete_population = 0usize;

        // Resident feature links point from the newest caused section toward its predecessors.
        // This direct chart follows the same descending multiway merge as the card owner. Equal
        // handles advance together, so the union count stays exact without semantic ranking.
        loop {
            let mut next = None::<u32>;
            for (feature_at, feature) in leader_features.iter().copied().enumerate() {
                let Some(incidence) = usize::try_from(feature)
                    .ok()
                    .and_then(|at| self.compact_feature_incidence.get(at))
                else {
                    continue;
                };
                let Some(cursor) = cursors.get(feature_at).copied() else {
                    continue;
                };
                let Some(section_at) = cursor
                    .checked_sub(1)
                    .and_then(|at| incidence.get(at))
                    .copied()
                else {
                    continue;
                };
                next = Some(next.map_or(section_at, |standing| standing.max(section_at)));
            }
            let Some(section_at) = next else {
                break;
            };
            for (feature_at, feature) in leader_features.iter().copied().enumerate() {
                let Some(incidence) = usize::try_from(feature)
                    .ok()
                    .and_then(|at| self.compact_feature_incidence.get(at))
                else {
                    continue;
                };
                let Some(cursor) = cursors.get(feature_at).copied() else {
                    continue;
                };
                if cursor
                    .checked_sub(1)
                    .and_then(|at| incidence.get(at))
                    .copied()
                    == Some(section_at)
                {
                    cursors[feature_at] -= 1;
                }
            }
            complete_population = complete_population.saturating_add(1);
            if handles.len() < aperture {
                handles.push(section_at);
            }
        }
        (handles, complete_population)
    }

    fn finish_restriction(
        &self,
        leader: &LaboratoryResearchLeader,
        leader_features: &[u32],
        feature_mask_words: usize,
        transport_mask_words: usize,
        output: &[u32],
    ) -> LaboratoryWorldReturn {
        let row_words = text_cuda::RETURN_MASK_AT
            .saturating_add(feature_mask_words)
            .saturating_add(transport_mask_words);
        let complete_population = output
            .get(text_cuda::RETURN_COMPLETE_POPULATION)
            .copied()
            .and_then(|population| usize::try_from(population).ok())
            .unwrap_or(0);
        let handle_population = output
            .get(text_cuda::RETURN_HANDLE_POPULATION)
            .copied()
            .and_then(|population| usize::try_from(population).ok())
            .unwrap_or(0);
        let expected_words = handle_population
            .checked_mul(row_words)
            .and_then(|words| words.checked_add(text_cuda::RETURN_HEADER_WORDS));
        if row_words <= text_cuda::RETURN_MASK_AT
            || expected_words.is_none()
            || output.len() < expected_words.unwrap_or(usize::MAX)
            || complete_population < handle_population
        {
            return LaboratoryWorldReturn {
                leader: leader.identity.clone(),
                sections: Vec::new(),
                complete_population,
                omitted_population: complete_population,
                deferred: Vec::new(),
            };
        }

        let sections = (0..handle_population)
            .filter_map(|handle_at| {
                let output_at = handle_at
                    .checked_mul(row_words)?
                    .checked_add(text_cuda::RETURN_HEADER_WORDS)?;
                let section_at = *output.get(output_at + text_cuda::RETURN_SECTION_HANDLE)?;
                let mask_at = output_at.checked_add(text_cuda::RETURN_MASK_AT)?;
                let words = output.get(mask_at..mask_at.checked_add(row_words - 1)?)?;
                if words[..feature_mask_words].iter().all(|word| *word == 0) {
                    return None;
                }
                let section = self.sections.get(usize::try_from(section_at).ok()?)?;
                let occurrence = self
                    .corpus
                    .occurrences
                    .get(usize::try_from(section.occurrence_at).ok()?)?;
                let text = occurrence.text.get(section.range.clone())?.to_owned();
                let local_at = usize::try_from(section.local_at).ok()?;
                let matched_features = leader_features
                    .iter()
                    .copied()
                    .enumerate()
                    .filter_map(|(query_at, feature)| {
                        (words[query_at / u32::BITS as usize]
                            & (1u32 << (query_at % u32::BITS as usize))
                            != 0)
                            .then(|| {
                                self.feature_catalogue
                                    .get(usize::try_from(feature).ok()?)
                                    .cloned()
                            })?
                    })
                    .collect::<BTreeSet<_>>();
                Some(LaboratoryReturnedSection {
                    identity: format!(
                        "{}/{}/surface-{local_at}",
                        leader.identity, occurrence.identity
                    ),
                    source_identity: format!("{}/surface-{local_at}", occurrence.identity),
                    source: format!(
                        "text-material/{}/{}",
                        role_name(occurrence.role),
                        phase_name(&occurrence.phase)
                    ),
                    receiver: occurrence.receiver(),
                    line: local_at,
                    kind: match occurrence.role {
                        TextMaterialRole::Human => LaboratorySourceKind::DialogueUser,
                        TextMaterialRole::Assistant => {
                            if occurrence.phase == TextMaterialPhase::Emanated {
                                LaboratorySourceKind::EmanatedAnswer
                            } else {
                                LaboratorySourceKind::DialogueAssistant
                            }
                        }
                        TextMaterialRole::Document => LaboratorySourceKind::Theory,
                    },
                    text,
                    matched_features,
                })
            })
            .collect::<Vec<_>>();

        // The junction, on the card port. The device found what shares features with the leader;
        // the admission law decides which of those the current actually crosses to, and what
        // dilates past the horizon is retained rather than dropped.
        let mut deferred = Vec::new();
        let sections = sections
            .into_iter()
            .filter(
                |section| match leader.admits(section.matched_features.len()) {
                    LeaderAdmission::Crosses { .. } => true,
                    LeaderAdmission::Defers {
                        service_rounds,
                        reflection,
                    } => {
                        deferred.push(LaboratoryDeferredSection {
                            source_identity: section.source_identity.clone(),
                            source: section.source.clone(),
                            matched_features: section.matched_features.iter().cloned().collect(),
                            service_rounds,
                            reflection,
                        });
                        false
                    }
                    LeaderAdmission::NoTravelingSection => false,
                },
            )
            .collect::<Vec<_>>();
        let omitted_population = complete_population.saturating_sub(sections.len());
        LaboratoryWorldReturn {
            leader: leader.identity.clone(),
            sections,
            complete_population,
            omitted_population,
            deferred,
        }
    }

    /// Admit a generated linguistic deed as later material. It is not relabelled as inherited
    /// dialogue, and its new recurrence changes all subsequent local restrictions.
    pub fn receive_emanated(
        &mut self,
        identity: impl Into<String>,
        text: impl Into<String>,
    ) -> Result<(), TextMaterialError> {
        self.receive_emanated_caused(identity, text, Default::default())
    }

    /// Admit a generated deed with the exact source identities which caused it.
    ///
    /// Corpus adjacency is not ancestry.  Callers which know the selected witnesses must supply
    /// them; callers which do not leave the causal fiber open rather than assigning the most
    /// recently stored occurrence as a fabricated parent.
    pub fn receive_emanated_caused(
        &mut self,
        identity: impl Into<String>,
        text: impl Into<String>,
        caused_by: BTreeSet<String>,
    ) -> Result<(), TextMaterialError> {
        let identity = identity.into();
        let text = text.into();
        if text.trim().len() < 2 {
            return Err(TextMaterialError::EmptyText);
        }
        let digest = sha256_hex(text.as_bytes());
        let native_identity = format!("self-emanated:{identity}");
        let version_identity = format!("{native_identity}:{digest}");
        if self
            .corpus
            .occurrences
            .iter()
            .any(|occurrence| occurrence.identity == version_identity)
        {
            return Ok(());
        }
        let native_version_population = self
            .corpus
            .occurrences
            .iter()
            .filter(|occurrence| occurrence.native_identity == native_identity)
            .count();
        let ordinal = u64::try_from(self.corpus.occurrences.len())
            .map_err(|_| TextMaterialError::CarrierExtent)?;
        let witness = TextMaterialWitness {
            source_kind: TextMaterialSourceKind::SelfEmanated,
            identity_species: TextMaterialIdentitySpecies::SelfEmanated,
            container: "continuing-text-body".to_owned(),
            conversation: "continuing-text-body".to_owned(),
            raw_record: ordinal,
            raw_start: 0,
            raw_end: u64::try_from(text.len()).map_err(|_| TextMaterialError::CarrierExtent)?,
            timestamp: String::new(),
            native_parent: None,
            sidechain: false,
        };
        self.corpus.occurrences.push(TextMaterialOccurrence {
            identity: version_identity,
            native_identity,
            surface_sha256: digest,
            ordinal,
            role: TextMaterialRole::Assistant,
            phase: TextMaterialPhase::Emanated,
            text,
            witnesses: BTreeSet::from([witness]),
            caused_by,
        });
        self.corpus.receipt.witnessed_occurrences = self
            .corpus
            .receipt
            .witnessed_occurrences
            .checked_add(1)
            .ok_or(TextMaterialError::CarrierExtent)?;
        self.corpus.receipt.unique_occurrences = self
            .corpus
            .receipt
            .unique_occurrences
            .checked_add(1)
            .ok_or(TextMaterialError::CarrierExtent)?;
        self.corpus.receipt.assistant_occurrences = self
            .corpus
            .receipt
            .assistant_occurrences
            .checked_add(1)
            .ok_or(TextMaterialError::CarrierExtent)?;
        self.corpus.receipt.self_emanated_witnesses = self
            .corpus
            .receipt
            .self_emanated_witnesses
            .checked_add(1)
            .ok_or(TextMaterialError::CarrierExtent)?;
        // This receipt counts native identities which have become plural, not every version
        // beyond the first. The transition from one to two versions founds the fiber once.
        if native_version_population == 1 {
            self.corpus.receipt.native_version_fibers = self
                .corpus
                .receipt
                .native_version_fibers
                .checked_add(1)
                .ok_or(TextMaterialError::CarrierExtent)?;
        }
        self.condition_appended_occurrence(
            usize::try_from(ordinal).map_err(|_| TextMaterialError::CarrierExtent)?,
        )
    }

    /// Carry only one newly appended occurrence through the contemporary morphology. Existing
    /// sections and transports remain standing; no prior text or incidence is rescanned.
    fn condition_appended_occurrence(
        &mut self,
        occurrence_at: usize,
    ) -> Result<(), TextMaterialError> {
        let occurrence = self
            .corpus
            .occurrences
            .get(occurrence_at)
            .ok_or(TextMaterialError::CarrierExtent)?;
        let text = occurrence.text.clone();
        let source_kinds = occurrence
            .witnesses
            .iter()
            .map(|witness| witness.source_kind)
            .collect::<BTreeSet<_>>();
        let occurrence_at =
            u32::try_from(occurrence_at).map_err(|_| TextMaterialError::CarrierExtent)?;
        self.receipt.surface_bytes = self
            .receipt
            .surface_bytes
            .checked_add(u64::try_from(text.len()).map_err(|_| TextMaterialError::CarrierExtent)?)
            .ok_or(TextMaterialError::CarrierExtent)?;
        self.receipt.source_kinds.extend(source_kinds);

        for (local_at, range) in local_surface_ranges(&text).into_iter().enumerate() {
            let surface = &text[range.clone()];
            let features = text_features(surface);
            if features.is_empty() {
                continue;
            }
            let tokens = lexical_tokens(surface);
            self.receipt.token_occurrences = self
                .receipt
                .token_occurrences
                .checked_add(
                    u64::try_from(tokens.len()).map_err(|_| TextMaterialError::CarrierExtent)?,
                )
                .ok_or(TextMaterialError::CarrierExtent)?;
            let mut token_path = LocalSequence::with_capacity(tokens.len());
            for token in tokens {
                let token_id = if let Some(token_id) = self.token_lookup.get(&token).copied() {
                    let population = self
                        .token_population
                        .get_mut(
                            usize::try_from(token_id)
                                .map_err(|_| TextMaterialError::CarrierExtent)?,
                        )
                        .ok_or(TextMaterialError::CarrierExtent)?;
                    if *population == 1 {
                        self.receipt.recurrent_tokens = self
                            .receipt
                            .recurrent_tokens
                            .checked_add(1)
                            .ok_or(TextMaterialError::CarrierExtent)?;
                    }
                    *population = population
                        .checked_add(1)
                        .ok_or(TextMaterialError::CarrierExtent)?;
                    token_id
                } else {
                    let token_id = u32::try_from(self.token_catalogue.len())
                        .map_err(|_| TextMaterialError::CarrierExtent)?;
                    self.token_lookup
                        .try_insert(token.clone(), token_id)
                        .map_err(|_| TextMaterialError::CarrierExtent)?;
                    self.token_catalogue.push(token);
                    self.token_population.push(1);
                    self.receipt.distinct_tokens = self
                        .receipt
                        .distinct_tokens
                        .checked_add(1)
                        .ok_or(TextMaterialError::CarrierExtent)?;
                    token_id
                };
                token_path.push(token_id);
            }
            for pair in token_path.windows(2) {
                let key = (pair[0], pair[1]);
                match self
                    .transport_population
                    .binary_search_by_key(&key, |transport| (transport.source, transport.target))
                {
                    Ok(at) => {
                        let transport = self
                            .transport_population
                            .get_mut(at)
                            .ok_or(TextMaterialError::CarrierExtent)?;
                        if transport.population == 1 {
                            self.receipt.recurrent_transports = self
                                .receipt
                                .recurrent_transports
                                .checked_add(1)
                                .ok_or(TextMaterialError::CarrierExtent)?;
                        }
                        transport.population = transport
                            .population
                            .checked_add(1)
                            .ok_or(TextMaterialError::CarrierExtent)?;
                    }
                    Err(at) => {
                        self.transport_population.insert(
                            at,
                            TextMaterialTransportPopulation {
                                source: key.0,
                                target: key.1,
                                population: 1,
                            },
                        );
                        self.receipt.distinct_transports = self
                            .receipt
                            .distinct_transports
                            .checked_add(1)
                            .ok_or(TextMaterialError::CarrierExtent)?;
                    }
                }
                self.receipt.transport_occurrences = self
                    .receipt
                    .transport_occurrences
                    .checked_add(1)
                    .ok_or(TextMaterialError::CarrierExtent)?;
            }
            let section_at =
                u32::try_from(self.sections.len()).map_err(|_| TextMaterialError::CarrierExtent)?;
            let feature_ids = intern_feature_section(
                &mut self.feature_catalogue,
                &mut self.feature_lookup,
                &mut self.compact_feature_incidence,
                &features,
                section_at,
            )?;
            self.sections.push(TextMaterialSection {
                occurrence_at,
                local_at: u32::try_from(local_at).map_err(|_| TextMaterialError::CarrierExtent)?,
                range,
                feature_ids,
                token_path,
            });
        }
        self.receipt.conditioned_occurrences = self.corpus.occurrences.len();
        self.receipt.conditioned_sections = self.sections.len();
        self.receipt.indexed_features = self.feature_catalogue.len();
        Ok(())
    }

    fn rebuild_conditioned_morphology(&mut self) -> Result<(), TextMaterialError> {
        self.sections.clear();
        self.feature_catalogue.clear();
        self.feature_lookup.clear();
        self.compact_feature_incidence.clear();
        self.token_catalogue.clear();
        self.token_lookup.clear();
        self.token_population.clear();
        self.transport_population.clear();
        let mut transport_population = BTreeMap::<(u32, u32), u64>::new();
        let mut surface_bytes = 0u64;
        let mut token_occurrences = 0u64;
        let mut transport_occurrences = 0u64;
        let mut source_kinds = LocalSet::new();
        for (occurrence_at, occurrence) in self.corpus.occurrences.iter().enumerate() {
            surface_bytes = surface_bytes
                .checked_add(
                    u64::try_from(occurrence.text.len())
                        .map_err(|_| TextMaterialError::CarrierExtent)?,
                )
                .ok_or(TextMaterialError::CarrierExtent)?;
            source_kinds.extend(
                occurrence
                    .witnesses
                    .iter()
                    .map(|witness| witness.source_kind),
            );
            let occurrence_at =
                u32::try_from(occurrence_at).map_err(|_| TextMaterialError::CarrierExtent)?;
            for (local_at, range) in local_surface_ranges(&occurrence.text)
                .into_iter()
                .enumerate()
            {
                let surface = &occurrence.text[range.clone()];
                let features = text_features(surface);
                if features.is_empty() {
                    continue;
                }
                let tokens = lexical_tokens(surface);
                token_occurrences = token_occurrences
                    .checked_add(
                        u64::try_from(tokens.len())
                            .map_err(|_| TextMaterialError::CarrierExtent)?,
                    )
                    .ok_or(TextMaterialError::CarrierExtent)?;
                let mut token_path = LocalSequence::with_capacity(tokens.len());
                for token in tokens {
                    let token_id = if let Some(token_id) = self.token_lookup.get(&token).copied() {
                        token_id
                    } else {
                        let token_id = u32::try_from(self.token_catalogue.len())
                            .map_err(|_| TextMaterialError::CarrierExtent)?;
                        self.token_lookup
                            .try_insert(token.clone(), token_id)
                            .map_err(|_| TextMaterialError::CarrierExtent)?;
                        self.token_catalogue.push(token);
                        self.token_population.push(0);
                        token_id
                    };
                    let population = self
                        .token_population
                        .get_mut(
                            usize::try_from(token_id)
                                .map_err(|_| TextMaterialError::CarrierExtent)?,
                        )
                        .ok_or(TextMaterialError::CarrierExtent)?;
                    *population = population
                        .checked_add(1)
                        .ok_or(TextMaterialError::CarrierExtent)?;
                    token_path.push(token_id);
                }
                for pair in token_path.windows(2) {
                    let population = transport_population.entry((pair[0], pair[1])).or_default();
                    *population = population
                        .checked_add(1)
                        .ok_or(TextMaterialError::CarrierExtent)?;
                    transport_occurrences = transport_occurrences
                        .checked_add(1)
                        .ok_or(TextMaterialError::CarrierExtent)?;
                }
                let section_at = u32::try_from(self.sections.len())
                    .map_err(|_| TextMaterialError::CarrierExtent)?;
                let feature_ids = intern_feature_section(
                    &mut self.feature_catalogue,
                    &mut self.feature_lookup,
                    &mut self.compact_feature_incidence,
                    &features,
                    section_at,
                )?;
                self.sections.push(TextMaterialSection {
                    occurrence_at,
                    local_at: u32::try_from(local_at)
                        .map_err(|_| TextMaterialError::CarrierExtent)?,
                    range,
                    feature_ids,
                    token_path,
                });
            }
        }
        self.transport_population = transport_population
            .into_iter()
            .map(
                |((source, target), population)| TextMaterialTransportPopulation {
                    source,
                    target,
                    population,
                },
            )
            .collect();
        self.receipt = TextMaterialAtlasReceipt {
            schema: "life.exact-text-material-atlas-receipt.v1".to_owned(),
            conditioned_occurrences: self.corpus.occurrences.len(),
            conditioned_sections: self.sections.len(),
            surface_bytes,
            token_occurrences,
            distinct_tokens: self.token_catalogue.len(),
            distinct_transports: self.transport_population.len(),
            transport_occurrences,
            indexed_features: self.feature_catalogue.len(),
            recurrent_tokens: self
                .token_population
                .iter()
                .filter(|population| **population > 1)
                .count(),
            recurrent_transports: self
                .transport_population
                .iter()
                .filter(|transport| transport.population > 1)
                .count(),
            source_kinds,
        };
        Ok(())
    }

    fn validate(&self) -> Result<(), TextMaterialError> {
        if self.schema != REST_SCHEMA
            || self.feature_catalogue.len() != self.feature_lookup.len()
            || self.feature_catalogue.len() != self.compact_feature_incidence.len()
            || self.receipt.indexed_features != self.feature_catalogue.len()
            || self.token_catalogue.len() != self.token_population.len()
            || self.token_lookup.len() != self.token_catalogue.len()
            || self.receipt.conditioned_occurrences != self.corpus.occurrences.len()
            || self.receipt.conditioned_sections != self.sections.len()
        {
            return Err(TextMaterialError::InvalidRest);
        }
        for (at, token) in self.token_catalogue.iter().enumerate() {
            if self.token_lookup.get(token).copied()
                != Some(u32::try_from(at).map_err(|_| TextMaterialError::InvalidRest)?)
            {
                return Err(TextMaterialError::InvalidRest);
            }
        }
        for (at, feature) in self.feature_catalogue.iter().enumerate() {
            if feature.is_empty()
                || self.feature_lookup.get(feature).copied()
                    != Some(u32::try_from(at).map_err(|_| TextMaterialError::InvalidRest)?)
            {
                return Err(TextMaterialError::InvalidRest);
            }
            let sections = self
                .compact_feature_incidence
                .get(at)
                .ok_or(TextMaterialError::InvalidRest)?;
            if sections.windows(2).any(|pair| pair[0] >= pair[1])
                || sections
                    .iter()
                    .any(|at| usize::try_from(*at).map_or(true, |at| at >= self.sections.len()))
            {
                return Err(TextMaterialError::InvalidRest);
            }
        }
        for section in &self.sections {
            let occurrence = self
                .corpus
                .occurrences
                .get(
                    usize::try_from(section.occurrence_at)
                        .map_err(|_| TextMaterialError::InvalidRest)?,
                )
                .ok_or(TextMaterialError::InvalidRest)?;
            if occurrence.text.get(section.range.clone()).is_none()
                || section
                    .feature_ids
                    .windows(2)
                    .any(|pair| pair[0] >= pair[1])
                || section.feature_ids.iter().any(|feature| {
                    usize::try_from(*feature)
                        .map_or(true, |feature| feature >= self.feature_catalogue.len())
                })
                || section.token_path.iter().any(|token| {
                    usize::try_from(*token)
                        .map_or(true, |token| token >= self.token_catalogue.len())
                })
            {
                return Err(TextMaterialError::InvalidRest);
            }
        }
        if self
            .transport_population
            .windows(2)
            .any(|pair| (pair[0].source, pair[0].target) >= (pair[1].source, pair[1].target))
            || self.transport_population.iter().any(|transport| {
                transport.population == 0
                    || usize::try_from(transport.source)
                        .map_or(true, |source| source >= self.token_catalogue.len())
                    || usize::try_from(transport.target)
                        .map_or(true, |target| target >= self.token_catalogue.len())
            })
        {
            return Err(TextMaterialError::InvalidRest);
        }
        Ok(())
    }
}

fn local_surface_ranges(text: &str) -> Vec<Range<usize>> {
    let mut ranges = Vec::new();
    let mut start = 0usize;
    for (at, character) in text.char_indices() {
        if !matches!(character, '.' | '?' | '!' | '\n') {
            continue;
        }
        let end = at + character.len_utf8();
        if let Some(range) = trimmed_range(text, start..end) {
            if lexical_tokens(&text[range.clone()]).len() >= 3 {
                ranges.push(range);
            }
        }
        start = end;
    }
    if let Some(range) = trimmed_range(text, start..text.len()) {
        if lexical_tokens(&text[range.clone()]).len() >= 3 {
            ranges.push(range);
        }
    }
    if ranges.is_empty() && lexical_tokens(text).len() >= 3 {
        if let Some(range) = trimmed_range(text, 0..text.len()) {
            ranges.push(range);
        }
    }
    ranges
}

fn intern_feature_section(
    catalogue: &mut LocalSequence<String>,
    lookup: &mut LocalRelations<String, u32>,
    incidence: &mut LocalSequence<LocalSequence<u32>>,
    features: &BTreeSet<String>,
    section: u32,
) -> Result<LocalSequence<u32>, TextMaterialError> {
    let mut identities = LocalSequence::with_capacity(features.len());
    for feature in features {
        let identity = if let Some(identity) = lookup.get(feature).copied() {
            identity
        } else {
            let identity =
                u32::try_from(catalogue.len()).map_err(|_| TextMaterialError::CarrierExtent)?;
            lookup
                .try_insert(feature.clone(), identity)
                .map_err(|_| TextMaterialError::CarrierExtent)?;
            catalogue.push(feature.clone());
            incidence.push(LocalSequence::new());
            identity
        };
        incidence
            .get_mut(usize::try_from(identity).map_err(|_| TextMaterialError::CarrierExtent)?)
            .ok_or(TextMaterialError::CarrierExtent)?
            .push(section);
        identities.push(identity);
    }
    identities.sort_unstable();
    identities.dedup();
    Ok(identities)
}

fn trimmed_range(text: &str, mut range: Range<usize>) -> Option<Range<usize>> {
    while range.start < range.end {
        let character = text[range.start..range.end].chars().next()?;
        if !character.is_whitespace() {
            break;
        }
        range.start += character.len_utf8();
    }
    while range.start < range.end {
        let character = text[range.start..range.end].chars().next_back()?;
        if !character.is_whitespace() {
            break;
        }
        range.end -= character.len_utf8();
    }
    (range.start < range.end).then_some(range)
}

const fn role_name(role: TextMaterialRole) -> &'static str {
    match role {
        TextMaterialRole::Human => "human",
        TextMaterialRole::Assistant => "assistant",
        TextMaterialRole::Document => "document",
    }
}

fn phase_name(phase: &TextMaterialPhase) -> &str {
    match phase {
        TextMaterialPhase::Received => "received",
        TextMaterialPhase::Commentary => "commentary",
        TextMaterialPhase::FinalAnswer => "final-answer",
        TextMaterialPhase::Response => "response",
        TextMaterialPhase::Document => "document",
        TextMaterialPhase::Emanated => "emanated",
        TextMaterialPhase::Other(other) => other,
    }
}

const fn source_kind_tag(kind: TextMaterialSourceKind) -> u8 {
    match kind {
        TextMaterialSourceKind::CodexRollout => 1,
        TextMaterialSourceKind::CodexHistory => 2,
        TextMaterialSourceKind::ClaudeCode => 3,
        TextMaterialSourceKind::ClaudeHistory => 4,
        TextMaterialSourceKind::ParsedDocument => 5,
        TextMaterialSourceKind::SelfEmanated => 6,
    }
}

fn empty_last(value: &str) -> (bool, &str) {
    (value.is_empty(), value)
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex_digest(&Sha256::digest(bytes))
}

fn hex_digest(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temporary(label: &str) -> PathBuf {
        let serial = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        std::env::temp_dir().join(format!(
            "soma-text-material-{label}-{}-{serial}.jsonl",
            std::process::id()
        ))
    }

    fn temporary_directory(label: &str) -> PathBuf {
        let serial = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "soma-text-material-{label}-{}-{serial}",
            std::process::id()
        ));
        std::fs::create_dir_all(&root).unwrap();
        root
    }

    #[test]
    fn codex_and_claude_cross_as_one_text_species_with_distinct_lineage() {
        let codex = temporary("codex");
        let claude = temporary("claude");
        std::fs::write(
            &codex,
            concat!(
                "{\"timestamp\":\"2026-01-01T00:00:00Z\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"user\",\"id\":\"u1\",\"content\":[{\"type\":\"input_text\",\"text\":\"Current conditions the shared ecology.\"}]}}\n",
                "{\"timestamp\":\"2026-01-01T00:00:01Z\",\"type\":\"response_item\",\"payload\":{\"type\":\"function_call\",\"name\":\"dark\"}}\n",
            ),
        )
        .unwrap();
        std::fs::write(
            &claude,
            concat!(
                "{\"type\":\"assistant\",\"uuid\":\"a1\",\"parentUuid\":null,\"sessionId\":\"s1\",\"timestamp\":\"2026-01-01T00:00:02Z\",\"message\":{\"role\":\"assistant\",\"content\":[{\"type\":\"thinking\",\"thinking\":\"dark\"},{\"type\":\"text\",\"text\":\"The returned answer changes later conduct.\"}]}}\n",
                "{\"type\":\"user\",\"uuid\":\"tool\",\"parentUuid\":\"a1\",\"sessionId\":\"s1\",\"message\":{\"role\":\"user\",\"content\":[{\"type\":\"tool_result\",\"content\":\"dark\"}]}}\n",
            ),
        )
        .unwrap();
        let corpus = ExactTextMaterialCorpus::import(
            vec![
                TextMaterialInput::CodexRollout(codex.clone()),
                TextMaterialInput::ClaudeCode(claude.clone()),
            ],
            &[],
            2,
        )
        .unwrap();
        assert_eq!(corpus.occurrences().len(), 2);
        assert_eq!(corpus.receipt().codex_witnesses, 1);
        assert_eq!(corpus.receipt().claude_witnesses, 1);
        assert_eq!(corpus.occurrences()[0].receiver(), TEXT_USER_RECEIVER);
        let atlas = ExactTextMaterialAtlas::condition(corpus).unwrap();
        assert!(atlas.receipt().distinct_transports > 0);
        let mut atlas = atlas;
        atlas
            .receive_emanated(
                "answer-0",
                "The generated answer returns and changes later conduct.",
            )
            .unwrap();
        atlas
            .receive_emanated_caused(
                "answer-0",
                "A corrected generated answer changes the same native version fiber.",
                BTreeSet::from(["world-return-0".to_owned()]),
            )
            .unwrap();
        atlas
            .receive_emanated_caused(
                "answer-0",
                "A third generated answer remains inside that already-founded version fiber.",
                BTreeSet::from(["world-return-0".to_owned(), "answer-revision-1".to_owned()]),
            )
            .unwrap();
        assert_eq!(atlas.corpus().receipt().native_version_fibers, 1);
        assert!(atlas
            .corpus()
            .occurrences()
            .last()
            .is_some_and(|occurrence| {
                occurrence.caused_by
                    == BTreeSet::from(["world-return-0".to_owned(), "answer-revision-1".to_owned()])
                    && occurrence
                        .witnesses
                        .iter()
                        .all(|witness| witness.native_parent.is_none())
            }));
        let incremental_rest = atlas.encode_native_bytes().unwrap();
        atlas.rebuild_conditioned_morphology().unwrap();
        assert_eq!(atlas.encode_native_bytes().unwrap(), incremental_rest);
        let refusal = atlas
            .mount_cuda(i32::MAX)
            .expect_err("an unavailable device ordinal must refuse without consuming the cpu");
        assert_eq!(
            refusal.atlas().encode_native_bytes().unwrap(),
            incremental_rest
        );
        std::fs::remove_file(codex).unwrap();
        std::fs::remove_file(claude).unwrap();
    }

    #[test]
    fn exact_duplicate_occurrences_merge_witnesses_without_erasing_recurrence() {
        let left = temporary("left");
        let right = temporary("right");
        let record = "{\"timestamp\":\"2026-01-01T00:00:00Z\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"user\",\"id\":\"same\",\"content\":[{\"type\":\"input_text\",\"text\":\"One occurrence has two container witnesses.\"}]}}\n";
        std::fs::write(&left, record).unwrap();
        std::fs::write(&right, record).unwrap();
        let corpus = ExactTextMaterialCorpus::import(
            vec![
                TextMaterialInput::CodexRollout(left.clone()),
                TextMaterialInput::CodexRollout(right.clone()),
            ],
            &[],
            2,
        )
        .unwrap();
        assert_eq!(corpus.occurrences().len(), 1);
        assert_eq!(corpus.occurrences()[0].witnesses.len(), 2);
        assert_eq!(corpus.receipt().exact_duplicate_witnesses, 1);
        std::fs::remove_file(left).unwrap();
        std::fs::remove_file(right).unwrap();
    }

    #[test]
    fn histories_and_unidentified_rollouts_found_typed_plural_occurrences() {
        let codex_history = temporary("codex-history");
        let claude_history = temporary("claude-history");
        let left = temporary("codex-unidentified-left");
        let right = temporary("codex-unidentified-right");
        std::fs::write(
            &codex_history,
            concat!(
                "{\"session_id\":\"history-left\",\"ts\":1,\"text\":\"The same exact surface remains a first occurrence.\"}\n",
                "{\"session_id\":\"history-right\",\"ts\":2,\"text\":\"The same exact surface remains a first occurrence.\"}\n",
            ),
        )
        .unwrap();
        std::fs::write(
            &claude_history,
            "{\"display\":\"Claude history crosses the same material mouth.\",\"pastedContents\":{},\"project\":\"fixture\",\"sessionId\":\"claude-history\",\"timestamp\":3}\n",
        )
        .unwrap();
        for (path, session) in [(&left, "rollout-left"), (&right, "rollout-right")] {
            std::fs::write(
                path,
                format!(
                    "{{\"type\":\"session_meta\",\"payload\":{{\"id\":\"{session}\",\"session_id\":\"{session}\"}}}}\n{{\"timestamp\":\"2026-01-01T00:00:00Z\",\"type\":\"response_item\",\"payload\":{{\"type\":\"message\",\"role\":\"user\",\"content\":[{{\"type\":\"input_text\",\"text\":\"An absent provider id does not erase this occurrence.\"}}]}}}}\n"
                ),
            )
            .unwrap();
        }
        let corpus = ExactTextMaterialCorpus::import(
            vec![
                TextMaterialInput::CodexHistory(codex_history.to_owned()),
                TextMaterialInput::ClaudeHistory(claude_history.to_owned()),
                TextMaterialInput::CodexRollout(left.to_owned()),
                TextMaterialInput::CodexRollout(right.to_owned()),
            ],
            &[],
            2,
        )
        .unwrap();
        assert_eq!(corpus.occurrences().len(), 5);
        assert_eq!(corpus.receipt().codex_history_witnesses, 2);
        assert_eq!(corpus.receipt().claude_history_witnesses, 1);
        assert_eq!(corpus.receipt().codex_witnesses, 2);
        assert_eq!(corpus.receipt().founded_identity_witnesses, 5);
        assert!(corpus.occurrences().iter().all(|occurrence| occurrence
            .witnesses
            .iter()
            .all(|witness| witness.identity_species
                == TextMaterialIdentitySpecies::FoundedFromContainerRecordRange)));
        assert!(corpus.occurrences().iter().any(|occurrence| occurrence
            .witnesses
            .iter()
            .any(|witness| witness.conversation == "rollout-left")));
        assert!(corpus.occurrences().iter().any(|occurrence| occurrence
            .witnesses
            .iter()
            .any(|witness| witness.conversation == "rollout-right")));
        std::fs::remove_file(codex_history).unwrap();
        std::fs::remove_file(claude_history).unwrap();
        std::fs::remove_file(left).unwrap();
        std::fs::remove_file(right).unwrap();
    }

    /// The rollout fixture that carries `payload.id` on every message record.
    ///
    /// The 2026-08-11 audit convicted the older fixture for omitting it: the defect under test —
    /// a message identity occupying the conversation coordinate — could not fire on material that
    /// carried no message identity at all, so the test wore a passing result over a deleted
    /// chronology. `CLAUDE.md` §8: a check whose material cannot vary the property under test is
    /// the same defect as a check that cannot fail.
    const ROLLOUT_CARRYING_MESSAGE_IDENTITIES: &str = concat!(
        "{\"type\":\"session_meta\",\"payload\":{\"id\":\"019f-meta\",\"session_id\":\"019f-session\"}}\n",
        "{\"timestamp\":\"2026-01-01T00:00:00Z\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"user\",\"id\":\"msg_0\",\"content\":[{\"type\":\"input_text\",\"text\":\"The first received current opens the container.\"}]}}\n",
        "{\"timestamp\":\"2026-01-01T00:00:01Z\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"assistant\",\"phase\":\"final_answer\",\"id\":\"msg_1\",\"content\":[{\"type\":\"output_text\",\"text\":\"The returned answer follows the received current.\"}]}}\n",
        "{\"timestamp\":\"2026-01-01T00:00:02Z\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"user\",\"id\":\"msg_2\",\"content\":[{\"type\":\"input_text\",\"text\":\"The second received current follows that answer.\"}]}}\n",
    );

    #[test]
    fn a_rollout_conversation_is_the_session_and_never_a_message_identity() {
        let rollout = temporary("rollout-chronology");
        std::fs::write(&rollout, ROLLOUT_CARRYING_MESSAGE_IDENTITIES).unwrap();
        let corpus = ExactTextMaterialCorpus::import(
            vec![TextMaterialInput::CodexRollout(rollout.clone())],
            &[],
            1,
        )
        .unwrap();
        assert_eq!(corpus.occurrences().len(), 3);
        for occurrence in corpus.occurrences() {
            for witness in &occurrence.witnesses {
                assert_eq!(
                    witness.conversation, "019f-session",
                    "the conversation is the container's session, not the message identity"
                );
            }
        }
        // Chronology inside the container: each visible occurrence names the one before it.
        assert!(corpus.occurrences()[0].caused_by.is_empty());
        assert_eq!(
            corpus.occurrences()[1].caused_by,
            BTreeSet::from(["codex:msg_0".to_owned()])
        );
        assert_eq!(
            corpus.occurrences()[2].caused_by,
            BTreeSet::from(["codex:msg_1".to_owned()])
        );
        std::fs::remove_file(rollout).unwrap();
    }

    /// The same container with **no** `payload.id` on any message record, so every identity in it
    /// is founded by the membrane rather than supplied by the container. The relocation control
    /// carries both species: a supplied identity is container-independent for free, and proves
    /// nothing about the founding law.
    const ROLLOUT_WITHOUT_MESSAGE_IDENTITIES: &str = concat!(
        "{\"type\":\"session_meta\",\"payload\":{\"id\":\"019e-meta\",\"session_id\":\"019e-session\"}}\n",
        "{\"timestamp\":\"2026-01-02T00:00:00Z\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"user\",\"content\":[{\"type\":\"input_text\",\"text\":\"An absent provider identity founds one from the record.\"}]}}\n",
        "{\"timestamp\":\"2026-01-02T00:00:01Z\",\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"assistant\",\"phase\":\"final_answer\",\"content\":[{\"type\":\"output_text\",\"text\":\"The founded identity is the record address itself.\"}]}}\n",
    );

    #[test]
    fn one_container_read_at_two_cpu_paths_founds_one_identical_body() {
        // The relocation control. A corpus address which moves when the container moves is a
        // lineage in an absolute frame — `CLAUDE.md` §0 lesson 2 — and no hash comparison can see
        // it, because both frames hash consistently inside themselves.
        let left_root = temporary_directory("relocation-left");
        let right_root = temporary_directory("relocation-right");
        let supplied = "rollout-2026-01-01T00-00-00-supplied.jsonl";
        let founded = "rollout-2026-01-02T00-00-00-founded.jsonl";
        for root in [&left_root, &right_root] {
            std::fs::write(root.join(supplied), ROLLOUT_CARRYING_MESSAGE_IDENTITIES).unwrap();
            std::fs::write(root.join(founded), ROLLOUT_WITHOUT_MESSAGE_IDENTITIES).unwrap();
        }

        let read = |root: &Path| {
            let corpus = ExactTextMaterialCorpus::import(
                vec![
                    TextMaterialInput::CodexRollout(root.join(supplied)),
                    TextMaterialInput::CodexRollout(root.join(founded)),
                ],
                &[],
                2,
            )
            .unwrap();
            assert_eq!(
                corpus.receipt().founded_identity_witnesses,
                2,
                "the relocation control must exercise the founding law, not only supplied ids"
            );
            let identities = corpus
                .occurrences()
                .iter()
                .map(|occurrence| occurrence.identity.clone())
                .collect::<Vec<_>>();
            let containers = corpus
                .containers()
                .iter()
                .map(|container| container.source.clone())
                .collect::<Vec<_>>();
            let rest = ExactTextMaterialAtlas::condition(corpus)
                .unwrap()
                .encode_native_bytes()
                .unwrap();
            (identities, containers, rest)
        };
        let (left_identities, left_containers, left_rest) = read(&left_root);
        let (right_identities, right_containers, right_rest) = read(&right_root);

        assert_eq!(
            sha256_hex(&left_rest),
            sha256_hex(&right_rest),
            "the sealed content address must not move when the container moves"
        );
        assert_eq!(left_identities, right_identities);
        assert_eq!(
            left_containers,
            vec![supplied.to_owned(), founded.to_owned()]
        );
        assert_eq!(left_containers, right_containers);

        // And neither cpu frame survives anywhere inside the body it was read into.
        let sealed = String::from_utf8(left_rest).unwrap();
        for root in [&left_root, &right_root] {
            assert!(
                !sealed.contains(root.to_str().unwrap()),
                "a cpu coordinate reached the sealed body"
            );
        }

        for root in [&left_root, &right_root] {
            std::fs::remove_file(root.join(supplied)).unwrap();
            std::fs::remove_file(root.join(founded)).unwrap();
            std::fs::remove_dir(root).unwrap();
        }
    }

    #[test]
    fn two_containers_of_one_kind_under_one_address_are_refused() {
        let left_root = temporary_directory("collision-left");
        let right_root = temporary_directory("collision-right");
        let name = "rollout-2026-01-01T00-00-00-collision.jsonl";
        let left = left_root.join(name);
        let right = right_root.join(name);
        std::fs::write(&left, ROLLOUT_CARRYING_MESSAGE_IDENTITIES).unwrap();
        std::fs::write(&right, ROLLOUT_CARRYING_MESSAGE_IDENTITIES).unwrap();
        let refusal = ExactTextMaterialCorpus::import(
            vec![
                TextMaterialInput::CodexRollout(left.clone()),
                TextMaterialInput::CodexRollout(right.clone()),
            ],
            &[],
            2,
        )
        .expect_err("one address cannot separate two containers");
        assert!(matches!(
            refusal,
            TextMaterialError::ContainerAddressCollision(_)
        ));
        std::fs::remove_file(left).unwrap();
        std::fs::remove_file(right).unwrap();
        std::fs::remove_dir(left_root).unwrap();
        std::fs::remove_dir(right_root).unwrap();
    }

    #[test]
    fn bounded_source_handles_follow_incidence_without_semantic_ranking() {
        let corpus = ExactTextMaterialCorpus::import(
            Vec::new(),
            &[ParsedTextDocument {
                identity: "incidence-body".to_owned(),
                source: "fixture/incidence-body".to_owned(),
                sections: vec![
                    "Exact incidence carries the first caused section.".to_owned(),
                    "Exact incidence carries the second caused section.".to_owned(),
                    "Exact incidence carries the third caused section.".to_owned(),
                ],
            }],
            1,
        )
        .unwrap();
        let atlas = ExactTextMaterialAtlas::condition(corpus).unwrap();
        let (feature_at, incidence) = atlas
            .compact_feature_incidence
            .iter()
            .enumerate()
            .find(|(_, incidence)| incidence.len() == 3)
            .expect("the shared exact/incidence feature reaches all three sections");
        let feature = u32::try_from(feature_at).unwrap();
        let (handles, complete) = atlas.bounded_source_handles(&[feature], 1);
        assert_eq!(complete, incidence.len());
        assert_eq!(handles.as_ref(), &[*incidence.last().unwrap()]);
    }
}
