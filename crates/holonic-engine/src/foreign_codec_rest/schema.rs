//! A source-detached exterior codebook rest.
//!
//! This owner composes the source-asset identity already returned by Station B with the
//! source/native display correspondence needed by a later lifted body.  It is deliberately only
//! a boundary codec: it carries no segmentation law, vocabulary ontology, model transport, or
//! semantic category.  A row says which source address and source bytes were carried across the
//! boundary and which native address/surface is available after the source departs.
//!
//! JSON and compact TSV are exterior wires only. `mount` validates the schema, canonical row order,
//! source identity and row digest before exposing any surface. Missing source IDs are not mapped
//! to a guessed value: they return an explicit open reconstruction fibre.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::path::Path;

pub const REST_SCHEMA: &str = "holonic-engine.phoenix.exterior-codebook-rest.v1";

pub(crate) fn digest_bytes(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// Identity of the foreign occurrence and its codec siblings, copied from Station B's receipt.
/// Paths are lineage only; a mounted rest never opens them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceAssetIdentity {
    pub model_sha256: String,
    pub tokenizer_sha256: String,
    pub tokenizer_config_sha256: String,
    pub config_sha256: String,
    pub model_content_sha256: String,
}

/// One source/native exterior correspondence. IDs are addresses, not semantic classes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodebookEntry {
    pub source_id: u32,
    pub source_piece: String,
    pub native_id: u32,
    pub native_surface: String,
}

/// A named vocabulary remainder rather than an accidental fallback. `extent` is the declared
/// vocabulary population; `represented` is what this rest actually seals.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpenFibre {
    pub axis: String,
    pub extent: u64,
    pub represented: u64,
    pub reason: String,
}

/// Exterior vocabulary coverage only. Operation, layer, and source-population testimony belongs
/// to the operation correspondence/rest owners and must not be duplicated here.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoverageSummary {
    pub represented_token_ids: u32,
}

/// A content-addressed descriptor for companion tokenizer files. The native manifest carries this
/// small descriptor; W1 copies the exact bytes separately under their digests rather than
/// expanding multi-megabyte JSON into the manifest.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExteriorCodecDescriptor {
    pub tokenizer_json_sha256: String,
    pub tokenizer_json_len: u64,
    pub tokenizer_config_sha256: Option<String>,
    pub tokenizer_config_json_len: Option<u64>,
}

/// Exact companion bytes read once at the construction boundary. This is an exterior codec face,
/// not an engine tokenizer implementation. Callers may write these bytes to content-addressed
/// companion files and retain only [`ExteriorCodecDescriptor`] in the native rest.
#[derive(Debug, PartialEq, Eq)]
pub struct ExteriorCodecArtifact {
    pub tokenizer_json: Vec<u8>,
    pub tokenizer_config_json: Option<Vec<u8>>,
}

impl ExteriorCodecArtifact {
    pub fn from_bytes(tokenizer_json: Vec<u8>, tokenizer_config_json: Option<Vec<u8>>) -> Self {
        Self {
            tokenizer_json,
            tokenizer_config_json,
        }
    }

    pub fn from_paths(
        tokenizer_path: impl AsRef<Path>,
        tokenizer_config_path: Option<impl AsRef<Path>>,
    ) -> Result<Self, RestError> {
        let tokenizer_json =
            std::fs::read(tokenizer_path).map_err(|error| RestError::Io(error.to_string()))?;
        let tokenizer_config_json = tokenizer_config_path
            .map(|path| std::fs::read(path).map_err(|error| RestError::Io(error.to_string())))
            .transpose()?;
        Ok(Self::from_bytes(tokenizer_json, tokenizer_config_json))
    }

    pub fn descriptor(&self) -> ExteriorCodecDescriptor {
        ExteriorCodecDescriptor {
            tokenizer_json_sha256: digest_bytes(&self.tokenizer_json),
            tokenizer_json_len: self.tokenizer_json.len() as u64,
            tokenizer_config_sha256: self.tokenizer_config_json.as_deref().map(digest_bytes),
            tokenizer_config_json_len: self
                .tokenizer_config_json
                .as_ref()
                .map(|bytes| bytes.len() as u64),
        }
    }
}

/// Validate the detached descriptor even when its companion bytes are not mounted yet. The
/// descriptor's lengths cannot be recomputed without bytes, but their optional fields must be
/// paired and their content digests must still bind to the originating asset identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RestError {
    WrongSchema(String),
    EmptyVocabulary,
    EntryOutOfRange {
        id: u32,
        extent: u32,
    },
    RepeatedSourceId(u32),
    RepeatedNativeId(u32),
    UnsortedEntries,
    NativeEntryOutOfRange {
        id: u32,
        extent: u32,
    },
    MissingNativeId {
        id: u32,
        extent: u32,
    },
    CoverageDisagrees {
        represented: u32,
        entries: u32,
    },
    FullCoverageIncomplete {
        axis: &'static str,
        expected: u32,
        actual: u32,
    },
    WrongOpenAxis(String),
    CodecDigestMismatch {
        kind: &'static str,
        expected: String,
        actual: String,
    },
    CodecIdentityMismatch {
        kind: &'static str,
        source: String,
        artifact: String,
    },
    OpenFibreExceedsExtent {
        axis: String,
        represented: u64,
        extent: u64,
    },
    OpenFibreDisagrees {
        extent: u64,
        represented: u64,
        expected_extent: u64,
        expected_represented: u64,
    },
    DigestMismatch {
        expected: String,
        actual: String,
    },
    Json(String),
    MalformedTsv(String),
    Io(String),
}

impl std::fmt::Display for RestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongSchema(schema) => write!(f, "wrong rest schema {schema}"),
            Self::EmptyVocabulary => f.write_str("empty codebook rest"),
            Self::EntryOutOfRange { id, extent } => {
                write!(f, "source id {id} outside extent {extent}")
            }
            Self::RepeatedSourceId(id) => write!(f, "repeated source id {id}"),
            Self::RepeatedNativeId(id) => write!(f, "repeated native id {id}"),
            Self::UnsortedEntries => f.write_str("entries are not in source-id order"),
            Self::NativeEntryOutOfRange { id, extent } => {
                write!(f, "native id {id} outside extent {extent}")
            }
            Self::MissingNativeId { id, extent } => {
                write!(f, "native id {id} remains open within extent {extent}")
            }
            Self::CoverageDisagrees {
                represented,
                entries,
            } => write!(
                f,
                "coverage says {represented} represented ids, rest carries {entries}"
            ),
            Self::FullCoverageIncomplete {
                axis,
                expected,
                actual,
            } => write!(
                f,
                "full vocabulary coverage for {axis} expects {expected} entries, found {actual}"
            ),
            Self::WrongOpenAxis(axis) => {
                write!(f, "codebook open fibre has non-vocabulary axis {axis}")
            }
            Self::CodecDigestMismatch {
                kind,
                expected,
                actual,
            } => write!(f, "{kind} codec digest {actual} does not match {expected}"),
            Self::CodecIdentityMismatch {
                kind,
                source,
                artifact,
            } => write!(
                f,
                "{kind} codec identity {artifact} does not match source {source}"
            ),
            Self::OpenFibreExceedsExtent {
                axis,
                represented,
                extent,
            } => write!(
                f,
                "open fibre {axis} represents {represented} of extent {extent}"
            ),
            Self::OpenFibreDisagrees {
                extent,
                represented,
                expected_extent,
                expected_represented,
            } => write!(
                f,
                "vocabulary open fibre {extent}:{represented} does not match required {expected_extent}:{expected_represented}"
            ),
            Self::DigestMismatch { expected, actual } => {
                write!(f, "codebook digest {actual} does not match {expected}")
            }
            Self::Json(error) => write!(f, "rest json: {error}"),
            Self::MalformedTsv(error) => write!(f, "rest tsv: {error}"),
            Self::Io(error) => write!(f, "rest io: {error}"),
        }
    }
}

impl std::error::Error for RestError {}
