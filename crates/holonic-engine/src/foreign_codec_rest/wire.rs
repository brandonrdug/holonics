use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::path::Path;

use super::schema::*;
use super::validation::{validate_codec, validate_codec_descriptor};

/// The sealed source-detached boundary rest.
#[derive(Debug, Serialize, Deserialize)]
pub struct ExteriorCodebookRest {
    pub schema: String,
    pub source: SourceAssetIdentity,
    pub vocabulary_extent: u32,
    pub entries: Vec<CodebookEntry>,
    pub coverage: CoverageSummary,
    pub open: Vec<OpenFibre>,
    /// Optional in the compact codebook TSV view; required by a native rest that promises to
    /// continue encoding/decoding after source detachment.
    #[serde(default)]
    pub codec: Option<ExteriorCodecDescriptor>,
    /// Derived native-address index. It is deliberately not serialized or hashed: the semantic
    /// rows remain source-ordered, while this compact row-number permutation gives native lookup
    /// logarithmic cost for arbitrary bijections without duplicating row payloads.
    #[serde(skip)]
    native_index: Vec<u32>,
    pub codebook_sha256: String,
}

impl PartialEq for ExteriorCodebookRest {
    fn eq(&self, other: &Self) -> bool {
        self.schema == other.schema
            && self.source == other.source
            && self.vocabulary_extent == other.vocabulary_extent
            && self.entries == other.entries
            && self.coverage == other.coverage
            && self.open == other.open
            && self.codec == other.codec
            && self.codebook_sha256 == other.codebook_sha256
    }
}

impl Eq for ExteriorCodebookRest {}

/// A native read is either founded by a row or explicitly remains in the retained fibre.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeRead<'a> {
    Surface(&'a str),
    Open {
        native_id: u32,
        extent: u32,
        represented: u32,
    },
}

impl ExteriorCodebookRest {
    /// Seal the caller's already-derived correspondence. The owner does not read tokenizer JSON
    /// or invent a surface transform; the caller supplies each native surface explicitly.
    pub fn seal(
        source: SourceAssetIdentity,
        vocabulary_extent: u32,
        entries: Vec<CodebookEntry>,
        coverage: CoverageSummary,
        open: Vec<OpenFibre>,
    ) -> Result<Self, RestError> {
        Self::seal_with_codec(source, vocabulary_extent, entries, coverage, open, None)
    }

    /// Seal a codebook together with the exact tokenizer exterior chart. The bytes are retained
    /// so a later native mount can continue the codec after all source paths have disappeared.
    pub fn seal_with_codec(
        source: SourceAssetIdentity,
        vocabulary_extent: u32,
        entries: Vec<CodebookEntry>,
        mut coverage: CoverageSummary,
        open: Vec<OpenFibre>,
        codec: Option<ExteriorCodecArtifact>,
    ) -> Result<Self, RestError> {
        if vocabulary_extent == 0 {
            return Err(RestError::EmptyVocabulary);
        }
        for (position, entry) in entries.iter().enumerate() {
            if entry.source_id >= vocabulary_extent {
                return Err(RestError::EntryOutOfRange {
                    id: entry.source_id,
                    extent: vocabulary_extent,
                });
            }
            if entry.native_id >= vocabulary_extent {
                return Err(RestError::NativeEntryOutOfRange {
                    id: entry.native_id,
                    extent: vocabulary_extent,
                });
            }
            if position > 0 {
                let previous = &entries[position - 1];
                if previous.source_id == entry.source_id {
                    return Err(RestError::RepeatedSourceId(entry.source_id));
                }
                if previous.source_id > entry.source_id {
                    return Err(RestError::UnsortedEntries);
                }
            }
        }
        let mut native_index: Vec<u32> = (0..entries.len()).map(|row| row as u32).collect();
        native_index.sort_unstable_by_key(|row| entries[*row as usize].native_id);
        for pair in native_index.windows(2) {
            let left = entries[pair[0] as usize].native_id;
            let right = entries[pair[1] as usize].native_id;
            if left == right {
                return Err(RestError::RepeatedNativeId(right));
            }
        }
        if coverage.represented_token_ids != entries.len() as u32 {
            return Err(RestError::CoverageDisagrees {
                represented: coverage.represented_token_ids,
                entries: entries.len() as u32,
            });
        }
        if coverage.represented_token_ids > vocabulary_extent {
            return Err(RestError::CoverageDisagrees {
                represented: coverage.represented_token_ids,
                entries: entries.len() as u32,
            });
        }
        for fibre in &open {
            if fibre.axis != "vocabulary-id" {
                return Err(RestError::WrongOpenAxis(fibre.axis.clone()));
            }
            if fibre.represented > fibre.extent {
                return Err(RestError::OpenFibreExceedsExtent {
                    axis: fibre.axis.clone(),
                    represented: fibre.represented,
                    extent: fibre.extent,
                });
            }
        }
        let codec_descriptor = codec.map(|artifact| {
            let descriptor = artifact.descriptor();
            (artifact, descriptor)
        });
        if let Some((artifact, descriptor)) = &codec_descriptor {
            validate_codec(&source, descriptor, artifact)?;
        }
        if coverage.represented_token_ids == vocabulary_extent {
            let expected = vocabulary_extent;
            let source_complete = entries
                .iter()
                .enumerate()
                .all(|(index, entry)| entry.source_id == index as u32);
            if !source_complete {
                return Err(RestError::FullCoverageIncomplete {
                    axis: "source-id",
                    expected,
                    actual: entries.len() as u32,
                });
            }
            if !open.is_empty() {
                return Err(RestError::FullCoverageIncomplete {
                    axis: "open-fibre",
                    expected: 0,
                    actual: open.len() as u32,
                });
            }
        } else {
            if open.len() != 1 {
                return Err(RestError::FullCoverageIncomplete {
                    axis: "open-fibre",
                    expected: 1,
                    actual: open.len() as u32,
                });
            }
            let fibre = &open[0];
            if fibre.extent != u64::from(vocabulary_extent)
                || fibre.represented != u64::from(entries.len() as u32)
            {
                return Err(RestError::OpenFibreDisagrees {
                    extent: fibre.extent,
                    represented: fibre.represented,
                    expected_extent: u64::from(vocabulary_extent),
                    expected_represented: entries.len() as u64,
                });
            }
        }
        coverage.represented_token_ids = entries.len() as u32;
        let mut rest = Self {
            schema: REST_SCHEMA.to_owned(),
            source,
            vocabulary_extent,
            entries,
            coverage,
            open,
            codec: codec_descriptor.map(|(_, descriptor)| descriptor),
            native_index,
            codebook_sha256: String::new(),
        };
        rest.codebook_sha256 = rest.digest();
        Ok(rest)
    }

    /// Validate a mounted wire and return the detached rest. No source/model path is consulted.
    pub fn mount(mut wire: Self) -> Result<Self, RestError> {
        if wire.schema != REST_SCHEMA {
            return Err(RestError::WrongSchema(wire.schema));
        }
        let expected = wire.codebook_sha256.clone();
        let actual = wire.digest();
        if expected != actual {
            return Err(RestError::DigestMismatch { expected, actual });
        }
        let digest = wire.codebook_sha256.clone();
        wire.codebook_sha256 = digest;
        let codec = wire.codec.clone();
        if let Some(descriptor) = &codec {
            validate_codec_descriptor(&wire.source, descriptor)?;
        }
        let mut mounted = Self::seal(
            wire.source,
            wire.vocabulary_extent,
            wire.entries,
            wire.coverage,
            wire.open,
        )?;
        mounted.codec = codec;
        mounted.codebook_sha256 = mounted.digest();
        Ok(mounted)
    }

    /// Validate an already-mounted codebook without taking ownership of, or rebuilding, its
    /// row population.  The native rest uses this borrowed receipt at its admission boundary;
    /// cloning a complete exterior vocabulary merely to authenticate it would duplicate the
    /// continuing owner.
    pub fn validate(&self) -> Result<(), RestError> {
        if self.schema != REST_SCHEMA {
            return Err(RestError::WrongSchema(self.schema.clone()));
        }
        let expected = &self.codebook_sha256;
        let actual = self.digest();
        if expected != &actual {
            return Err(RestError::DigestMismatch {
                expected: expected.clone(),
                actual,
            });
        }
        if self.vocabulary_extent == 0 {
            return Err(RestError::EmptyVocabulary);
        }
        let mut native_ids = std::collections::BTreeSet::new();
        for (position, entry) in self.entries.iter().enumerate() {
            if entry.source_id >= self.vocabulary_extent {
                return Err(RestError::EntryOutOfRange {
                    id: entry.source_id,
                    extent: self.vocabulary_extent,
                });
            }
            if entry.native_id >= self.vocabulary_extent {
                return Err(RestError::NativeEntryOutOfRange {
                    id: entry.native_id,
                    extent: self.vocabulary_extent,
                });
            }
            if position > 0 {
                let previous = &self.entries[position - 1];
                if previous.source_id == entry.source_id {
                    return Err(RestError::RepeatedSourceId(entry.source_id));
                }
                if previous.source_id > entry.source_id {
                    return Err(RestError::UnsortedEntries);
                }
            }
            if !native_ids.insert(entry.native_id) {
                return Err(RestError::RepeatedNativeId(entry.native_id));
            }
        }
        if self.coverage.represented_token_ids != self.entries.len() as u32
            || self.coverage.represented_token_ids > self.vocabulary_extent
        {
            return Err(RestError::CoverageDisagrees {
                represented: self.coverage.represented_token_ids,
                entries: self.entries.len() as u32,
            });
        }
        for fibre in &self.open {
            if fibre.axis != "vocabulary-id" {
                return Err(RestError::WrongOpenAxis(fibre.axis.clone()));
            }
            if fibre.represented > fibre.extent {
                return Err(RestError::OpenFibreExceedsExtent {
                    axis: fibre.axis.clone(),
                    represented: fibre.represented,
                    extent: fibre.extent,
                });
            }
        }
        if let Some(codec) = &self.codec {
            validate_codec_descriptor(&self.source, codec)?;
        }
        if self.coverage.represented_token_ids == self.vocabulary_extent {
            let source_complete = self
                .entries
                .iter()
                .enumerate()
                .all(|(index, entry)| entry.source_id == index as u32);
            if !source_complete {
                return Err(RestError::FullCoverageIncomplete {
                    axis: "source-id",
                    expected: self.vocabulary_extent,
                    actual: self.entries.len() as u32,
                });
            }
            if !self.open.is_empty() {
                return Err(RestError::FullCoverageIncomplete {
                    axis: "open-fibre",
                    expected: 0,
                    actual: self.open.len() as u32,
                });
            }
        } else {
            if self.open.len() != 1 {
                return Err(RestError::FullCoverageIncomplete {
                    axis: "open-fibre",
                    expected: 1,
                    actual: self.open.len() as u32,
                });
            }
            let fibre = &self.open[0];
            if fibre.extent != u64::from(self.vocabulary_extent)
                || fibre.represented != self.entries.len() as u64
            {
                return Err(RestError::OpenFibreDisagrees {
                    extent: fibre.extent,
                    represented: fibre.represented,
                    expected_extent: u64::from(self.vocabulary_extent),
                    expected_represented: self.entries.len() as u64,
                });
            }
        }
        Ok(())
    }

    /// Validate this mounted codebook together with its separately retained companion bytes,
    /// without taking or duplicating either owner.
    pub fn validate_with_codec(&self, artifact: &ExteriorCodecArtifact) -> Result<(), RestError> {
        self.validate()?;
        let descriptor = self
            .codec
            .as_ref()
            .ok_or_else(|| RestError::CodecDigestMismatch {
                kind: "tokenizer",
                expected: "descriptor present".into(),
                actual: "descriptor absent".into(),
            })?;
        validate_codec(&self.source, descriptor, artifact)
    }

    /// Mount the compact rest and authenticate the separately copied codec companions.
    pub fn mount_with_codec(
        wire: Self,
        artifact: ExteriorCodecArtifact,
    ) -> Result<Self, RestError> {
        let mounted = Self::mount(wire)?;
        let descriptor = mounted
            .codec
            .as_ref()
            .ok_or_else(|| RestError::CodecDigestMismatch {
                kind: "tokenizer",
                expected: "descriptor present".into(),
                actual: "descriptor absent".into(),
            })?;
        validate_codec(&mounted.source, descriptor, &artifact)?;
        Ok(mounted)
    }

    pub fn read_json(path: impl AsRef<Path>) -> Result<Self, RestError> {
        let bytes = std::fs::read(path).map_err(|error| RestError::Io(error.to_string()))?;
        let wire: Self =
            serde_json::from_slice(&bytes).map_err(|error| RestError::Json(error.to_string()))?;
        Self::mount(wire)
    }

    /// Recover a complete source codebook once, at the construction boundary. The closure is the
    /// caller's explicit source→native chart; this owner does not name or infer a tokenizer law.
    /// The returned rest owns every row and may be mounted after `path` is absent.
    pub fn recover_from_json<F>(
        path: impl AsRef<Path>,
        source: SourceAssetIdentity,
        native_surface: F,
        mut coverage: CoverageSummary,
        open: Vec<OpenFibre>,
    ) -> Result<Self, RestError>
    where
        F: Fn(&str) -> String,
    {
        let bytes = std::fs::read(path).map_err(|error| RestError::Io(error.to_string()))?;
        let value: serde_json::Value =
            serde_json::from_slice(&bytes).map_err(|error| RestError::Json(error.to_string()))?;
        let vocab = value
            .get("model")
            .and_then(|model| model.get("vocab"))
            .and_then(serde_json::Value::as_object)
            .ok_or_else(|| RestError::Json("model.vocab is absent".to_owned()))?;
        let mut rows = Vec::with_capacity(vocab.len());
        let mut extent = 0u32;
        for (piece, id) in vocab {
            let id = id.as_u64().ok_or_else(|| {
                RestError::Json(format!("vocab id for {piece} is not an integer"))
            })?;
            let id = u32::try_from(id)
                .map_err(|_| RestError::Json(format!("vocab id for {piece} exceeds u32")))?;
            extent = extent.max(id.saturating_add(1));
            rows.push(CodebookEntry {
                source_id: id,
                source_piece: piece.clone(),
                native_id: id,
                native_surface: native_surface(piece),
            });
        }
        rows.sort_by_key(|entry| entry.source_id);
        coverage.represented_token_ids = rows.len() as u32;
        Self::seal(source, extent, rows, coverage, open)
    }

    /// Recover the vocabulary and exact tokenizer companions at the construction boundary. The
    /// returned rest contains only content-addressed descriptors; callers retain the returned
    /// artifact and stream its bytes to companion files in the native rest.
    pub fn recover_from_json_with_codec<F>(
        path: impl AsRef<Path>,
        tokenizer_path: impl AsRef<Path>,
        tokenizer_config_path: Option<impl AsRef<Path>>,
        source: SourceAssetIdentity,
        native_surface: F,
        coverage: CoverageSummary,
        open: Vec<OpenFibre>,
    ) -> Result<(Self, ExteriorCodecArtifact), RestError>
    where
        F: Fn(&str) -> String,
    {
        let artifact = ExteriorCodecArtifact::from_paths(tokenizer_path, tokenizer_config_path)?;
        let rest = Self::recover_from_json(path, source, native_surface, coverage, open)?;
        let rest = Self::seal_with_codec_ref(
            rest.source,
            rest.vocabulary_extent,
            rest.entries,
            rest.coverage,
            rest.open,
            Some(&artifact),
        )?;
        Ok((rest, artifact))
    }

    /// Seal while borrowing the potentially large exterior codec artifact. The returned rest
    /// retains only its authenticated descriptor, so the caller remains the sole owner of the
    /// companion bytes it must write.
    pub fn seal_with_codec_ref(
        source: SourceAssetIdentity,
        vocabulary_extent: u32,
        entries: Vec<CodebookEntry>,
        coverage: CoverageSummary,
        open: Vec<OpenFibre>,
        codec: Option<&ExteriorCodecArtifact>,
    ) -> Result<Self, RestError> {
        let descriptor = codec.map(ExteriorCodecArtifact::descriptor);
        if let Some((artifact, descriptor)) = codec.zip(descriptor.as_ref()) {
            validate_codec(&source, descriptor, artifact)?;
        }
        let mut rest = Self::seal(source, vocabulary_extent, entries, coverage, open)?;
        rest.codec = descriptor;
        rest.codebook_sha256 = rest.digest();
        Ok(rest)
    }

    pub fn write_json(&self, path: impl AsRef<Path>) -> Result<(), RestError> {
        let bytes =
            serde_json::to_vec_pretty(self).map_err(|error| RestError::Json(error.to_string()))?;
        std::fs::write(path, bytes).map_err(|error| RestError::Io(error.to_string()))
    }

    /// Compact source-detached wire for the complete codebook. Metadata is one JSON line; each
    /// row carries JSON-escaped source/native faces so tabs and newlines in source pieces remain
    /// lossless. This is an exterior wire, not a runtime parser ontology.
    pub fn write_tsv(&self, path: impl AsRef<Path>) -> Result<(), RestError> {
        #[derive(Serialize)]
        struct CodebookMetadata<'a> {
            schema: &'a str,
            source: &'a SourceAssetIdentity,
            vocabulary_extent: u32,
            coverage: &'a CoverageSummary,
            open: &'a [OpenFibre],
            codec: &'a Option<ExteriorCodecDescriptor>,
            codebook_sha256: &'a str,
        }
        let metadata_wire = CodebookMetadata {
            schema: &self.schema,
            source: &self.source,
            vocabulary_extent: self.vocabulary_extent,
            coverage: &self.coverage,
            open: &self.open,
            codec: &self.codec,
            codebook_sha256: &self.codebook_sha256,
        };
        let metadata = serde_json::to_string(&metadata_wire)
            .map_err(|error| RestError::Json(error.to_string()))?;
        let mut text = String::with_capacity(self.entries.len() * 24);
        text.push_str("#meta ");
        text.push_str(&metadata);
        text.push('\n');
        text.push_str("source_id\tsource_piece\tnative_id\tnative_surface\n");
        for entry in &self.entries {
            let source = serde_json::to_string(&entry.source_piece)
                .map_err(|error| RestError::Json(error.to_string()))?;
            let native = serde_json::to_string(&entry.native_surface)
                .map_err(|error| RestError::Json(error.to_string()))?;
            text.push_str(&format!(
                "{}\t{}\t{}\t{}\n",
                entry.source_id, source, entry.native_id, native
            ));
        }
        std::fs::write(path, text).map_err(|error| RestError::Io(error.to_string()))
    }

    pub fn read_tsv(path: impl AsRef<Path>) -> Result<Self, RestError> {
        let text =
            std::fs::read_to_string(path).map_err(|error| RestError::Io(error.to_string()))?;
        let mut lines = text.lines();
        let metadata = lines
            .next()
            .ok_or_else(|| RestError::MalformedTsv("missing metadata".to_owned()))?;
        let metadata = metadata
            .strip_prefix("#meta ")
            .ok_or_else(|| RestError::MalformedTsv("metadata prefix".to_owned()))?;
        let wire: Self = serde_json::from_str(metadata)
            .map_err(|error| RestError::MalformedTsv(error.to_string()))?;
        let header = lines
            .next()
            .ok_or_else(|| RestError::MalformedTsv("missing header".to_owned()))?;
        if header != "source_id\tsource_piece\tnative_id\tnative_surface" {
            return Err(RestError::MalformedTsv("header".to_owned()));
        }
        let mut rows = Vec::with_capacity(wire.coverage.represented_token_ids as usize);
        for line in lines {
            let fields: Vec<&str> = line.split('\t').collect();
            if fields.len() != 4 {
                return Err(RestError::MalformedTsv(format!(
                    "row has {} fields",
                    fields.len()
                )));
            }
            let source_id = fields[0]
                .parse::<u32>()
                .map_err(|error| RestError::MalformedTsv(error.to_string()))?;
            let source_piece = serde_json::from_str(fields[1])
                .map_err(|error| RestError::MalformedTsv(error.to_string()))?;
            let native_id = fields[2]
                .parse::<u32>()
                .map_err(|error| RestError::MalformedTsv(error.to_string()))?;
            let native_surface = serde_json::from_str(fields[3])
                .map_err(|error| RestError::MalformedTsv(error.to_string()))?;
            rows.push(CodebookEntry {
                source_id,
                source_piece,
                native_id,
                native_surface,
            });
        }
        if rows.len() != wire.coverage.represented_token_ids as usize {
            return Err(RestError::MalformedTsv(format!(
                "metadata rows {} but wire rows {}",
                wire.coverage.represented_token_ids,
                rows.len()
            )));
        }
        Self::mount(Self {
            entries: rows,
            ..wire
        })
    }

    /// Native surface for a represented native address. Unknown addresses remain an open fibre.
    pub fn native_surface(&self, native_id: u32) -> Result<&str, RestError> {
        match self.read_native(native_id) {
            NativeRead::Surface(surface) => Ok(surface),
            NativeRead::Open {
                native_id, extent, ..
            } => Err(RestError::MissingNativeId {
                id: native_id,
                extent,
            }),
        }
    }

    pub fn read_native(&self, native_id: u32) -> NativeRead<'_> {
        self.native_index
            .binary_search_by_key(&native_id, |row| self.entries[*row as usize].native_id)
            .ok()
            .map(|index| &self.entries[self.native_index[index] as usize])
            .map_or(
                NativeRead::Open {
                    native_id,
                    extent: self.vocabulary_extent,
                    represented: self.entries.len() as u32,
                },
                |entry| NativeRead::Surface(entry.native_surface.as_str()),
            )
    }

    /// The source address corresponding to one native address, if this rest represents it.
    pub fn source_id(&self, native_id: u32) -> Option<u32> {
        self.native_index
            .binary_search_by_key(&native_id, |row| self.entries[*row as usize].native_id)
            .ok()
            .map(|index| &self.entries[self.native_index[index] as usize])
            .map(|entry| entry.source_id)
    }

    fn frame(hasher: &mut Sha256, bytes: &[u8]) {
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(bytes);
    }

    pub fn digest(&self) -> String {
        let mut hasher = Sha256::new();
        hasher.update(b"holonic-engine.phoenix.exterior-codebook-digest.v2");
        Self::frame(&mut hasher, self.source.model_sha256.as_bytes());
        Self::frame(&mut hasher, self.source.tokenizer_sha256.as_bytes());
        Self::frame(&mut hasher, self.source.tokenizer_config_sha256.as_bytes());
        Self::frame(&mut hasher, self.source.config_sha256.as_bytes());
        Self::frame(&mut hasher, self.source.model_content_sha256.as_bytes());
        hasher.update(self.vocabulary_extent.to_le_bytes());
        hasher.update(self.coverage.represented_token_ids.to_le_bytes());
        hasher.update((self.entries.len() as u64).to_le_bytes());
        for entry in &self.entries {
            hasher.update(entry.source_id.to_le_bytes());
            Self::frame(&mut hasher, entry.source_piece.as_bytes());
            hasher.update(entry.native_id.to_le_bytes());
            Self::frame(&mut hasher, entry.native_surface.as_bytes());
        }
        hasher.update((self.open.len() as u64).to_le_bytes());
        for fibre in &self.open {
            Self::frame(&mut hasher, fibre.axis.as_bytes());
            hasher.update(fibre.extent.to_le_bytes());
            hasher.update(fibre.represented.to_le_bytes());
            Self::frame(&mut hasher, fibre.reason.as_bytes());
        }
        match &self.codec {
            Some(codec) => {
                hasher.update([1]);
                Self::frame(&mut hasher, codec.tokenizer_json_sha256.as_bytes());
                hasher.update(codec.tokenizer_json_len.to_le_bytes());
                match (
                    &codec.tokenizer_config_sha256,
                    codec.tokenizer_config_json_len,
                ) {
                    (Some(digest), Some(length)) => {
                        hasher.update([1]);
                        Self::frame(&mut hasher, digest.as_bytes());
                        hasher.update(length.to_le_bytes());
                    }
                    (None, None) => hasher.update([0]),
                    _ => {
                        hasher.update([2]);
                    }
                }
            }
            None => hasher.update([0]),
        }
        format!("{:x}", hasher.finalize())
    }
}
