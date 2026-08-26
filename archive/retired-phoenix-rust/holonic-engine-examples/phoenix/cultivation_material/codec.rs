//! Recovered W3 codec paths over the authenticated W1 exterior companions.
//!
//! The tokenizer JSON and the pretokenized codebook-surface passage are two exterior routes. A
//! label cannot found a codec variant: the returned receipt carries both path identities and the
//! source/native address populations which made their equivalence (or defect) observable.

use holonic_engine::foreign_codec_rest::{ExteriorCodebookRest, ExteriorCodecArtifact};
use sha2::{Digest, Sha256};
use tokenizers::Tokenizer;

use super::admission::TokenizedMaterial;
use super::types::CodecPath;
use super::types::MaterialInput;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AddSpecialTokens {
    Disabled,
    #[cfg(test)]
    Enabled,
}

impl AddSpecialTokens {
    fn as_bool(self) -> bool {
        match self {
            Self::Disabled => false,
            #[cfg(test)]
            Self::Enabled => true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CodecPathPassage {
    pub path: CodecPath,
    pub identity: String,
    pub source_ids: Vec<u32>,
    pub native_ids: Vec<u32>,
    pub native_surfaces: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CodecEquivalenceReceipt {
    pub add_special_tokens: AddSpecialTokens,
    pub tokenizer: CodecPathPassage,
    pub pretokenized: CodecPathPassage,
    pub equivalent: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CodecPathRefusal {
    UnsupportedCodec(String),
    OpenSourceId(u32),
    NativeSurface { native_id: u32, reason: String },
}

impl std::fmt::Display for CodecPathRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedCodec(reason) => write!(f, "unsupported W1 exterior codec: {reason}"),
            Self::OpenSourceId(id) => write!(f, "source token {id} is open in W1 codebook"),
            Self::NativeSurface { native_id, reason } => {
                write!(f, "native surface {native_id} refused: {reason}")
            }
        }
    }
}

impl std::error::Error for CodecPathRefusal {}

/// Read and enact tokenizer.json directly from the detached artifact bytes.
pub fn tokenizer_json_path(
    codebook: &ExteriorCodebookRest,
    artifact: &ExteriorCodecArtifact,
    text: &str,
    add_special_tokens: AddSpecialTokens,
) -> Result<CodecPathPassage, CodecPathRefusal> {
    let tokenizer = Tokenizer::from_bytes(&artifact.tokenizer_json)
        .map_err(|error| CodecPathRefusal::UnsupportedCodec(error.to_string()))?;
    let encoding = tokenizer
        .encode(text, add_special_tokens.as_bool())
        .map_err(|error| CodecPathRefusal::UnsupportedCodec(error.to_string()))?;
    let descriptor = artifact.descriptor();
    let companion_identity = format!(
        "{}:{}",
        descriptor.tokenizer_json_sha256,
        descriptor
            .tokenizer_config_sha256
            .as_deref()
            .unwrap_or("absent")
    );
    passage(
        codebook,
        CodecPath::TokenizerJson,
        &encoding.get_ids(),
        &companion_identity,
        add_special_tokens,
    )
}

/// Enact the pretokenized route through W1's codebook surfaces. The source IDs remain source
/// addresses until this owner explicitly crosses them with `native_id`.
pub fn pretokenized_codebook_surface_path(
    codebook: &ExteriorCodebookRest,
    source_ids: &[u32],
    add_special_tokens: AddSpecialTokens,
) -> Result<CodecPathPassage, CodecPathRefusal> {
    passage(
        codebook,
        CodecPath::PretokenizedCodebookSurface,
        source_ids,
        "codebook-surface",
        add_special_tokens,
    )
}

/// Found a W3 codec variant only when both exterior routes are enacted and returned together.
pub fn recover_codec_paths(
    codebook: &ExteriorCodebookRest,
    artifact: &ExteriorCodecArtifact,
    text: &str,
    pretokenized_source_ids: &[u32],
    add_special_tokens: AddSpecialTokens,
) -> Result<CodecEquivalenceReceipt, CodecPathRefusal> {
    let tokenizer = tokenizer_json_path(codebook, artifact, text, add_special_tokens)?;
    let pretokenized =
        pretokenized_codebook_surface_path(codebook, pretokenized_source_ids, add_special_tokens)?;
    let equivalent = tokenizer.source_ids == pretokenized.source_ids
        && tokenizer.native_ids == pretokenized.native_ids;
    Ok(CodecEquivalenceReceipt {
        add_special_tokens,
        tokenizer,
        pretokenized,
        equivalent,
    })
}

/// Turn a successful two-path return into the material passage consumed by W3 admission.  The
/// path identities, rather than a caller label, become the codec lineage field.
pub fn tokenized_codec_variant<'a>(
    input: MaterialInput<'a>,
    receipt: &CodecEquivalenceReceipt,
) -> Result<TokenizedMaterial<'a>, CodecPathRefusal> {
    if !receipt.equivalent {
        return Err(CodecPathRefusal::UnsupportedCodec(
            "tokenizer and pretokenized paths are not equivalent".to_owned(),
        ));
    }
    let codec_variant = format!(
        "w3-paths:{}:{}",
        receipt.tokenizer.identity, receipt.pretokenized.identity
    );
    Ok(TokenizedMaterial {
        input,
        token_ids: receipt.tokenizer.native_ids.clone(),
        codec_variant,
    })
}

fn passage(
    codebook: &ExteriorCodebookRest,
    path: CodecPath,
    source_ids: &[u32],
    companion_identity: &str,
    add_special_tokens: AddSpecialTokens,
) -> Result<CodecPathPassage, CodecPathRefusal> {
    let native_ids = source_ids
        .iter()
        .map(|source_id| {
            codebook
                .native_id(*source_id)
                .map_err(|_| CodecPathRefusal::OpenSourceId(*source_id))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let native_surfaces = native_ids
        .iter()
        .map(|native_id| {
            codebook
                .native_surface(*native_id)
                .map(str::to_owned)
                .map_err(|error| CodecPathRefusal::NativeSurface {
                    native_id: *native_id,
                    reason: error.to_string(),
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let identity = path_identity(
        path,
        companion_identity,
        add_special_tokens,
        source_ids,
        &native_ids,
    );
    Ok(CodecPathPassage {
        path,
        identity,
        source_ids: source_ids.to_vec(),
        native_ids,
        native_surfaces,
    })
}

fn path_identity(
    path: CodecPath,
    companion_identity: &str,
    add_special_tokens: AddSpecialTokens,
    source_ids: &[u32],
    native_ids: &[u32],
) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"holonic-engine.phoenix.w3-codec-path.v1");
    hasher.update([match path {
        CodecPath::TokenizerJson => 0,
        CodecPath::PretokenizedCodebookSurface => 1,
    }]);
    hasher.update([add_special_tokens.as_bool() as u8]);
    frame(&mut hasher, companion_identity.as_bytes());
    hasher.update((source_ids.len() as u64).to_le_bytes());
    for id in source_ids {
        hasher.update(id.to_le_bytes());
    }
    hasher.update((native_ids.len() as u64).to_le_bytes());
    for id in native_ids {
        hasher.update(id.to_le_bytes());
    }
    format!("{:x}", hasher.finalize())
}

fn frame(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}
