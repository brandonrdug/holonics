//! Text application faces over the neutral recurrent operator.
//!
//! Tokenization, source tensor names, vocabulary scoring, and rendered text remain here. The native
//! operation receives carrier populations and returns interval emissions without knowing this codec.

use std::{fs::File, path::Path};

use holonic_engine::{
    embedding_fiber::{AlignedMaterial, MountedReadout, ResidentReadout, ScorePopulation},
    foreign_map::{ForeignContainer, ForeignMapError, manifest_safetensors},
    native_ecology::holonic_intelligence::{NativeFullOperationEmission, NativeOperatorEmission},
};
use serde::Serialize;
use thiserror::Error;
use tokenizers::Tokenizer;

pub struct AthenaTextOccurrenceApplication {
    tokenizer: Tokenizer,
    file: File,
    container: ForeignContainer,
    layer: usize,
    carrier_extent: usize,
    interaction_extent: usize,
}

/// Codec-only application for the complete native recurrence. It opens no coefficient container
/// and supplies only exterior text occurrences and rendered token faces.
pub struct AthenaTokenApplication {
    tokenizer: Tokenizer,
}

pub struct AthenaVocabularyFace<'chart> {
    mounted: MountedReadout<'chart>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AthenaRenderedTokenFace {
    pub selected: u32,
    pub equal_score_population: Vec<u32>,
    pub rendered: String,
    pub collapsed_interval_population: usize,
    pub score_population: usize,
    pub exact_multiply_accumulates: u64,
}

#[derive(Debug, Error)]
pub enum AthenaRecurrentApplicationError {
    #[error("tokenizer: {0}")]
    Tokenizer(String),
    #[error(transparent)]
    Foreign(#[from] ForeignMapError),
    #[error("the application occurrence has the wrong shape")]
    Shape,
    #[error("the emitted interval face is malformed")]
    Emission,
    #[error("resident vocabulary readout: {0}")]
    Resident(String),
}

impl AthenaTextOccurrenceApplication {
    pub fn open(
        root: &Path,
        layer: usize,
        carrier_extent: usize,
        interaction_extent: usize,
    ) -> Result<Self, AthenaRecurrentApplicationError> {
        let tokenizer = Tokenizer::from_file(root.join("tokenizer.json"))
            .map_err(|error| AthenaRecurrentApplicationError::Tokenizer(error.to_string()))?;
        let model = root.join("model.safetensors");
        let (file, container) = manifest_safetensors(
            model
                .to_str()
                .ok_or(AthenaRecurrentApplicationError::Shape)?,
        )?;
        Ok(Self {
            tokenizer,
            file,
            container,
            layer,
            carrier_extent,
            interaction_extent,
        })
    }

    pub fn encode(&self, material: &str) -> Result<Vec<u32>, AthenaRecurrentApplicationError> {
        self.tokenizer
            .encode(material, true)
            .map(|encoding| encoding.get_ids().to_vec())
            .map_err(|error| AthenaRecurrentApplicationError::Tokenizer(error.to_string()))
    }

    pub fn occurrence_carriers(
        &mut self,
        token: u32,
    ) -> Result<(Vec<u16>, Vec<u16>), AthenaRecurrentApplicationError> {
        let (carrier, width) = self.container.read_rows_bf16(
            &mut self.file,
            "model.language_model.embed_tokens.weight",
            token as usize,
            1,
        )?;
        if width != self.carrier_extent {
            return Err(AthenaRecurrentApplicationError::Shape);
        }
        let (per_layer, packed_width) = self.container.read_rows_bf16(
            &mut self.file,
            "model.language_model.embed_tokens_per_layer.weight",
            token as usize,
            1,
        )?;
        let from = self
            .layer
            .checked_mul(self.interaction_extent)
            .ok_or(AthenaRecurrentApplicationError::Shape)?;
        let to = from
            .checked_add(self.interaction_extent)
            .ok_or(AthenaRecurrentApplicationError::Shape)?;
        if to > packed_width || per_layer.len() != packed_width {
            return Err(AthenaRecurrentApplicationError::Shape);
        }
        Ok((carrier, per_layer[from..to].to_vec()))
    }

    pub fn mount_vocabulary<'chart>(
        &mut self,
        readout: &'chart ResidentReadout,
    ) -> Result<AthenaVocabularyFace<'chart>, AthenaRecurrentApplicationError> {
        let words = self
            .container
            .read_bf16_whole(&mut self.file, "model.language_model.embed_tokens.weight")?;
        let mounted = readout
            .mount_bfloat16(&words, self.carrier_extent)
            .map_err(|error| AthenaRecurrentApplicationError::Resident(error.to_string()))?;
        Ok(AthenaVocabularyFace { mounted })
    }

    pub fn render_token(
        &self,
        vocabulary: &AthenaVocabularyFace<'_>,
        emission: &NativeOperatorEmission,
    ) -> Result<AthenaRenderedTokenFace, AthenaRecurrentApplicationError> {
        if emission.rows != 1
            || emission.width != self.carrier_extent
            || emission.intervals.len() != self.carrier_extent
        {
            return Err(AthenaRecurrentApplicationError::Emission);
        }
        let mut collapsed = 0usize;
        let entries = emission
            .intervals
            .iter()
            .map(|(lower, upper)| {
                if lower != upper {
                    collapsed += 1;
                }
                let midpoint = i128::from(*lower) + (i128::from(*upper) - i128::from(*lower)) / 2;
                i64::try_from(midpoint).map_err(|_| AthenaRecurrentApplicationError::Emission)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let entry_octaves = entries
            .iter()
            .map(|entry| 64 - entry.unsigned_abs().max(1).leading_zeros())
            .max()
            .unwrap_or(1);
        let query = AlignedMaterial {
            negatives: entries.iter().filter(|entry| **entry < 0).count() as u64,
            entries,
            exponent: -(emission.grain as i32),
            entry_octaves,
        };
        let scores = vocabulary
            .mounted
            .score(&query, None)
            .map_err(|error| AthenaRecurrentApplicationError::Resident(error.to_string()))?;
        let (selected, equal) = greatest(&scores)?;
        let rendered = self
            .tokenizer
            .decode(&[selected], false)
            .map_err(|error| AthenaRecurrentApplicationError::Tokenizer(error.to_string()))?;
        Ok(AthenaRenderedTokenFace {
            selected,
            equal_score_population: equal,
            rendered,
            collapsed_interval_population: collapsed,
            score_population: scores.scores.len(),
            exact_multiply_accumulates: scores.exact_multiply_accumulates,
        })
    }

    /// Select and render one application token from the complete native vocabulary emission. The
    /// engine has already enacted the tied boundary and soft-cap reaction; this application adds no
    /// matrix, candidate family, or source lookup.
    pub fn render_full_emission(
        &self,
        emission: &NativeFullOperationEmission,
    ) -> Result<AthenaRenderedTokenFace, AthenaRecurrentApplicationError> {
        render_complete_emission(&self.tokenizer, emission)
    }
}

impl AthenaTokenApplication {
    pub fn open(root: &Path) -> Result<Self, AthenaRecurrentApplicationError> {
        let tokenizer = Tokenizer::from_file(root.join("tokenizer.json"))
            .map_err(|error| AthenaRecurrentApplicationError::Tokenizer(error.to_string()))?;
        Ok(Self { tokenizer })
    }

    pub fn encode(&self, material: &str) -> Result<Vec<u32>, AthenaRecurrentApplicationError> {
        self.tokenizer
            .encode(material, true)
            .map(|encoding| encoding.get_ids().to_vec())
            .map_err(|error| AthenaRecurrentApplicationError::Tokenizer(error.to_string()))
    }

    pub fn render(
        &self,
        emission: &NativeFullOperationEmission,
    ) -> Result<AthenaRenderedTokenFace, AthenaRecurrentApplicationError> {
        render_complete_emission(&self.tokenizer, emission)
    }
}

fn render_complete_emission(
    tokenizer: &Tokenizer,
    emission: &NativeFullOperationEmission,
) -> Result<AthenaRenderedTokenFace, AthenaRecurrentApplicationError> {
    let vocabulary = tokenizer.get_vocab_size(true);
    if emission.rows == 0
        || emission.width != vocabulary
        || emission.intervals.len() != emission.rows.saturating_mul(vocabulary)
    {
        return Err(AthenaRecurrentApplicationError::Emission);
    }
    let from = (emission.rows - 1) * vocabulary;
    let mut collapsed = 0usize;
    let values = emission
        .intervals
        .iter()
        .skip(from)
        .map(|(lower, upper)| {
            if lower != upper {
                collapsed += 1;
            }
            i128::from(*lower) + (i128::from(*upper) - i128::from(*lower)) / 2
        })
        .collect::<Vec<_>>();
    let greatest = values
        .iter()
        .copied()
        .max()
        .ok_or(AthenaRecurrentApplicationError::Emission)?;
    let equal = values
        .iter()
        .enumerate()
        .filter_map(|(at, value)| (*value == greatest).then_some(at as u32))
        .collect::<Vec<_>>();
    let selected = *equal
        .first()
        .ok_or(AthenaRecurrentApplicationError::Emission)?;
    let rendered = tokenizer
        .decode(&[selected], false)
        .map_err(|error| AthenaRecurrentApplicationError::Tokenizer(error.to_string()))?;
    Ok(AthenaRenderedTokenFace {
        selected,
        equal_score_population: equal,
        rendered,
        collapsed_interval_population: collapsed,
        score_population: values.len(),
        exact_multiply_accumulates: 0,
    })
}

fn greatest(scores: &ScorePopulation) -> Result<(u32, Vec<u32>), AthenaRecurrentApplicationError> {
    let greatest = scores
        .scores
        .iter()
        .copied()
        .max()
        .ok_or(AthenaRecurrentApplicationError::Emission)?;
    let equal = scores
        .scores
        .iter()
        .enumerate()
        .filter_map(|(at, score)| (*score == greatest).then_some(at as u32))
        .collect::<Vec<_>>();
    Ok((equal[0], equal))
}
