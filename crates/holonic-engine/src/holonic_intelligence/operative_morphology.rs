//! Source-neutral operable morphology returned from actual inherited coefficient populations.
//!
//! The hot body owns generic shaped dyadic cross-sections and an ordered local operation. Foreign
//! tensor names, container paths, and digests remain in the cold witness. Recorded activation pairs
//! do not define states, generators, or receiver observations here.

use std::{fs, path::Path};

use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    exact_json,
    exact_value::ieee754::{decode_bfloat16_bits, round_into_bfloat16},
    foreign_map::{ForeignMapError, ForeignTensor, manifest_safetensors},
    resident_law::decimal_to_rat,
};

pub const NATIVE_OPERATOR_MORPHOLOGY_SCHEMA: &str = "holonic-engine.native-operator-morphology.v1";

/// One source-neutral exact dyadic coefficient `significand * 2^exponent`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeDyadicCoefficient {
    pub significand: i16,
    pub exponent: i16,
}

impl NativeDyadicCoefficient {
    pub fn from_bfloat16(word: u16) -> Result<Self, NativeOperatorMorphologyError> {
        let datum = decode_bfloat16_bits(word)
            .map_err(|_| NativeOperatorMorphologyError::NonfiniteCoefficient)?;
        let magnitude = datum
            .significand
            .to_i16()
            .ok_or(NativeOperatorMorphologyError::CoefficientOutsideNativeDyadic)?;
        let significand = if datum.negative {
            -magnitude
        } else {
            magnitude
        };
        let exponent = i16::try_from(datum.ulp_exponent)
            .map_err(|_| NativeOperatorMorphologyError::CoefficientOutsideNativeDyadic)?;
        Ok(Self {
            significand,
            exponent,
        })
    }

    pub fn value(self) -> Rat {
        if self.exponent >= 0 {
            Rat::from_integer(
                BigInt::from(self.significand) << usize::from(self.exponent.unsigned_abs()),
            )
        } else {
            Rat::new(
                BigInt::from(self.significand),
                BigInt::from(1u8) << usize::from(self.exponent.unsigned_abs()),
            )
        }
    }

    pub fn validate(self) -> Result<(), NativeOperatorMorphologyError> {
        if !(-133..=120).contains(&self.exponent) || self.significand.unsigned_abs() > 255 {
            return Err(NativeOperatorMorphologyError::CoefficientOutsideNativeDyadic);
        }
        Ok(())
    }

    pub fn bfloat16_word(self) -> Result<u16, NativeOperatorMorphologyError> {
        let (word, residual) = round_into_bfloat16(&self.value())
            .map_err(|_| NativeOperatorMorphologyError::CoefficientOutsideNativeDyadic)?;
        if !residual.is_zero() {
            return Err(NativeOperatorMorphologyError::CoefficientOutsideNativeDyadic);
        }
        Ok(word)
    }
}

/// One shaped constitutive cross-section. Its address is native and carries no source tensor name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeDyadicMatrix {
    pub address: String,
    pub rows: usize,
    pub columns: usize,
    pub coefficients: Vec<NativeDyadicCoefficient>,
}

impl NativeDyadicMatrix {
    fn from_bfloat16(
        address: impl Into<String>,
        tensor: &ForeignTensor,
        words: Vec<u16>,
    ) -> Result<Self, NativeOperatorMorphologyError> {
        if tensor.shape.len() != 2 || words.len() != tensor.shape[0].saturating_mul(tensor.shape[1])
        {
            return Err(NativeOperatorMorphologyError::Shape);
        }
        let matrix = Self {
            address: address.into(),
            rows: tensor.shape[0],
            columns: tensor.shape[1],
            coefficients: words
                .into_iter()
                .map(NativeDyadicCoefficient::from_bfloat16)
                .collect::<Result<_, _>>()?,
        };
        matrix.validate()?;
        Ok(matrix)
    }

    pub fn validate(&self) -> Result<(), NativeOperatorMorphologyError> {
        if self.address.is_empty()
            || self.rows == 0
            || self.columns == 0
            || self.coefficients.len() != self.rows.saturating_mul(self.columns)
        {
            return Err(NativeOperatorMorphologyError::Shape);
        }
        self.coefficients
            .iter()
            .try_for_each(|value| value.validate())
    }

    /// Serial exact receiver used only as parity testimony beside the resident operation.
    pub fn apply_exact(&self, carrier: &[Rat]) -> Result<Vec<Rat>, NativeOperatorMorphologyError> {
        self.validate()?;
        if carrier.len() != self.columns {
            return Err(NativeOperatorMorphologyError::Carrier);
        }
        Ok(self
            .coefficients
            .chunks_exact(self.columns)
            .map(|row| {
                row.iter().zip(carrier).fold(
                    Rat::from_integer(BigInt::from(0)),
                    |sum, (coefficient, value)| sum + coefficient.value() * value,
                )
            })
            .collect())
    }

    pub fn bfloat16_words(&self) -> Result<Vec<u16>, NativeOperatorMorphologyError> {
        self.coefficients
            .iter()
            .copied()
            .map(NativeDyadicCoefficient::bfloat16_word)
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeOperatorKind {
    Contract {
        matrix: String,
    },
    GeluTanh,
    HadamardOccurrence,
    RmsNorm {
        gain_population: usize,
        epsilon: Rat,
    },
    Reentry,
}

/// One actual source-neutral operator complex for the per-operation carrier.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOperatorMorphology {
    pub schema: String,
    pub carrier_extent: usize,
    pub interaction_extent: usize,
    pub matrices: Vec<NativeDyadicMatrix>,
    pub norm_gain: Vec<NativeDyadicCoefficient>,
    pub operations: Vec<NativeOperatorKind>,
    pub open_exterior: Vec<String>,
}

impl NativeOperatorMorphology {
    pub fn validate(&self) -> Result<(), NativeOperatorMorphologyError> {
        let epsilon = match self.operations.get(4) {
            Some(NativeOperatorKind::RmsNorm { epsilon, .. }) => epsilon.clone(),
            _ => return Err(NativeOperatorMorphologyError::Malformed),
        };
        if self.schema != NATIVE_OPERATOR_MORPHOLOGY_SCHEMA
            || self.carrier_extent == 0
            || self.interaction_extent == 0
            || self.matrices.len() != 2
            || self.matrices[0].address != "operator/input-cross-section"
            || self.matrices[0].rows != self.interaction_extent
            || self.matrices[0].columns != self.carrier_extent
            || self.matrices[1].address != "operator/output-cross-section"
            || self.matrices[1].rows != self.carrier_extent
            || self.matrices[1].columns != self.interaction_extent
            || self.norm_gain.len() != self.carrier_extent
            || self.operations
                != vec![
                    NativeOperatorKind::Contract {
                        matrix: "operator/input-cross-section".to_owned(),
                    },
                    NativeOperatorKind::GeluTanh,
                    NativeOperatorKind::HadamardOccurrence,
                    NativeOperatorKind::Contract {
                        matrix: "operator/output-cross-section".to_owned(),
                    },
                    NativeOperatorKind::RmsNorm {
                        gain_population: self.carrier_extent,
                        epsilon,
                    },
                    NativeOperatorKind::Reentry,
                ]
            || self.open_exterior.iter().any(String::is_empty)
        {
            return Err(NativeOperatorMorphologyError::Malformed);
        }
        self.matrices
            .iter()
            .try_for_each(NativeDyadicMatrix::validate)?;
        self.norm_gain.iter().try_for_each(|value| value.validate())
    }

    pub fn epsilon(&self) -> &Rat {
        match self.operations.get(4) {
            Some(NativeOperatorKind::RmsNorm { epsilon, .. }) => epsilon,
            _ => panic!("unvalidated morphology has no RMS reaction"),
        }
    }
}

/// Source-specific ancestry physically separate from the operable morphology.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOperatorColdWitness {
    pub source_container: String,
    pub source_layer: usize,
    pub input_matrix: String,
    pub input_sha256: String,
    pub output_matrix: String,
    pub output_sha256: String,
    pub norm_gain: String,
    pub norm_gain_sha256: String,
    pub source_activation: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOperatorInsufficiency {
    pub admitted_operation: String,
    pub omitted_source_operation_count: usize,
    pub open: Vec<String>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct NativeOperatorDismantlingReturn {
    pub native: NativeOperatorMorphology,
    pub exterior: NativeOperatorColdWitness,
    pub insufficiency: NativeOperatorInsufficiency,
}

#[derive(Debug, Error)]
pub enum NativeOperatorMorphologyError {
    #[error("foreign container: {0}")]
    Foreign(#[from] ForeignMapError),
    #[error("the source configuration is missing the required exact operation field")]
    Configuration,
    #[error("the source coefficient is not finite")]
    NonfiniteCoefficient,
    #[error("the source coefficient does not fit the native dyadic carrier")]
    CoefficientOutsideNativeDyadic,
    #[error("the operator population has the wrong shape")]
    Shape,
    #[error("the presented carrier has the wrong extent")]
    Carrier,
    #[error("the native operator morphology is malformed")]
    Malformed,
    #[error("source I/O: {0}")]
    Io(String),
}

/// Dismantle one actual inherited per-layer interaction branch into generic native operations.
pub fn dismantle_native_operator(
    root: &Path,
    layer: usize,
) -> Result<NativeOperatorDismantlingReturn, NativeOperatorMorphologyError> {
    let container_path = root.join("model.safetensors");
    let (mut file, container) = manifest_safetensors(
        container_path
            .to_str()
            .ok_or_else(|| NativeOperatorMorphologyError::Io("non-text path".to_owned()))?,
    )?;
    let input_name = format!("model.language_model.layers.{layer}.per_layer_input_gate.weight");
    let output_name = format!("model.language_model.layers.{layer}.per_layer_projection.weight");
    let norm_name = format!("model.language_model.layers.{layer}.post_per_layer_input_norm.weight");
    let input_tensor = container.tensor(&input_name)?.clone();
    let output_tensor = container.tensor(&output_name)?.clone();
    let norm_tensor = container.tensor(&norm_name)?.clone();
    let input_words = container.read_bf16_whole(&mut file, &input_name)?;
    let output_words = container.read_bf16_whole(&mut file, &output_name)?;
    let norm_words = container.read_bf16_whole(&mut file, &norm_name)?;
    if norm_tensor.shape != vec![input_tensor.shape.get(1).copied().unwrap_or(0)] {
        return Err(NativeOperatorMorphologyError::Shape);
    }

    let configuration = fs::read_to_string(root.join("config.json"))
        .map_err(|error| NativeOperatorMorphologyError::Io(error.to_string()))?;
    let text = exact_json::field(&configuration, "text_config")
        .ok_or(NativeOperatorMorphologyError::Configuration)?;
    let activation = exact_json::field(text, "hidden_activation")
        .and_then(exact_json::as_string)
        .ok_or(NativeOperatorMorphologyError::Configuration)?;
    if activation != "gelu_pytorch_tanh" {
        return Err(NativeOperatorMorphologyError::Configuration);
    }
    let epsilon_text = exact_json::field(text, "rms_norm_eps")
        .ok_or(NativeOperatorMorphologyError::Configuration)?;
    let epsilon =
        decimal_to_rat(epsilon_text).ok_or(NativeOperatorMorphologyError::Configuration)?;
    if epsilon <= Rat::from_integer(BigInt::from(0)) {
        return Err(NativeOperatorMorphologyError::Configuration);
    }

    let carrier_extent = input_tensor.shape[1];
    let interaction_extent = input_tensor.shape[0];
    if output_tensor.shape != vec![carrier_extent, interaction_extent] {
        return Err(NativeOperatorMorphologyError::Shape);
    }
    let operations = vec![
        NativeOperatorKind::Contract {
            matrix: "operator/input-cross-section".to_owned(),
        },
        NativeOperatorKind::GeluTanh,
        NativeOperatorKind::HadamardOccurrence,
        NativeOperatorKind::Contract {
            matrix: "operator/output-cross-section".to_owned(),
        },
        NativeOperatorKind::RmsNorm {
            gain_population: carrier_extent,
            epsilon,
        },
        NativeOperatorKind::Reentry,
    ];
    let native = NativeOperatorMorphology {
        schema: NATIVE_OPERATOR_MORPHOLOGY_SCHEMA.to_owned(),
        carrier_extent,
        interaction_extent,
        matrices: vec![
            NativeDyadicMatrix::from_bfloat16(
                "operator/input-cross-section",
                &input_tensor,
                input_words.clone(),
            )?,
            NativeDyadicMatrix::from_bfloat16(
                "operator/output-cross-section",
                &output_tensor,
                output_words.clone(),
            )?,
        ],
        norm_gain: norm_words
            .iter()
            .copied()
            .map(NativeDyadicCoefficient::from_bfloat16)
            .collect::<Result<_, _>>()?,
        operations,
        open_exterior: vec![
            "attention, feed-forward, remaining layers, final rebase, and emission remain open"
                .to_owned(),
        ],
    };
    native.validate()?;
    Ok(NativeOperatorDismantlingReturn {
        native,
        exterior: NativeOperatorColdWitness {
            source_container: container_path.display().to_string(),
            source_layer: layer,
            input_matrix: input_name,
            input_sha256: words_sha256(&input_words),
            output_matrix: output_name,
            output_sha256: words_sha256(&output_words),
            norm_gain: norm_name,
            norm_gain_sha256: words_sha256(&norm_words),
            source_activation: activation,
        },
        insufficiency: NativeOperatorInsufficiency {
            admitted_operation: "per-layer-interaction-branch".to_owned(),
            omitted_source_operation_count: container.tensors.len().saturating_sub(3),
            open: vec!["the remaining inherited operator complex has not crossed".to_owned()],
        },
    })
}

fn words_sha256(words: &[u16]) -> String {
    let mut digest = Sha256::new();
    for word in words {
        digest.update(word.to_le_bytes());
    }
    format!("{:x}", digest.finalize())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_dyadic_roundtrip_retains_exact_values() {
        for word in [0x0000, 0x3f80, 0xbf40, 0x0001, 0x7f7f] {
            let native = NativeDyadicCoefficient::from_bfloat16(word).expect("finite");
            assert_eq!(
                native.value(),
                decode_bfloat16_bits(word).expect("source").value()
            );
            native.validate().expect("valid");
        }
        assert!(NativeDyadicCoefficient::from_bfloat16(0x7f80).is_err());
    }

    #[test]
    fn generic_matrix_applies_the_actual_dyadic_coefficients() {
        let tensor = ForeignTensor {
            name: "cold/name".to_owned(),
            dtype: crate::foreign_map::ForeignDtype::Bf16,
            shape: vec![2, 2],
            start: 0,
            end: 8,
        };
        let matrix = NativeDyadicMatrix::from_bfloat16(
            "operator/test",
            &tensor,
            vec![0x3f80, 0x4000, 0xbf80, 0x3f00],
        )
        .expect("matrix");
        let result = matrix
            .apply_exact(&[
                Rat::from_integer(BigInt::from(3)),
                Rat::from_integer(BigInt::from(4)),
            ])
            .expect("apply");
        assert_eq!(
            result,
            vec![Rat::from_integer(11.into()), Rat::from_integer((-1).into())]
        );
        assert!(
            !serde_json::to_vec(&matrix)
                .expect("wire")
                .windows(b"cold/name".len())
                .any(|window| window == b"cold/name")
        );
    }
}
