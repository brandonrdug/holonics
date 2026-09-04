//! Exact and projected exterior export lenses for native morphology artifacts.

mod onnx;
mod safetensors;

use std::collections::BTreeSet;

use holonic_engine::receiver_exact_compression::{Observation, ReceiverId};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::{
    ConfigurationEvaluationReceipt, ExportCodecKind, InferenceConfigurationAddress,
    MorphologyArtifactError, NativeMorphologyArtifact,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExportPurpose {
    RestedInference,
    Cultivation,
    WorldReturn,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MorphologyExportRequest {
    pub codec: ExportCodecKind,
    pub receiver_family: BTreeSet<ReceiverId>,
    pub purpose: ExportPurpose,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MorphologyExportArtifact {
    pub codec: ExportCodecKind,
    pub media_type: String,
    pub schema_or_opset: String,
    pub bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExactMorphologyExport {
    pub artifact: MorphologyExportArtifact,
    pub receiver_family: BTreeSet<ReceiverId>,
    pub complete_package_round_trip: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConfigurationSeparator {
    pub configuration: InferenceConfigurationAddress,
    pub left_observations: Vec<Observation>,
    pub right_observations: Vec<Observation>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProjectedMorphologyExport {
    pub artifact: MorphologyExportArtifact,
    pub collapsed_package_fibre: Vec<Vec<u8>>,
    pub separator: ConfigurationSeparator,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum MorphologyExportRefusal {
    ReceiverOutsidePackage,
    CultivationIsNotRestedInference,
    WorldReturnIsNotRestedInference,
    NativeAnatomyDoesNotCollapse,
    NoConfigurationSeparator,
    ValueOutsideCodec,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "disposition", rename_all = "kebab-case")]
pub enum MorphologyExportReturn {
    Exact(ExactMorphologyExport),
    Projected(ProjectedMorphologyExport),
    Refused(MorphologyExportRefusal),
}

#[derive(Debug, Error)]
pub enum MorphologyExportError {
    #[error("the morphology artifact refused export: {0}")]
    Package(#[from] MorphologyArtifactError),
    #[error("the exterior export wire is malformed: {0}")]
    Wire(String),
}

pub fn export_morphology(
    package: &NativeMorphologyArtifact,
    request: MorphologyExportRequest,
) -> Result<MorphologyExportReturn, MorphologyExportError> {
    package.validate()?;
    if request.receiver_family.is_empty()
        || !request
            .receiver_family
            .is_subset(&package.manifest.receiver_capability.native_receiver_family)
    {
        return Ok(MorphologyExportReturn::Refused(
            MorphologyExportRefusal::ReceiverOutsidePackage,
        ));
    }
    match request.purpose {
        ExportPurpose::Cultivation => {
            return Ok(MorphologyExportReturn::Refused(
                MorphologyExportRefusal::CultivationIsNotRestedInference,
            ));
        }
        ExportPurpose::WorldReturn => {
            return Ok(MorphologyExportReturn::Refused(
                MorphologyExportRefusal::WorldReturnIsNotRestedInference,
            ));
        }
        ExportPurpose::RestedInference => {}
    }
    let artifact = match request.codec {
        ExportCodecKind::Safetensors => safetensors::exact(package)?,
        ExportCodecKind::Onnx => onnx::exact(package)?,
    };
    let imported = import_exact_export(&artifact)?;
    let complete_package_round_trip = imported.canonical_bytes()? == package.canonical_bytes()?;
    if !complete_package_round_trip {
        return Err(MorphologyExportError::Wire(
            "the alleged exact export did not recover its package".to_owned(),
        ));
    }
    Ok(MorphologyExportReturn::Exact(ExactMorphologyExport {
        artifact,
        receiver_family: request.receiver_family,
        complete_package_round_trip,
    }))
}

pub fn import_exact_export(
    artifact: &MorphologyExportArtifact,
) -> Result<NativeMorphologyArtifact, MorphologyExportError> {
    match artifact.codec {
        ExportCodecKind::Safetensors => safetensors::import_exact(artifact),
        ExportCodecKind::Onnx => onnx::import_exact(artifact),
    }
}

/// Export the common anatomy of two variants while retaining the complete collapsed package fibre
/// and the first configuration which distinguishes their receiver consequences.
pub fn project_common_anatomy(
    left: &NativeMorphologyArtifact,
    right: &NativeMorphologyArtifact,
    codec: ExportCodecKind,
) -> Result<MorphologyExportReturn, MorphologyExportError> {
    left.validate()?;
    right.validate()?;
    if left.manifest.anatomy != right.manifest.anatomy {
        return Ok(MorphologyExportReturn::Refused(
            MorphologyExportRefusal::NativeAnatomyDoesNotCollapse,
        ));
    }
    let Some(separator) = first_separator(&left.evaluation, &right.evaluation) else {
        return Ok(MorphologyExportReturn::Refused(
            MorphologyExportRefusal::NoConfigurationSeparator,
        ));
    };
    let left_artifact = match codec {
        ExportCodecKind::Safetensors => safetensors::anatomy(left)?,
        ExportCodecKind::Onnx => onnx::anatomy(left)?,
    };
    let right_artifact = match codec {
        ExportCodecKind::Safetensors => safetensors::anatomy(right)?,
        ExportCodecKind::Onnx => onnx::anatomy(right)?,
    };
    if left_artifact != right_artifact {
        return Ok(MorphologyExportReturn::Refused(
            MorphologyExportRefusal::NativeAnatomyDoesNotCollapse,
        ));
    }
    Ok(MorphologyExportReturn::Projected(
        ProjectedMorphologyExport {
            artifact: left_artifact,
            collapsed_package_fibre: vec![left.canonical_bytes()?, right.canonical_bytes()?],
            separator,
        },
    ))
}

fn first_separator(
    left: &[ConfigurationEvaluationReceipt],
    right: &[ConfigurationEvaluationReceipt],
) -> Option<ConfigurationSeparator> {
    left.iter().find_map(|left| {
        right
            .iter()
            .find(|right| {
                right.configuration == left.configuration && right.observations != left.observations
            })
            .map(|right| ConfigurationSeparator {
                configuration: left.configuration.clone(),
                left_observations: left.observations.clone(),
                right_observations: right.observations.clone(),
            })
    })
}

#[cfg(test)]
mod tests;
