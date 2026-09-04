use holonics_hna::AthenaAlphaApplication;
use holonic_engine::native_ecology::holonic_intelligence::NativeInferenceRequest;
use life::native_intelligence::{NativeCirculationBoundary, NativeCirculationSnapshot};
use serde::{Deserialize, Serialize};

use crate::{ApplicationError, VariantExperimentSpec};

pub const VARIANT_EVALUATION_SCHEMA: &str = "org.holonics.variant-evaluation.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BoundaryEvaluation {
    pub generation: u64,
    pub future_population: usize,
    pub actual_successor_population: usize,
    pub open_obligation_population: usize,
    pub boundary: NativeCirculationBoundary,
}

impl From<NativeCirculationBoundary> for BoundaryEvaluation {
    fn from(boundary: NativeCirculationBoundary) -> Self {
        Self {
            generation: boundary.generation,
            future_population: boundary.futures.len(),
            actual_successor_population: boundary.actual_successors.len(),
            open_obligation_population: boundary.open_obligations.len(),
            boundary,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VariantEvaluationReceipt {
    pub schema: String,
    pub experiment: String,
    pub current: BoundaryEvaluation,
    pub withdrawn: Option<BoundaryEvaluation>,
    pub restored: Option<BoundaryEvaluation>,
    pub cultivation_separates_current_from_withdrawn: Option<bool>,
    pub restoration_exact: Option<bool>,
    pub current_snapshot_unchanged: bool,
    pub open: Vec<String>,
}

pub(crate) fn evaluate_snapshot(
    snapshot: &NativeCirculationSnapshot,
    experiment: &VariantExperimentSpec,
) -> Result<VariantEvaluationReceipt, ApplicationError> {
    let request = NativeInferenceRequest {
        address: experiment.ingress.clone(),
        receiver: experiment.receiver,
    };
    let current = AthenaAlphaApplication::remount(snapshot.clone())
        .map_err(owner)?
        .conduct(request.clone())
        .map_err(owner)?;
    if snapshot.commits.is_empty() {
        return Ok(VariantEvaluationReceipt {
            schema: VARIANT_EVALUATION_SCHEMA.to_owned(),
            experiment: experiment.name.clone(),
            current: current.into(),
            withdrawn: None,
            restored: None,
            cultivation_separates_current_from_withdrawn: None,
            restoration_exact: None,
            current_snapshot_unchanged: true,
            open: vec!["withdrawal evaluation requires at least one committed return".to_owned()],
        });
    }

    let (predecessor, commit) = AthenaAlphaApplication::remount(snapshot.clone())
        .map_err(owner)?
        .withdraw_last_commit()
        .map_err(owner)?;
    let predecessor_snapshot = predecessor.snapshot().map_err(owner)?;
    drop(predecessor);
    let withdrawn = AthenaAlphaApplication::remount(predecessor_snapshot.clone())
        .map_err(owner)?
        .conduct(request.clone())
        .map_err(owner)?;
    let restored = AthenaAlphaApplication::remount(predecessor_snapshot)
        .map_err(owner)?
        .replay_commit(commit)
        .map_err(owner)?;
    let restored_snapshot = restored.snapshot().map_err(owner)?;
    let restored_boundary = restored.conduct(request).map_err(owner)?;
    let restoration_exact = restored_snapshot.canonical_bytes().map_err(owner)?
        == snapshot.canonical_bytes().map_err(owner)?
        && restored_boundary == current;
    let cultivation_separates = withdrawn.emission != current.emission
        || withdrawn.futures != current.futures
        || withdrawn.actual_successors != current.actual_successors
        || withdrawn.open_obligations != current.open_obligations;

    Ok(VariantEvaluationReceipt {
        schema: VARIANT_EVALUATION_SCHEMA.to_owned(),
        experiment: experiment.name.clone(),
        current: current.into(),
        withdrawn: Some(withdrawn.into()),
        restored: Some(restored_boundary.into()),
        cultivation_separates_current_from_withdrawn: Some(cultivation_separates),
        restoration_exact: Some(restoration_exact),
        current_snapshot_unchanged: true,
        open: if cultivation_separates {
            Vec::new()
        } else {
            vec!["the selected experiment does not separate the latest committed delta".to_owned()]
        },
    })
}

fn owner(error: impl std::fmt::Display) -> ApplicationError {
    ApplicationError::Owner(error.to_string())
}
