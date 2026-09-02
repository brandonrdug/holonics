use std::collections::BTreeSet;

use life::native_intelligence::MorphologyVariantManifest;
use serde::{Deserialize, Serialize};

use crate::ApplicationError;

pub const VARIANT_WORKSPACE_SCHEMA: &str = "org.holonics.variant-workspace.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ArtifactKind {
    Snapshot,
    ColdWitness,
    Insufficiency,
    LiftReceipt,
    Experiment,
    Run,
    Boundary,
    Candidate,
    Commit,
    Decline,
    Evaluation,
    Onnx,
    Safetensors,
    ExportReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactReference {
    pub kind: ArtifactKind,
    pub relative_path: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CurrentVariant {
    pub generation: u64,
    pub snapshot: ArtifactReference,
    pub morphology: MorphologyVariantManifest,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LiftReference {
    pub ordinal: u64,
    pub source_kind: String,
    pub source_address: String,
    pub cold_witness: ArtifactReference,
    pub insufficiency: ArtifactReference,
    pub receipt: ArtifactReference,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExperimentReference {
    pub name: String,
    pub artifact: ArtifactReference,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RunReference {
    pub ordinal: u64,
    pub artifact: ArtifactReference,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompletedRunReference {
    pub ordinal: u64,
    pub disposition: String,
    pub artifact: ArtifactReference,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VariantWorkspaceManifest {
    pub schema: String,
    pub label: String,
    pub next_ordinal: u64,
    pub current: Option<CurrentVariant>,
    pub lifts: Vec<LiftReference>,
    pub experiments: Vec<ExperimentReference>,
    pub active_run: Option<RunReference>,
    pub completed_runs: Vec<CompletedRunReference>,
    pub evaluations: Vec<ArtifactReference>,
    pub exports: Vec<ArtifactReference>,
    pub open_capabilities: BTreeSet<String>,
}

impl VariantWorkspaceManifest {
    pub fn empty(label: String) -> Result<Self, ApplicationError> {
        let manifest = Self {
            schema: VARIANT_WORKSPACE_SCHEMA.to_owned(),
            label,
            next_ordinal: 1,
            current: None,
            lifts: Vec::new(),
            experiments: Vec::new(),
            active_run: None,
            completed_runs: Vec::new(),
            evaluations: Vec::new(),
            exports: Vec::new(),
            open_capabilities: BTreeSet::from([
                "raw-model-directory-lift-open".to_owned(),
                "qualitative-emission-codec-open".to_owned(),
                "persistent-configurable-diffusion-open".to_owned(),
            ]),
        };
        manifest.validate()?;
        Ok(manifest)
    }

    pub fn allocate(&mut self) -> Result<u64, ApplicationError> {
        let ordinal = self.next_ordinal;
        self.next_ordinal = self.next_ordinal.checked_add(1).ok_or_else(|| {
            ApplicationError::Workspace("workspace artifact ordinal overflow".to_owned())
        })?;
        Ok(ordinal)
    }

    pub fn validate(&self) -> Result<(), ApplicationError> {
        if self.schema != VARIANT_WORKSPACE_SCHEMA || self.label.trim().is_empty() {
            return Err(ApplicationError::Workspace(
                "unknown workspace schema or empty label".to_owned(),
            ));
        }
        if let Some(current) = &self.current {
            if current.snapshot.kind != ArtifactKind::Snapshot
                || current.generation != current.morphology.lineage.generation
            {
                return Err(ApplicationError::Workspace(
                    "current snapshot, generation, and morphology manifest disagree".to_owned(),
                ));
            }
        }
        if self.active_run.as_ref().is_some_and(|active| {
            self.completed_runs
                .iter()
                .any(|completed| completed.ordinal == active.ordinal)
        }) {
            return Err(ApplicationError::Workspace(
                "one run is both active and completed".to_owned(),
            ));
        }
        let mut experiment_names = BTreeSet::new();
        if self
            .experiments
            .iter()
            .any(|experiment| !experiment_names.insert(&experiment.name))
        {
            return Err(ApplicationError::Workspace(
                "experiment names are not unique".to_owned(),
            ));
        }
        for artifact in self.artifacts() {
            validate_relative(&artifact.relative_path)?;
        }
        Ok(())
    }

    pub fn artifacts(&self) -> Vec<&ArtifactReference> {
        let mut artifacts = Vec::new();
        if let Some(current) = &self.current {
            artifacts.push(&current.snapshot);
        }
        for lift in &self.lifts {
            artifacts.extend([&lift.cold_witness, &lift.insufficiency, &lift.receipt]);
        }
        artifacts.extend(self.experiments.iter().map(|item| &item.artifact));
        artifacts.extend(self.active_run.iter().map(|item| &item.artifact));
        artifacts.extend(self.completed_runs.iter().map(|item| &item.artifact));
        artifacts.extend(self.evaluations.iter());
        artifacts.extend(self.exports.iter());
        artifacts
    }
}

pub(crate) fn validate_relative(path: &str) -> Result<(), ApplicationError> {
    let path = std::path::Path::new(path);
    if path.as_os_str().is_empty()
        || path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, std::path::Component::Normal(_)))
    {
        return Err(ApplicationError::RootEscape(path.to_path_buf()));
    }
    Ok(())
}
