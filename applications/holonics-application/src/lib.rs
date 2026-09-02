//! Explicit-root application lifecycle for source-neutral morphology variants.
//!
//! This crate composes existing lift, package, circulation, cultivation, evaluation, and export
//! owners. It does not implement another inference law or interpret filesystem paths as identity.

mod artifact;
mod evaluation;
mod manifest;
mod workspace;

use std::path::PathBuf;

use thiserror::Error;

pub use evaluation::{BoundaryEvaluation, VariantEvaluationReceipt};
pub use manifest::{
    ArtifactKind, ArtifactReference, CompletedRunReference, CurrentVariant, ExperimentReference,
    LiftReference, RunReference, VariantWorkspaceManifest, VARIANT_WORKSPACE_SCHEMA,
};
pub use workspace::{
    VariantExperimentSpec, VariantRunBoundary, VariantRunRecord, VariantRunState, VariantWorkspace,
    VariantWorkspaceInspection, WorkspaceReturn, VARIANT_EXPERIMENT_SCHEMA, VARIANT_RUN_SCHEMA,
};

#[derive(Debug, Error)]
pub enum ApplicationError {
    #[error("{path}: {reason}")]
    Io { path: PathBuf, reason: String },
    #[error("the application wire is malformed: {0}")]
    Wire(String),
    #[error("the variant workspace refused: {0}")]
    Workspace(String),
    #[error("the composed owner refused: {0}")]
    Owner(String),
    #[error("the immutable artifact already exists: {0}")]
    ExistingArtifact(PathBuf),
    #[error("the artifact path leaves the explicit workspace root: {0}")]
    RootEscape(PathBuf),
}
