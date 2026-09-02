use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use athena_alpha::{
    addressed_ingress, returned_local_interaction, AthenaAlphaApplication, BASE_CONFIGURATION,
};
use holonic_engine::{
    native_ecology::holonic_intelligence::{
        ExteriorModality, NativeInferenceAddress, NativeInferenceRequest,
    },
    receiver_exact_compression::ReceiverId,
    BoundaryId, EventId, ExactComplexWaveCurrent,
};
use life::native_intelligence::{
    export_morphology, ExportCodecKind, ExportPurpose, MorphologyExportRequest,
    MorphologyExportReturn, NativeCirculationBoundary, NativeCirculationConfiguration,
    NativeCirculationSnapshot, NativeCultivationCandidate, NativeDeclineReceipt,
    NativeMorphologyCommit, NativeMorphologyPackage,
};
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};

use crate::artifact::{ArtifactStore, MANIFEST_FILE};
use crate::evaluation::{evaluate_snapshot, VariantEvaluationReceipt};
use crate::manifest::{
    ArtifactKind, ArtifactReference, CompletedRunReference, CurrentVariant, ExperimentReference,
    LiftReference, RunReference, VariantWorkspaceManifest,
};
use crate::ApplicationError;

pub const VARIANT_EXPERIMENT_SCHEMA: &str = "org.holonics.variant-experiment.v1";
pub const VARIANT_RUN_SCHEMA: &str = "org.holonics.variant-run.v1";
pub const GEMMA_RECEIPT_LIFT_SCHEMA: &str = "org.holonics.gemma-receipt-lift.v1";
pub const WORKSPACE_EXPORT_SCHEMA: &str = "org.holonics.workspace-export.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VariantExperimentSpec {
    pub schema: String,
    pub name: String,
    pub ingress: NativeInferenceAddress,
    pub receiver: ReceiverId,
}

impl VariantExperimentSpec {
    fn validate(&self) -> Result<(), ApplicationError> {
        if self.schema != VARIANT_EXPERIMENT_SCHEMA
            || !valid_name(&self.name)
            || self.ingress.spool.is_empty()
            || self.ingress.thread.is_empty()
        {
            return Err(ApplicationError::Workspace(
                "malformed variant experiment specification".to_owned(),
            ));
        }
        Ok(())
    }

    fn request(&self) -> NativeInferenceRequest {
        addressed_ingress(
            self.ingress.spool.clone(),
            self.ingress.thread.clone(),
            self.ingress.occurrence,
            self.receiver,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "state", rename_all = "kebab-case")]
pub enum VariantRunState {
    Boundary {
        current_boundary: ArtifactReference,
    },
    Candidate {
        current_boundary: ArtifactReference,
        candidate: ArtifactReference,
    },
    Committed {
        successor_snapshot: ArtifactReference,
        candidate: ArtifactReference,
        commit: ArtifactReference,
    },
    Declined {
        unchanged_snapshot: ArtifactReference,
        candidate: Option<ArtifactReference>,
        decline: ArtifactReference,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VariantRunRecord {
    pub schema: String,
    pub ordinal: u64,
    pub experiment: String,
    pub predecessor_snapshot: ArtifactReference,
    pub boundary_history: Vec<ArtifactReference>,
    pub state: VariantRunState,
}

impl VariantRunRecord {
    fn validate(&self) -> Result<(), ApplicationError> {
        if self.schema != VARIANT_RUN_SCHEMA
            || self.ordinal == 0
            || !valid_name(&self.experiment)
            || self.predecessor_snapshot.kind != ArtifactKind::Snapshot
            || self.boundary_history.is_empty()
            || self
                .boundary_history
                .iter()
                .any(|artifact| artifact.kind != ArtifactKind::Boundary)
        {
            return Err(ApplicationError::Workspace(
                "malformed variant run record".to_owned(),
            ));
        }
        Ok(())
    }

    fn current_boundary(&self) -> Result<&ArtifactReference, ApplicationError> {
        match &self.state {
            VariantRunState::Boundary { current_boundary }
            | VariantRunState::Candidate {
                current_boundary, ..
            } => Ok(current_boundary),
            _ => Err(ApplicationError::Workspace(
                "the run has no active circulation boundary".to_owned(),
            )),
        }
    }

    fn artifacts(&self) -> Vec<&ArtifactReference> {
        let mut artifacts = vec![&self.predecessor_snapshot];
        artifacts.extend(self.boundary_history.iter());
        match &self.state {
            VariantRunState::Boundary { current_boundary } => artifacts.push(current_boundary),
            VariantRunState::Candidate {
                current_boundary,
                candidate,
            } => artifacts.extend([current_boundary, candidate]),
            VariantRunState::Committed {
                successor_snapshot,
                candidate,
                commit,
            } => artifacts.extend([successor_snapshot, candidate, commit]),
            VariantRunState::Declined {
                unchanged_snapshot,
                candidate,
                decline,
            } => {
                artifacts.push(unchanged_snapshot);
                artifacts.extend(candidate.iter());
                artifacts.push(decline);
            }
        }
        artifacts
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GemmaReceiptLiftReceipt {
    pub schema: String,
    pub ordinal: u64,
    pub source_address: String,
    pub receiver: ReceiverId,
    pub modality_occurrences: BTreeMap<ExteriorModality, usize>,
    pub cold_excitation_population: usize,
    pub open_exterior: Vec<String>,
    pub generation: u64,
    pub snapshot: ArtifactReference,
    pub cold_witness: ArtifactReference,
    pub insufficiency: ArtifactReference,
    pub foreign_execution: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorkspaceExportReceipt {
    pub schema: String,
    pub generation: u64,
    pub codec: ExportCodecKind,
    pub media_type: String,
    pub schema_or_opset: String,
    pub receiver_family: BTreeSet<ReceiverId>,
    pub complete_package_round_trip: bool,
    pub artifact: ArtifactReference,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct WorkspaceReturn<T> {
    pub workspace_root: PathBuf,
    pub current_snapshot: Option<PathBuf>,
    pub written_artifacts: Vec<PathBuf>,
    pub value: T,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VariantRunBoundary {
    pub run: VariantRunRecord,
    pub boundary: NativeCirculationBoundary,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VariantWorkspaceInspection {
    pub manifest: VariantWorkspaceManifest,
    pub active: Option<VariantRunBoundary>,
}

#[derive(Debug)]
pub struct VariantWorkspace {
    store: ArtifactStore,
    manifest: VariantWorkspaceManifest,
}

impl VariantWorkspace {
    pub fn create(root: &Path, label: impl Into<String>) -> Result<Self, ApplicationError> {
        let store = ArtifactStore::create(root)?;
        if store.manifest_path().exists() {
            return Err(ApplicationError::ExistingArtifact(store.manifest_path()));
        }
        let manifest = VariantWorkspaceManifest::empty(label.into())?;
        store.write_json_new(MANIFEST_FILE, &manifest)?;
        Self::open(store.root())
    }

    pub fn open(root: &Path) -> Result<Self, ApplicationError> {
        let store = ArtifactStore::open(root)?;
        let manifest: VariantWorkspaceManifest = store.read_manifest()?;
        manifest.validate()?;
        for artifact in manifest.artifacts() {
            let _ = store.read(&artifact.relative_path)?;
        }
        for run_reference in manifest
            .active_run
            .iter()
            .map(|run| &run.artifact)
            .chain(manifest.completed_runs.iter().map(|run| &run.artifact))
        {
            let run: VariantRunRecord = store.read_json(&run_reference.relative_path)?;
            run.validate()?;
            for artifact in run.artifacts() {
                let _ = store.read(&artifact.relative_path)?;
            }
        }
        for experiment in &manifest.experiments {
            let spec: VariantExperimentSpec =
                store.read_json(&experiment.artifact.relative_path)?;
            spec.validate()?;
            if spec.name != experiment.name {
                return Err(ApplicationError::Workspace(
                    "experiment reference and specification disagree".to_owned(),
                ));
            }
        }
        if let Some(current) = &manifest.current {
            let snapshot = read_snapshot(&store, &current.snapshot)?;
            let package = NativeMorphologyPackage::read(&snapshot.package_wire).map_err(owner)?;
            if !package
                .manifest
                .receiver_capability
                .native_receiver_family
                .contains(&snapshot.configuration.address.receiver)
                || package.manifest != current.morphology
                || package.manifest.lineage.generation != current.generation
            {
                return Err(ApplicationError::Workspace(
                    "current manifest does not reconstruct the current snapshot".to_owned(),
                ));
            }
        }
        Ok(Self { store, manifest })
    }

    pub fn root(&self) -> &Path {
        self.store.root()
    }

    pub fn manifest(&self) -> &VariantWorkspaceManifest {
        &self.manifest
    }

    pub fn inspect(&self) -> Result<WorkspaceReturn<VariantWorkspaceInspection>, ApplicationError> {
        let active = if self.manifest.active_run.is_some() {
            let (_, run) = self.active_run()?;
            let boundary = self.read_boundary(run.current_boundary()?)?;
            Some(VariantRunBoundary { run, boundary })
        } else {
            None
        };
        self.returned(
            Vec::new(),
            VariantWorkspaceInspection {
                manifest: self.manifest.clone(),
                active,
            },
        )
    }

    pub fn import_snapshot(
        &mut self,
        source: &Path,
    ) -> Result<WorkspaceReturn<CurrentVariant>, ApplicationError> {
        self.require_unfounded()?;
        let bytes = fs::read(source).map_err(|error| ApplicationError::Io {
            path: source.to_path_buf(),
            reason: error.to_string(),
        })?;
        let snapshot = NativeCirculationSnapshot::read(&bytes).map_err(owner)?;
        let application = AthenaAlphaApplication::remount(snapshot.clone()).map_err(owner)?;
        let mut next = self.manifest.clone();
        let ordinal = next.allocate()?;
        let reference = artifact(
            ArtifactKind::Snapshot,
            format!(
                "snapshots/generation-{}-import-{ordinal}.snapshot.json",
                application.generation()
            ),
        );
        let path = self.store.write_new(
            &reference.relative_path,
            &snapshot.canonical_bytes().map_err(owner)?,
        )?;
        let current = CurrentVariant {
            generation: application.generation(),
            snapshot: reference,
            morphology: application.package().manifest.clone(),
        };
        next.current = Some(current.clone());
        self.replace_manifest(next)?;
        self.returned(vec![path], current)
    }

    pub fn lift_gemma_receipt(
        &mut self,
        receipt_root: &Path,
        receiver: ReceiverId,
    ) -> Result<WorkspaceReturn<GemmaReceiptLiftReceipt>, ApplicationError> {
        self.require_unfounded()?;
        let source = receipt_root
            .canonicalize()
            .map_err(|error| ApplicationError::Io {
                path: receipt_root.to_path_buf(),
                reason: error.to_string(),
            })?;
        let mut configuration: NativeCirculationConfiguration =
            serde_json::from_str(BASE_CONFIGURATION)
                .map_err(|error| ApplicationError::Wire(error.to_string()))?;
        configuration.address.receiver = receiver;
        let admission =
            AthenaAlphaApplication::from_complete_gemma4_receipt(&source, configuration)
                .map_err(owner)?;
        let snapshot = admission.application.snapshot().map_err(owner)?;
        let mut next = self.manifest.clone();
        let ordinal = next.allocate()?;
        let base = format!("lifts/lift-{ordinal}");
        let cold = artifact(
            ArtifactKind::ColdWitness,
            format!("{base}/cold-witness.json"),
        );
        let insufficiency = artifact(
            ArtifactKind::Insufficiency,
            format!("{base}/insufficiency.json"),
        );
        let lift_artifact = artifact(
            ArtifactKind::LiftReceipt,
            format!("{base}/lift-receipt.json"),
        );
        let snapshot_artifact = artifact(
            ArtifactKind::Snapshot,
            format!("snapshots/generation-0-lift-{ordinal}.snapshot.json"),
        );
        let mut modality_occurrences = BTreeMap::new();
        for excitation in &admission.departed.cold_witness.excitations {
            *modality_occurrences
                .entry(excitation.exterior_modality)
                .or_default() += 1;
        }
        let receipt = GemmaReceiptLiftReceipt {
            schema: GEMMA_RECEIPT_LIFT_SCHEMA.to_owned(),
            ordinal,
            source_address: source.display().to_string(),
            receiver,
            modality_occurrences,
            cold_excitation_population: admission.departed.cold_witness.excitations.len(),
            open_exterior: admission.departed.cold_witness.open_exterior.clone(),
            generation: 0,
            snapshot: snapshot_artifact.clone(),
            cold_witness: cold.clone(),
            insufficiency: insufficiency.clone(),
            foreign_execution: false,
        };
        let written = vec![
            self.store
                .write_json_new(&cold.relative_path, &admission.departed.cold_witness)?,
            self.store.write_json_new(
                &insufficiency.relative_path,
                &admission.departed.insufficiency,
            )?,
            self.store.write_new(
                &snapshot_artifact.relative_path,
                &snapshot.canonical_bytes().map_err(owner)?,
            )?,
            self.store
                .write_json_new(&lift_artifact.relative_path, &receipt)?,
        ];
        let current = CurrentVariant {
            generation: 0,
            snapshot: snapshot_artifact,
            morphology: admission.application.package().manifest.clone(),
        };
        next.current = Some(current);
        next.lifts.push(LiftReference {
            ordinal,
            source_kind: "complete-gemma4-excitation-receipt".to_owned(),
            source_address: source.display().to_string(),
            cold_witness: cold,
            insufficiency,
            receipt: lift_artifact,
        });
        self.replace_manifest(next)?;
        self.returned(written, receipt)
    }

    pub fn define_experiment(
        &mut self,
        name: impl Into<String>,
        ingress_ordinal: usize,
        receiver: Option<ReceiverId>,
    ) -> Result<WorkspaceReturn<VariantExperimentSpec>, ApplicationError> {
        let name = name.into();
        if self
            .manifest
            .experiments
            .iter()
            .any(|experiment| experiment.name == name)
        {
            return Err(ApplicationError::Workspace(format!(
                "experiment {name:?} already exists"
            )));
        }
        let application = self.current_application()?;
        let address = application
            .package()
            .hot()
            .realization()
            .ingress_sections
            .get(ingress_ordinal)
            .ok_or_else(|| {
                ApplicationError::Workspace(format!(
                    "ingress ordinal {ingress_ordinal} is outside the current package"
                ))
            })?;
        let receiver = receiver.unwrap_or(
            application
                .snapshot()
                .map_err(owner)?
                .configuration
                .address
                .receiver,
        );
        if !application
            .package()
            .manifest
            .receiver_capability
            .native_receiver_family
            .contains(&receiver)
        {
            return Err(ApplicationError::Workspace(
                "experiment receiver is outside the current package family".to_owned(),
            ));
        }
        let experiment = VariantExperimentSpec {
            schema: VARIANT_EXPERIMENT_SCHEMA.to_owned(),
            name: name.clone(),
            ingress: NativeInferenceAddress {
                spool: address.spool.clone(),
                thread: address.thread.clone(),
                occurrence: address.occurrence,
            },
            receiver,
        };
        experiment.validate()?;
        let reference = artifact(ArtifactKind::Experiment, format!("experiments/{name}.json"));
        let path = self
            .store
            .write_json_new(&reference.relative_path, &experiment)?;
        let mut next = self.manifest.clone();
        next.experiments.push(ExperimentReference {
            name,
            artifact: reference,
        });
        self.replace_manifest(next)?;
        self.returned(vec![path], experiment)
    }

    pub fn conduct(
        &mut self,
        experiment_name: &str,
    ) -> Result<WorkspaceReturn<VariantRunBoundary>, ApplicationError> {
        self.require_no_active_run()?;
        let experiment = self.experiment(experiment_name)?;
        let application = self.current_application()?;
        let boundary = application.conduct(experiment.request()).map_err(owner)?;
        let mut next = self.manifest.clone();
        let ordinal = next.allocate()?;
        let base = format!("runs/run-{ordinal}");
        let boundary_reference =
            artifact(ArtifactKind::Boundary, format!("{base}/boundary-0.json"));
        let run_reference = artifact(ArtifactKind::Run, format!("{base}/run.json"));
        let predecessor_snapshot = next
            .current
            .as_ref()
            .expect("current application checked")
            .snapshot
            .clone();
        let run = VariantRunRecord {
            schema: VARIANT_RUN_SCHEMA.to_owned(),
            ordinal,
            experiment: experiment.name,
            predecessor_snapshot,
            boundary_history: vec![boundary_reference.clone()],
            state: VariantRunState::Boundary {
                current_boundary: boundary_reference.clone(),
            },
        };
        run.validate()?;
        let written = vec![
            self.store
                .write_json_new(&boundary_reference.relative_path, &boundary)?,
            self.store
                .write_json_new(&run_reference.relative_path, &run)?,
        ];
        next.active_run = Some(RunReference {
            ordinal,
            artifact: run_reference,
        });
        self.replace_manifest(next)?;
        self.returned(written, VariantRunBoundary { run, boundary })
    }

    pub fn continue_active(
        &mut self,
        successor_ordinal: usize,
    ) -> Result<WorkspaceReturn<VariantRunBoundary>, ApplicationError> {
        let (run_reference, mut run) = self.active_run()?;
        if !matches!(run.state, VariantRunState::Boundary { .. }) {
            return Err(ApplicationError::Workspace(
                "a staged candidate must be committed or declined before continuation".to_owned(),
            ));
        }
        self.require_run_predecessor(&run)?;
        let boundary = self.read_boundary(run.current_boundary()?)?;
        let successor = boundary
            .actual_successors
            .get(successor_ordinal)
            .ok_or_else(|| {
                ApplicationError::Workspace(format!(
                    "successor ordinal {successor_ordinal} is outside the active boundary"
                ))
            })?;
        let next_boundary = self
            .current_application()?
            .continue_from(&boundary, &successor.address)
            .map_err(owner)?;
        let next_reference = artifact(
            ArtifactKind::Boundary,
            format!(
                "runs/run-{}/boundary-{}.json",
                run.ordinal,
                run.boundary_history.len()
            ),
        );
        let path = self
            .store
            .write_json_new(&next_reference.relative_path, &next_boundary)?;
        run.boundary_history.push(next_reference.clone());
        run.state = VariantRunState::Boundary {
            current_boundary: next_reference,
        };
        run.validate()?;
        self.store
            .replace_json(&run_reference.relative_path, &run)?;
        self.returned(
            vec![path, self.store.absolute(&run_reference.relative_path)?],
            VariantRunBoundary {
                run,
                boundary: next_boundary,
            },
        )
    }

    pub fn stage_return(
        &mut self,
        occurrence: EventId,
        boundary_address: BoundaryId,
        current: ExactComplexWaveCurrent,
        storage: Rat,
    ) -> Result<WorkspaceReturn<NativeCultivationCandidate>, ApplicationError> {
        let (run_reference, mut run) = self.active_run()?;
        if !matches!(run.state, VariantRunState::Boundary { .. }) {
            return Err(ApplicationError::Workspace(
                "the active run already has a staged candidate".to_owned(),
            ));
        }
        self.require_run_predecessor(&run)?;
        let boundary = self.read_boundary(run.current_boundary()?)?;
        let returned = returned_local_interaction(
            boundary.emission.address.clone(),
            occurrence,
            boundary_address,
            current,
            storage,
            BTreeSet::new(),
        )
        .map_err(owner)?;
        let candidate = self
            .current_application()?
            .stage_return(&boundary, returned)
            .map_err(owner)?;
        let candidate_reference = artifact(
            ArtifactKind::Candidate,
            format!("runs/run-{}/candidate.json", run.ordinal),
        );
        let path = self
            .store
            .write_json_new(&candidate_reference.relative_path, &candidate)?;
        run.state = VariantRunState::Candidate {
            current_boundary: run.current_boundary()?.clone(),
            candidate: candidate_reference,
        };
        run.validate()?;
        self.store
            .replace_json(&run_reference.relative_path, &run)?;
        self.returned(
            vec![path, self.store.absolute(&run_reference.relative_path)?],
            candidate,
        )
    }

    pub fn commit(&mut self) -> Result<WorkspaceReturn<NativeMorphologyCommit>, ApplicationError> {
        let (run_reference, run) = self.active_run()?;
        self.require_run_predecessor(&run)?;
        let candidate_reference = match &run.state {
            VariantRunState::Candidate { candidate, .. } => candidate,
            _ => {
                return Err(ApplicationError::Workspace(
                    "the active run has no staged return candidate".to_owned(),
                ))
            }
        };
        let candidate: NativeCultivationCandidate =
            self.store.read_json(&candidate_reference.relative_path)?;
        let (application, commit) = self
            .current_application()?
            .commit(candidate)
            .map_err(owner)?;
        let snapshot = application.snapshot().map_err(owner)?;
        let generation = application.generation();
        let snapshot_reference = artifact(
            ArtifactKind::Snapshot,
            format!(
                "snapshots/generation-{generation}-run-{}.snapshot.json",
                run.ordinal
            ),
        );
        let commit_reference = artifact(
            ArtifactKind::Commit,
            format!("runs/run-{}/commit.json", run.ordinal),
        );
        let completed_reference = artifact(
            ArtifactKind::Run,
            format!("runs/run-{}/completed.json", run.ordinal),
        );
        let completed = VariantRunRecord {
            state: VariantRunState::Committed {
                successor_snapshot: snapshot_reference.clone(),
                candidate: candidate_reference.clone(),
                commit: commit_reference.clone(),
            },
            ..run.clone()
        };
        let written = vec![
            self.store.write_new(
                &snapshot_reference.relative_path,
                &snapshot.canonical_bytes().map_err(owner)?,
            )?,
            self.store
                .write_json_new(&commit_reference.relative_path, &commit)?,
            self.store
                .write_json_new(&completed_reference.relative_path, &completed)?,
        ];
        let mut next = self.manifest.clone();
        next.current = Some(CurrentVariant {
            generation,
            snapshot: snapshot_reference,
            morphology: application.package().manifest.clone(),
        });
        next.active_run = None;
        next.completed_runs.push(CompletedRunReference {
            ordinal: run.ordinal,
            disposition: "committed".to_owned(),
            artifact: completed_reference,
        });
        self.replace_manifest(next)?;
        let _ = run_reference;
        self.returned(written, commit)
    }

    pub fn decline(&mut self) -> Result<WorkspaceReturn<NativeDeclineReceipt>, ApplicationError> {
        let (_run_reference, run) = self.active_run()?;
        self.require_run_predecessor(&run)?;
        let boundary = self.read_boundary(run.current_boundary()?)?;
        let before = self.current_snapshot()?;
        let (application, decline) = self
            .current_application()?
            .decline(&boundary)
            .map_err(owner)?;
        let after = application.snapshot().map_err(owner)?;
        if before.canonical_bytes().map_err(owner)? != after.canonical_bytes().map_err(owner)? {
            return Err(ApplicationError::Workspace(
                "decline changed the current snapshot".to_owned(),
            ));
        }
        let decline_reference = artifact(
            ArtifactKind::Decline,
            format!("runs/run-{}/decline.json", run.ordinal),
        );
        let completed_reference = artifact(
            ArtifactKind::Run,
            format!("runs/run-{}/completed.json", run.ordinal),
        );
        let candidate = match &run.state {
            VariantRunState::Candidate { candidate, .. } => Some(candidate.clone()),
            _ => None,
        };
        let completed = VariantRunRecord {
            state: VariantRunState::Declined {
                unchanged_snapshot: run.predecessor_snapshot.clone(),
                candidate,
                decline: decline_reference.clone(),
            },
            ..run.clone()
        };
        let written = vec![
            self.store
                .write_json_new(&decline_reference.relative_path, &decline)?,
            self.store
                .write_json_new(&completed_reference.relative_path, &completed)?,
        ];
        let mut next = self.manifest.clone();
        next.active_run = None;
        next.completed_runs.push(CompletedRunReference {
            ordinal: run.ordinal,
            disposition: "declined".to_owned(),
            artifact: completed_reference,
        });
        self.replace_manifest(next)?;
        self.returned(written, decline)
    }

    pub fn evaluate(
        &mut self,
        experiment_name: &str,
    ) -> Result<WorkspaceReturn<VariantEvaluationReceipt>, ApplicationError> {
        let experiment = self.experiment(experiment_name)?;
        let snapshot = self.current_snapshot()?;
        let receipt = evaluate_snapshot(&snapshot, &experiment)?;
        let mut next = self.manifest.clone();
        let ordinal = next.allocate()?;
        let reference = artifact(
            ArtifactKind::Evaluation,
            format!("evaluations/evaluation-{ordinal}.json"),
        );
        let path = self
            .store
            .write_json_new(&reference.relative_path, &receipt)?;
        next.evaluations.push(reference);
        self.replace_manifest(next)?;
        self.returned(vec![path], receipt)
    }

    pub fn export(
        &mut self,
        codec: ExportCodecKind,
    ) -> Result<WorkspaceReturn<WorkspaceExportReceipt>, ApplicationError> {
        let snapshot = self.current_snapshot()?;
        let package = NativeMorphologyPackage::read(&snapshot.package_wire).map_err(owner)?;
        let returned = export_morphology(
            &package,
            MorphologyExportRequest {
                codec: codec.clone(),
                receiver_family: package
                    .manifest
                    .receiver_capability
                    .native_receiver_family
                    .clone(),
                purpose: ExportPurpose::RestedInference,
            },
        )
        .map_err(owner)?;
        let MorphologyExportReturn::Exact(exact) = returned else {
            return Err(ApplicationError::Owner(format!(
                "workspace export returned {returned:?}"
            )));
        };
        let mut next = self.manifest.clone();
        let ordinal = next.allocate()?;
        let extension = match codec {
            ExportCodecKind::Onnx => "onnx",
            ExportCodecKind::Safetensors => "safetensors",
        };
        let export_reference = artifact(
            match codec {
                ExportCodecKind::Onnx => ArtifactKind::Onnx,
                ExportCodecKind::Safetensors => ArtifactKind::Safetensors,
            },
            format!("exports/export-{ordinal}.{extension}"),
        );
        let receipt_reference = artifact(
            ArtifactKind::ExportReceipt,
            format!("exports/export-{ordinal}.receipt.json"),
        );
        let receipt = WorkspaceExportReceipt {
            schema: WORKSPACE_EXPORT_SCHEMA.to_owned(),
            generation: package.manifest.lineage.generation,
            codec: codec.clone(),
            media_type: exact.artifact.media_type.clone(),
            schema_or_opset: exact.artifact.schema_or_opset.clone(),
            receiver_family: exact.receiver_family.clone(),
            complete_package_round_trip: exact.complete_package_round_trip,
            artifact: export_reference.clone(),
        };
        let written = vec![
            self.store
                .write_new(&export_reference.relative_path, &exact.artifact.bytes)?,
            self.store
                .write_json_new(&receipt_reference.relative_path, &receipt)?,
        ];
        next.exports.extend([export_reference, receipt_reference]);
        self.replace_manifest(next)?;
        self.returned(written, receipt)
    }

    fn current_snapshot(&self) -> Result<NativeCirculationSnapshot, ApplicationError> {
        let current = self.manifest.current.as_ref().ok_or_else(|| {
            ApplicationError::Workspace("the workspace has no current variant".to_owned())
        })?;
        read_snapshot(&self.store, &current.snapshot)
    }

    fn current_application(&self) -> Result<AthenaAlphaApplication, ApplicationError> {
        AthenaAlphaApplication::remount(self.current_snapshot()?).map_err(owner)
    }

    fn experiment(&self, name: &str) -> Result<VariantExperimentSpec, ApplicationError> {
        let reference = self
            .manifest
            .experiments
            .iter()
            .find(|experiment| experiment.name == name)
            .ok_or_else(|| ApplicationError::Workspace(format!("unknown experiment {name:?}")))?;
        let experiment: VariantExperimentSpec =
            self.store.read_json(&reference.artifact.relative_path)?;
        experiment.validate()?;
        Ok(experiment)
    }

    fn active_run(&self) -> Result<(ArtifactReference, VariantRunRecord), ApplicationError> {
        let active = self.manifest.active_run.as_ref().ok_or_else(|| {
            ApplicationError::Workspace("the workspace has no active run".to_owned())
        })?;
        let run: VariantRunRecord = self.store.read_json(&active.artifact.relative_path)?;
        run.validate()?;
        if run.ordinal != active.ordinal {
            return Err(ApplicationError::Workspace(
                "active run reference and record disagree".to_owned(),
            ));
        }
        Ok((active.artifact.clone(), run))
    }

    fn read_boundary(
        &self,
        reference: &ArtifactReference,
    ) -> Result<NativeCirculationBoundary, ApplicationError> {
        if reference.kind != ArtifactKind::Boundary {
            return Err(ApplicationError::Workspace(
                "run boundary reference has another artifact kind".to_owned(),
            ));
        }
        self.store.read_json(&reference.relative_path)
    }

    fn require_run_predecessor(&self, run: &VariantRunRecord) -> Result<(), ApplicationError> {
        let current = self.manifest.current.as_ref().ok_or_else(|| {
            ApplicationError::Workspace("the workspace has no current variant".to_owned())
        })?;
        if current.snapshot != run.predecessor_snapshot {
            return Err(ApplicationError::Workspace(
                "active run predecessor is not the current workspace snapshot".to_owned(),
            ));
        }
        Ok(())
    }

    fn require_unfounded(&self) -> Result<(), ApplicationError> {
        if self.manifest.current.is_some() || !self.manifest.lifts.is_empty() {
            return Err(ApplicationError::Workspace(
                "the workspace already has a current variant".to_owned(),
            ));
        }
        self.require_no_active_run()
    }

    fn require_no_active_run(&self) -> Result<(), ApplicationError> {
        if self.manifest.active_run.is_some() {
            return Err(ApplicationError::Workspace(
                "the workspace already owns an active run".to_owned(),
            ));
        }
        Ok(())
    }

    fn replace_manifest(
        &mut self,
        manifest: VariantWorkspaceManifest,
    ) -> Result<(), ApplicationError> {
        manifest.validate()?;
        for artifact in manifest.artifacts() {
            let _ = self.store.read(&artifact.relative_path)?;
        }
        self.store.replace_manifest(&manifest)?;
        self.manifest = manifest;
        Ok(())
    }

    fn returned<T>(
        &self,
        written_artifacts: Vec<PathBuf>,
        value: T,
    ) -> Result<WorkspaceReturn<T>, ApplicationError> {
        let current_snapshot = self
            .manifest
            .current
            .as_ref()
            .map(|current| self.store.absolute(&current.snapshot.relative_path))
            .transpose()?;
        Ok(WorkspaceReturn {
            workspace_root: self.store.root().to_path_buf(),
            current_snapshot,
            written_artifacts,
            value,
        })
    }
}

fn read_snapshot(
    store: &ArtifactStore,
    reference: &ArtifactReference,
) -> Result<NativeCirculationSnapshot, ApplicationError> {
    if reference.kind != ArtifactKind::Snapshot {
        return Err(ApplicationError::Workspace(
            "current snapshot reference has another artifact kind".to_owned(),
        ));
    }
    NativeCirculationSnapshot::read(&store.read(&reference.relative_path)?).map_err(owner)
}

fn artifact(kind: ArtifactKind, relative_path: String) -> ArtifactReference {
    ArtifactReference {
        kind,
        relative_path,
    }
}

fn valid_name(name: &str) -> bool {
    !name.is_empty()
        && name
            .chars()
            .all(|character| character.is_ascii_alphanumeric() || matches!(character, '-' | '_'))
}

fn owner(error: impl std::fmt::Display) -> ApplicationError {
    ApplicationError::Owner(error.to_string())
}
