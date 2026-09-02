use holonic_engine::{
    receiver_exact_compression::ReceiverId, BoundaryId, EventId, ExactComplexWaveCurrent,
};
use holonics_application::{VariantWorkspace, WorkspaceReturn};
use life::native_intelligence::ExportCodecKind;
use serde::Serialize;

use crate::adapters::AdapterReturn;
use crate::runtime::{parse_rat, WorkbenchError};
use crate::{ExportCodecArgument, WorkspaceCommand};

pub fn execute(command: WorkspaceCommand) -> Result<AdapterReturn, WorkbenchError> {
    match command {
        WorkspaceCommand::Create { root, label } => {
            let workspace = VariantWorkspace::create(&root, label).map_err(owner)?;
            returned(
                "workspace/create",
                "created an explicit-root empty variant workspace",
                workspace.inspect().map_err(owner)?,
            )
        }
        WorkspaceCommand::Inspect { root } => {
            let workspace = VariantWorkspace::open(&root).map_err(owner)?;
            returned(
                "workspace/inspect",
                "returned the current variant, experiments, active run, completed runs, evaluations, exports, and open capabilities",
                workspace.inspect().map_err(owner)?,
            )
        }
        WorkspaceCommand::LiftGemmaReceipt {
            root,
            receipt,
            receiver,
        } => {
            let mut workspace = VariantWorkspace::open(&root).map_err(owner)?;
            returned(
                "workspace/lift-gemma-receipt",
                "lifted an actual complete excitation receipt through Soulkiller and founded generation 0 without foreign execution",
                workspace
                    .lift_gemma_receipt(&receipt, ReceiverId(receiver))
                    .map_err(owner)?,
            )
        }
        WorkspaceCommand::ImportSnapshot { root, snapshot } => {
            let mut workspace = VariantWorkspace::open(&root).map_err(owner)?;
            returned(
                "workspace/import-snapshot",
                "imported one valid native circulation snapshot as the current variant",
                workspace.import_snapshot(&snapshot).map_err(owner)?,
            )
        }
        WorkspaceCommand::DefineExperiment {
            root,
            name,
            ingress,
            receiver,
        } => {
            let mut workspace = VariantWorkspace::open(&root).map_err(owner)?;
            returned(
                "workspace/define-experiment",
                "stored one resolved native ingress and receiver experiment",
                workspace
                    .define_experiment(name, ingress, receiver.map(ReceiverId))
                    .map_err(owner)?,
            )
        }
        WorkspaceCommand::Conduct { root, experiment } => {
            let mut workspace = VariantWorkspace::open(&root).map_err(owner)?;
            returned(
                "workspace/conduct",
                "conducted the current variant and persisted its complete active boundary",
                workspace.conduct(&experiment).map_err(owner)?,
            )
        }
        WorkspaceCommand::Continue { root, successor } => {
            let mut workspace = VariantWorkspace::open(&root).map_err(owner)?;
            returned(
                "workspace/continue",
                "continued through one actual successor and persisted the next boundary",
                workspace.continue_active(successor).map_err(owner)?,
            )
        }
        WorkspaceCommand::StageReturn {
            root,
            occurrence,
            boundary,
            real,
            imaginary,
            storage,
        } => {
            let mut workspace = VariantWorkspace::open(&root).map_err(owner)?;
            returned(
                "workspace/stage-return",
                "persisted one explicit genuinely later return as an uncommitted cultivation candidate",
                workspace
                    .stage_return(
                        EventId(occurrence),
                        BoundaryId(boundary),
                        ExactComplexWaveCurrent::new(parse_rat(&real)?, parse_rat(&imaginary)?),
                        parse_rat(&storage)?,
                    )
                    .map_err(owner)?,
            )
        }
        WorkspaceCommand::Commit { root } => {
            let mut workspace = VariantWorkspace::open(&root).map_err(owner)?;
            returned(
                "workspace/commit",
                "committed the staged local return and advanced the current immutable snapshot",
                workspace.commit().map_err(owner)?,
            )
        }
        WorkspaceCommand::Decline { root } => {
            let mut workspace = VariantWorkspace::open(&root).map_err(owner)?;
            returned(
                "workspace/decline",
                "declined the active boundary and preserved the current snapshot byte-exactly",
                workspace.decline().map_err(owner)?,
            )
        }
        WorkspaceCommand::Evaluate { root, experiment } => {
            let mut workspace = VariantWorkspace::open(&root).map_err(owner)?;
            returned(
                "workspace/evaluate",
                "returned current, latest-withdrawn, and replay-restored conduct without changing the current variant",
                workspace.evaluate(&experiment).map_err(owner)?,
            )
        }
        WorkspaceCommand::Export { root, codec } => {
            let mut workspace = VariantWorkspace::open(&root).map_err(owner)?;
            returned(
                "workspace/export",
                "wrote an exact rested-inference export and explicit artifact receipt",
                workspace.export(export_codec(codec)).map_err(owner)?,
            )
        }
    }
}

fn returned<T: Serialize>(
    subject: &str,
    summary: &str,
    returned: WorkspaceReturn<T>,
) -> Result<AdapterReturn, WorkbenchError> {
    Ok(AdapterReturn::consequence(
        subject,
        summary,
        serde_json::to_value(returned).map_err(|error| WorkbenchError::Owner(error.to_string()))?,
    ))
}

fn export_codec(codec: ExportCodecArgument) -> ExportCodecKind {
    match codec {
        ExportCodecArgument::Onnx => ExportCodecKind::Onnx,
        ExportCodecArgument::Safetensors => ExportCodecKind::Safetensors,
    }
}

fn owner(error: impl std::fmt::Display) -> WorkbenchError {
    WorkbenchError::Owner(error.to_string())
}
