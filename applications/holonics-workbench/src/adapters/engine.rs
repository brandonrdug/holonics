use holonic_engine::cuda_refine::CudaRefineExecutor;
use life::native_intelligence::{
    export_morphology, ExportCodecKind, ExportPurpose, MorphologyExportRequest,
    MorphologyExportReturn, NativeCirculationSnapshot, NativeMorphologyPackage,
};
use serde_json::json;

use crate::adapters::AdapterReturn;
use crate::runtime::WorkbenchError;
use crate::store;
use crate::{EngineCommand, EventLevel, ExportCodecArgument};

pub fn status() -> AdapterReturn {
    let cpu_threads = std::thread::available_parallelism()
        .map(|threads| threads.get())
        .unwrap_or(1);
    let gpu = CudaRefineExecutor::new()
        .map(|card| {
            json!({
                "available": true,
                "device": card.device_name(),
                "block_threads": card.block_threads()
            })
        })
        .unwrap_or_else(|error| json!({"available": false, "obstruction": error.to_string()}));
    AdapterReturn::consequence(
        "engine/status",
        format!("observed {cpu_threads} CPU hardware thread(s) and the CUDA apparatus chart"),
        json!({
            "cpu_hardware_threads": cpu_threads,
            "gpu": gpu,
            "semantic_float_policy": "exact/no-float in the productive cone",
            "runtime": "consumer-workstation"
        }),
    )
}

pub fn capabilities() -> AdapterReturn {
    AdapterReturn {
        level: EventLevel::Information,
        subject: "workbench/capabilities".to_owned(),
        summary: "returned the callable workbench surface and explicit open fibres".to_owned(),
        payload: Some(json!({
            "implemented": {
                "workbench": ["demo", "structured-request", "session-lifecycle", "typed-receipts"],
                "athena": ["demo-open", "open", "inspect", "conduct", "continue", "return", "decline", "diffuse-demo", "snapshot", "export"],
                "eros": ["mouth", "atlas"],
                "soulkiller": ["inspect", "config", "index", "onnx"],
                "engine": ["status", "capabilities", "package", "export"],
                "presentation": ["cli-human", "cli-json-envelope", "cli-jsonl-events", "ratatui-guided"]
            },
            "open": [
                "unrestricted Soulkiller dismantling from arbitrary model directories",
                "qualitative language/image/audio generation",
                "general engine plugin discovery",
                "multi-instance distributed ecology control"
            ]
        })),
    }
}

pub fn execute(command: EngineCommand) -> Result<AdapterReturn, WorkbenchError> {
    match command {
        EngineCommand::Package { path } => {
            let package = read_package(&path)?;
            Ok(AdapterReturn::consequence(
                "engine/package",
                format!(
                    "read generation {} package with {} native state(s), {} thread(s), and {} open obligation(s)",
                    package.manifest.lineage.generation,
                    package.manifest.anatomy.native_population,
                    package.manifest.anatomy.thread_population,
                    package.manifest.anatomy.open_obligation_population
                ),
                serde_json::to_value(&package.manifest)
                    .map_err(|error| WorkbenchError::Owner(error.to_string()))?,
            ))
        }
        EngineCommand::Export {
            package,
            codec,
            path,
        } => {
            let package_value = read_package(&package)?;
            let returned = export_morphology(
                &package_value,
                MorphologyExportRequest {
                    codec: export_codec(codec),
                    receiver_family: package_value
                        .manifest
                        .receiver_capability
                        .native_receiver_family
                        .clone(),
                    purpose: ExportPurpose::RestedInference,
                },
            )
            .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
            let MorphologyExportReturn::Exact(exact) = returned else {
                return Err(WorkbenchError::Owner(format!(
                    "engine export returned {returned:?}"
                )));
            };
            store::write(&path, &exact.artifact.bytes)?;
            Ok(AdapterReturn::consequence(
                "engine/export",
                format!(
                    "exported {} as {:?} to {} with exact package round trip",
                    package.display(),
                    exact.artifact.codec,
                    path.display()
                ),
                serde_json::to_value(exact)
                    .map_err(|error| WorkbenchError::Owner(error.to_string()))?,
            ))
        }
    }
}

fn read_package(path: &std::path::Path) -> Result<NativeMorphologyPackage, WorkbenchError> {
    let bytes = store::read(path)?;
    if let Ok(package) = NativeMorphologyPackage::read(&bytes) {
        return Ok(package);
    }
    let snapshot = NativeCirculationSnapshot::read(&bytes)
        .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
    NativeMorphologyPackage::read(&snapshot.package_wire)
        .map_err(|error| WorkbenchError::Owner(error.to_string()))
}

fn export_codec(codec: ExportCodecArgument) -> ExportCodecKind {
    match codec {
        ExportCodecArgument::Onnx => ExportCodecKind::Onnx,
        ExportCodecArgument::Safetensors => ExportCodecKind::Safetensors,
    }
}
