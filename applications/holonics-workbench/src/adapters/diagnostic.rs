use holonic_engine::cuda_refine::CudaRefineExecutor;
use serde_json::json;

use crate::adapters::AdapterReturn;
use crate::EventLevel;

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
        "workbench/status",
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
        summary: "returned the callable workbench surface".to_owned(),
        payload: Some(json!({
            "implemented": {
                "hna": ["run", "inspect", "infer", "train", "session", "native-session",
                        "mathematical-session", "wave-session", "coupled-wave-session",
                        "field-session", "wave-control"],
                "diagnostic": {
                    "soulkiller": ["inspect", "config", "index", "onnx"],
                    "workbench": ["status", "capabilities"]
                },
                "presentation": ["cli-human", "cli-json-envelope", "cli-jsonl-events"]
            }
        })),
    }
}
