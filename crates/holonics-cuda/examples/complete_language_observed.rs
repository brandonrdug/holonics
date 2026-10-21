//! CUDA-owned adapter of the unchanged complete-language exterior, with no fallback.
#![allow(dead_code, clippy::disallowed_methods, clippy::disallowed_types)]

#[path = "complete_language_observed/dispatch.rs"]
mod dispatch;
#[path = "../../holonics/examples/solenoidal_alpha.rs"]
mod exterior;

use exterior::{CompleteLanguageTrainingBackend, run_complete_language_with_execution};
use holonics::hnn::reference::observed::HostObservedEpochExecution;
use holonics_cuda::hnn::ObservedEpochDevice;
use std::error::Error;
use std::io::Write;
use std::path::Path;

fn run(args: &[String]) -> Result<(), Box<dyn Error>> {
    if args.first().map(String::as_str) != Some("complete-language") {
        return Err("requires complete-language and an explicit backend".into());
    }
    let command = args.get(1).ok_or("missing command")?;
    match args.get(2).map(String::as_str) {
        Some("host-reference") => run_complete_language_with_execution(
            &args[1..], &HostObservedEpochExecution, CompleteLanguageTrainingBackend::HostReference),
        Some("cuda-observed-epoch-device0") if matches!(command.as_str(),"train-retained-fibre-v1"|"train-local-retained-fibre-v1"|"train-prepared-local-retained-fibre-v1"|"train-prepared-local-retained-held-v1"|"train-source-framing-retained-held-v1") => {
            // Opening failure propagates before data access or output creation. No host retry.
            let execution = dispatch::TracedCard::new(ObservedEpochDevice::open(0)?);
            let result = run_complete_language_with_execution(
                &args[1..], &execution, CompleteLanguageTrainingBackend::CudaObservedEpochDevice0);
            let result = result.and_then(|()| execution.require_actual_dispatch().map_err(Into::into));
            if let Some(out) = args.get(10).map(Path::new).filter(|p| p.is_dir()) {
                let mut file = std::fs::OpenOptions::new().write(true).create_new(true)
                    .open(out.join("CUDA_EXECUTION.json"))?;
                file.write_all(execution.receipt(result.is_ok()).as_bytes())?;
                file.sync_all()?;
            }
            result
        }
        _ => Err("explicit host-reference or RetainedFibreV1 cuda-observed-epoch-device0 required; no fallback".into()),
    }
}
fn main() {
    if let Err(error) = run(&std::env::args().skip(1).collect::<Vec<_>>()) {
        eprintln!("complete-language adapter error: {error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
#[path = "complete_language_observed/controls.rs"]
mod controls;

#[cfg(test)]
#[path = "complete_language_observed/refusal_control.rs"]
mod refusal_control;
