//! Consumer application adapters; the native session owns training/inference recurrence.
use holonics_hna::native::{
    resume_wave_control, run_wave_control, run_wave_control_with_options, WaveControlSpec,
    WaveRunOptions,
};

use super::AdapterReturn;
use crate::{HnaCommand, WorkbenchError};

fn owner(error: impl std::fmt::Display) -> WorkbenchError {
    WorkbenchError::Owner(error.to_string())
}

pub fn execute(command: HnaCommand) -> Result<AdapterReturn, WorkbenchError> {
    match command {
        HnaCommand::NativeSession { .. } => Err(owner("native streaming sessions require the process stream entry point or holonics_hna::HnaStream, not a batch response collector")),
        HnaCommand::MathematicalSession { .. } => Err(owner("mathematical streaming sessions require the process stream entry point or holonics_hna::HnaStream, not a batch response collector")),
        HnaCommand::WaveSession { .. } | HnaCommand::CoupledWaveSession { .. } => Err(owner("wave streaming sessions require the process stream entry point or holonics_hna::HnaStream, not a batch response collector")),
        HnaCommand::FieldSession { .. } => Err(owner("field streaming sessions require the process stream entry point or holonics_hna::HnaStream, not a batch response collector")),
        HnaCommand::WaveControl {
            source,
            resume,
            cycles,
            checkpoint,
        } => {
            let options = WaveRunOptions { cycles, checkpoint };
            if resume && options.checkpoint.is_none() {
                return Err(owner("resumed wave-control command requires a fresh checkpoint path"));
            }
            let result = if resume {
                resume_wave_control(&source, &options).map_err(owner)?
            } else if options.cycles.is_none() && options.checkpoint.is_none() {
                let bytes = std::fs::read(&source).map_err(owner)?;
                let spec: WaveControlSpec = serde_json::from_slice(&bytes).map_err(owner)?;
                run_wave_control(&spec).map_err(owner)?
            } else {
                let bytes = std::fs::read(&source).map_err(owner)?;
                let spec: WaveControlSpec = serde_json::from_slice(&bytes).map_err(owner)?;
                run_wave_control_with_options(&spec, &options).map_err(owner)?
            };
            let payload = serde_json::to_value(&result).map_err(owner)?;
            let mut returned=AdapterReturn::consequence(
                "hna/wave-control",
                "Ran the declared native wave-control operation",
                payload,
            );
            if result.interruption.is_some() || result.checkpoint_error.is_some() {
                returned.level=crate::EventLevel::Obstruction;
                returned.summary="Native wave control interrupted or failed to publish; actual consequences are retained in the report".into();
            }
            Ok(returned)
        }
    }
}
