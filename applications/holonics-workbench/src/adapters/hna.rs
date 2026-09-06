//! Consumer application adapters; the native session owns training/inference recurrence.
use std::path::Path;

use holonics::hna::{
    inspect_native_restricted_rest,
    native::{run_wave_control, WaveControlSpec},
    run_hna, AthenaTokenApplication, HnaCultivationAperture, HnaOccurrence, HnaRunReceipt,
    HnaRunRequest, HnaSource,
};
use serde_json::json;

use super::AdapterReturn;
use crate::{HnaCommand, WorkbenchError};

fn owner(error: impl std::fmt::Display) -> WorkbenchError {
    WorkbenchError::Owner(error.to_string())
}

pub fn execute(command: HnaCommand) -> Result<AdapterReturn, WorkbenchError> {
    match command {
        HnaCommand::Session { .. } => Err(owner("streaming HNA sessions require the process stream entry point or holonics::hna::HnaStream, not a batch response collector")),
        HnaCommand::NativeSession { .. } => Err(owner("native streaming sessions require the process stream entry point or holonics::hna::HnaStream, not a batch response collector")),
        HnaCommand::WaveControl { spec } => {
            let bytes = std::fs::read(&spec).map_err(owner)?;
            let spec: WaveControlSpec = serde_json::from_slice(&bytes).map_err(owner)?;
            let result = run_wave_control(&spec).map_err(owner)?;
            let payload = serde_json::to_value(&result).map_err(owner)?;
            let mut returned=AdapterReturn::consequence(
                "hna/wave-control",
                "Ran the declared native wave-control specification",
                payload,
            );
            if result.interruption.is_some() {
                returned.level=crate::EventLevel::Obstruction;
                returned.summary="Native wave control interrupted; actual exterior consequences are retained in the report".into();
            }
            Ok(returned)
        }
        HnaCommand::Run { request } => {
            let bytes = std::fs::read(&request).map_err(owner)?;
            let request: HnaRunRequest = serde_json::from_slice(&bytes).map_err(owner)?;
            let result = run_hna(request).map_err(owner)?;
            Ok(returned(result, None))
        }
        HnaCommand::Inspect { rest } => {
            let result = inspect_native_restricted_rest(&rest).map_err(owner)?;
            Ok(AdapterReturn::consequence(
                "hna/inspect",
                "Read the native restricted-rest header",
                json!(result),
            ))
        }
        HnaCommand::Infer { model, text } => run_text(&model, vec![text], None),
        HnaCommand::Train {
            model,
            sequence,
            learning_shift,
            series_terms,
        } => {
            let texts: Vec<String> =
                serde_json::from_slice(&std::fs::read(sequence).map_err(owner)?).map_err(owner)?;
            run_text(
                &model,
                texts,
                Some(HnaCultivationAperture {
                    learning_shift,
                    series_terms,
                }),
            )
        }
    }
}

fn run_text(
    model: &Path,
    texts: Vec<String>,
    cultivation: Option<HnaCultivationAperture>,
) -> Result<AdapterReturn, WorkbenchError> {
    if texts.is_empty() || texts.iter().any(|text| text.is_empty()) {
        return Err(owner("provide non-empty text occurrences"));
    }
    let codec = AthenaTokenApplication::open(model).map_err(owner)?;
    let occurrences = texts
        .iter()
        .map(|text| {
            codec
                .encode(text)
                .map(|row_addresses| HnaOccurrence {
                    row_addresses,
                    history: Vec::new(),
                })
                .map_err(owner)
        })
        .collect::<Result<Vec<_>, _>>()?;
    if cultivation.is_some() {
        validate_developmental_sequence(&occurrences)?;
    }
    let result = run_hna(HnaRunRequest {
        source: HnaSource::ResidentOperatorDirectory {
            root: model.to_owned(),
        },
        receiver: "terminal-face".into(),
        occurrences,
        cultivation,
        include_trace: false,
    })
    .map_err(owner)?;
    let text = result
        .cycles
        .iter()
        .map(|cycle| {
            codec
                .decode_addresses(&[cycle.selected_face.selected])
                .map_err(owner)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(returned(result, Some(text)))
}

fn validate_developmental_sequence(occurrences: &[HnaOccurrence]) -> Result<(), WorkbenchError> {
    if occurrences.len() < 2
        || occurrences.windows(2).any(|pair| {
            let (before, after) = (&pair[0].row_addresses, &pair[1].row_addresses);
            after.len() <= before.len() || !after.starts_with(before)
        })
    {
        return Err(owner(
            "current HNA training needs at least two strictly extending tokenized prefixes; provide one continuing sequence",
        ));
    }
    Ok(())
}

fn returned(result: HnaRunReceipt, text: Option<Vec<String>>) -> AdapterReturn {
    let faces = text
        .as_ref()
        .map(|words| format!("; selected text: {words:?}"))
        .unwrap_or_default();
    AdapterReturn::consequence(
        "hna/run",
        format!(
            "Completed {} native cycles at generation {}{}; run receipt, not a saved model",
            result.cycles.len(),
            result.final_generation,
            faces,
        ),
        json!({"artifact_kind": "hna-run-receipt", "selected_text": text, "value": result}),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn occurrence(row_addresses: Vec<u32>) -> HnaOccurrence {
        HnaOccurrence {
            row_addresses,
            history: vec![],
        }
    }

    #[test]
    fn training_rejects_unrelated_or_nonextending_sequences_before_cuda() {
        assert!(validate_developmental_sequence(&[occurrence(vec![1])]).is_err());
        assert!(
            validate_developmental_sequence(&[occurrence(vec![1]), occurrence(vec![2, 3])])
                .is_err()
        );
        assert!(
            validate_developmental_sequence(&[occurrence(vec![1]), occurrence(vec![1])]).is_err()
        );
        assert!(
            validate_developmental_sequence(&[occurrence(vec![1]), occurrence(vec![1, 2])]).is_ok()
        );
    }

    #[test]
    fn cli_exposes_native_run_and_typed_training_apertures() {
        let invocation = crate::parse_cli([
            "holonics",
            "hna",
            "train",
            "model",
            "sequence.json",
            "--learning-shift",
            "12",
        ])
        .unwrap();
        assert!(matches!(
            invocation.command,
            Some(crate::WorkbenchCommand::Hna(HnaCommand::Train {
                learning_shift: 12,
                ..
            }))
        ));
    }
}
