//! A separate-process continuation of the declared recorded digital action. No calibration,
//! condition selection or received target is supplied here. This is persistence evidence,
//! not additional acoustic learning or a learned utterance-response law.
use super::*;

pub(super) fn run(args: &[String]) -> Result<()> {
    if args.len() != 5 {
        return Err(
            "usage: --continue CHECKPOINT WAV_PATH NEW_REPORT.json NEW_AUDIO_DIR NEW_CHECKPOINT"
                .into(),
        );
    }
    let checkpoint = Path::new(&args[0]);
    let wav = Path::new(&args[1]);
    let report_path = Path::new(&args[2]);
    let directory = Path::new(&args[3]);
    let next_checkpoint = Path::new(&args[4]);
    for path in [report_path, directory, next_checkpoint] {
        if path.exists() {
            return Err(format!("output already exists: {}", path.display()).into());
        }
    }
    let started = Instant::now();
    let saved = NativeSavedConditionalField::read(checkpoint)?;
    let mut application: Value = serde_json::from_slice(saved.application())?;
    if application["schema"] != "holonics.recorded-temporal-continuation.v1"
        || application["source_complex"] != WIDTH
        || application["response_complex"] != 2
        || application["phase_extent"] != WIDTH
        || application["pcm_divisor"] != DIVISOR
        || application["pcm_gain"] != PCM_GAIN
    {
        return Err("checkpoint has a different temporal application chart".into());
    }
    let recording = ExactAcousticOccurrence::read(
        wav,
        format!("recorded-temporal-continuation:{}", wav.display()),
        4096,
        4096,
        1,
    )?;
    if application["sample_rate"].as_u64() != Some(u64::from(recording.sample_rate)) {
        return Err("the saved digital response requires its original sample clock".into());
    }
    let completed = application["completed_recordings"]
        .as_u64()
        .ok_or("missing completed recording chronology")?
        .checked_add(1)
        .ok_or("recording chronology overflow")?;
    let readout = ResidentReadout::new()?;
    let s = ResidentSurface::on(&readout)?;
    let mut report = json!({"schema":"holonics.recorded-temporal-continuation.v1",
        "truth_status":"established-bounded","evidence_tags":["measured"],
        "scope":"persisted controlled digital action on a later recording; no new calibration or target",
        "predecessor_checkpoint":checkpoint,"predecessor_application":application,
        "source":{"path":wav,"sha256":recording.source_sha256,"octets":recording.source_octets,
            "samples":recording.samples.len(),"sample_rate":recording.sample_rate,
            "occurrence":recording.occurrence,"receiver":1,"lineage":completed},
        "stages":{},"sound_model":false,"conversation_model":false});
    let (mut body, held, mut field, mut sources, anchors, stream, _) =
        stage(&s, &mut report, "cold_remount", || Ok(saved.remount(&s)?))?;
    if sources.len() != 1 || sources[0].is_none() || !anchors.is_empty() {
        return Err("checkpoint must carry its one continuing field source".into());
    }
    let before_occurrences = body.occurrences();
    let before_contacts = held.contacts();
    let before_field = field.occurrence_count();
    let chart = AcousticFieldChart::from_acoustic(
        &recording,
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(completed),
        Rat::from_integer(0.into()),
        WIDTH,
        DIVISOR,
    )?;
    fs::create_dir(directory)?;
    let directory = directory.canonicalize()?;

    // The first complete four-coefficient aperture is an explicit small receiver comparison,
    // not native grain or a sample recurrence. The complete waveform action below uses all PCM.
    let (prediction, next_source, lineage) =
        stage(&s, &mut report, "resident_relation_and_field", || {
            let cell = chart.mount_cell(&s, 0)?;
            let prediction =
                body.advance_bilinear_contact(cell.rational()?, held.current(), None)?;
            let mut occurrence =
                NativeFieldOccurrence::through(sources[0].take().unwrap(), Vec::new());
            let emitted = field.advance_current_resident(&mut occurrence, prediction.current())?;
            Ok((prediction, emitted.source, emitted.lineage))
        })?;
    let complete = stage(&s, &mut report, "whole_recording_mount", || {
        Ok(chart.mount_complete(&s)?)
    })?;
    let output = stage(
        &s,
        &mut report,
        "whole_recording_successor_condition",
        || {
            Ok(convolve_resident(
                &s,
                complete.temporal_view()?,
                ResidentPhaseCurrentView::new(
                    held.current(),
                    PhaseCurrentReceiverId(2),
                    PhaseCurrentLineageId(completed),
                    Rat::from_integer(0.into()),
                    chart.section().sample_step.clone(),
                    WIDTH as u32,
                    2,
                )?,
                PhaseCurrentReceiverId(5),
                PhaseCurrentLineageId(completed),
            )?)
        },
    )?;
    report["whole_recording"] = stage(&s, &mut report, "cold_terminal_receiver", || {
        Ok(
            json!({"source_raw_extent":chart.section().raw_extent(),"response_raw_extent":2,
            "output_raw_extent":chart.section().raw_extent()+1,"gain":PCM_GAIN.to_string(),
            "successor_condition":publish_temporal(&s, &output, &directory,
                "successor-condition", recording.sample_rate)?}),
        )
    })?;
    report["native_field"] = json!({"prior_occurrences":before_field,
        "occurrences":field.occurrence_count(),"lineage":lineage});
    report["relation"] = json!({"prior_occurrences":before_occurrences,
        "occurrences":body.occurrences(),"prior_contacts":before_contacts,"contacts":held.contacts(),
        "received_targets":0});
    report["bounded_prediction"] = stage(&s, &mut report, "cold_prediction_receiver", || {
        returned(&prediction)
    })?;
    application["completed_recordings"] = json!(completed);
    application["last_source"] = report["source"].clone();
    let receipt = stage(&s, &mut report, "cold_checkpoint", || {
        Ok(save_conditional_checkpoint(
            next_checkpoint,
            &body,
            &held,
            &field,
            &[Some(&next_source)],
            &[],
            &stream,
            &serde_json::to_vec(&application)?,
        )?)
    })?;
    report["checkpoint"] = json!({"path":receipt.path,"octets":receipt.bytes});
    report["elapsed_seconds"] = json!(started.elapsed().as_secs_f64());
    report["final_census"] = json!(s.census());
    write_new(report_path, &serde_json::to_vec_pretty(&report)?)?;
    println!(
        "{}",
        json!({"report":report_path,"checkpoint":next_checkpoint,
        "completed_recordings":completed,"received_targets":0})
    );
    Ok(())
}
