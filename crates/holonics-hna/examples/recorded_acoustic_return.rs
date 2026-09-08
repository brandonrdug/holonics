//! Actual recorded excitation/receiver evidence against an explicit initial unit response.
//! This returns the complete temporal defect; it does not fit or certify a room model.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::ResidentConstitutiveCurrent,
    phase_current::{
        resident::{
            compare_resident, convolve_resident, return_response_resident, ResidentPhaseCurrentView,
        },
        PhaseCurrentLineageId, PhaseCurrentReceiverId,
    },
    resident_section::{ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface},
    ExactComplexWaveCurrent,
};
use holonics_hna::native::acoustic_field::AcousticFieldChart;
use life::{
    mathematical_source::ExactAcousticOccurrence,
    native_intelligence::NativeAcousticTemporalPcm16Projection,
};
use num_rational::BigRational as Rat;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{
    error::Error,
    fs::{self, OpenOptions},
    io::Write,
    path::{Path, PathBuf},
    time::Instant,
};

type Result<T> = std::result::Result<T, Box<dyn Error>>;
const DIVISOR: i64 = 32768;
const PHASE_EXTENT: usize = 4;

fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = OpenOptions::new().write(true).create_new(true).open(path)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    Ok(())
}
fn stage<T>(
    s: &ResidentSurface<'_>,
    report: &mut Value,
    name: &str,
    f: impl FnOnce() -> Result<T>,
) -> Result<T> {
    let before = s.census();
    #[cfg(target_os = "macos")]
    let gpu_before = s.metal_execution_timing();
    let started = Instant::now();
    let result = f();
    let after = s.census();
    report["stages"][name] = json!({
        "seconds":started.elapsed().as_secs_f64(),
        "section_readouts":after.section_read_outs-before.section_read_outs,
        "numerical_egress_octets":after.egress_section_octets-before.egress_section_octets,
        "ingress_octets":after.ingress_octets-before.ingress_octets,
        "receipt_egress_octets":after.egress_receipt_octets-before.egress_receipt_octets,
        "deeds":after.deed_launches-before.deed_launches,
        "allocations":after.allocations-before.allocations,
        "resident_octets_now":after.resident_octets_now,
        "resident_octets_peak":after.resident_octets_peak
    });
    #[cfg(target_os = "macos")]
    {
        let gpu_after = s.metal_execution_timing();
        report["stages"][name]["gpu_seconds"] =
            json!(gpu_after.gpu_seconds - gpu_before.gpu_seconds);
        report["stages"][name]["unavailable_gpu_timestamps"] =
            json!(gpu_after.unavailable_timestamps - gpu_before.unavailable_timestamps);
    }
    result
}
fn source_report(source: &ExactAcousticOccurrence) -> Value {
    json!({"path":source.locator,"sha256":source.source_sha256,"octets":source.source_octets,
        "occurrence":source.occurrence,"sample_rate":source.sample_rate,"frames":source.samples.len(),"origin":"0"})
}
fn publish(
    s: &ResidentSurface<'_>,
    section: &ResidentSection<'_>,
    view: ResidentPhaseCurrentView<'_, '_>,
    directory: &Path,
    name: &str,
    rate: u32,
    audio: bool,
) -> Result<Value> {
    let rest = s.detach_section(section, 64)?;
    let bytes = rest.canonical_bytes()?;
    let path = directory.join(format!("{name}.section"));
    write_new(&path, &bytes)?;
    let mut report = json!({"section_path":path,"section_sha256":format!("{:x}",Sha256::digest(&bytes)),
        "section_octets":bytes.len(),"frames":view.raw_extent(),"origin":view.origin().to_string(),
        "sample_step":view.sample_step().to_string(),"receiver":view.receiver().0,"lineage":view.lineage().0});
    if audio {
        if rest.intervals.iter().any(|(a, b)| a != b) || rest.intervals.last().unwrap().0 <= 0 {
            return Err("terminal section is not an exact rational point".into());
        }
        let denominator = rest.intervals.last().unwrap().0;
        let coordinates: Vec<_> = rest.intervals[..rest.intervals.len() - 1]
            .chunks_exact(2)
            .map(|p| {
                ExactComplexWaveCurrent::new(
                    Rat::new(p[0].0.into(), denominator.into()),
                    Rat::new(p[1].0.into(), denominator.into()),
                )
            })
            .collect();
        let projection = NativeAcousticTemporalPcm16Projection::found(
            view.receiver(),
            view.lineage(),
            view.origin().clone(),
            view.sample_step().clone(),
            rate,
            Rat::from_integer(DIVISOR.into()),
            &coordinates,
        )?;
        let wav = projection.wav_bytes()?;
        let wav_path = directory.join(format!("{name}.wav"));
        write_new(&wav_path, &wav)?;
        report["wav_path"] = json!(wav_path);
        report["wav_sha256"] = json!(format!("{:x}", Sha256::digest(&wav)));
        report["pcm_gain"] = json!(DIVISOR);
        report["clipped_sample_population"] = json!(projection.clipped_sample_population);
        report["projection_fibre"] = json!("the complete exact section is retained; remainder = current * gain - PCM at each timed quadrature");
    }
    Ok(report)
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).map(PathBuf::from).collect();
    if args.len() != 4 {
        return Err("usage: recorded_acoustic_return EXCITATION_PCM16.wav OBSERVED_PCM16.wav NEW_REPORT.json NEW_OUTPUT_DIRECTORY".into());
    }
    let [excitation_path, observation_path, report_path, directory] = args.as_slice() else {
        unreachable!()
    };
    if report_path.exists() || directory.exists() {
        return Err("output report and directory must be new".into());
    }
    let started = Instant::now();
    let excitation = ExactAcousticOccurrence::read(
        excitation_path,
        "recorded-excitation",
        4096,
        4096,
        PHASE_EXTENT,
    )?;
    let observation = ExactAcousticOccurrence::read(
        observation_path,
        "recorded-microphone-return",
        4096,
        4096,
        PHASE_EXTENT,
    )?;
    if excitation.sample_rate != observation.sample_rate {
        return Err("the supplied raw recordings do not share one sample clock".into());
    }
    let rate = excitation.sample_rate;
    let chart = |source: &ExactAcousticOccurrence, receiver, lineage| {
        AcousticFieldChart::from_acoustic(
            source,
            PhaseCurrentReceiverId(receiver),
            PhaseCurrentLineageId(lineage),
            Rat::from_integer(0.into()),
            PHASE_EXTENT,
            DIVISOR,
        )
    };
    let source_chart = chart(&excitation, 1, 1)?;
    let observed_chart = chart(&observation, 9, 2)?;
    let mut report = json!({"schema":"holonics.recorded-acoustic-return.v2","status":"running",
        "excitation":source_report(&excitation),"observation":source_report(&observation),
        "clock_contract":"caller supplies simultaneously recorded raw channels with common origin; no delay alignment or resampling",
        "initial_response":{"real":1,"imaginary":0,"denominator":1,"origin":"0","extent":1},
        "initial_response_scope":"explicit unit digital starting current, not a measured room transfer or cultivated model",
        "phase_extent":PHASE_EXTENT,"divisor":DIVISOR,"stages":{},"generator_developed":false,
        "native_development":"none; this receiver retains the actual defect for subsequent constitutive contact",
        "response_return_scope":"resident response adjoint returned in the original unit-response chart; no PCM rendering and no developed room model"});
    fs::create_dir_all(directory)?;
    let readout = ResidentReadout::new()?;
    let s = ResidentSurface::on(&readout)?;
    report["device"] = json!(s.device_name());
    let source = stage(&s, &mut report, "mount_excitation", || {
        Ok(source_chart.mount_complete(&s)?)
    })?;
    let initial = stage(&s, &mut report, "mount_initial_response", || {
        Ok(s.mount_section_rest(&ResidentSectionRest::found(
            1,
            3,
            ResidentGrain(0),
            64,
            vec![(1, 1), (0, 0), (1, 1)],
        )?)?)
    })?;
    let prediction = stage(&s, &mut report, "predict_before_reception", || {
        let response = ResidentPhaseCurrentView::new(
            ResidentConstitutiveCurrent::rational(&initial)?,
            PhaseCurrentReceiverId(8),
            PhaseCurrentLineageId(3),
            Rat::from_integer(0.into()),
            Rat::new(1.into(), rate.into()),
            PHASE_EXTENT as u32,
            1,
        )?;
        Ok(convolve_resident(
            &s,
            source.temporal_view()?,
            response,
            PhaseCurrentReceiverId(9),
            PhaseCurrentLineageId(4),
        )?)
    })?;
    let observed = stage(&s, &mut report, "mount_observed_return", || {
        Ok(observed_chart.mount_complete(&s)?)
    })?;
    let difference = stage(&s, &mut report, "native_oriented_return", || {
        Ok(compare_resident(
            &s,
            prediction.view()?,
            observed.temporal_view()?,
            PhaseCurrentLineageId(5),
        )?)
    })?;
    let response_return = stage(&s, &mut report, "resident_response_adjoint", || {
        Ok(return_response_resident(
            &s,
            &prediction,
            &difference,
            PhaseCurrentLineageId(6),
        )?)
    })?;
    report["support"] = json!(difference.support());
    report["prediction"] = stage(&s, &mut report, "cold_prediction", || {
        publish(
            &s,
            prediction.section(),
            prediction.view()?,
            directory,
            "prediction",
            rate,
            false,
        )
    })?;
    report["difference"] = stage(&s, &mut report, "cold_difference_and_audio", || {
        publish(
            &s,
            difference.section(),
            difference.view()?,
            directory,
            "difference",
            rate,
            true,
        )
    })?;
    report["response_return"] = stage(&s, &mut report, "cold_response_return", || {
        publish(
            &s,
            response_return.section(),
            response_return.view()?,
            directory,
            "response_return",
            rate,
            false,
        )
    })?;
    report["seconds"] = json!(started.elapsed().as_secs_f64());
    report["status"] = json!("returned");
    write_new(report_path, &serde_json::to_vec_pretty(&report)?)?;
    println!(
        "{}",
        serde_json::to_string(
            &json!({"status":"returned","report":report_path,"seconds":report["seconds"]})
        )?
    );
    Ok(())
}
