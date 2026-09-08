//! Recorded acoustic temporal contact over an explicit unit impulse response.
//!
//! This driver supplies the native temporal owner with complete recorded source/receiver
//! sections.  It reports the measured affine return and successor chronology; it does not claim
//! a room model, a language model, or semantic usefulness.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, ResidentTemporalConditionCurrent, ResidentTemporalConditionPreimage,
    },
    phase_current::{PhaseCurrentLineageId, PhaseCurrentReceiverId},
    resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface, TransferCensus},
};
use holonics_hna::native::acoustic_field::AcousticFieldChart;
use life::mathematical_source::ExactAcousticOccurrence;
use num_rational::BigRational as Rat;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    error::Error,
    fs::{self, OpenOptions},
    io::Write,
    path::{Path, PathBuf},
    time::Instant,
};

type Result<T> = std::result::Result<T, Box<dyn Error>>;
const PHASE_EXTENT: usize = 4;
const DIVISOR: i64 = 32768;

fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = OpenOptions::new().write(true).create_new(true).open(path)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    Ok(())
}

fn work(before: &TransferCensus, after: &TransferCensus, seconds: f64) -> Value {
    json!({
        "seconds": seconds,
        "section_readouts": after.section_read_outs - before.section_read_outs,
        "numerical_egress_octets": after.egress_section_octets - before.egress_section_octets,
        "ingress_octets": after.ingress_octets - before.ingress_octets,
        "receipt_egress_octets": after.egress_receipt_octets - before.egress_receipt_octets,
        "deeds": after.deed_launches - before.deed_launches,
        "allocations": after.allocations - before.allocations,
        "resident_octets_now": after.resident_octets_now,
        "resident_octets_peak": after.resident_octets_peak
    })
}

fn stage<T>(
    surface: &ResidentSurface<'_>,
    report: &mut Value,
    name: &str,
    action: impl FnOnce() -> Result<T>,
) -> Result<T> {
    report["active_stage"] = json!(name);
    eprintln!("{}", json!({"stage":name,"status":"started"}));
    let before = surface.census();
    #[cfg(target_os = "macos")]
    let gpu_before = surface.metal_execution_timing();
    let started = Instant::now();
    let result = action();
    report["stages"][name] = work(&before, &surface.census(), started.elapsed().as_secs_f64());
    #[cfg(target_os = "macos")]
    {
        let gpu_after = surface.metal_execution_timing();
        report["stages"][name]["gpu_seconds"] =
            json!(gpu_after.gpu_seconds - gpu_before.gpu_seconds);
        report["stages"][name]["unavailable_gpu_timestamps"] =
            json!(gpu_after.unavailable_timestamps - gpu_before.unavailable_timestamps);
    }
    eprintln!(
        "{}",
        json!({"stage":name,"status":if result.is_ok(){"returned"}else{"refused"},"seconds":report["stages"][name]["seconds"]})
    );
    result
}

fn occurrence_report(source: &ExactAcousticOccurrence) -> Value {
    json!({
        "path": source.locator,
        "sha256": source.source_sha256,
        "octets": source.source_octets,
        "occurrence": source.occurrence,
        "sample_rate": source.sample_rate,
        "frames": source.samples.len()
    })
}

fn complex_values(values: &[holonic_engine::ExactComplexWaveCurrent]) -> Vec<Value> {
    values
        .iter()
        .map(|value| json!({"real": value.real.to_string(), "imaginary": value.imaginary.to_string()}))
        .collect()
}

fn publish_section(
    surface: &ResidentSurface<'_>,
    section: &holonic_engine::resident_section::ResidentSection<'_>,
    directory: &Path,
    name: &str,
    metadata: Value,
) -> Result<Value> {
    let rest = surface.detach_section(section, 64)?;
    let bytes = rest.canonical_bytes()?;
    let path = directory.join(format!("{name}.section"));
    write_new(&path, &bytes)?;
    let mut result = metadata;
    result["section_path"] = json!(path);
    result["section_sha256"] = json!(format!("{:x}", Sha256::digest(&bytes)));
    result["section_octets"] = json!(bytes.len());
    result["section_wire"] = json!({
        "rows": rest.rows,
        "width": rest.width,
        "grain": rest.grain.0,
        "bound_octaves": rest.bound_octaves
    });
    Ok(result)
}

fn publish_view(
    surface: &ResidentSurface<'_>,
    view: holonic_engine::phase_current::resident::ResidentPhaseEnclosureView<'_, '_>,
    directory: &Path,
    name: &str,
) -> Result<Value> {
    publish_section(
        surface,
        view.section(),
        directory,
        name,
        json!({
            "receiver": view.receiver().0,
            "lineage": view.lineage().0,
            "origin": view.origin().to_string(),
            "sample_step": view.sample_step().to_string(),
            "phase_extent": view.phase_extent(),
            "raw_extent": view.raw_extent(),
            "wide_offset": view.wide_offset(),
            "grain": view.grain()
        }),
    )
}

fn unit_response<'c>(
    surface: &'c ResidentSurface<'c>,
    taps: usize,
) -> Result<holonic_engine::resident_section::ResidentSection<'c>> {
    let width = taps
        .checked_mul(2)
        .and_then(|n| n.checked_add(1))
        .ok_or("response aperture overflow")?;
    let mut intervals = Vec::with_capacity(width);
    for index in 0..taps {
        intervals.push(if index == 0 { (1, 1) } else { (0, 0) });
        intervals.push((0, 0));
    }
    intervals.push((1, 1));
    Ok(surface.mount_section_rest(&ResidentSectionRest::found(
        1,
        intervals.len(),
        ResidentGrain(0),
        64,
        intervals,
    )?)?)
}

fn support_value(
    support: &holonic_engine::phase_current::resident::PhaseComparisonSupport,
) -> Value {
    serde_json::to_value(support).expect("phase support is serializable")
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).map(PathBuf::from).collect();
    if args.len() < 6 || (args.len() - 4) % 2 != 0 {
        return Err("usage: recorded_acoustic_contact NEW_REPORT.json NEW_OUTPUT_DIRECTORY RESPONSE_TAPS GRAIN EXCITATION.wav OBSERVED.wav [EXCITATION.wav OBSERVED.wav ...]".into());
    }
    let report_path = &args[0];
    let output_directory = &args[1];
    let taps = args[2]
        .to_str()
        .ok_or("RESPONSE_TAPS is not UTF-8")?
        .parse::<usize>()?;
    let grain = args[3]
        .to_str()
        .ok_or("GRAIN is not UTF-8")?
        .parse::<u32>()?;
    if taps == 0 || !(1..=120).contains(&grain) || report_path.exists() || output_directory.exists()
    {
        return Err(
            "report/directory must be new; RESPONSE_TAPS and GRAIN must be positive and bounded"
                .into(),
        );
    }
    fs::create_dir(output_directory)?;
    let started = Instant::now();
    let readout = ResidentReadout::new()?;
    let surface = ResidentSurface::on(&readout)?;
    let mut report = json!({
        "device": surface.device_name(),
        "schema": "holonics.recorded-acoustic-contact.v1",
        "status": "running",
        "scope": "controlled digital temporal action over recorded PCM coefficients",
        "sound_model": false,
        "conversation_model": false,
        "learned_room": false,
        "native_response_changed": false,
        "native_response_change_claim": "the successor response is the actual result of the declared native temporal contact; no semantic or physical room interpretation is asserted",
        "response_control": {"taps": taps, "initial": "h[0]=1, all remaining taps=0", "grain": grain},
        "phase_extent": PHASE_EXTENT,
        "pcm_divisor": DIVISOR,
        "pairs": [],
        "stages": {}
    });
    let first_excitation = ExactAcousticOccurrence::read(
        &args[4],
        "recorded-acoustic-contact-excitation-0",
        4096,
        4096,
        PHASE_EXTENT,
    )?;
    let response_section = unit_response(&surface, taps)?;
    let first_rate = first_excitation.sample_rate;
    let response_chart =
        holonic_engine::native_ecology::constitutive_fibre::TemporalResponseChart {
            receiver: PhaseCurrentReceiverId(8),
            origin: Rat::from_integer(0.into()),
            sample_step: Rat::new(1.into(), first_rate.into()),
            phase_extent: PHASE_EXTENT as u32,
            raw_extent: taps,
        };
    let mut current = ResidentTemporalConditionCurrent::retain(
        &surface,
        response_section,
        response_chart,
        PhaseCurrentLineageId(3),
        grain,
        ConditionContactMetric::UnitAdmittanceRealification,
    )?;
    for pair in 0..(args.len() - 4) / 2 {
        let excitation_path = &args[4 + 2 * pair];
        let observed_path = &args[5 + 2 * pair];
        let excitation = if pair == 0 {
            first_excitation.clone()
        } else {
            ExactAcousticOccurrence::read(
                excitation_path,
                format!("recorded-acoustic-contact-excitation-{pair}"),
                4096,
                4096,
                PHASE_EXTENT,
            )?
        };
        let observed = ExactAcousticOccurrence::read(
            observed_path,
            format!("recorded-acoustic-contact-observed-{pair}"),
            4096,
            4096,
            PHASE_EXTENT,
        )?;
        if excitation.sample_rate != observed.sample_rate || excitation.sample_rate != first_rate {
            return Err("all supplied pairs must share one sample clock".into());
        }
        let source_chart = AcousticFieldChart::from_acoustic(
            &excitation,
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(10 + pair as u64 * 2),
            Rat::from_integer(0.into()),
            PHASE_EXTENT,
            DIVISOR,
        )?;
        let observed_chart = AcousticFieldChart::from_acoustic(
            &observed,
            PhaseCurrentReceiverId(9),
            PhaseCurrentLineageId(11 + pair as u64 * 2),
            Rat::from_integer(0.into()),
            PHASE_EXTENT,
            DIVISOR,
        )?;
        let mut pair_report = json!({
            "pair": pair,
            "excitation": occurrence_report(&excitation),
            "observation": occurrence_report(&observed),
            "chronology": {
                "pre_contact_cut": current.contacts(),
                "current_cut": current.contacts(),
                "successor_cut": current.contacts() + 1
            },
            "hot_zero_numerical_reads": null
        });
        let source = stage(
            &surface,
            &mut report,
            &format!("pair_{pair}_mount_source"),
            || Ok(source_chart.mount_complete(&surface)?),
        )?;
        let before = stage(
            &surface,
            &mut report,
            &format!("pair_{pair}_snapshot_current"),
            || Ok(current.snapshot()),
        )?;
        let prediction = stage(
            &surface,
            &mut report,
            &format!("pair_{pair}_predict_before_observation"),
            || {
                Ok(
                    holonic_engine::phase_current::resident::convolve_enclosed_resident(
                        &surface,
                        source.temporal_view()?,
                        before.view(),
                        PhaseCurrentReceiverId(9),
                        PhaseCurrentLineageId(20 + pair as u64 * 10),
                    )?,
                )
            },
        )?;
        let observed_section = stage(
            &surface,
            &mut report,
            &format!("pair_{pair}_mount_observation"),
            || Ok(observed_chart.mount_complete(&surface)?),
        )?;
        let difference = stage(
            &surface,
            &mut report,
            &format!("pair_{pair}_compare_observation"),
            || {
                Ok(
                    holonic_engine::phase_current::resident::compare_enclosed_resident(
                        &surface,
                        prediction.view(),
                        observed_section.temporal_view()?,
                        PhaseCurrentLineageId(21 + pair as u64 * 10),
                    )?,
                )
            },
        )?;
        pair_report["support"] = support_value(difference.support());
        let preimage =
            ResidentTemporalConditionPreimage::from_return(&before, &prediction, &difference)?;
        let contact = stage(
            &surface,
            &mut report,
            &format!("pair_{pair}_native_temporal_contact"),
            || Ok(current.contact(preimage, PhaseCurrentLineageId(22 + pair as u64 * 10))?),
        )?;
        let after = current.snapshot();
        pair_report["hot_zero_numerical_reads"] = json!(
            [
                format!("pair_{pair}_predict_before_observation"),
                format!("pair_{pair}_compare_observation"),
                format!("pair_{pair}_native_temporal_contact")
            ]
            .iter()
            .all(|name| report["stages"][name]["section_readouts"] == 0
                && report["stages"][name]["numerical_egress_octets"] == 0)
        );
        let reading = stage(
            &surface,
            &mut report,
            &format!("pair_{pair}_cold_successor_inspection"),
            || {
                let reading = after.inspect(&surface)?;
                if !after.view().inspect(&surface)?.contains(reading.response()) {
                    return Err(
                        "native response enclosure does not contain its exact cold construction"
                            .into(),
                    );
                }
                Ok(reading)
            },
        )?;
        pair_report["condition_reading"] = json!({
            "response": complex_values(reading.response()),
            "cold": true,
            "enclosure_contains_exact_current": true,
            "response_changed": reading.prior().is_some_and(|prior| prior != reading.response())
        });
        pair_report["prediction"] = stage(
            &surface,
            &mut report,
            &format!("pair_{pair}_cold_prediction"),
            || {
                publish_view(
                    &surface,
                    prediction.view(),
                    output_directory,
                    &format!("pair_{pair}_prediction"),
                )
            },
        )?;
        pair_report["difference"] = stage(
            &surface,
            &mut report,
            &format!("pair_{pair}_cold_difference"),
            || {
                publish_view(
                    &surface,
                    difference.view(),
                    output_directory,
                    &format!("pair_{pair}_difference"),
                )
            },
        )?;
        pair_report["unexplained"] = stage(
            &surface,
            &mut report,
            &format!("pair_{pair}_cold_unexplained"),
            || {
                publish_view(
                    &surface,
                    contact.unexplained(),
                    output_directory,
                    &format!("pair_{pair}_unexplained"),
                )
            },
        )?;
        pair_report["incoming_normal_e"] = stage(
            &surface,
            &mut report,
            &format!("pair_{pair}_cold_incoming_normal_e"),
            || {
                publish_view(
                    &surface,
                    contact.incoming_normal_e(),
                    output_directory,
                    &format!("pair_{pair}_incoming_normal_e"),
                )
            },
        )?;
        pair_report["returned_normal_e"] = stage(
            &surface,
            &mut report,
            &format!("pair_{pair}_cold_returned_normal_e"),
            || {
                let restricted = contact.returned_normal_e();
                let mut output = publish_view(
                    &surface,
                    restricted.full,
                    output_directory,
                    &format!("pair_{pair}_returned_normal_e"),
                )?;
                output["normal_support"] = json!(restricted.range);
                Ok(output)
            },
        )?;
        let contact_report = stage(
            &surface,
            &mut report,
            &format!("pair_{pair}_cold_contact_report"),
            || {
                publish_view(
                    &surface,
                    contact.successor(),
                    output_directory,
                    &format!("pair_{pair}_successor_response"),
                )
            },
        )?;
        pair_report["contact_report"] = contact_report.clone();
        pair_report["normal_leg_offsets"] = json!({
            "section_path": contact_report["section_path"].clone(),
            "section_sha256": contact_report["section_sha256"].clone(),
            "incoming_h": {"wide_offset": contact.incoming_normal_h().wide_offset(), "grain": contact.incoming_normal_h().grain()},
            "returned_h": {"wide_offset": contact.returned_normal_h().wide_offset(), "grain": contact.returned_normal_h().grain()},
            "difference_h": {"wide_offset": contact.difference_h().wide_offset(), "grain": contact.difference_h().grain()},
            "successor": {"wide_offset": contact.successor().wide_offset(), "grain": contact.successor().grain()}
        });
        report["pairs"].as_array_mut().unwrap().push(pair_report);
    }
    report["status"] = json!("returned");
    report["native_response_changed"] = json!(
        report["pairs"]
            .as_array()
            .unwrap()
            .iter()
            .any(|pair| pair["condition_reading"]["response_changed"] == true)
    );
    report["contacts"] = json!(current.contacts());
    report["elapsed_seconds"] = json!(started.elapsed().as_secs_f64());
    report["final_census"] = json!(surface.census());
    write_new(report_path, &serde_json::to_vec_pretty(&report)?)?;
    println!(
        "{}",
        json!({"status":"returned", "report":report_path, "contacts":current.contacts()})
    );
    Ok(())
}
