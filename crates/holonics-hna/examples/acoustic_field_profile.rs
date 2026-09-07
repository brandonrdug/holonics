//! Profile complete recorded temporal sections through the shared native field.
//! This receiver measures the declared material chart; it does not grade sound/language learning.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{NativeConstitutiveField, NativeFieldReceiverStatus},
    phase_current::{PhaseCurrentLineageId, PhaseCurrentReceiverId},
    resident_section::ResidentSurface,
};
use holonics_hna::native::{acoustic_field::AcousticFieldChart, NativeModelSpec};
use life::mathematical_source::ExactAcousticOccurrence;
use serde_json::json;
use std::{env, fs, time::Instant};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    if args.len() < 2 {
        return Err("usage: acoustic_field_profile SEED WAV [WAV ...]".into());
    }
    let spec = NativeModelSpec::read(&fs::read(&args[0])?)?;
    let mount_started = Instant::now();
    let readout = ResidentReadout::new()?;
    let surface = ResidentSurface::on(&readout)?;
    let mut field = NativeConstitutiveField::found(&surface, spec.material()?)?;
    let mount_ns = mount_started.elapsed().as_nanos();
    for (source_index, path) in args[1..].iter().enumerate() {
        let cold_started = Instant::now();
        let bytes = fs::read(path)?;
        let source = ExactAcousticOccurrence::from_wav_bytes(
            &bytes,
            format!("acoustic-field-source:{source_index}"),
            path,
            4096,
            4096,
            1,
        )?;
        let mut chart = AcousticFieldChart::from_acoustic(
            &source,
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(source_index as u64),
            num_rational::BigRational::from_integer(0.into()),
            field.nodes(),
            32768,
        )?;
        let cold_ns = cold_started.elapsed().as_nanos();
        let start = field.occurrence_count();
        let before = field.census();
        #[cfg(target_os = "macos")]
        let timing_before = surface.metal_execution_timing();
        let mut latency = Vec::new();
        let mut counts = [0u64; 3];
        let mut first = None;
        let mut last = None;
        let mut failure = None;
        let started = Instant::now();
        while !chart.is_complete() {
            let tick = Instant::now();
            // Recorded time adjacency is not a receiving interaction. No source handle is
            // fabricated or attached here. The SAME held field continues across all inputs.
            match chart.advance_status(&mut field, &mut None) {
                Ok((support, step)) => {
                    latency.push(tick.elapsed().as_nanos());
                    counts[match step.receiver {
                        NativeFieldReceiverStatus::Unique => 0,
                        NativeFieldReceiverStatus::OutsideDomain => 1,
                        NativeFieldReceiverStatus::Plural => 2,
                    }] += 1;
                    // Inspect the product at the two declared boundaries. Intermediate full
                    // sources remain in the native owner; the profiler does not duplicate them.
                    if first.is_none() || chart.is_complete() {
                        let observed = json!({"support":support,"lineage":step.lineage,
                        "outgoing":step.outgoing,"held_successor":step.held_successor,
                        "receiver":step.receiver,"formed_pivot":step.formed_pivot,
                        "successor_rank":step.successor_rank});
                        if first.is_none() {
                            first = Some(observed.clone());
                        }
                        last = Some(observed);
                    }
                }
                Err(error) => {
                    failure = Some(
                        json!({"error":error.to_string(), "support":chart.next_support(),
                        "uncertain":field.pending_lineage().is_some()}),
                    );
                    break;
                }
            }
        }
        let elapsed_ns = started.elapsed().as_nanos();
        let after = field.census();
        #[cfg(target_os = "macos")]
        let device_timing = {
            let timing_after = surface.metal_execution_timing();
            json!({"gpu_seconds":timing_after.gpu_seconds-timing_before.gpu_seconds,
                "completed_command_buffers":timing_after.completed_command_buffers-timing_before.completed_command_buffers,
                "unavailable_timestamps":timing_after.unavailable_timestamps-timing_before.unavailable_timestamps,
                "scope":"Metal command-buffer GPU start/end span; includes native field and terminal census"})
        };
        #[cfg(not(target_os = "macos"))]
        let device_timing = serde_json::Value::Null;
        latency.sort_unstable();
        let quantile = |p: usize| {
            latency
                .get(latency.len().saturating_sub(1) * p / 100)
                .copied()
        };
        let profile = field.intrinsic_profile();
        let profile_census = field.census();
        println!(
            "{}",
            json!({
                "schema":"holonics.acoustic-field-profile.v1",
                "scope":"complete timed coefficient fields over declared fixed material; no learned grain or acoustic-language product",
                "build_debug_assertions":cfg!(debug_assertions),
                "source":path,"source_sha256":source.source_sha256,
                "samples":source.samples.len(),"sample_rate":source.sample_rate,
                "complete":chart.is_complete(),"failure":failure,
                "native_from":start,"native_until":field.occurrence_count(),
                "source_duration_seconds":source.samples.len() as f64 / source.sample_rate as f64,
                "mount_ns":mount_ns,"decode_and_chart_ns":cold_ns,"loop_ns":elapsed_ns,
                "loop_includes":"chart delivery, native operation, terminal readout and observer JSON construction; excludes mount/decode/final stdout",
                "median_field_ns":quantile(50),"p95_field_ns":quantile(95),"max_field_ns":latency.last(),
                "receivers":{"unique":counts[0],"outside_domain":counts[1],"plural":counts[2]},
                "profile":{"ports":field.nodes(),"source_real_extent":profile.extents.source_extent,
                    "receiver_real_extent":profile.extents.target_extent,"relation_real_extent":profile.extents.relation_extent,
                    "retained_sources":profile.reconstruction_extent,"dimensions":format!("{:?}",profile.dimensions),
                    "current_frame":field.current_frame().ordinal(),"recharts":profile.recharts.len(),
                    "incidence_changes":profile.incidence_changes.len(),
                    "profile_added_readouts":profile_census.section_read_outs-after.section_read_outs},
            "census_before":before,"census_after":after,"first":first,"last":last,
            "device_timing":device_timing,
                "persistence":"native field rest/remount is not implemented by this receiver"
            })
        );
        if failure.is_some() {
            return Err("native field refused; complete obstruction printed".into());
        }
    }
    Ok(())
}
