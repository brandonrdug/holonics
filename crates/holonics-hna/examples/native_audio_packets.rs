//! Measure recorded PCM delivery through the public acoustic application. This is an execution
//! receiver, not cultivation or evidence of acoustic/English competence. No samples are skipped.
use holonics_hna::native::{
    AcousticApplication, NativeModelSpec, NativeSessionError, with_native_session,
};
use life::mathematical_source::ExactAcousticOccurrence;
use std::{env, fs, time::Instant};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    if args.len() < 3 {
        return Err("usage: native_audio_packets SEED PACKET_SAMPLES WAV [WAV ...]".into());
    }
    let spec = NativeModelSpec::read(&fs::read(&args[0])?)?;
    let packet: usize = args[1].parse()?;
    if packet == 0 {
        return Err("packet size must be positive".into());
    }
    with_native_session(&spec, |session| {
        let mut app: Option<AcousticApplication> = None;
        for (index, path) in args[2..].iter().enumerate() {
            let bytes = fs::read(path)?;
            let occurrence = ExactAcousticOccurrence::from_wav_bytes(
                &bytes,
                format!("recorded-packet-measurement:{index}"),
                path,
                4096,
                4096,
                1,
            )
            .map_err(|e| NativeSessionError::Application(e.to_string()))?;
            if let Some(app) = app.as_mut() {
                app.append_recording(session, &occurrence, &bytes, 32768, None)?;
            } else {
                app = Some(AcousticApplication::found(
                    &spec,
                    &occurrence,
                    &bytes,
                    32768,
                    None,
                    session,
                )?);
            }
            let app = app.as_mut().expect("attached source");
            let before = session.inspect().census;
            let started = Instant::now();
            let mut latency = Vec::new();
            while !app.complete() {
                let tick = Instant::now();
                app.advance_packet(session, packet)?;
                latency.push(tick.elapsed().as_nanos());
            }
            let elapsed = started.elapsed().as_nanos();
            latency.sort_unstable();
            let after = session.inspect().census;
            println!(
                "{}",
                serde_json::json!({
                    "scope":"ordered unlinked PCM ingress; no learned audio-language capability",
                    "source":path,"source_sha256":occurrence.source_sha256,
                    "source_samples":occurrence.samples.len(),"sample_rate":occurrence.sample_rate,
                    "native_start":app.native_start(),"native_end":session.occurrence_count(),
                    "recordings":app.recording_count(),"packet_samples":packet,
                    "elapsed_ns":elapsed,"packet_median_ns":latency[latency.len()/2],
                    "packet_p95_ns":latency[(latency.len()-1)*95/100],"packet_max_ns":latency.last(),
                    "deed_launches":after.deed_launches-before.deed_launches,
                    "synchronizations":after.synchronizations-before.synchronizations,
                    "allocations":after.allocations-before.allocations,
                    "ingress_octets":after.ingress_octets-before.ingress_octets,
                    "egress_section_octets":after.egress_section_octets-before.egress_section_octets,
                    "egress_receipt_octets":after.egress_receipt_octets-before.egress_receipt_octets,
                    "first_return":app.steps().first(),"last_return":app.steps().last(),
                })
            );
        }
        Ok(())
    })?;
    Ok(())
}
