//! Attach actual recorded intervals to the public acoustic current port. This is source
//! preparation and codec verification; no native condition or learner is manufactured here.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    phase_current::{PhaseCurrentLineageId, PhaseCurrentReceiverId},
    resident_section::ResidentSurface,
};
use holonics_hna::native::recorded::{read_response_links, RecordedResponseSections};
use life::mathematical_source::ExactAcousticOccurrence;
use num_rational::BigRational;
use serde_json::{json, Value};
use std::{collections::BTreeMap, error::Error, fs, io::Write, path::PathBuf, time::Instant};

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() != 3 {
        return Err(
            "usage: recorded_acoustic_sections CORPUS_DIRECTORY PORT_EXTENT NEW_RECEIPT.json"
                .into(),
        );
    }
    let root = PathBuf::from(&args[0]);
    let extent: usize = args[1].parse()?;
    if extent == 0 {
        return Err("port extent must be positive".into());
    }
    let output = PathBuf::from(&args[2]);
    if output.exists() {
        return Err("receipt already exists".into());
    }
    let started = Instant::now();
    let index_path = root.join("response-links.exact.jsonl");
    let links = read_response_links(&index_path)?;
    let provenance_path = root.join("provenance.json");
    let provenance: Value = serde_json::from_slice(&fs::read(&provenance_path)?)?;
    let audio = provenance["audio"]
        .as_array()
        .ok_or("missing audio provenance")?;
    let mut rows: Vec<Option<Value>> = vec![None; links.len()];
    let mut recordings = Vec::new();
    let mut refusals = BTreeMap::<String, usize>::new();
    for (index, link) in links.iter().enumerate() {
        if let Some(refusal) = link.refusal() {
            *refusals.entry(refusal.code.clone()).or_default() += 1;
            rows[index] = Some(json!({"index":index,"session":link.session,
                "adjacency_pair_id":link.adjacency_pair_id,"refusal":{
                    "code":refusal.code,"detail":refusal.detail,
                    "source_clock_refusals":refusal.source_clock_refusals,
                    "target_clock_refusals":refusal.target_clock_refusals}}));
        }
    }
    let mut resident_example = None;
    let mut resolved = 0usize;
    for entry in audio {
        let session = entry["session"].as_str().ok_or("missing session")?;
        let source_path = PathBuf::from(entry["path"].as_str().ok_or("missing source path")?);
        let path = root
            .join("audio")
            .join(source_path.file_name().ok_or("missing audio filename")?);
        let recording = ExactAcousticOccurrence::read(&path, session, 4096, 4096, 1)?;
        if entry["sha256"].as_str() != Some(&recording.source_sha256)
            || entry["bytes"].as_u64() != Some(recording.source_octets)
            || entry["frames"].as_u64() != Some(recording.samples.len() as u64)
            || entry["sample_rate"].as_u64() != Some(recording.sample_rate.into())
        {
            return Err(
                format!("audio source differs from its acquisition receipt: {session}").into(),
            );
        }
        let mut session_resolved = 0;
        for (index, link) in links
            .iter()
            .enumerate()
            .filter(|(_, l)| l.session.as_deref() == Some(session))
        {
            let Some((source, target)) = link.resolved() else {
                continue;
            };
            if rows[index].is_some() {
                return Err("repeated recording binding".into());
            }
            let rate = u64::from(recording.sample_rate);
            let count = recording.samples.len() as u64;
            let source_frames = source.interval.covering_frames(rate, count)?;
            let target_frames = target.interval.covering_frames(rate, count)?;
            rows[index] = Some(json!({"index":index,"session":session,
                "adjacency_pair_id":link.adjacency_pair_id,
                "source":{"id":source.dialogue_act_id,"begin":source.interval.begin_decimal,
                    "end":source.interval.end_decimal,"frames":[source_frames.begin_frame,source_frames.end_frame]},
                "target":{"id":target.dialogue_act_id,"begin":target.interval.begin_decimal,
                    "end":target.interval.end_decimal,"frames":[target_frames.begin_frame,target_frames.end_frame]},
                "target_begin_minus_source_end":(&target.interval.begin-&source.interval.end).to_string()}));
            session_resolved += 1;
            resolved += 1;
            if resident_example.is_none() {
                let sections = RecordedResponseSections::bind(
                    link,
                    &recording,
                    PhaseCurrentReceiverId(1),
                    PhaseCurrentLineageId(1),
                    PhaseCurrentLineageId(2),
                    BigRational::from_integer(0.into()),
                    extent,
                    32768,
                )?;
                for chart in [sections.source(), sections.target()] {
                    if chart.reconstruct_samples() != recording.samples[chart.source_range()] {
                        return Err("interval chart does not reconstruct its addressed PCM".into());
                    }
                }
                let readout = ResidentReadout::new()?;
                let surface = ResidentSurface::on(&readout)?;
                let before = surface.census();
                let source_cells = (0..sections.source().section().cells.len())
                    .map(|i| sections.source().mount_cell(&surface, i))
                    .collect::<Result<Vec<_>, _>>()?;
                let target_cells = (0..sections.target().section().cells.len())
                    .map(|i| sections.target().mount_cell(&surface, i))
                    .collect::<Result<Vec<_>, _>>()?;
                for cell in source_cells.iter().chain(&target_cells) {
                    cell.rational()?;
                }
                let after_mount = surface.census();
                let first = source_cells.first().ok_or("empty source cells")?;
                let last = target_cells.last().ok_or("empty target cells")?;
                let first_words = surface.read_out(first.section())?;
                let last_words = surface.read_out(last.section())?;
                resident_example = Some(
                    json!({"index":index,"adjacency_pair_id":link.adjacency_pair_id,
                    "recording":path,"source_sha256":recording.source_sha256,
                    "source_cells":source_cells.len(),"target_cells":target_cells.len(),
                    "source_samples":sections.source().section().raw_extent(),
                    "target_samples":sections.target().section().raw_extent(),
                    "first_source_support":first.support(),"last_target_support":last.support(),
                    "first_source_words":first_words,"last_target_words":last_words,
                    "census_before":before,"census_after_complete_mount":after_mount,
                    "census_after_two_cold_receivers":surface.census()}),
                );
            }
        }
        recordings.push(json!({"session":session,"path":path,"sha256":recording.source_sha256,
            "samples":recording.samples.len(),"sample_rate":recording.sample_rate,"resolved_links":session_resolved}));
    }
    if rows.iter().any(Option::is_none) {
        return Err("a resolved record lacks its recording binding".into());
    }
    let report = json!({"schema":"holonics.recorded-acoustic-sections.v1",
        "truth_status":"established-bounded","evidence_tags":["measured"],
        "scope":"complete annotation/clock attachment and one complete resident source/response pair; no native learning",
        "annotation_index":index_path,"acquisition_receipt":provenance_path,
        "records":rows,"recordings":recordings,"resolved":resolved,"refusals":refusals,
        "port_extent":extent,"resident_pair":resident_example,"elapsed_seconds":started.elapsed().as_secs_f64(),
        "native_condition_inferred":false,"native_learning_executed":false,
        "acoustic_model_established":false,"conversation_quality_established":false});
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&output)?;
    serde_json::to_writer_pretty(&mut file, &report)?;
    file.write_all(b"\n")?;
    println!(
        "{}",
        json!({"receipt":output,"records":links.len(),"resolved":resolved,"refusals":refusals})
    );
    Ok(())
}
