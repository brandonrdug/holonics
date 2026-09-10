//! Research source attachment: an exterior symbol chart, the generic resident difference
//! receiver, and the existing accumulated normal response. No learner or emitter lives here.
use holonic_engine::{
    codec_recovery::SymbolAlphabet,
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{ResidentConstitutiveSection, ResidentNormalMaterial},
    resident_section::{ResidentGrain, ResidentSurface},
};
use holonics_hna::{
    alpha::exposure::{ExposurePartition, ExposureReader},
    native::section_input::SymbolCurrentChart,
    publish_new,
};
use std::{collections::BTreeSet, error::Error, fs, io, path::PathBuf, time::Instant};

#[derive(serde::Serialize)]
struct NativeStateData<'a> {
    schema: &'static str,
    rows: usize,
    width: usize,
    grain: u32,
    bound_octaves: u32,
    intervals: &'a [(i64, i64)],
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let [source, frames, grain, probe_sites, output] = args.as_slice() else {
        return Err(
            "usage: conversation_difference_field SOURCE FRAMES GRAIN PROBE_SITES NEW_DIRECTORY"
                .into(),
        );
    };
    let frames = frames.parse::<u64>()?;
    let grain = ResidentGrain(grain.parse::<u32>()?);
    let probe_sites = probe_sites.parse::<usize>()?;
    if frames == 0 {
        return Err("declare a nonempty exterior frame aperture".into());
    }
    let output = PathBuf::from(output);
    if output.exists() {
        return Err("output directory already exists".into());
    }
    // Calibrate only the exterior alphabet of this declared development prefix. This read
    // retains symbols, not passages. Reopening the source below supplies the actual occurrences.
    let calibration_start = Instant::now();
    let mut reader = ExposureReader::open(source)?;
    let source_origin = reader.cursor();
    let mut alphabet = BTreeSet::new();
    let mut calibrated_frames = 0;
    while calibrated_frames < frames {
        let Some(frame) = reader.peek()? else {
            break;
        };
        if frame.partition == ExposurePartition::Development {
            for part in frame.development_parts()? {
                if let Some(text) = &part.text {
                    alphabet.extend(text.chars());
                }
            }
        }
        let sequence = frame.sequence;
        reader.acknowledge(sequence)?;
        calibrated_frames += 1;
    }
    let alphabet = SymbolAlphabet::from_chars(&alphabet.into_iter().collect::<Vec<_>>())
        .map_err(|e| format!("exterior alphabet: {e:?}"))?;
    let chart = SymbolCurrentChart::declared(alphabet);
    let calibration_seconds = calibration_start.elapsed().as_secs_f64();
    fs::create_dir(&output)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&output, fs::Permissions::from_mode(0o700))?;
    }
    let readout = ResidentReadout::new()?;
    let surface = ResidentSurface::on(&readout)?;
    let mut body = ResidentNormalMaterial::found(
        &surface,
        chart.alphabet().len(),
        chart.alphabet().len(),
        grain,
    )?;
    let body_residency = surface.census().resident_octets_now;
    let mut reader = ExposureReader::resume(source_origin)?;
    let mut records = Vec::new();
    let mut consumed = 0;
    let mut development = 0;
    let mut parts_seen = 0;
    let mut short_parts = 0;
    let mut scalar_count = 0;
    let mut octets = 0;
    while consumed < calibrated_frames {
        let Some(frame) = reader.peek()? else {
            return Err("calibrated source prefix disappeared".into());
        };
        if frame.partition == ExposurePartition::Development {
            development += 1;
            for part in frame.development_parts()? {
                let Some(text) = &part.text else {
                    continue;
                };
                parts_seen += 1;
                let symbols = chart.decode_text(text)?;
                scalar_count += symbols.len();
                octets += text.len();
                if symbols.len() < 3 {
                    short_parts += 1;
                    continue;
                }
                let current = chart.mount(&surface, &symbols)?;
                let input = ResidentConstitutiveSection::integers(&current)?;
                let start = Instant::now();
                let before = surface.census();
                let difference = input.differences(&surface)?;
                let returned = body.receive_section(difference.source(), difference.observed())?;
                let after = surface.census();
                let seconds = start.elapsed().as_secs_f64();
                // Read several actual receiver sites. They are evidence only and never feed
                // the fitting operation or select developmental material.
                let probes = (0..returned.rows().min(probe_sites))
                    .map(|row| {
                        Ok(serde_json::json!({"site":row+1,
                        "before":returned.before(row)?.inspect()?,
                        "after":returned.forward(row)?.inspect()?}))
                    })
                    .collect::<Result<Vec<_>, Box<dyn Error>>>()?;
                let record = serde_json::json!({"sequence":frame.sequence,"part":part.ordinal,
                    "source_scalars":symbols.len(),"source_octets":text.len(),"local_comparisons":returned.rows(),
                    "native_seconds":seconds,"native_deeds":after.deed_launches-before.deed_launches,
                    "numerical_section_readouts_during_operation":after.section_read_outs-before.section_read_outs,
                    "ingress_octets_during_operation":after.ingress_octets-before.ingress_octets,
                    "observations":body.observations(),"probes":probes});
                eprintln!(
                    "source {} part {}: {} current comparisons, {:.3}s",
                    frame.sequence,
                    part.ordinal,
                    returned.rows(),
                    seconds
                );
                records.push(record);
            }
        }
        let sequence = frame.sequence;
        reader.acknowledge(sequence)?;
        consumed += 1;
        if surface.census().resident_octets_now != body_residency {
            return Err("source occurrence remained resident after its return left scope".into());
        }
    }
    let state = body.state_wire()?;
    let geometry = body.inspect()?;
    let objective = geometry.objective()?;
    let summary = serde_json::json!({"schema":"holonics.conversation-difference-field.v1",
        "scope":"local source-difference response; no semantic-context or language-attainment claim",
        "calibrated_frames":calibrated_frames,"development_frames":development,"parts":parts_seen,
        "short_parts_without_three_site_support":short_parts,"source_scalars":scalar_count,"source_octets":octets,
        "alphabet_coordinates":chart.alphabet().len(),"source_port_components":3*chart.components(),
        "target_components":chart.components(),"observed_local_comparisons":body.observations(),
        "grain":grain.0,"source_ports":["current-minus-previous","current","previous"],
        "observed_receiver":"next-minus-current","reported_sites_per_part":probe_sites,
        "body_resident_octets":body_residency,"state_words":state.intervals.len(),
        "calibration_seconds":calibration_seconds,"objective":objective});
    let data = NativeStateData {
        schema: "holonics.normal-state-data.v1",
        rows: state.rows,
        width: state.width,
        grain: state.grain.0,
        bound_octaves: state.bound_octaves,
        intervals: &state.intervals,
    };
    publish_new(output.join("native-state.json"), |file| {
        serde_json::to_writer(file, &data).map_err(io::Error::other)
    })?;
    for (name, value) in [
        ("returns.json", serde_json::to_value(records)?),
        (
            "exterior-chart.json",
            serde_json::to_value(chart.alphabet())?,
        ),
        ("source-cursor.json", serde_json::to_value(reader.cursor())?),
        ("summary.json", summary.clone()),
    ] {
        publish_new(output.join(name), |file| {
            serde_json::to_writer(file, &value).map_err(io::Error::other)
        })?;
    }
    println!("{}", summary);
    Ok(())
}
