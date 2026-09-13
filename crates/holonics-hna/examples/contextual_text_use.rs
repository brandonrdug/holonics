//! Bounded contextual-text experiment over the admitted exposure reader and native wave owner.
//! This is an application driver: it supplies source apertures and records native returns.
use holonics_hna::{
    alpha::exposure::{ExposureCursor, ExposureFamily, ExposurePartition, ExposureReader},
    native::{
        with_seeded_wave_session, NativeSessionError, NativeWaveSavedSession, NativeWaveSeedSpec,
        NATIVE_WAVE_SEED_SCHEMA,
    },
    publish_new, HnaStreamState,
};
use num_traits::Signed;
use serde::Serialize;
use serde_json::Value;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::{
    collections::BTreeSet,
    env,
    error::Error,
    fs, io,
    path::{Path, PathBuf},
    time::Instant,
};

type Result<T> = std::result::Result<T, Box<dyn Error>>;

#[derive(Serialize)]
struct Family {
    family: ExposureFamily,
    sequence: u64,
    part: u64,
    pointer: String,
    chars: usize,
}
#[derive(Serialize)]
struct Report {
    schema: &'static str,
    completed: bool,
    output: String,
    aperture: Aperture,
    source: PathBuf,
    seed: NativeWaveSeedSpec,
    probe: String,
    families: Vec<Family>,
    observations: Option<u64>,
    cursor: Option<Value>,
    exposure_cursor: Option<ExposureCursor>,
    pending_exposure_sequence: Option<u64>,
    progress: Value,
    elapsed_micros: u128,
    errors: Vec<String>,
    checkpoint: Option<String>,
}
#[derive(Serialize)]
struct Aperture {
    development_parts: usize,
    max_chars_per_part: usize,
    cycles: usize,
    emit_count: usize,
    observation: &'static str,
}

fn json(path: &Path, value: &impl Serialize) -> Result<()> {
    publish_new(path, |file| {
        #[cfg(unix)]
        {
            file.set_permissions(fs::Permissions::from_mode(0o600))?;
        }
        serde_json::to_writer(file, value).map_err(io::Error::other)
    })?;
    Ok(())
}

fn main() -> Result<()> {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.len() == 2 && args[0] == "--inspect" {
        NativeWaveSavedSession::read(&args[1])?.with_session(|session,_| {
            let field=session.wave().joint_source().joint().inspect()?;
            let state=session.wave().fibre().inspect_material()?;
            let largest=|values:&[Vec<holonic_engine::dimensional_wave::ExactComplexWaveCurrent>]| values.iter().flatten()
                .map(|v|v.real.abs()+v.imaginary.abs()).max().map(|v|v.to_string());
            let center_l1=field.center.iter().map(|v|v.real.abs()+v.imaginary.abs()).sum::<num_rational::BigRational>();
            println!("{}",serde_json::json!({"inspect":session.inspect(),"joint_center_l1":center_l1.to_string(),
                "joint_radius":field.radius.to_string(),"coefficient_max_l1":largest(&state.material.coefficients),
                "coefficient_radius":state.material.radius.to_string(),"normal_max_l1":largest(&state.source_normal),
                "cross_max_l1":largest(&state.cross_source),"normal_error":state.source_normal_error.to_string(),
                "cross_error":state.cross_source_error.to_string(),"target_energy":state.target_energy.to_string(),
                "target_energy_error":state.target_energy_error.to_string(),"normal_residual":state.normal_residual_upper.to_string()}));
            Ok(())
        })?;
        return Ok(());
    }
    if !(7..=8).contains(&args.len()) {
        return Err("usage: contextual_text_use EXPOSURE_JSONL OUTPUT_DIRECTORY DEVELOPMENT_PARTS MAX_CHARS_PER_PART CYCLES PROBE_TEXT EMIT_COUNT [addressed|next-current]".into());
    }
    let exposure = PathBuf::from(&args[0]);
    let output = PathBuf::from(&args[1]);
    let aperture = Aperture {
        development_parts: args[2].parse()?,
        max_chars_per_part: args[3].parse()?,
        cycles: args[4].parse()?,
        emit_count: args[6].parse()?,
        observation: match args.get(7).map(String::as_str).unwrap_or("addressed") {
            "addressed" => "addressed",
            "next-current" => "next-current",
            _ => return Err("observation must be addressed or next-current".into()),
        },
    };
    if aperture.development_parts == 0
        || aperture.max_chars_per_part < 3
        || aperture.cycles == 0
        || aperture.emit_count == 0
    {
        return Err(
            "positive development parts, cycles and emissions, with at least three characters per part, are required".into(),
        );
    }
    if output.exists() {
        return Err(format!("output directory already exists: {}", output.display()).into());
    }
    fs::create_dir(&output)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&output, fs::Permissions::from_mode(0o700))?;
    }

    let started = Instant::now();
    // This pass plans the bounded source aperture and discovers its codec alphabet. Its cursor is
    // disposable planning state. The fresh delivery reader below owns actual acknowledgements.
    let mut planning_reader = ExposureReader::open(&exposure)?;
    let mut selected = Vec::<(ExposureFamily, u64, u64, String, String)>::new();
    let mut alphabet = BTreeSet::new();
    while selected.len() < aperture.development_parts {
        let Some(frame) = planning_reader.peek()? else {
            break;
        };
        let sequence = frame.sequence;
        let source_family = frame.family.clone();
        let parts = if frame.partition == ExposurePartition::Development {
            frame.development_parts()?.to_vec()
        } else {
            Vec::new()
        };
        planning_reader.acknowledge(sequence)?;
        for part in parts {
            let Some(text) = part.text else { continue };
            let chars: String = text.chars().take(aperture.max_chars_per_part).collect();
            if chars.chars().count() < 3 {
                continue;
            }
            alphabet.extend(chars.chars());
            let family = selected.len();
            selected.push((
                source_family.clone(),
                sequence,
                part.ordinal,
                part.pointer,
                chars,
            ));
            eprintln!(
                "development family {family} sequence {sequence} part {}",
                part.ordinal
            );
            if selected.len() == aperture.development_parts {
                break;
            }
        }
    }
    if selected.len() != aperture.development_parts {
        return Err("source ended before the requested development-part aperture".into());
    }
    let probe = &args[5];
    if probe.chars().count() < 2 || probe.chars().any(|c| !alphabet.contains(&c)) {
        return Err("probe contains a character outside the admitted development alphabet".into());
    }
    let first: Vec<char> = selected[0].4.chars().take(2).collect();
    let spec = NativeWaveSeedSpec {
        schema: NATIVE_WAVE_SEED_SCHEMA.into(),
        symbols: alphabet.iter().copied().collect(),
        seed: first.iter().collect(),
        grain: 64,
    };
    let planned_by_sequence = selected.iter().enumerate().fold(
        std::collections::BTreeMap::<u64, Vec<(usize, u64, String, String)>>::new(),
        |mut by_sequence, (family, (_, sequence, part, pointer, text))| {
            by_sequence.entry(*sequence).or_default().push((
                family,
                *part,
                pointer.clone(),
                text.clone(),
            ));
            by_sequence
        },
    );
    // This reader is the actual cold-delivery cursor. A selected occurrence remains pending until
    // every selected part has completed all declared native cycles.
    let mut delivery_reader = ExposureReader::open(&exposure)?;
    let mut exposure_cursor = Some(delivery_reader.cursor());
    let mut pending_exposure_sequence = None;
    let mut errors = Vec::new();
    let mut result_output = String::new();
    let mut checkpoint = None;
    let mut progress = serde_json::json!({"stage":"mount"});
    let native = with_seeded_wave_session(&spec, |session| {
        let mut process_parts = |cycle: usize, source_parts: &[(usize, String)]| -> bool {
            for (family, text) in source_parts {
                let chars: Vec<char> = text.chars().collect();
                progress = serde_json::json!({"stage":"part-source","cycle":cycle,"part":family});
                // The first pair already supplied the exact initial state. Later parts/cycles
                // offer their actual initial pair to the continuing state, without a reset.
                if cycle != 0 || *family != 0 {
                    if let Err(error) = session.actuate_text(&chars[..2].iter().collect::<String>())
                    {
                        errors.push(format!("cycle {cycle} family {family} actuation: {error}"));
                        return false;
                    }
                }
                for index in 2..chars.len() {
                    if index % 8 == 2 {
                        eprintln!(
                            "cycle {cycle}, part {family}, symbol {index}/{}",
                            chars.len()
                        );
                    }
                    let returned = if aperture.observation == "next-current" {
                        progress = serde_json::json!({"stage":"observation","cycle":cycle,"part":family,"symbol":index});
                        session.receive_next_symbol(&chars[index].to_string())
                    } else {
                        progress = serde_json::json!({"stage":"prediction","cycle":cycle,"part":family,"symbol":index});
                        let prediction = match session.predict_symbol(false) {
                            Ok(value) => value,
                            Err(error) => {
                                errors.push(format!(
                                    "cycle {cycle} family {family} prediction {index}: {error}"
                                ));
                                return false;
                            }
                        };
                        let Some(id) = prediction["action"]["prediction"].as_u64() else {
                            errors.push(format!("cycle {cycle} family {family} prediction {index}: missing native handle"));
                            return false;
                        };
                        progress = serde_json::json!({"stage":"observation","cycle":cycle,"part":family,"symbol":index,"prediction":id});
                        session.receive_symbol(id, &chars[index].to_string())
                    };
                    if let Err(error) = returned {
                        errors.push(format!(
                            "cycle {cycle} family {family} observation {index}: {error}"
                        ));
                        return false;
                    }
                    progress = serde_json::json!({"stage":"source-feedback","cycle":cycle,"part":family,"symbol":index});
                    if let Err(error) =
                        session.actuate_text(&chars[index - 1..=index].iter().collect::<String>())
                    {
                        errors.push(format!(
                            "cycle {cycle} family {family} source {index}: {error}"
                        ));
                        return false;
                    }
                }
            }
            true
        };
        let mut delivered_parts = Vec::<Vec<(usize, String)>>::new();
        'development: for cycle in 0..aperture.cycles {
            if cycle == 0 {
                while delivered_parts.len() < planned_by_sequence.len() {
                    let Some(frame) = delivery_reader
                        .peek()
                        .map_err(|error| NativeSessionError::Application(error.to_string()))?
                    else {
                        errors.push(
                            "source ended before all planned occurrences were natively used".into(),
                        );
                        break 'development;
                    };
                    let sequence = frame.sequence;
                    let Some(planned_parts) = planned_by_sequence.get(&sequence) else {
                        // Non-selected cold occurrences may advance. A selected occurrence stays
                        // pending until every selected part has completed its native use.
                        delivery_reader
                            .acknowledge(sequence)
                            .map_err(|error| NativeSessionError::Application(error.to_string()))?;
                        exposure_cursor = Some(delivery_reader.cursor());
                        continue;
                    };
                    pending_exposure_sequence = Some(sequence);
                    let actual_parts = frame
                        .development_parts()
                        .map_err(|error| NativeSessionError::Application(error.to_string()))?
                        .to_vec();
                    let source_parts: Option<Vec<(usize, String)>> = planned_parts
                        .iter()
                        .map(|(family, ordinal, pointer, expected)| {
                            actual_parts
                                .iter()
                                .find(|part| {
                                    part.ordinal == *ordinal
                                        && part.pointer == *pointer
                                        && part.text.as_ref().is_some_and(|text| {
                                            text.chars()
                                                .take(aperture.max_chars_per_part)
                                                .collect::<String>()
                                                == *expected
                                        })
                                })
                                .and_then(|part| part.text.as_ref())
                                .map(|_| (*family, expected.clone()))
                        })
                        .collect::<Option<Vec<_>>>();
                    let Some(source_parts) = source_parts else {
                        errors.push(format!("planned source occurrence {sequence} no longer matches its actual visible parts"));
                        break 'development;
                    };
                    if !process_parts(cycle, &source_parts) {
                        break 'development;
                    }
                    delivery_reader
                        .acknowledge(sequence)
                        .map_err(|error| NativeSessionError::Application(error.to_string()))?;
                    exposure_cursor = Some(delivery_reader.cursor());
                    pending_exposure_sequence = None;
                    delivered_parts.push(source_parts);
                }
            } else {
                for source_parts in &delivered_parts {
                    if !process_parts(cycle, source_parts) {
                        break 'development;
                    }
                }
            }
        }
        if errors.is_empty() {
            progress = serde_json::json!({"stage":"probe-source"});
            if let Err(error) = session.actuate_text(probe) {
                errors.push(format!("probe actuation: {error}"));
            }
            let mut previous = probe.chars().last();
            for index in 0..aperture.emit_count {
                if errors.is_empty() {
                    progress = serde_json::json!({"stage":"probe-emission","symbol":index});
                    match session.next_symbol(false) {
                        Ok(value) => {
                            if let Some(text) = value["text"].as_str() {
                                result_output.push_str(text);
                            } else {
                                errors.push("native emission returned no text".into());
                            }
                        }
                        Err(error) => errors.push(format!("probe emission: {error}")),
                    }
                }
                if errors.is_empty() {
                    progress = serde_json::json!({"stage":"probe-feedback","symbol":index});
                    if let (Some(old), Some(generated)) = (previous, result_output.chars().last()) {
                        let pair: String = [old, generated].into_iter().collect();
                        if let Err(error) = session.actuate_text(&pair) {
                            errors.push(format!("probe source feedback: {error}"));
                        }
                        previous = Some(generated);
                    }
                }
            }
        }
        if errors.is_empty() {
            progress = serde_json::json!({"stage":"complete"});
        }
        let native_checkpoint = output.join("native.wave");
        match session.checkpoint_stream(&native_checkpoint, &HnaStreamState::default()) {
            Ok(_) => checkpoint = Some(native_checkpoint.display().to_string()),
            Err(error) => errors.push(format!("checkpoint: {error}")),
        }
        Ok(session.inspect())
    });
    let (observations, cursor, completed) = match native {
        Ok(inspect) => (
            inspect["observations"].as_u64(),
            Some(inspect["cursor"].clone()),
            errors.is_empty(),
        ),
        Err(error) => {
            errors.push(error.to_string());
            (None, None, false)
        }
    };
    let families = selected
        .into_iter()
        .map(|(family, sequence, part, pointer, text)| Family {
            family,
            sequence,
            part,
            pointer,
            chars: text.chars().count(),
        })
        .collect();
    let report = Report {
        schema: "org.holonics.hna.contextual-text-use.v1",
        completed,
        output: result_output,
        aperture,
        source: exposure,
        seed: spec,
        probe: probe.clone(),
        families,
        observations,
        elapsed_micros: started.elapsed().as_micros(),
        cursor,
        exposure_cursor,
        pending_exposure_sequence,
        progress,
        errors,
        checkpoint,
    };
    json(&output.join("report.json"), &report)?;
    println!("{}", serde_json::to_string(&report)?);
    if completed {
        Ok(())
    } else {
        Err("contextual experiment returned an error; see report.json".into())
    }
}
