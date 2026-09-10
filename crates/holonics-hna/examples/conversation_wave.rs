//! A continuing generator develops from whole measured fields. Source decoding, intake
//! scheduling, durable delivery and requested observations are exterior application work.
use holonic_engine::{
    codec_recovery::SymbolAlphabet,
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        NormalWaveRest, ResidentConstitutiveSection, ResidentNormalMaterial,
    },
    resident_section::{ResidentGrain, ResidentSurface},
};
use holonics_hna::{
    alpha::exposure::{ExposureCursor, ExposurePartition, ExposureReader},
    native::section_input::SymbolCurrentChart,
    publish_new,
};
use std::{
    collections::BTreeSet,
    error::Error,
    fs::{self, File},
    io::{self, BufReader},
    path::Path,
    time::Instant,
};
type Result<T> = std::result::Result<T, Box<dyn Error>>;

fn json<T: serde::Serialize>(path: impl AsRef<Path>, value: &T) -> Result<()> {
    publish_new(path, |file| {
        serde_json::to_writer(file, value).map_err(io::Error::other)
    })?;
    Ok(())
}
fn main() -> Result<()> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let actuating = args.first().is_some_and(|mode| mode == "actuate");
    let (chart,mut reader,rest,grain,take,steps,output)=match args.as_slice() {
        [mode,source,calibration,take,grain,steps,output] if mode=="start"=>{
            let calibration=calibration.parse::<u64>()?;
            let take=take.parse::<u64>()?;
            if take==0||calibration<take {return Err("declare nonempty intake within the calibration aperture".into());}
            let mut reader=ExposureReader::open(source)?;
            let origin=reader.cursor();
            let mut alphabet=BTreeSet::new();
            for _ in 0..calibration {
                let Some(frame)=reader.peek()? else {break};
                if frame.partition==ExposurePartition::Development {
                    for part in frame.development_parts()? {
                        if let Some(text)=&part.text {alphabet.extend(text.chars());}
                    }
                }
                let sequence=frame.sequence;reader.acknowledge(sequence)?;
            }
            let alphabet=SymbolAlphabet::from_chars(&alphabet.into_iter().collect::<Vec<_>>())
                .map_err(|e|format!("exterior alphabet: {e:?}"))?;
            (SymbolCurrentChart::declared(alphabet),ExposureReader::resume(origin)?,None,
                ResidentGrain(grain.parse::<u32>()?),take,steps.parse::<u64>()?,output)
        }
        [mode,previous,take,steps,output] if mode=="resume"||mode=="actuate"=>{
            let previous=Path::new(previous);
            let summary:serde_json::Value=serde_json::from_reader(File::open(previous.join("summary.json"))?)?;
            if summary["schema"]!="holonics.conversation-wave.v1" {
                return Err("not a completed conversation-wave intake".into());
            }
            let alphabet:SymbolAlphabet=serde_json::from_reader(File::open(previous.join("exterior-chart.json"))?)?;
            let cursor:ExposureCursor=serde_json::from_reader(File::open(previous.join("source-cursor.json"))?)?;
            let file=File::open(previous.join("model.wave"))?;
            let octets=file.metadata()?.len();
            let start=Instant::now();eprintln!("validating continuing generator");
            let rest=NormalWaveRest::read(&mut BufReader::new(file),octets)?;
            eprintln!("validation returned in {:.3}s",start.elapsed().as_secs_f64());
            if alphabet.len()!=rest.material().roots() {return Err("exterior/native chart extent disagreement".into());}
            let grain=rest.material().grain();
            (SymbolCurrentChart::declared(alphabet),ExposureReader::resume(cursor)?,Some(rest),grain,
                take.parse::<u64>()?,steps.parse::<u64>()?,output)
        }
        _=>return Err("usage: conversation_wave start SOURCE CALIBRATE_FRAMES TAKE_FRAMES GRAIN GENERATE_STEPS NEW_DIRECTORY | resume PREVIOUS_DIRECTORY TAKE_FRAMES GENERATE_STEPS NEW_DIRECTORY | actuate PREVIOUS_DIRECTORY TAKE_FRAMES GENERATE_STEPS NEW_DIRECTORY".into()),
    };
    let output = Path::new(output);
    if output.exists() {
        return Err("output directory already exists".into());
    }
    fs::create_dir(output)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(output, fs::Permissions::from_mode(0o700))?;
    }
    let readout = ResidentReadout::new()?;
    let surface = ResidentSurface::on(&readout)?;
    let mut body = rest
        .map(|r| r.remount(&surface, |step| eprintln!("decoded word {step}")))
        .transpose()?;
    let first_sequence = reader.cursor().next_sequence;
    let mut short_parts = 0usize;
    let mut fields = Vec::new();
    let mut frames = 0;
    let mut scalars = 0usize;
    let mut octets = 0usize;
    while frames < take {
        let Some(frame) = reader.peek()? else { break };
        if frame.partition == ExposurePartition::Development {
            for part in frame.development_parts()? {
                let Some(text) = &part.text else { continue };
                let symbols = chart.decode_text(text)?;
                scalars += symbols.len();
                octets += text.len();
                if symbols.len() < 2 {
                    short_parts += 1;
                    continue;
                }
                let section = chart.mount(&surface, &symbols)?;
                let input = ResidentConstitutiveSection::integers(&section)?;
                if body.is_none() {
                    // Actual first source currents define the initial receiver chart. Their
                    // two endpoints are one seed, not a retained source sequence.
                    let material = ResidentNormalMaterial::found(
                        &surface,
                        chart.alphabet().len(),
                        chart.alphabet().len(),
                        grain,
                    )?;
                    body = Some(
                        material
                            .into_difference_wave(input.row(0)?, input.row(1)?)
                            .map_err(|r| r.reason)?,
                    );
                }
                if actuating {
                    let body = body.as_mut().expect("restored source-action body");
                    let before = surface.census();
                    let clock = Instant::now();
                    let returned = body.actuate_section(input)?;
                    let seconds = clock.elapsed().as_secs_f64();
                    let after = surface.census();
                    let joint = returned.after().inspect()?;
                    fields.push(serde_json::json!({"sequence":frame.sequence,"part":part.ordinal,
                        "source_scalars":symbols.len(),"source_octets":text.len(),"source_contacts":symbols.len()-1,
                        "observations":returned.successor_fibre().material_observations,"current_epoch":body.epoch(),
                        "joint_radius":joint.radius,"seconds":seconds,"native_deeds":after.deed_launches-before.deed_launches,
                        "numerical_readouts_during_actuation":after.section_read_outs-before.section_read_outs,
                        "ingress_octets_during_actuation":after.ingress_octets-before.ingress_octets}));
                    eprintln!(
                        "source {} part {}: {} contacts, {:.3}s",
                        frame.sequence,
                        part.ordinal,
                        symbols.len() - 1,
                        seconds
                    );
                    continue;
                }
                if symbols.len() < 3 {
                    short_parts += 1;
                    continue;
                }
                let body = body.as_mut().expect("actual source seed");
                let before = surface.census();
                let clock = Instant::now();
                let difference = input.differences(&surface)?;
                let returned = body.develop_section(difference.source(), difference.observed())?;
                let seconds = clock.elapsed().as_secs_f64();
                let after = surface.census();
                let record = serde_json::json!({"sequence":frame.sequence,"part":part.ordinal,
                    "source_scalars":symbols.len(),"source_octets":text.len(),
                    "comparisons":returned.comparison.rows(),"observations":returned.successor_fibre.material_observations,
                    "rebased_joint_enclosure":returned.rebased_joint_enclosure,"current_epoch":body.epoch(),
                    "seconds":seconds,"native_deeds":after.deed_launches-before.deed_launches,
                    "numerical_readouts_during_development":after.section_read_outs-before.section_read_outs,
                    "ingress_octets_during_development":after.ingress_octets-before.ingress_octets});
                eprintln!(
                    "source {} part {}: {} comparisons, {:.3}s",
                    frame.sequence,
                    part.ordinal,
                    returned.comparison.rows(),
                    seconds
                );
                fields.push(record);
            }
        }
        let sequence = frame.sequence;
        reader.acknowledge(sequence)?;
        frames += 1;
    }
    let mut body = body.ok_or("no two-current source seed was available")?;
    let first_epoch = body.epoch();
    let mut trajectory = Vec::new();
    let mut obstruction = None;
    for _ in 0..steps {
        let before = surface.census();
        let clock = Instant::now();
        match body.advance() {
            Ok(returned) => {
                let seconds = clock.elapsed().as_secs_f64();
                let after = surface.census();
                trajectory.push(serde_json::json!({"epoch":body.epoch(),"reading":returned.inspect()?,"seconds":seconds,
                    "numerical_readouts_during_generation":after.section_read_outs-before.section_read_outs,
                    "ingress_octets_during_generation":after.ingress_octets-before.ingress_octets}));
                eprintln!("generated current {} in {:.3}s", body.epoch(), seconds);
            }
            Err(error) => {
                obstruction = Some(error.to_string());
                break;
            }
        }
    }
    let saved = body.rest()?;
    publish_new(output.join("model.wave"), |file| {
        saved.write(file).map_err(io::Error::other)
    })?;
    json(output.join("exterior-chart.json"), chart.alphabet())?;
    json(output.join("source-cursor.json"), &reader.cursor())?;
    json(output.join("fields.json"), &fields)?;
    json(output.join("trajectory.json"), &trajectory)?;
    let summary = serde_json::json!({"schema":"holonics.conversation-wave.v1",
        "scope":"source action and development of a continuing local generator; not general contextual language",
        "intake_operation":if actuating {"actuation"} else {"development"},
        "first_sequence":first_sequence,"next_sequence":reader.cursor().next_sequence,"frames":frames,
        "fields":fields.len(),"short_parts_without_local_comparison":short_parts,"source_scalars":scalars,"source_octets":octets,
        "alphabet_coordinates":chart.alphabet().len(),"grain":grain.0,"observations":saved.material().observations(),
        "first_current_epoch":first_epoch,"final_current_epoch":body.epoch(),"word_steps":body.steps(),
        "requested_generated_steps":steps,"returned_generated_steps":trajectory.len(),"generation_obstruction":obstruction,
        "resident_octets":surface.census().resident_octets_now,"model_rest_octets":fs::metadata(output.join("model.wave"))?.len()});
    // Publish the completion record last. A failed partial directory is not a resumable run.
    json(output.join("summary.json"), &summary)?;
    println!("{summary}");
    if let Some(reason) = obstruction {
        return Err(reason.into());
    }
    Ok(())
}
