//! A declared native temporal action learned from recorded coefficient observations.
//! The digital response controls do not assert a physical room or utterance-response law.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, ConditionPreimageReading, ConstitutiveReading,
        NativeConstitutiveField, NativeFieldOccurrence, NativeJunctionSeed, NativePhaseCurrent,
        ResidentConstitutiveCurrent, ResidentConstitutiveFibre, ResidentConstitutiveReturn,
    },
    phase_current::{
        resident::{convolve_resident, ResidentPhaseConvolution, ResidentPhaseCurrentView},
        PhaseCurrentLineageId, PhaseCurrentReceiverId,
    },
    resident_section::{
        ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface, TransferCensus,
    },
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
const WIDTH: usize = 4;
const DIVISOR: i64 = 32768;
const PCM_GAIN: i64 = 8192;
const CONTROLS: [[i64; 4]; 5] = [
    [0, 0, 0, 0],
    [1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, 0, 1, 0],
    [0, 0, 0, 1],
];

fn strings(values: &[Rat]) -> Vec<String> {
    values.iter().map(ToString::to_string).collect()
}
fn work(before: &TransferCensus, after: &TransferCensus, seconds: f64) -> Value {
    json!({"seconds":seconds,"section_readouts":after.section_read_outs-before.section_read_outs,
        "numerical_egress_octets":after.egress_section_octets-before.egress_section_octets,
        "ingress_octets":after.ingress_octets-before.ingress_octets,
        "receipt_egress_octets":after.egress_receipt_octets-before.egress_receipt_octets,
        "deeds":after.deed_launches-before.deed_launches,
        "allocations":after.allocations-before.allocations,
        "resident_octets_now":after.resident_octets_now,"resident_octets_peak":after.resident_octets_peak})
}
fn stage<T>(
    s: &ResidentSurface<'_>,
    report: &mut Value,
    name: &str,
    action: impl FnOnce() -> Result<T>,
) -> Result<T> {
    report["active_stage"] = json!(name);
    let before = s.census();
    #[cfg(target_os = "macos")]
    let gpu_before = s.metal_execution_timing();
    let started = Instant::now();
    let result = action();
    report["stages"][name] = work(&before, &s.census(), started.elapsed().as_secs_f64());
    #[cfg(target_os = "macos")]
    {
        let after = s.metal_execution_timing();
        report["stages"][name]["gpu_seconds"] = json!(after.gpu_seconds - gpu_before.gpu_seconds);
        report["stages"][name]["completed_command_buffers"] =
            json!(after.completed_command_buffers - gpu_before.completed_command_buffers);
        report["stages"][name]["unavailable_gpu_timestamps"] =
            json!(after.unavailable_timestamps - gpu_before.unavailable_timestamps);
    }
    result
}
fn mount<'c>(
    s: &'c ResidentSurface<'c>,
    coordinates: &[i64],
    den: i64,
) -> Result<ResidentSection<'c>> {
    let mut words: Vec<_> = coordinates.iter().map(|v| (*v, *v)).collect();
    words.push((den, den));
    Ok(s.mount_section_rest(&ResidentSectionRest::found(
        1,
        words.len(),
        ResidentGrain(0),
        64,
        words,
    )?)?)
}
fn rational<'a, 'c>(s: &'a ResidentSection<'c>) -> Result<ResidentConstitutiveCurrent<'a, 'c>> {
    Ok(ResidentConstitutiveCurrent::rational(s)?)
}
fn response<'a, 'c>(
    s: &'a ResidentSection<'c>,
    step: &Rat,
    id: u64,
) -> Result<ResidentPhaseCurrentView<'a, 'c>> {
    Ok(ResidentPhaseCurrentView::new(
        rational(s)?,
        PhaseCurrentReceiverId(2),
        PhaseCurrentLineageId(id),
        Rat::from_integer(0.into()),
        step.clone(),
        WIDTH as u32,
        2,
    )?)
}
fn point(s: &ResidentSurface<'_>, section: &ResidentSection<'_>) -> Result<Value> {
    let words = s.read_out(section)?;
    if words.len() < 2 || words.iter().any(|(a, b)| a != b) || words.last().unwrap().0 <= 0 {
        return Err("terminal point/denominator refusal".into());
    }
    let den = words.last().unwrap().0;
    let coordinates: Vec<_> = words[..words.len() - 1]
        .iter()
        .map(|p| Rat::new(p.0.into(), den.into()))
        .collect();
    Ok(json!({"coordinates":strings(&coordinates),"raw_words":words}))
}
fn section_wire(rest: &ResidentSectionRest) -> Value {
    json!({"rows":rest.rows,"width":rest.width,"grain":rest.grain.0,
        "bound_octaves":rest.bound_octaves,"intervals":rest.intervals})
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = OpenOptions::new().write(true).create_new(true).open(path)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    Ok(())
}

// One cold terminal receiver. The complete canonical native section and declared gain retain
// every quantization/clipping fibre; the stereo WAV is only its timed exterior projection.
fn publish_temporal(
    s: &ResidentSurface<'_>,
    current: &ResidentPhaseConvolution<'_, '_>,
    directory: &Path,
    name: &str,
    sample_rate: u32,
) -> Result<Value> {
    let view = current.view()?;
    let rest = s.detach_section(current.section(), 64)?;
    if rest.intervals.iter().any(|(a, b)| a != b) || rest.intervals.last().unwrap().0 <= 0 {
        return Err("temporal terminal requires an exact rational point".into());
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
        sample_rate,
        Rat::from_integer(PCM_GAIN.into()),
        &coordinates,
    )?;
    let section_bytes = rest.canonical_bytes()?;
    let wav_bytes = projection.wav_bytes()?;
    let section_path = directory.join(format!("{name}.section"));
    let wav_path = directory.join(format!("{name}.wav"));
    write_new(&section_path, &section_bytes)?;
    write_new(&wav_path, &wav_bytes)?;
    Ok(json!({
        "receiver":view.receiver().0,"lineage":view.lineage().0,
        "origin":view.origin().to_string(),"sample_step":view.sample_step().to_string(),
        "sample_rate":sample_rate,"frames":projection.frames.len(),
        "clipped_sample_population":projection.clipped_sample_population,
        "projection_schema":projection.schema,
        "section_path":section_path,"section_sha256":format!("{:x}",Sha256::digest(&section_bytes)),
        "section_octets":section_bytes.len(),
        "wav_path":wav_path,"wav_sha256":format!("{:x}",Sha256::digest(&wav_bytes)),
        "wav_octets":wav_bytes.len(),
        "fibre_decoder":"read the canonical ResidentSectionRest rational point; at the declared gain, residual = current * gain - PCM, and current = (PCM + residual) / gain"
    }))
}
fn returned(result: &ResidentConstitutiveReturn<'_>) -> Result<Value> {
    Ok(match result.inspect()?.predecessor_reading {
        ConstitutiveReading::Unique { current } => {
            json!({"status":"unique","coordinates":strings(&current)})
        }
        ConstitutiveReading::Plural {
            particular,
            directions,
        } => json!({"status":"plural",
            "particular":strings(&particular),"directions":directions.iter().map(|v|strings(v)).collect::<Vec<_>>()}),
        ConstitutiveReading::OutsideDomain { source_remainder } => {
            json!({"status":"outside-domain","residual":strings(&source_remainder)})
        }
    })
}

fn experiment<'c>(
    s: &'c ResidentSurface<'c>,
    chart: &AcousticFieldChart,
    body: &mut ResidentConstitutiveFibre<'c>,
    report: &mut Value,
    audio_directory: Option<&Path>,
) -> Result<()> {
    // Eight interior clock cuts are fixed before any current is observed. Cuts 3/9 and 6/9
    // are held out; the other six train. No silence, amplitude, rank or answer selects a cut.
    let full_cells = chart.section().raw_extent() / WIDTH;
    if full_cells < 9 {
        return Err("recording needs at least nine complete temporal cells".into());
    }
    let indices: Vec<_> = (1..=8).map(|i| i * (full_cells - 1) / 9).collect();
    let training_indices: Vec<_> = indices
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != 2 && *i != 5)
        .map(|(_, v)| *v)
        .collect();
    let hidden_index = indices[2];
    let later_index = indices[5];
    report["selection"] = json!({"rule":"eight fixed interior chronological cuts at ninths; third and sixth held out",
        "training_cells":training_indices,"hidden_cell":hidden_index,"later_cell":later_index});
    let cells: Vec<_> = training_indices
        .iter()
        .map(|i| chart.mount_cell(s, *i))
        .collect::<std::result::Result<_, _>>()?;
    let hidden_cell = chart.mount_cell(s, hidden_index)?;
    let later_cell = chart.mount_cell(s, later_index)?;
    let zero = mount(s, &[0; 2 * WIDTH], DIVISOR)?;
    let controls: Vec<_> = CONTROLS
        .iter()
        .map(|v| mount(s, v, 1))
        .collect::<Result<_>>()?;
    let hidden_response = mount(s, &[2, -1, 5, 3], 3)?;
    report["training_supports"] =
        json!(cells.iter().map(|cell| cell.support()).collect::<Vec<_>>());
    report["hidden_support"] = json!(hidden_cell.support());
    report["later_support"] = json!(later_cell.support());
    report["training_observations"] = json!(0);
    report["calibration_observations"] = json!(0);
    stage(s, report, "zero_source_calibration", || {
        for (i, c) in controls.iter().enumerate() {
            let source = ResidentPhaseCurrentView::new(
                rational(&zero)?,
                PhaseCurrentReceiverId(1),
                PhaseCurrentLineageId(2),
                Rat::from_integer(0.into()),
                chart.section().sample_step.clone(),
                WIDTH as u32,
                WIDTH,
            )?;
            let actual = convolve_resident(
                s,
                source,
                response(c, &chart.section().sample_step, 10 + i as u64)?,
                PhaseCurrentReceiverId(3),
                PhaseCurrentLineageId(20 + i as u64),
            )?;
            body.advance_bilinear_contact(rational(&zero)?, rational(c)?, Some(actual.current()?))?;
        }
        Ok(())
    })?;
    report["calibration_observations"] = json!(body.occurrences());
    let calibration_cut = body.occurrences();
    let training = stage(s, report, "recorded_development", || {
        for cell in &cells {
            for (i, c) in controls.iter().enumerate() {
                let actual = convolve_resident(
                    s,
                    cell.temporal_view()?,
                    response(c, cell.sample_step(), 10 + i as u64)?,
                    PhaseCurrentReceiverId(3),
                    PhaseCurrentLineageId(30 + body.occurrences()),
                )?;
                body.advance_bilinear_contact(
                    cell.rational()?,
                    rational(c)?,
                    Some(actual.current()?),
                )?;
            }
        }
        Ok(())
    });
    report["training_observations"] = json!(body.occurrences() - calibration_cut);
    training?;
    // The unit digital response is an explicit initial current already exercised in development,
    // not a point selected from inferred evidence. Keep the actual source cell, immutable contact
    // and prediction alive across subsequent reception, so later inference cannot rewrite them.
    let free = stage(s, report, "free_condition_evidence", || {
        let source = ResidentPhaseCurrentView::new(
            rational(&zero)?,
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(2),
            Rat::from_integer(0.into()),
            chart.section().sample_step.clone(),
            WIDTH as u32,
            WIDTH,
        )?;
        let observed = convolve_resident(
            s,
            source,
            response(&controls[1], &chart.section().sample_step, 11)?,
            PhaseCurrentReceiverId(3),
            PhaseCurrentLineageId(105),
        )?;
        Ok(body.read_condition_preimage(rational(&zero)?, observed.current()?)?)
    })?;
    let (mut held, free_contact, anticipated) =
        stage(s, report, "generation_before_observation", || {
            let mut held = body.retain_condition_current(
                rational(&controls[1])?,
                ConditionContactMetric::UnitAdmittanceRealification,
            )?;
            let contact = held.contact(&free)?;
            let prediction =
                body.advance_bilinear_contact(hidden_cell.rational()?, contact.successor(), None)?;
            Ok((held, contact, prediction))
        })?;
    let actual = stage(s, report, "hidden_native_observation", || {
        Ok(convolve_resident(
            s,
            hidden_cell.temporal_view()?,
            response(&hidden_response, hidden_cell.sample_step(), 100)?,
            PhaseCurrentReceiverId(3),
            PhaseCurrentLineageId(101),
        )?)
    })?;
    let cut = body.occurrences();
    let preimage = stage(s, report, "condition_preimage", || {
        Ok(body.read_condition_preimage(hidden_cell.rational()?, actual.current()?)?)
    })?;
    report["preimage_relation_cut"] = json!(preimage.relation_cut());
    if body.occurrences() != cut {
        return Err("condition read changed the continuing relation".into());
    }
    let identified_contact = stage(s, report, "actual_condition_contact", || {
        Ok(held.contact(&preimage)?)
    })?;
    let generated = stage(s, report, "generation_after_contact", || {
        Ok(body.advance_bilinear_contact(
            later_cell.rational()?,
            identified_contact.successor(),
            None,
        )?)
    })?;
    // The two actual prediction carriers enter one ordinary native field recurrence. The field
    // has the caller-declared target aperture. Both occurrences receive no exterior values;
    // their resident inputs remain the actual prediction carriers supplied to this field.
    let mut generated_field = NativeConstitutiveField::found_with_enclosed_junction(
        s,
        (0..WIDTH + 1)
            .map(|_| NativeJunctionSeed {
                incoming_admittance: 1,
                held_admittance: 1,
                incoming_transport: NativePhaseCurrent::unit(),
                initial_held: NativePhaseCurrent::zero(),
            })
            .collect(),
        ResidentGrain(72),
    )?;
    let (first_field_lineage, second_field_lineage) =
        stage(s, report, "native_generated_field_recurrence", || {
            let mut entering = NativeFieldOccurrence::entering(Vec::new());
            let first =
                generated_field.advance_current_resident(&mut entering, anticipated.current())?;
            let first_lineage = first.lineage.clone();
            let mut linked = NativeFieldOccurrence::through(first.source, Vec::new());
            let second =
                generated_field.advance_current_resident(&mut linked, generated.current())?;
            Ok((first_lineage, second.lineage.clone()))
        })?;
    let image = stage(s, report, "whole_condition_image", || {
        Ok(body.read_condition_image(later_cell.rational()?, &preimage)?)
    })?;
    // Consume the whole supported image without selecting a condition. The unit first tap
    // preserves its coefficients; the declared zero second tap retains one extra zero tail.
    let image_carried = stage(s, report, "whole_image_temporal_continuation", || {
        let source = ResidentPhaseCurrentView::new(
            image.current(),
            PhaseCurrentReceiverId(3),
            PhaseCurrentLineageId(103),
            later_cell.support().begin.clone(),
            later_cell.sample_step().clone(),
            WIDTH as u32,
            WIDTH + 1,
        )?;
        Ok(convolve_resident(
            s,
            source,
            response(&controls[1], later_cell.sample_step(), 11)?,
            PhaseCurrentReceiverId(4),
            PhaseCurrentLineageId(104),
        )?)
    });
    // Attempt the native point consumer directly. Its device-side disposition check refuses
    // plural/outside conditions; the host does not inspect a fibre to select subsequent conduct.
    let predicted = stage(s, report, "inferred_prediction", || {
        Ok(body.advance_bilinear_contact(later_cell.rational()?, preimage.current(), None)?)
    });
    let later_actual = stage(s, report, "later_native_observation", || {
        Ok(convolve_resident(
            s,
            later_cell.temporal_view()?,
            response(&hidden_response, later_cell.sample_step(), 100)?,
            PhaseCurrentReceiverId(3),
            PhaseCurrentLineageId(102),
        )?)
    })?;
    let refined = stage(s, report, "received_family_refinement", || {
        Ok(image.receive(later_actual.current()?)?)
    });

    // Conduct each complete recording in one native operation. Both operations happen now;
    // the first reuses immutable earlier standing as a declared comparison, not retroactive
    // prediction. The learned local condition is the resident response operand throughout.
    let whole_outputs = if audio_directory.is_some() {
        let complete = stage(s, report, "whole_recording_mount", || {
            Ok(chart.mount_complete(s)?)
        })?;
        // Keep the input allocation alive through both complete operations, then publish only
        // their owned outputs. No PCM sample or phase-cell ordinal becomes a native event.
        let conduct = |condition, lineage| -> Result<ResidentPhaseConvolution<'_, 'c>> {
            Ok(convolve_resident(
                s,
                complete.temporal_view()?,
                ResidentPhaseCurrentView::new(
                    condition,
                    PhaseCurrentReceiverId(2),
                    PhaseCurrentLineageId(lineage),
                    Rat::from_integer(0.into()),
                    chart.section().sample_step.clone(),
                    WIDTH as u32,
                    2,
                )?,
                PhaseCurrentReceiverId(5),
                PhaseCurrentLineageId(lineage),
            )?)
        };
        let initial = stage(s, report, "whole_recording_initial_condition", || {
            conduct(free_contact.successor(), 110)
        })?;
        let successor = stage(s, report, "whole_recording_successor_condition", || {
            conduct(identified_contact.successor(), 111)
        })?;
        let directory = audio_directory.unwrap();
        let sample_rate = report["source"]["sample_rate"].as_u64().unwrap() as u32;
        let received = stage(s, report, "whole_recording_terminal_receiver", || {
            Ok(
                json!({"source_raw_extent":chart.section().raw_extent(),"response_raw_extent":2,
                "output_raw_extent":chart.section().raw_extent()+1,"gain":PCM_GAIN.to_string(),
                "channel_interpretation":"real-left-imaginary-right",
                "chronology":"both complete outputs are conducted after observation; the first uses the retained earlier condition for comparison",
                "initial_condition":publish_temporal(s,&initial,directory,"initial-condition",sample_rate)?,
                "successor_condition":publish_temporal(s,&successor,directory,"successor-condition",sample_rate)?}),
            )
        })?;
        Some(received)
    } else {
        None
    };

    // All numerical inspection happens after native development, inference and comparison act.
    let observed = stage(s, report, "terminal_observer", || {
        let condition = match preimage.inspect()? {
            ConditionPreimageReading::Compatible {
                particular,
                directions,
            } => json!({
                "status":if directions.is_empty(){"unique"}else{"plural"},"particular":strings(&particular),
                "directions":directions.iter().map(|v|strings(v)).collect::<Vec<_>>()}),
            ConditionPreimageReading::OutsideRepresentedRelation { residual } => {
                json!({"status":"outside","residual":strings(&residual)})
            }
        };
        let prediction = match &predicted {
            Ok(value) => returned(value)?,
            Err(error) => json!({"status":"native-consumer-refused","error":error.to_string()}),
        };
        let later = point(s, later_actual.section())?;
        let agreement = prediction["coordinates"].is_array()
            && prediction["coordinates"] == later["coordinates"];
        let carried = match &image_carried {
            Ok(value) => point(s, value.section())?,
            Err(error) => json!({"status":"native-consumer-refused","error":error.to_string()}),
        };
        let refined = match &refined {
            Ok(value) => json!({"reading":value.inspect()?}),
            Err(error) => json!({"status":"native-consumer-refused","error":error.to_string()}),
        };
        let current_cycle = json!({
            "initial_condition":point(s,&controls[1])?,
            "free_contact":free_contact.inspect()?,
            "identified_contact":identified_contact.inspect()?,
            "prediction_before_observation":returned(&anticipated)?,
            "prediction_after_contact":returned(&generated)?,
            "before_relation_cut":anticipated.occurrence(),
            "after_relation_cut":generated.occurrence(),
            "contacts":held.contacts(),
        });
        let field_incoming = (0..2)
            .map(|at| generated_field.inspect_incoming(at))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        let field_junctions = (0..2)
            .map(|at| {
                generated_field
                    .inspect_junction(at)
                    .map(|rest| rest.as_ref().map(section_wire))
            })
            .collect::<std::result::Result<Vec<_>, _>>()?;
        let native_field = json!({
            "nodes":WIDTH + 1,
            "grain":72,
            "linked_occurrences":1,
            "empty_exterior_input":true,
            "lineages":[first_field_lineage.clone(),second_field_lineage.clone()],
            "actual_incoming":field_incoming,
            "junction_reports":field_junctions,
            "junction_covariance":generated_field.inspect_junction_covariance()?.as_ref().map(section_wire),
            "internal_currents":generated_field.inspect_internal_currents()?,
            "occurrence_count":generated_field.occurrence_count(),
        });
        Ok(
            json!({"preimage":condition,"prediction":prediction,"later_actual":later,"exact_agreement":agreement,
            "actual_condition_current_cycle":current_cycle,
            "prediction_carriers":{"anticipated":{"occurrence":anticipated.occurrence(),"reading":anticipated.inspect()?},
                "generated":{"occurrence":generated.occurrence(),"reading":generated.inspect()?}},
            "native_generated_field":native_field,
            "temporal_support_external_to_field":{"hidden":hidden_cell.support(),"later":later_cell.support(),
                "binding":"recorded temporal support remains exterior lineage to the native field"},
            "whole_image":image.inspect()?,"whole_image_carried":carried,"refined_condition":refined,
            "hidden_source":point(s,hidden_cell.section())?,"later_source":point(s,later_cell.section())?,
            "hidden_response":point(s,&hidden_response)?,"hidden_actual":point(s,actual.section())?}),
        )
    })?;
    report["observation"] = observed;
    if let Some(whole) = whole_outputs {
        report["whole_recording"] = whole;
    }
    // Completion is an observer statement about this comparison, never a generation gate.
    let mut expected = report["observation"]["later_actual"]["coordinates"]
        .as_array()
        .unwrap()
        .clone();
    expected.extend([json!("0"), json!("0")]);
    report["complete_bounded_comparison"] =
        json!(report["observation"]["whole_image_carried"]["coordinates"] == json!(expected));
    Ok(())
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if !(2..=3).contains(&args.len()) {
        return Err(
            "usage: recorded_temporal_action WAV_PATH NEW_REPORT.json [NEW_AUDIO_DIR]".into(),
        );
    }
    let wav_path = PathBuf::from(&args[0]);
    let report_path = PathBuf::from(&args[1]);
    if report_path.exists() {
        return Err("report already exists".into());
    }
    let audio_directory = args.get(2).map(PathBuf::from);
    let audio_directory = audio_directory
        .map(|directory| -> Result<PathBuf> {
            if let Some(parent) = directory.parent().filter(|p| !p.as_os_str().is_empty()) {
                fs::create_dir_all(parent)?;
            }
            fs::create_dir(&directory)?;
            Ok(directory.canonicalize()?)
        })
        .transpose()?;
    let started = Instant::now();
    let recording = ExactAcousticOccurrence::read(
        &wav_path,
        format!("recorded-temporal-action:{}", wav_path.display()),
        4096,
        4096,
        1,
    )?;
    let decode_seconds = started.elapsed().as_secs_f64();
    let readout = ResidentReadout::new()?;
    let s = ResidentSurface::on(&readout)?;
    let chart = AcousticFieldChart::from_acoustic(
        &recording,
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(1),
        Rat::from_integer(0.into()),
        WIDTH,
        DIVISOR,
    )?;
    let mut report = json!({"schema":if audio_directory.is_some(){"holonics.recorded-temporal-action.v5"}else{"holonics.recorded-temporal-action.v4"},"truth_status":"established-bounded",
        "evidence_tags":["measured"],"scope":"declared complex polynomial action on recorded coefficients",
        "source":{"path":wav_path,"sha256":recording.source_sha256,"octets":recording.source_octets,
            "samples":recording.samples.len(),"sample_rate":recording.sample_rate,"occurrence":recording.occurrence,
            "receiver":1,"lineage":1},
        "aperture":{"source_complex":WIDTH,"condition_complex":2,"target_complex":WIDTH+1,"pcm_divisor":DIVISOR,
            "field_nodes":WIDTH+1,"field_grain":72,
            "interpretation":"caller-declared recorded coefficient and native field aperture, not learned semantic grain"},
        "response_control":{"coordinates":["2","-1","5","3"],"denominator":"3",
            "interpretation":"independently controlled complex digital two-tap action; no physical room/utterance response claim"},
        "training_controls":CONTROLS,"decode_seconds":decode_seconds,"active_stage":"found-owner","stages":{},
        "complete_bounded_comparison":false,"sound_model":false,"conversation_model":false});
    match ResidentConstitutiveFibre::found_bilinear_contact(&s, WIDTH, 2, WIDTH + 1) {
        Ok(mut body) => {
            if let Err(error) = experiment(
                &s,
                &chart,
                &mut body,
                &mut report,
                audio_directory.as_deref(),
            ) {
                report["refusal"] =
                    json!({"stage":report["active_stage"],"error":error.to_string()});
            }
            report["learner_occurrences"] = json!(body.occurrences());
        }
        Err(error) => report["refusal"] = json!({"stage":"found-owner","error":error.to_string()}),
    }
    report["elapsed_seconds"] = json!(started.elapsed().as_secs_f64());
    report["final_census"] = json!(s.census());
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&report_path)?;
    serde_json::to_writer_pretty(&mut file, &report)?;
    file.write_all(b"\n")?;
    file.sync_all()?;
    println!(
        "{}",
        json!({"report":report_path,"recorded_observations":report["training_observations"],
        "preimage":report["observation"]["preimage"]["status"],
        "point_condition_agreement":report["observation"]["exact_agreement"],
        "whole_family_agreement":report["complete_bounded_comparison"],"refusal":report["refusal"]})
    );
    Ok(())
}
