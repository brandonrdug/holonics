//! File commands over the public continuing temporal response boundary.
use clap::Subcommand;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, ResidentTemporalConditionCurrent, TemporalResponseChart,
    },
    phase_current::{
        PhaseCurrentLineageId, PhaseCurrentReceiverId, resident::ResidentPhaseEnclosureView,
    },
    resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface},
};
use holonics_hna::native::temporal_acoustic::{
    SavedTemporalAcousticSession, TemporalAcousticChart, TemporalAcousticSession,
};
use life::{
    mathematical_source::ExactAcousticOccurrence,
    native_intelligence::NativeAcousticEnclosedTemporalPcm16Projection,
};
use num_rational::BigRational as Rat;
use serde_json::{Value, json};
use std::{
    error::Error,
    fs,
    io::{BufWriter, Write},
    path::{Path, PathBuf},
    time::Instant,
};

type Result<T> = std::result::Result<T, Box<dyn Error>>;

#[derive(Subcommand)]
pub enum Action {
    /// Start from an explicit unit impulse and receive complete excitation/observation pairs.
    Start {
        /// Caller-declared causal response aperture in samples; not learned acoustic grains.
        #[arg(long)]
        taps: usize,
        /// Numerical binary enclosure grain, independent of the response aperture.
        #[arg(long)]
        grain: u32,
        /// New directory receiving a durable response, contact report and predicted sound.
        #[arg(long)]
        output: PathBuf,
        /// Positive exact PCM units per native unit, recorded in every output receipt.
        #[arg(long, default_value = "32768")]
        gain: Rat,
        /// Alternating excitation.wav observation.wav paths; pairs share their original clock.
        #[arg(required = true, num_args = 2..)]
        pairs: Vec<PathBuf>,
    },
    /// Receive additional complete pairs using a saved response and its exact construction.
    Continue {
        checkpoint: PathBuf,
        #[arg(long)]
        output: PathBuf,
        #[arg(long, default_value = "32768")]
        gain: Rat,
        #[arg(required = true, num_args = 2..)]
        pairs: Vec<PathBuf>,
    },
    /// Produce timed sound from a saved response and source recording, without an observation.
    Predict {
        checkpoint: PathBuf,
        wav: PathBuf,
        #[arg(long)]
        occurrence: String,
        #[arg(long)]
        output: PathBuf,
        #[arg(long, default_value = "32768")]
        gain: Rat,
    },
    /// Read the saved chart and recording chronology without mounting a native device.
    Inspect { checkpoint: PathBuf },
}

fn read(path: &Path, occurrence: String) -> Result<ExactAcousticOccurrence> {
    Ok(ExactAcousticOccurrence::read(
        path, occurrence, 4096, 4096, 4,
    )?)
}
fn write_json(path: &Path, value: &impl serde::Serialize) -> Result<()> {
    holonics_hna::publish_new(path, |file| {
        let mut output = BufWriter::new(file);
        serde_json::to_writer(&mut output, value).map_err(std::io::Error::other)?;
        output.flush()
    })?;
    Ok(())
}

/// This explicitly cold receiver keeps the source ball in its projection record. WAV is only
/// the two-channel numerical representative; hearing it does not establish acoustic usefulness.
fn render(
    surface: &ResidentSurface<'_>,
    view: ResidentPhaseEnclosureView<'_, '_>,
    directory: &Path,
    name: &str,
    sample_rate: u32,
    gain: &Rat,
) -> Result<Value> {
    let started = Instant::now();
    let ball = view.inspect(surface)?;
    let projection = NativeAcousticEnclosedTemporalPcm16Projection::found(
        view.receiver(),
        view.lineage(),
        view.origin().clone(),
        view.sample_step().clone(),
        sample_rate,
        gain.clone(),
        &ball,
    )?;
    // Keep this actual output boundary explicit and recoverable even if subsequent publication fails.
    let receipt = directory.join(format!("{name}.projection.json"));
    write_json(&receipt, &projection)?;
    let wav = directory.join(format!("{name}.wav"));
    let bytes = projection.wav_bytes()?;
    holonics_hna::publish_new(&wav, |file| file.write_all(&bytes))?;
    Ok(
        json!({"wav":wav,"projection":receipt,"frames":projection.frames.len(),"sample_rate":sample_rate,
        "channels":["real","imaginary"],"radius_native_units":projection.radius.to_string(),
        "clipped_coordinates":projection.clipped_sample_population,"gain":gain.to_string(),
        "cold_receiver_seconds":started.elapsed().as_secs_f64(),"wav_is_numerical_representative":true}),
    )
}

fn receive_pairs(
    surface: &ResidentSurface<'_>,
    session: &mut TemporalAcousticSession<'_>,
    pairs: &[PathBuf],
    output: &Path,
    gain: &Rat,
    mount: Value,
) -> Result<()> {
    let started = Instant::now();
    let mut results = Vec::new();
    let mut failure = None;
    for pair in pairs.chunks_exact(2) {
        let cut = session.contacts();
        eprintln!(
            "{}",
            json!({"stage":"recorded_contact","cut":cut,"status":"started"})
        );
        let result = (|| -> Result<Value> {
            let source = read(&pair[0], format!("temporal-excitation-{cut}"))?;
            let observed = read(&pair[1], format!("temporal-observed-{cut}"))?;
            session.receive(&source, Rat::from_integer(0.into()), &observed, Rat::from_integer(0.into()), |returned| -> Result<Value> {
                let sound = render(surface, returned.prediction.view(), output, &format!("prediction_cut_{cut}"), source.sample_rate, gain)?;
                Ok(json!({"contact":returned.receipt,"prediction_work":returned.prediction_work,
                    "difference_work":returned.difference_work,"contact_work":returned.contact_work,"sound":sound}))
            })?
        })();
        match result {
            Ok(result) => results.push(result),
            Err(error) => {
                failure = Some(error.to_string());
                break;
            }
        }
        eprintln!(
            "{}",
            json!({"stage":"recorded_contact","cut":cut,"successor_cut":session.contacts(),"status":"returned"})
        );
    }
    // A cold receiver failure may follow an already completed contact. Save that actual successor
    // before reporting failure; do not rewind it or replay the same observation silently.
    let checkpoint = output.join("response.hna");
    let checkpoint_started = Instant::now();
    let saved = session.save(&checkpoint);
    let (octets, checkpoint_error) = match saved {
        Ok(receipt) => (Some(receipt.bytes), None),
        Err(error) => (None, Some(error.to_string())),
    };
    let report = json!({"schema":"holonics.temporal-acoustic-application.v1",
        "scope":"continuing recorded temporal response and cold enclosed PCM receiver",
        "status":if failure.is_none() && checkpoint_error.is_none(){"returned"}else{"incomplete"},
        "device":surface.device_name(),"mount":mount,"contacts":session.contacts(),"results":results,
        "history":session.history(),"failure":failure,"checkpoint":checkpoint,"checkpoint_octets":octets,
        "checkpoint_error":checkpoint_error,"checkpoint_seconds":checkpoint_started.elapsed().as_secs_f64(),
        "elapsed_seconds":started.elapsed().as_secs_f64(),"final_census":surface.census(),
        "useful_sound_model":false,"conversation_model":false,"streaming":false});
    write_json(&output.join("return.json"), &report)?;
    println!(
        "{}",
        json!({"status":report["status"],"report":output.join("return.json"),"checkpoint":checkpoint,"contacts":session.contacts()})
    );
    if failure.is_some() || checkpoint_error.is_some() {
        return Err("recorded operation or publication incomplete; return.json identifies the saved successor and error".into());
    }
    Ok(())
}

fn validate_output_pairs(output: &Path, pairs: &[PathBuf], gain: &Rat) -> Result<()> {
    if pairs.is_empty() || pairs.len() % 2 != 0 {
        return Err("supply complete excitation/observation pairs".into());
    }
    if gain <= &Rat::from_integer(0.into()) {
        return Err("gain must be positive".into());
    }
    fs::create_dir(output)?;
    Ok(())
}

pub fn run(command: Action) -> Result<()> {
    if let Action::Inspect { checkpoint } = &command {
        let saved = SavedTemporalAcousticSession::read(checkpoint)?;
        println!(
            "{}",
            serde_json::to_string_pretty(&json!({"checkpoint":checkpoint,"chart":saved.chart(),
            "response_chart":saved.response().chart(),"grain":saved.response().grain(),
            "contacts":saved.response().contacts(),"history":saved.history()}))?
        );
        return Ok(());
    }
    let readout = ResidentReadout::new()?;
    let surface = ResidentSurface::on(&readout)?;
    match command {
        Action::Start {
            taps,
            grain,
            output,
            gain,
            pairs,
        } => {
            if taps == 0 || !(1..=120).contains(&grain) {
                return Err("positive response taps and grain in 1..=120 required".into());
            }
            validate_output_pairs(&output, &pairs, &gain)?;
            let source = read(&pairs[0], "initial-clock".into())?;
            let width = taps
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .filter(|n| *n <= u32::MAX as usize)
                .ok_or("response aperture overflow")?;
            let mut words = vec![(0, 0); width];
            words[0] = (1, 1);
            words[width - 1] = (1, 1);
            let section = surface.mount_section_rest(&ResidentSectionRest::found(
                1,
                width,
                ResidentGrain(0),
                64,
                words,
            )?)?;
            let current = ResidentTemporalConditionCurrent::retain(
                &surface,
                section,
                TemporalResponseChart {
                    receiver: PhaseCurrentReceiverId(8),
                    origin: Rat::from_integer(0.into()),
                    sample_step: Rat::new(1.into(), source.sample_rate.into()),
                    phase_extent: 4,
                    raw_extent: taps,
                },
                PhaseCurrentLineageId(3),
                grain,
                ConditionContactMetric::UnitAdmittanceRealification,
            )?;
            let mut session = TemporalAcousticSession::retain(
                &surface,
                current,
                TemporalAcousticChart {
                    sample_rate: source.sample_rate,
                    pcm_divisor: 32768,
                    source_receiver: PhaseCurrentReceiverId(1),
                    output_receiver: PhaseCurrentReceiverId(9),
                },
            )?;
            receive_pairs(
                &surface,
                &mut session,
                &pairs,
                &output,
                &gain,
                json!({"kind":"explicit_unit_impulse","taps":taps,"grain":grain}),
            )?;
        }
        Action::Continue {
            checkpoint,
            output,
            gain,
            pairs,
        } => {
            validate_output_pairs(&output, &pairs, &gain)?;
            let saved = SavedTemporalAcousticSession::read(&checkpoint)?;
            let started = Instant::now();
            let before = surface.census();
            let mut session = saved.remount(&surface)?;
            let after = surface.census();
            let mount = json!({"kind":"remount","checkpoint":checkpoint,"cut":session.contacts(),"seconds":started.elapsed().as_secs_f64(),
                "deeds":after.deed_launches-before.deed_launches,"section_readouts":after.section_read_outs-before.section_read_outs,
                "ingress_octets":after.ingress_octets-before.ingress_octets});
            receive_pairs(&surface, &mut session, &pairs, &output, &gain, mount)?;
        }
        Action::Predict {
            checkpoint,
            wav,
            occurrence,
            output,
            gain,
        } => {
            if gain <= Rat::from_integer(0.into()) {
                return Err("gain must be positive".into());
            }
            fs::create_dir(&output)?;
            let saved = SavedTemporalAcousticSession::read(&checkpoint)?;
            let before = surface.census();
            let started = Instant::now();
            let session = saved.remount(&surface)?;
            let after = surface.census();
            let remount = json!({"seconds":started.elapsed().as_secs_f64(),"deeds":after.deed_launches-before.deed_launches,
                "section_readouts":after.section_read_outs-before.section_read_outs,"ingress_octets":after.ingress_octets-before.ingress_octets});
            let source = read(&wav, occurrence)?;
            let report = session.predict(&source,Rat::from_integer(0.into()),PhaseCurrentLineageId(u64::MAX),|prediction,work| -> Result<Value> {
                let sound = render(&surface,prediction.view(),&output,"prediction",source.sample_rate,&gain)?;
                Ok(json!({"schema":"holonics.temporal-acoustic-prediction.v1","status":"returned","checkpoint":checkpoint,
                    "source":wav,"source_sha256":source.source_sha256,"source_octets":source.source_octets,
                    "occurrence":source.occurrence,"response_cut":session.contacts(),"remount":remount,
                    "prediction_work":work,"sound":sound,"condition_updated":false}))
            })??;
            write_json(&output.join("return.json"), &report)?;
            println!(
                "{}",
                json!({"status":"returned","report":output.join("return.json"),"sound":output.join("prediction.wav")})
            );
        }
        Action::Inspect { .. } => unreachable!(),
    }
    Ok(())
}
