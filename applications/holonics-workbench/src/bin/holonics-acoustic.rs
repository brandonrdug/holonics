//! File/application boundary for exact sampled sound on the existing native HNA session.
use clap::{Parser, Subcommand};
use holonic_engine::phase_current::{PhaseCurrentLineageId, PhaseCurrentReceiverId};
use holonics_hna::native::{
    append_acoustic, resume_acoustic, run_acoustic_with_options, AcousticApplication,
    AcousticRunOptions, AcousticSavedApplication, CurrentWire, NativeModelSpec,
};
use life::mathematical_source::ExactAcousticOccurrence;
use life::native_intelligence::{NativeAcousticPotentialComplex, NativeAcousticReceiverChart};
use num_rational::BigRational;
use serde::Serialize;
use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
    time::Instant,
};

#[path = "holonics-acoustic/temporal.rs"]
mod temporal;

#[derive(Parser)]
#[command(about = "Exact sampled-sound experiments through one native phase ecology")]
struct Cli {
    #[command(subcommand)]
    command: Action,
}
#[derive(Subcommand)]
enum Action {
    /// Develop, persist and hear a continuing response over complete recording sections.
    Temporal {
        #[command(subcommand)]
        command: temporal::Action,
    },
    /// Inspect the sample position and complete last native return without replaying it.
    Inspect { source: PathBuf },
    /// Receive each PCM16 sample in order. Dataset labels never enter this interface.
    Run {
        #[arg(long)]
        seed: PathBuf,
        #[arg(long)]
        wav: PathBuf,
        /// Source occurrence coordinate, distinct from its filename/content.
        #[arg(long)]
        occurrence: String,
        #[arg(long)]
        checkpoint: PathBuf,
        /// Optional process cut. The remainder stays in the checkpoint.
        #[arg(long)]
        samples: Option<usize>,
        /// Exact digital amplitude divisor; this does not assert calibrated acoustic pressure.
        #[arg(long, default_value_t = 32768)]
        divisor: i64,
        /// JSON array of exact per-node gains for an explicitly declared one-sample digital return.
        #[arg(long)]
        return_couplings: Option<PathBuf>,
        /// Exterior source frame length and hop; this does not define native recurrence.
        #[arg(long, default_value_t = 4096)]
        frame_size: u32,
    },
    /// Append a complete new PCM recording to an existing acoustic owner/checkpoint.
    Append {
        /// Existing complete acoustic checkpoint whose continuing owner receives the recording.
        source: PathBuf,
        #[arg(long)]
        wav: PathBuf,
        /// Source occurrence coordinate, distinct from its filename/content.
        #[arg(long)]
        occurrence: String,
        #[arg(long)]
        checkpoint: PathBuf,
        /// Optional process cut. The remainder stays in the new checkpoint.
        #[arg(long)]
        samples: Option<usize>,
        /// Exact digital amplitude divisor; this does not assert calibrated acoustic pressure.
        #[arg(long, default_value_t = 32768)]
        divisor: i64,
        /// JSON array of exact per-node gains for an explicitly declared one-sample digital return.
        #[arg(long)]
        return_couplings: Option<PathBuf>,
        /// Exterior source frame length and hop; this does not define native recurrence.
        #[arg(long, default_value_t = 4096)]
        frame_size: u32,
    },
    /// Continue the next pending sample from a complete application/native checkpoint.
    Resume {
        source: PathBuf,
        #[arg(long)]
        checkpoint: PathBuf,
        #[arg(long)]
        samples: Option<usize>,
    },
    /// Calibrate one cold receiver, to reuse unchanged for subsequent sound comparisons.
    Receiver {
        source: PathBuf,
        #[arg(long)]
        output: PathBuf,
        #[arg(long, default_value_t = 44100)]
        sample_rate: u32,
        #[arg(long, default_value_t = 1)]
        stride: u32,
        #[arg(long, default_value_t = 64)]
        support: u32,
        #[arg(long, default_value_t = 80)]
        low_hz: u32,
        #[arg(long, default_value_t = 8000)]
        high_hz: u32,
    },
    /// Render actual native emitted currents through a previously saved cold receiver.
    Render {
        source: PathBuf,
        #[arg(long)]
        receiver: PathBuf,
        /// New directory containing WAV and exact production/receiver reconstruction artifacts.
        #[arg(long)]
        output: PathBuf,
    },
}
fn read<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T, Box<dyn std::error::Error>> {
    Ok(serde_json::from_slice(&fs::read(path)?)?)
}
fn write_new(path: &Path, bytes: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
    holonics_hna::publish_new(path, |file| {
        file.write_all(bytes)?;
        Ok(())
    })?;
    Ok(())
}
fn json_new(path: &Path, value: &impl Serialize) -> Result<(), Box<dyn std::error::Error>> {
    write_new(path, &serde_json::to_vec_pretty(value)?)
}
fn read_acoustic_occurrence(
    wav: &Path,
    occurrence: String,
    frame_size: u32,
) -> Result<(ExactAcousticOccurrence, Vec<u8>), Box<dyn std::error::Error>> {
    if frame_size == 0 {
        return Err("--frame-size must be positive".into());
    }
    let bytes = fs::read(wav)?;
    let source = ExactAcousticOccurrence::from_wav_bytes(
        &bytes,
        occurrence,
        wav.display().to_string(),
        frame_size,
        frame_size,
        1,
    )?;
    Ok((source, bytes))
}
fn recording_summary(app: &AcousticApplication) -> serde_json::Value {
    serde_json::json!({
        "occurrence": app.occurrence().occurrence,
        "locator": app.occurrence().locator,
        "sample_rate": app.occurrence().sample_rate,
        "sample_count": app.occurrence().samples.len(),
        "frame_length": app.occurrence().frame_length,
        "frame_hop": app.occurrence().frame_hop,
        "native_start": app.native_start(),
        "next_sample": app.cursor(),
        "complete": app.complete(),
        "pending": app.pending(),
    })
}
fn production(
    path: &Path,
) -> Result<
    (
        life::native_intelligence::NativeAcousticProductionSection,
        serde_json::Value,
    ),
    Box<dyn std::error::Error>,
> {
    let saved = AcousticSavedApplication::read(path)?;
    let app = saved.application();
    // These are exterior receiver/lineage coordinates. Serialized digests protect the
    // source chart, never identify holons or substitute for the emitted current fibre.
    use sha2::{Digest, Sha256};
    let digest = |bytes: &[u8]| {
        Sha256::digest(bytes)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    };
    let model = digest(&serde_json::to_vec(app.spec())?);
    let emissions = digest(&serde_json::to_vec(app.steps())?);
    let scope = serde_json::json!({"source_checkpoint":path,"input_complete":app.complete(),
        "next_input_sample":app.cursor(),"input_samples":app.occurrence().samples.len(),
        "sample_rate":app.occurrence().sample_rate,"pending_input":app.pending()});
    let section = app
        .production(
            model,
            emissions,
            PhaseCurrentReceiverId(0),
            PhaseCurrentLineageId(0),
            BigRational::from_integer(0.into()),
            BigRational::new(1.into(), app.occurrence().sample_rate.into()),
        )?
        .1;
    Ok((section, scope))
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let started = Instant::now();
    match Cli::parse().command {
        Action::Temporal { command } => temporal::run(command)?,
        Action::Inspect { source } => {
            let saved = AcousticSavedApplication::read(&source)?;
            let app = saved.application();
            println!(
                "{}",
                serde_json::to_string_pretty(&serde_json::json!({
                    "checkpoint":source, "occurrence":app.occurrence().occurrence,
                    "locator":app.occurrence().locator, "sample_rate":app.occurrence().sample_rate,
                    "total_samples":app.occurrence().samples.len(), "next_sample":app.cursor(),
                    "complete":app.complete(), "pending":app.pending(),
                    "pcm_divisor":app.pcm_divisor(),"digital_return_couplings":app.return_couplings(),
                    "first_native_return":app.steps().first(), "last_native_return":app.steps().last(),
                    "native_start":app.native_start(),
                    "recording_count":app.recording_count(),
                    "current_recording":recording_summary(app),
                    "completed_recordings":app.completed_recordings().iter().map(recording_summary).collect::<Vec<_>>()
                }))?
            );
        }
        Action::Run {
            seed,
            wav,
            occurrence,
            checkpoint,
            samples,
            divisor,
            return_couplings,
            frame_size,
        } => {
            let model: NativeModelSpec = read(&seed)?;
            let (occurrence, bytes) = read_acoustic_occurrence(&wav, occurrence, frame_size)?;
            let gains: Option<Vec<CurrentWire>> =
                return_couplings.as_deref().map(read).transpose()?;
            let run = run_acoustic_with_options(
                &model,
                &occurrence,
                &bytes,
                divisor,
                gains,
                &AcousticRunOptions {
                    samples,
                    checkpoint: Some(checkpoint.clone()),
                },
            )?;
            println!(
                "{}",
                serde_json::json!({"cursor":run.cursor,"complete":run.complete,
                "checkpoint":run.checkpoint,"checkpoint_octets":run.checkpoint_octets,
                "checkpoint_error":run.checkpoint_error,"interruption":run.interruption,
                "pending":run.pending,"elapsed_ns":started.elapsed().as_nanos()})
            );
            if run.interruption.is_some() || run.checkpoint_error.is_some() {
                std::process::exit(1);
            }
        }
        Action::Append {
            source,
            wav,
            occurrence,
            checkpoint,
            samples,
            divisor,
            return_couplings,
            frame_size,
        } => {
            let (occurrence, bytes) = read_acoustic_occurrence(&wav, occurrence, frame_size)?;
            let gains: Option<Vec<CurrentWire>> =
                return_couplings.as_deref().map(read).transpose()?;
            let run = append_acoustic(
                &source,
                &occurrence,
                &bytes,
                divisor,
                gains,
                &AcousticRunOptions {
                    samples,
                    checkpoint: Some(checkpoint),
                },
            )?;
            println!(
                "{}",
                serde_json::json!({"cursor":run.cursor,"complete":run.complete,
                "checkpoint":run.checkpoint,"checkpoint_octets":run.checkpoint_octets,
                "checkpoint_error":run.checkpoint_error,"interruption":run.interruption,
                "pending":run.pending,"elapsed_ns":started.elapsed().as_nanos()})
            );
            if run.interruption.is_some() || run.checkpoint_error.is_some() {
                std::process::exit(1);
            }
        }
        Action::Resume {
            source,
            checkpoint,
            samples,
        } => {
            let run = resume_acoustic(
                source,
                &AcousticRunOptions {
                    samples,
                    checkpoint: Some(checkpoint),
                },
            )?;
            println!(
                "{}",
                serde_json::json!({"cursor":run.cursor,"complete":run.complete,
                "checkpoint":run.checkpoint,"checkpoint_octets":run.checkpoint_octets,
                "checkpoint_error":run.checkpoint_error,"interruption":run.interruption,
                "pending":run.pending,"elapsed_ns":started.elapsed().as_nanos()})
            );
            if run.interruption.is_some() || run.checkpoint_error.is_some() {
                std::process::exit(1);
            }
        }
        Action::Receiver {
            source,
            output,
            sample_rate,
            stride,
            support,
            low_hz,
            high_hz,
        } => {
            let (current, scope) = production(&source)?;
            let receiver = NativeAcousticReceiverChart::calibrated_from(
                &current,
                sample_rate,
                stride,
                support,
                low_hz,
                high_hz,
            )?;
            json_new(&output, &receiver)?;
            println!(
                "{}",
                serde_json::json!({"receiver":output,"source_scope":scope,"elapsed_ns":started.elapsed().as_nanos()})
            );
        }
        Action::Render {
            source,
            receiver,
            output,
        } => {
            // One newly created artifact directory retains partial work if a later write fails.
            fs::create_dir(&output)?;
            let (current, scope) = production(&source)?;
            let receiver: NativeAcousticReceiverChart = read(&receiver)?;
            let potential = NativeAcousticPotentialComplex::found(&current, receiver)?;
            let pcm = potential.render_pcm16()?;
            json_new(&output.join("scope.json"), &scope)?;
            json_new(&output.join("production.json"), &current)?;
            json_new(&output.join("potential.json"), &potential)?;
            json_new(&output.join("projection.json"), &pcm)?;
            write_new(&output.join("sound.wav"), &pcm.wav_bytes()?)?;
            println!(
                "{}",
                serde_json::json!({"output":output,"source_scope":scope,"samples":pcm.samples.len(),
                "sample_rate":pcm.sample_rate,"elapsed_ns":started.elapsed().as_nanos()})
            );
        }
    }
    Ok(())
}
