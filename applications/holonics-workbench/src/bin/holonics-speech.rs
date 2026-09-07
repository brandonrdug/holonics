//! Curated WAV/text exposure at the public native application boundary.
use clap::{Parser, Subcommand};
use holonic_engine::phase_current::{PhaseCurrentLineageId, PhaseCurrentReceiverId};
use holonics_hna::native::{
    CurrentWire, NativeModelSpec, SpeechRun, SpeechRunOptions, SpeechSavedApplication,
    resume_speech, run_speech_with_options,
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

#[derive(Parser)]
#[command(about = "Curated sound then text exposure through one continuing native ecology")]
struct Cli {
    #[command(subcommand)]
    command: Action,
}

#[derive(Subcommand)]
enum Action {
    Run {
        #[arg(long)]
        seed: PathBuf,
        #[arg(long)]
        wav: PathBuf,
        #[arg(long)]
        occurrence: String,
        /// Separate source bytes; shared wording does not identify an acoustic occurrence.
        #[arg(long)]
        transcript: PathBuf,
        #[arg(long)]
        checkpoint: PathBuf,
        /// Exterior process cut across acoustic samples followed by transcript bytes.
        #[arg(long)]
        occurrences: Option<usize>,
        #[arg(long, default_value_t = 32768)]
        pcm_divisor: i64,
        #[arg(long, default_value_t = 256)]
        transcript_divisor: i64,
        /// Optional explicit digital return law; no law leaves arrivals unlinked.
        #[arg(long)]
        return_couplings: Option<PathBuf>,
    },
    Resume {
        source: PathBuf,
        #[arg(long)]
        checkpoint: PathBuf,
        #[arg(long)]
        occurrences: Option<usize>,
    },
    Inspect {
        source: PathBuf,
    },
    /// Make actual sound/text reaction emissions audible under a previously fixed receiver.
    Render {
        source: PathBuf,
        #[arg(long)]
        receiver: PathBuf,
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
fn report(run: SpeechRun, started: Instant) -> Result<(), Box<dyn std::error::Error>> {
    println!(
        "{}",
        serde_json::json!({
            "complete":run.complete,"acoustic_cursor":run.acoustic_cursor,
            "transcript_cursor":run.transcript_cursor,"pending":run.pending,
            "acoustic_pending":run.acoustic_pending,
            "checkpoint":run.checkpoint,"checkpoint_octets":run.checkpoint_octets,
            "checkpoint_error":run.checkpoint_error,"interruption":run.interruption,
            "first_text_return":run.transcript_steps.first(),
            "last_text_return":run.transcript_steps.last(),
            "elapsed_ns":started.elapsed().as_nanos()
        })
    );
    if run.interruption.is_some() || run.checkpoint_error.is_some() {
        std::process::exit(1);
    }
    Ok(())
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let started = Instant::now();
    match Cli::parse().command {
        Action::Run {
            seed,
            wav,
            occurrence,
            transcript,
            checkpoint,
            occurrences,
            pcm_divisor,
            transcript_divisor,
            return_couplings,
        } => {
            let spec: NativeModelSpec = read(&seed)?;
            let bytes = fs::read(&wav)?;
            let occurrence = ExactAcousticOccurrence::from_wav_bytes(
                &bytes,
                occurrence,
                wav.display().to_string(),
                1,
                1,
                1,
            )?;
            let gains: Option<Vec<CurrentWire>> =
                return_couplings.as_deref().map(read).transpose()?;
            let run = run_speech_with_options(
                &spec,
                &occurrence,
                &bytes,
                pcm_divisor,
                gains,
                &fs::read(transcript)?,
                transcript_divisor,
                &SpeechRunOptions {
                    occurrences,
                    checkpoint: Some(checkpoint),
                },
            )?;
            report(run, started)?;
        }
        Action::Resume {
            source,
            checkpoint,
            occurrences,
        } => {
            report(
                resume_speech(
                    source,
                    &SpeechRunOptions {
                        occurrences,
                        checkpoint: Some(checkpoint),
                    },
                )?,
                started,
            )?;
        }
        Action::Inspect { source } => {
            let saved = SpeechSavedApplication::read(&source)?;
            let app = saved.application();
            println!(
                "{}",
                serde_json::to_string_pretty(&serde_json::json!({
                    "checkpoint":source,"complete":app.complete(),
                    "acoustic_cursor":app.acoustic().cursor(),
                    "acoustic_samples":app.acoustic().occurrence().samples.len(),
                    "acoustic_pending":app.acoustic().pending(),
                    "transcript_cursor":app.transcript_cursor(),
                    "transcript_bytes":app.transcript(),"transcript_pending":app.pending(),
                    "last_sound_return":app.acoustic().steps().last(),
                    "first_text_return":app.transcript_steps().first(),
                    "last_text_return":app.transcript_steps().last()
                }))?
            );
        }
        Action::Render {
            source,
            receiver,
            output,
        } => {
            let saved = SpeechSavedApplication::read(&source)?;
            let app = saved.application();
            use sha2::{Digest, Sha256};
            let digest = |bytes: &[u8]| {
                Sha256::digest(bytes)
                    .iter()
                    .map(|byte| format!("{byte:02x}"))
                    .collect::<String>()
            };
            let model = digest(&serde_json::to_vec(app.acoustic().spec())?);
            let lineage = digest(&serde_json::to_vec(app)?);
            let section = app
                .production(
                    model,
                    lineage,
                    PhaseCurrentReceiverId(0),
                    PhaseCurrentLineageId(0),
                    BigRational::from_integer(0.into()),
                    BigRational::new(1.into(), app.acoustic().occurrence().sample_rate.into()),
                )?
                .1;
            let receiver: NativeAcousticReceiverChart = read(&receiver)?;
            let potential = NativeAcousticPotentialComplex::found(&section, receiver)?;
            let pcm = potential.render_pcm16()?;
            fs::create_dir(&output)?;
            let scope = serde_json::json!({"source_checkpoint":source,
                "input_complete":app.complete(),"acoustic_samples":app.acoustic().cursor(),
                "transcript_bytes":app.transcript_cursor(),
                "receiver_order":"sample arrivals followed by byte arrivals; sonification clock, no word alignment",
                "speech_recognition_or_synthesis_claimed":false});
            json_new(&output.join("scope.json"), &scope)?;
            json_new(&output.join("production.json"), &section)?;
            json_new(&output.join("potential.json"), &potential)?;
            json_new(&output.join("projection.json"), &pcm)?;
            write_new(&output.join("sound.wav"), &pcm.wav_bytes()?)?;
            println!(
                "{}",
                serde_json::json!({"output":output,"scope":scope,
                "samples":pcm.samples.len(),"sample_rate":pcm.sample_rate,
                "elapsed_ns":started.elapsed().as_nanos()})
            );
        }
    }
    Ok(())
}
