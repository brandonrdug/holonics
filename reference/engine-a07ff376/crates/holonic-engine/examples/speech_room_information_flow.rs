//! Real-corpus system identification through exact receiver-local currents.
//!
//! The world membrane exposes measured room impulse responses as returned
//! sections.  The production wave law conditions causal response modes from
//! those returns, then propagates an unheard LibriSpeech occurrence before the
//! selected room computes its return.  The same return is graded against every
//! contemporary mode.
//!
//! Raw PCM, transcript, and propagated current remain distinct material.  The
//! dyadic temporal sections are finite receiver quotients of the acquired
//! sensor streams; this experiment does not claim raw-sample room synthesis or
//! a linguistic response policy.

use std::collections::BTreeMap;
use std::env;
use std::error::Error;
use std::fmt::Write as _;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};

use claxon::FlacReader;
use holonic_engine::{
    CausalWorld, CpuExecutor, EventId, ExactEventLaw, ExactPhaseCurrentSection,
    ExactWavePropagationLaw, ExactWaveSection, PhaseCurrentLineageId, PhaseCurrentReceiverId,
    WaveConditioningEvent, WaveGenerationEvent, WaveInteractionId, WaveInteractionSpec,
    WaveLineageId, WaveModeReturnGrade, WavePredictionId, WavePredictionReturnEvent,
    WavePropagationEvent, WavePropagationRadiation, WavePropagationSpec, WavePropagationStanding,
    WaveReceiverId, WaveReceiverSpec, convolve_phase_current,
};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use relational_geometry::Rat;
use ron::ser::PrettyConfig;
use serde::{Deserialize, Serialize};

const TRANSCRIPT_RECEIVER: WaveReceiverId = WaveReceiverId(1);
const SOURCE_RECEIVER_BASE: u64 = 100;
const TARGET_RECEIVER_BASE: u64 = 200;
const INTERACTION_BASE: u64 = 300;

#[derive(Clone, Debug)]
struct Args {
    librispeech: PathBuf,
    rirs: PathBuf,
    output: PathBuf,
    rir_pattern: Option<String>,
    mode_limit: usize,
    finest_support: usize,
    workers: NonZeroUsize,
}

impl Args {
    fn parse() -> Result<Self, Box<dyn Error>> {
        let mut args = env::args().skip(1);
        let mut librispeech =
            PathBuf::from("runs/information-flow-datasets/source/LibriSpeech/dev-clean");
        let mut rirs = PathBuf::from("runs/information-flow-datasets/source/RIRS_NOISES");
        let mut output = PathBuf::from("runs/information-flow-distributions/speech-room");
        let mut rir_pattern = None;
        let mut mode_limit = 3_usize;
        let mut finest_support = 256_usize;
        let mut workers = std::thread::available_parallelism()?;
        while let Some(argument) = args.next() {
            let mut value = || -> Result<String, Box<dyn Error>> {
                args.next()
                    .ok_or_else(|| format!("missing value after {argument}").into())
            };
            match argument.as_str() {
                "--librispeech" => librispeech = PathBuf::from(value()?),
                "--rirs" => rirs = PathBuf::from(value()?),
                "--output" => output = PathBuf::from(value()?),
                "--rir-pattern" => rir_pattern = Some(value()?.to_ascii_lowercase()),
                "--mode-limit" => mode_limit = value()?.parse()?,
                "--finest-support" => finest_support = value()?.parse()?,
                "--workers" => {
                    workers = NonZeroUsize::new(value()?.parse()?)
                        .ok_or("worker count must be positive")?
                }
                "--help" | "-h" => {
                    println!(
                        "speech_room_information_flow \\\n+  [--librispeech PATH] [--rirs PATH] [--output PATH] \\\n+  [--rir-pattern TEXT] [--mode-limit N] [--finest-support N] [--workers N]"
                    );
                    std::process::exit(0);
                }
                _ => return Err(format!("unknown argument {argument}").into()),
            }
        }
        if mode_limit < 2 {
            return Err("mode-limit must be at least two".into());
        }
        if finest_support < 8 {
            return Err("finest-support must be at least eight".into());
        }
        Ok(Self {
            librispeech,
            rirs,
            output,
            rir_pattern,
            mode_limit,
            finest_support,
            workers,
        })
    }
}

#[derive(Clone, Debug)]
struct AudioMetadata {
    path: PathBuf,
    sample_rate: u32,
    channels: u16,
    bits_per_sample: u16,
    samples_per_channel: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ResponseIdentity {
    path: PathBuf,
    channel: u16,
    sample_rate: u32,
    bits_per_sample: u16,
    samples: u64,
}

#[derive(Clone, Debug, Default)]
struct FlowAccumulator {
    grain: usize,
    within: usize,
    current: i128,
    cells: u64,
    positive: u64,
    negative: u64,
    zero: u64,
    sign_changes: u64,
    last_sign: i8,
    total_absolute_current: u128,
    maximum_absolute_current: u128,
}

impl FlowAccumulator {
    fn new(grain: usize) -> Self {
        Self {
            grain,
            ..Self::default()
        }
    }

    fn receive(&mut self, sample: i32) {
        self.current += i128::from(sample);
        self.within += 1;
        if self.within == self.grain {
            self.close_cell();
        }
    }

    fn finish(&mut self) {
        if self.within != 0 {
            self.close_cell();
        }
    }

    fn close_cell(&mut self) {
        let sign = self.current.signum() as i8;
        match sign {
            1 => self.positive += 1,
            -1 => self.negative += 1,
            _ => self.zero += 1,
        }
        if sign != 0 && self.last_sign != 0 && sign != self.last_sign {
            self.sign_changes += 1;
        }
        if sign != 0 {
            self.last_sign = sign;
        }
        let absolute = self.current.unsigned_abs();
        self.total_absolute_current += absolute;
        self.maximum_absolute_current = self.maximum_absolute_current.max(absolute);
        self.cells += 1;
        self.within = 0;
        self.current = 0;
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct ResponseManifestEntry {
    relative_path: String,
    channel: u16,
    sample_rate: u32,
    bits_per_sample: u16,
    raw_samples: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct ExperimentManifest {
    schema: String,
    librispeech_root: String,
    room_response_root: String,
    utterances: usize,
    transcript_entries: usize,
    room_wave_files: usize,
    room_channels: usize,
    selected_source: String,
    selected_source_samples: u64,
    selected_transcript: String,
    transcript_section: ExactWaveSection,
    selected_responses: Vec<ResponseManifestEntry>,
    common_response_horizon_samples: u64,
    dyadic_grains_samples: Vec<usize>,
    sample_rate: u32,
    requested_workers: usize,
    phase_current_carrier: String,
    phase_local_products: BigUint,
    phase_carried_products: BigUint,
    phase_workers_used: BigUint,
    interpretation: String,
}

#[derive(Clone, Debug)]
struct SelectedResponse {
    identity: ResponseIdentity,
    samples: Vec<i32>,
}

#[derive(Clone, Debug)]
struct LibriSpeechInspection {
    utterance_rows: String,
    current_rows: String,
    lengths: Vec<(PathBuf, u64)>,
}

#[derive(Clone, Debug)]
struct GeneratedAtScale {
    scale: usize,
    grain: usize,
    interaction: WaveInteractionId,
    prediction: WavePredictionId,
    source: ExactWaveSection,
    return_kind: &'static str,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse()?;
    fs::create_dir_all(&args.output)?;

    let flac_paths = files_with_extension(&args.librispeech, "flac")?;
    if flac_paths.is_empty() {
        return Err(format!("no FLAC files under {}", args.librispeech.display()).into());
    }
    let transcript_paths = files_ending_with(&args.librispeech, ".trans.txt")?;
    let transcripts = read_transcripts(&transcript_paths)?;

    let wave_paths = files_with_extension(&args.rirs, "wav")?;
    if wave_paths.is_empty() {
        return Err(format!("no WAV files under {}", args.rirs.display()).into());
    }
    let wave_metadata = wave_paths
        .iter()
        .map(|path| wav_metadata(path))
        .collect::<Result<Vec<_>, _>>()?;
    let response_identities = response_identities(&wave_metadata, args.rir_pattern.as_deref());
    if response_identities.len() < args.mode_limit {
        return Err(format!(
            "only {} response channels match the requested membrane, need {}",
            response_identities.len(),
            args.mode_limit
        )
        .into());
    }
    let selected_identities = select_response_quantiles(&response_identities, args.mode_limit);
    let sample_rate = selected_identities[0].sample_rate;
    if selected_identities
        .iter()
        .any(|response| response.sample_rate != sample_rate)
    {
        return Err("selected response modes do not share a native sample rate".into());
    }
    let maximum_response = selected_identities
        .iter()
        .map(|response| response.samples)
        .max()
        .ok_or("selected response set is empty")?;
    let finest_grain = dyadic_grain_for_horizon(maximum_response, args.finest_support)?;
    let grains = vec![
        finest_grain,
        finest_grain.checked_mul(2).ok_or("grain overflow")?,
        finest_grain.checked_mul(4).ok_or("grain overflow")?,
    ];

    let speech_inspection = inspect_librispeech(&flac_paths, &transcripts, &grains)?;
    write_text(
        &args.output.join("utterances.tsv"),
        &speech_inspection.utterance_rows,
    )?;
    write_text(
        &args.output.join("utterance_current_distributions.tsv"),
        &speech_inspection.current_rows,
    )?;
    let source_path = select_median_utterance(&speech_inspection.lengths)?;
    let source_id = utterance_id(&source_path)?;
    let selected_transcript = transcripts
        .get(&source_id)
        .cloned()
        .ok_or_else(|| format!("missing transcript for {source_id}"))?;
    let (source_samples, source_sample_rate, source_bits) = read_mono_flac(&source_path)?;
    if source_sample_rate != sample_rate {
        return Err(format!(
            "source rate {source_sample_rate} differs from response rate {sample_rate}"
        )
        .into());
    }

    let (response_rows, room_channels) = inspect_room_waves(&wave_metadata, &grains)?;
    write_text(
        &args.output.join("room_current_distributions.tsv"),
        &response_rows,
    )?;
    let selected_responses = selected_identities
        .into_iter()
        .map(|identity| {
            let samples = read_wav_channel(&identity.path, identity.channel)?;
            Ok(SelectedResponse { identity, samples })
        })
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;

    let spec = propagation_spec(&grains)?;
    let law = ExactWavePropagationLaw::new(spec.clone(), CpuExecutor::multicore(args.workers))?;
    let mut world = CausalWorld::new(law.clone(), law.initial_standing());
    let mut receipts = Vec::new();
    let mut next_event = 1_u64;
    let mut next_lineage = 1_u64;

    // The measured impulse response itself is returned testimony.  No room
    // identity, response coefficient, or held-out successor is passed as a
    // parameter to the production law.
    for (scale, grain) in grains.iter().copied().enumerate() {
        for response in &selected_responses {
            let source = section(
                source_receiver(scale),
                next_lineage,
                sample_rate,
                grain,
                vec![BigInt::from(1)],
            )?;
            next_lineage += 1;
            let target = section(
                target_receiver(scale),
                next_lineage,
                sample_rate,
                grain,
                block_currents_at_horizon(&response.samples, grain, maximum_response)?,
            )?;
            next_lineage += 1;
            receipts.push(world.receive(&WavePropagationEvent::Condition(
                WaveConditioningEvent {
                    event: EventId(next_event),
                    interaction: interaction(scale),
                    source,
                    target_return: target,
                },
            ))?);
            next_event += 1;
        }
    }

    let mut generated = Vec::new();
    for (scale, grain) in grains.iter().copied().enumerate() {
        let source = section(
            source_receiver(scale),
            next_lineage,
            sample_rate,
            grain,
            block_currents(&source_samples, grain),
        )?;
        next_lineage += 1;
        for return_kind in ["quotient_control", "raw_sample_projection"] {
            let event = WavePropagationEvent::Generate(WaveGenerationEvent {
                event: EventId(next_event),
                interaction: interaction(scale),
                source: source.clone(),
            });

            // The exact logical successor is executor-independent on the real
            // corpus standing, not only on a small unit fixture.
            let serial = ExactWavePropagationLaw::new(spec.clone(), CpuExecutor::serial())?
                .enact(world.standing(), &event)?;
            let receipt = world.receive(&event)?;
            if serial.standing_after != *world.standing() {
                return Err("serial/cardinality-parallel standing departure".into());
            }
            let WavePropagationRadiation::Generated(generation) = &receipt.radiation[0] else {
                return Err("generation event emitted the wrong radiation".into());
            };
            generated.push(GeneratedAtScale {
                scale,
                grain,
                interaction: interaction(scale),
                prediction: generation.prediction,
                source: source.clone(),
                return_kind,
            });
            receipts.push(receipt);
            next_event += 1;
        }
    }

    // Exact rest/remount occurs while all three generated returns remain
    // pending.  Physical executor metadata is absent from this standing.
    let pending_ron = ron::ser::to_string_pretty(world.standing(), PrettyConfig::default())?;
    let mounted: WavePropagationStanding = ron::from_str(&pending_ron)?;
    if mounted != *world.standing() {
        return Err("pending standing did not remount exactly".into());
    }
    write_text(&args.output.join("pending_standing.ron"), &pending_ron)?;
    let mut world = CausalWorld::new(law, mounted);

    // Choose the median response mode.  Its world return is not calculated
    // until every scale has already produced a complete plural prediction.
    let returning_response = &selected_responses[selected_responses.len() / 2];
    let raw_response = &selected_responses[0];
    let sample_step = Rat::new(BigInt::from(1), BigInt::from(sample_rate));
    let phase_source = ExactPhaseCurrentSection::from_i32(
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(1),
        Rat::zero(),
        sample_step.clone(),
        finest_grain,
        &source_samples,
    )?;
    let phase_response = ExactPhaseCurrentSection::from_i32(
        PhaseCurrentReceiverId(2),
        PhaseCurrentLineageId(2),
        Rat::zero(),
        sample_step,
        finest_grain,
        &raw_response.samples,
    )?;
    let phase_receipt = convolve_phase_current(
        &phase_source,
        &phase_response,
        PhaseCurrentReceiverId(3),
        PhaseCurrentLineageId(3),
        CpuExecutor::multicore(args.workers),
    )?;
    let mut raw_projected = phase_receipt.output.flat_values();
    raw_projected.resize(
        source_samples
            .len()
            .checked_add(usize::try_from(maximum_response)?)
            .and_then(|extent| extent.checked_sub(1))
            .ok_or("common raw convolution extent overflow")?,
        BigInt::zero(),
    );
    write_text(
        &args.output.join("phase_current_receipt.ron"),
        &ron::ser::to_string_pretty(&phase_receipt, PrettyConfig::default())?,
    )?;
    let mut grade_rows = String::from(
        "return_kind\tscale\tgrain_samples\tinteraction\tmode\texact\tunresolved\tchart_departure\textent_departure\tresidual_components\tresidual_cells\tresidual_spans\n",
    );
    for generation in generated {
        let target_values = match generation.return_kind {
            "quotient_control" => {
                let kernel = block_currents_at_horizon(
                    &returning_response.samples,
                    generation.grain,
                    maximum_response,
                )?;
                convolve_exact(&section_values(&generation.source), &kernel)
            }
            "raw_sample_projection" => {
                let mut currents = block_bigint_currents(&raw_projected, generation.grain);
                let expected = generation
                    .source
                    .sample_count()
                    .checked_add(
                        block_currents_at_horizon(
                            &raw_response.samples,
                            generation.grain,
                            maximum_response,
                        )?
                        .len(),
                    )
                    .and_then(|extent| extent.checked_sub(1))
                    .ok_or("raw projected extent overflow")?;
                if currents.len() > expected {
                    return Err("raw projected return exceeds the causal horizon".into());
                }
                currents.resize(expected, BigInt::zero());
                currents
            }
            _ => return Err("unknown held-out return kind".into()),
        };
        let target = section(
            target_receiver(generation.scale),
            next_lineage,
            sample_rate,
            generation.grain,
            target_values,
        )?;
        next_lineage += 1;
        let receipt = world.receive(&WavePropagationEvent::Return(WavePredictionReturnEvent {
            event: EventId(next_event),
            prediction: generation.prediction,
            target_return: target,
            condition_after_grade: false,
        }))?;
        let WavePropagationRadiation::Returned(returned) = &receipt.radiation[0] else {
            return Err("return event emitted the wrong radiation".into());
        };
        append_grade_rows(
            &mut grade_rows,
            generation.return_kind,
            generation.scale,
            generation.grain,
            generation.interaction,
            &returned.grades,
        )?;
        receipts.push(receipt);
        next_event += 1;
    }
    write_text(&args.output.join("heldout_return_grades.tsv"), &grade_rows)?;

    let final_standing = ron::ser::to_string_pretty(world.standing(), PrettyConfig::default())?;
    write_text(&args.output.join("final_standing.ron"), &final_standing)?;
    write_text(
        &args.output.join("transition_receipts.ron"),
        &ron::ser::to_string_pretty(&receipts, PrettyConfig::default())?,
    )?;

    let transcript_section = ExactWaveSection::new(
        TRANSCRIPT_RECEIVER,
        WaveLineageId(next_lineage),
        Rat::zero(),
        Rat::from_integer(BigInt::from(1)),
        selected_transcript
            .chars()
            .map(|character| vec![Rat::from_integer(BigInt::from(u32::from(character)))])
            .collect(),
    )?;
    let manifest = ExperimentManifest {
        schema: "holonic-engine.speech-room-information-flow-manifest.v1".to_owned(),
        librispeech_root: args.librispeech.display().to_string(),
        room_response_root: args.rirs.display().to_string(),
        utterances: flac_paths.len(),
        transcript_entries: transcripts.len(),
        room_wave_files: wave_metadata.len(),
        room_channels,
        selected_source: source_path.display().to_string(),
        selected_source_samples: u64::try_from(source_samples.len())?,
        selected_transcript,
        transcript_section,
        selected_responses: selected_responses
            .iter()
            .map(|response| ResponseManifestEntry {
                relative_path: response.identity.path.display().to_string(),
                channel: response.identity.channel,
                sample_rate: response.identity.sample_rate,
                bits_per_sample: response.identity.bits_per_sample,
                raw_samples: response.identity.samples,
            })
            .collect(),
        common_response_horizon_samples: maximum_response,
        dyadic_grains_samples: grains,
        sample_rate,
        requested_workers: args.workers.get(),
        phase_current_carrier: phase_receipt.exact_integer_carrier.clone(),
        phase_local_products: phase_receipt.local_phase_products.clone(),
        phase_carried_products: phase_receipt.carried_phase_products.clone(),
        phase_workers_used: phase_receipt.execution.workers_used.clone(),
        interpretation: format!(
            "Exact signed ADC-current sections. Source PCM is {}-bit; measured room modes remain distinct; transcript code points are a separate receiver and do not fit the acoustic response.",
            source_bits
        ),
    };
    write_text(
        &args.output.join("manifest.ron"),
        &ron::ser::to_string_pretty(&manifest, PrettyConfig::default())?,
    )?;

    println!("wrote {}", args.output.display());
    println!(
        "{} utterances; {} room WAVs / {} channels; {} selected response modes",
        flac_paths.len(),
        wave_metadata.len(),
        room_channels,
        selected_responses.len()
    );
    println!(
        "held-out source: {} ({} samples); dyadic grains: {:?}",
        source_id,
        source_samples.len(),
        manifest.dyadic_grains_samples
    );
    Ok(())
}

fn source_receiver(scale: usize) -> WaveReceiverId {
    WaveReceiverId(SOURCE_RECEIVER_BASE + scale as u64)
}

fn target_receiver(scale: usize) -> WaveReceiverId {
    WaveReceiverId(TARGET_RECEIVER_BASE + scale as u64)
}

fn interaction(scale: usize) -> WaveInteractionId {
    WaveInteractionId(INTERACTION_BASE + scale as u64)
}

fn propagation_spec(grains: &[usize]) -> Result<WavePropagationSpec, Box<dyn Error>> {
    let mut receivers = vec![WaveReceiverSpec {
        id: TRANSCRIPT_RECEIVER,
        name: "transcript-codepoint chronology".to_owned(),
        channels: 1,
    }];
    let mut interactions = Vec::new();
    for (scale, grain) in grains.iter().enumerate() {
        receivers.push(WaveReceiverSpec {
            id: source_receiver(scale),
            name: format!("source signed-current section at grain {grain}"),
            channels: 1,
        });
        receivers.push(WaveReceiverSpec {
            id: target_receiver(scale),
            name: format!("propagated signed-current section at grain {grain}"),
            channels: 1,
        });
        interactions.push(WaveInteractionSpec {
            id: interaction(scale),
            name: format!("measured causal room response at grain {grain}"),
            source: source_receiver(scale),
            target: target_receiver(scale),
        });
    }
    Ok(WavePropagationSpec::new(receivers, interactions)?)
}

fn section(
    receiver: WaveReceiverId,
    lineage: u64,
    sample_rate: u32,
    grain: usize,
    values: Vec<BigInt>,
) -> Result<ExactWaveSection, Box<dyn Error>> {
    if values.is_empty() {
        return Err("cannot form an empty receiver section".into());
    }
    Ok(ExactWaveSection::new(
        receiver,
        WaveLineageId(lineage),
        Rat::zero(),
        Rat::new(
            BigInt::from(u64::try_from(grain)?),
            BigInt::from(sample_rate),
        ),
        values
            .into_iter()
            .map(|value| vec![Rat::from_integer(value)])
            .collect(),
    )?)
}

fn section_values(section: &ExactWaveSection) -> Vec<BigInt> {
    section
        .samples
        .iter()
        .map(|sample| {
            debug_assert!(sample[0].is_integer());
            sample[0].to_integer()
        })
        .collect()
}

fn block_currents(samples: &[i32], grain: usize) -> Vec<BigInt> {
    samples
        .chunks(grain)
        .map(|chunk| {
            chunk.iter().fold(BigInt::zero(), |current, sample| {
                current + BigInt::from(*sample)
            })
        })
        .collect()
}

fn block_bigint_currents(samples: &[BigInt], grain: usize) -> Vec<BigInt> {
    samples
        .chunks(grain)
        .map(|chunk| {
            chunk
                .iter()
                .fold(BigInt::zero(), |current, sample| current + sample)
        })
        .collect()
}

fn block_currents_at_horizon(
    samples: &[i32],
    grain: usize,
    horizon: u64,
) -> Result<Vec<BigInt>, Box<dyn Error>> {
    if u64::try_from(samples.len())? > horizon {
        return Err("response exceeds the declared common horizon".into());
    }
    let cells = horizon
        .checked_add(u64::try_from(grain)? - 1)
        .ok_or("response horizon overflow")?
        / u64::try_from(grain)?;
    let mut currents = block_currents(samples, grain);
    currents.resize(usize::try_from(cells)?, BigInt::zero());
    Ok(currents)
}

fn convolve_exact(source: &[BigInt], kernel: &[BigInt]) -> Vec<BigInt> {
    let mut target = vec![BigInt::zero(); source.len() + kernel.len() - 1];
    for (source_ordinal, source_current) in source.iter().enumerate() {
        if source_current.is_zero() {
            continue;
        }
        for (delay, response_current) in kernel.iter().enumerate() {
            if response_current.is_zero() {
                continue;
            }
            target[source_ordinal + delay] += source_current * response_current;
        }
    }
    target
}

fn append_grade_rows(
    output: &mut String,
    return_kind: &str,
    scale: usize,
    grain: usize,
    interaction: WaveInteractionId,
    grades: &[WaveModeReturnGrade],
) -> Result<(), Box<dyn Error>> {
    for grade in grades {
        let residual_cells = grade
            .residual_components
            .iter()
            .map(|component| component.residuals.len())
            .sum::<usize>();
        let residual_spans = grade
            .residual_components
            .iter()
            .map(|component| format!("{}..{}", component.first_sample, component.last_sample))
            .collect::<Vec<_>>()
            .join(",");
        writeln!(
            output,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            return_kind,
            scale,
            grain,
            interaction.0,
            grade.mode.0,
            grade.exact,
            grade.unresolved_prediction,
            grade.chart_departure,
            grade.extent_departure,
            grade.residual_components.len(),
            residual_cells,
            residual_spans
        )?;
    }
    Ok(())
}

fn files_with_extension(root: &Path, extension: &str) -> Result<Vec<PathBuf>, Box<dyn Error>> {
    let mut files = Vec::new();
    collect_files(root, &mut files)?;
    files.retain(|path| {
        path.extension()
            .is_some_and(|present| present.eq_ignore_ascii_case(extension))
    });
    files.sort();
    Ok(files)
}

fn files_ending_with(root: &Path, suffix: &str) -> Result<Vec<PathBuf>, Box<dyn Error>> {
    let mut files = Vec::new();
    collect_files(root, &mut files)?;
    files.retain(|path| path.to_string_lossy().ends_with(suffix));
    files.sort();
    Ok(files)
}

fn collect_files(root: &Path, output: &mut Vec<PathBuf>) -> Result<(), Box<dyn Error>> {
    for entry in fs::read_dir(root)? {
        let entry = entry?;
        let kind = entry.file_type()?;
        if kind.is_dir() {
            collect_files(&entry.path(), output)?;
        } else if kind.is_file() {
            output.push(entry.path());
        }
    }
    Ok(())
}

fn read_transcripts(paths: &[PathBuf]) -> Result<BTreeMap<String, String>, Box<dyn Error>> {
    let mut transcripts = BTreeMap::new();
    for path in paths {
        for line in BufReader::new(File::open(path)?).lines() {
            let line = line?;
            let Some((identity, text)) = line.split_once(' ') else {
                return Err(format!("malformed transcript line in {}", path.display()).into());
            };
            if transcripts
                .insert(identity.to_owned(), text.to_owned())
                .is_some()
            {
                return Err(format!("duplicate transcript identity {identity}").into());
            }
        }
    }
    Ok(transcripts)
}

fn utterance_id(path: &Path) -> Result<String, Box<dyn Error>> {
    Ok(path
        .file_stem()
        .ok_or_else(|| format!("missing file stem for {}", path.display()))?
        .to_string_lossy()
        .into_owned())
}

fn inspect_librispeech(
    paths: &[PathBuf],
    transcripts: &BTreeMap<String, String>,
    grains: &[usize],
) -> Result<LibriSpeechInspection, Box<dyn Error>> {
    let mut utterances = String::from("utterance\tpath\tsample_rate\tbits\tsamples\ttranscript\n");
    let mut flow = String::from(
        "utterance\tgrain_samples\tcells\tpositive\tnegative\tzero\tsign_changes\ttotal_absolute_current\tmaximum_absolute_current\n",
    );
    let mut lengths = Vec::with_capacity(paths.len());
    for path in paths {
        let identity = utterance_id(path)?;
        let transcript = transcripts
            .get(&identity)
            .ok_or_else(|| format!("missing transcript for {identity}"))?;
        let mut reader = FlacReader::open(path)?;
        let info = reader.streaminfo();
        if info.channels != 1 {
            return Err(format!("{} is not mono", path.display()).into());
        }
        let mut accumulators = grains
            .iter()
            .copied()
            .map(FlowAccumulator::new)
            .collect::<Vec<_>>();
        let mut samples = 0_u64;
        for sample in reader.samples() {
            let sample = sample?;
            samples += 1;
            for accumulator in &mut accumulators {
                accumulator.receive(sample);
            }
        }
        for accumulator in &mut accumulators {
            accumulator.finish();
            writeln!(
                flow,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                identity,
                accumulator.grain,
                accumulator.cells,
                accumulator.positive,
                accumulator.negative,
                accumulator.zero,
                accumulator.sign_changes,
                accumulator.total_absolute_current,
                accumulator.maximum_absolute_current
            )?;
        }
        writeln!(
            utterances,
            "{}\t{}\t{}\t{}\t{}\t{}",
            identity,
            path.display(),
            info.sample_rate,
            info.bits_per_sample,
            samples,
            transcript.replace(['\t', '\n'], " ")
        )?;
        lengths.push((path.clone(), samples));
    }
    Ok(LibriSpeechInspection {
        utterance_rows: utterances,
        current_rows: flow,
        lengths,
    })
}

fn select_median_utterance(lengths: &[(PathBuf, u64)]) -> Result<PathBuf, Box<dyn Error>> {
    if lengths.is_empty() {
        return Err("cannot select from an empty utterance corpus".into());
    }
    let mut ordered = lengths.to_vec();
    ordered.sort_by(|left, right| left.1.cmp(&right.1).then_with(|| left.0.cmp(&right.0)));
    Ok(ordered[ordered.len() / 2].0.clone())
}

fn read_mono_flac(path: &Path) -> Result<(Vec<i32>, u32, u32), Box<dyn Error>> {
    let mut reader = FlacReader::open(path)?;
    let info = reader.streaminfo();
    if info.channels != 1 {
        return Err(format!("{} is not mono", path.display()).into());
    }
    let sample_rate = info.sample_rate;
    let bits = info.bits_per_sample;
    let samples = reader.samples().collect::<Result<Vec<_>, _>>()?;
    Ok((samples, sample_rate, bits))
}

fn wav_metadata(path: &Path) -> Result<AudioMetadata, Box<dyn Error>> {
    let reader = hound::WavReader::open(path)?;
    let spec = reader.spec();
    if spec.sample_format != hound::SampleFormat::Int {
        return Err(format!("{} is not integer PCM", path.display()).into());
    }
    Ok(AudioMetadata {
        path: path.to_owned(),
        sample_rate: spec.sample_rate,
        channels: spec.channels,
        bits_per_sample: spec.bits_per_sample,
        samples_per_channel: u64::from(reader.duration()),
    })
}

fn response_identities(metadata: &[AudioMetadata], pattern: Option<&str>) -> Vec<ResponseIdentity> {
    let mut responses = metadata
        .iter()
        .filter(|metadata| {
            let path = metadata.path.to_string_lossy().to_ascii_lowercase();
            let filename = metadata
                .path
                .file_name()
                .map(|name| name.to_string_lossy().to_ascii_lowercase())
                .unwrap_or_default();
            !filename.contains("noise") && pattern.is_none_or(|pattern| path.contains(pattern))
        })
        .flat_map(|metadata| {
            (0..metadata.channels).map(|channel| ResponseIdentity {
                path: metadata.path.clone(),
                channel,
                sample_rate: metadata.sample_rate,
                bits_per_sample: metadata.bits_per_sample,
                samples: metadata.samples_per_channel,
            })
        })
        .collect::<Vec<_>>();
    responses.sort_by(|left, right| {
        left.samples
            .cmp(&right.samples)
            .then_with(|| left.path.cmp(&right.path))
            .then_with(|| left.channel.cmp(&right.channel))
    });
    responses
}

fn select_response_quantiles(
    responses: &[ResponseIdentity],
    count: usize,
) -> Vec<ResponseIdentity> {
    (0..count)
        .map(|ordinal| {
            let index = if count == 1 {
                responses.len() / 2
            } else {
                ordinal * (responses.len() - 1) / (count - 1)
            };
            responses[index].clone()
        })
        .collect()
}

fn dyadic_grain_for_horizon(horizon: u64, maximum_support: usize) -> Result<usize, Box<dyn Error>> {
    let maximum_support = u64::try_from(maximum_support)?;
    let required = horizon
        .checked_add(maximum_support - 1)
        .ok_or("horizon overflow")?
        / maximum_support;
    let required = usize::try_from(required.max(1))?;
    Ok(required.next_power_of_two())
}

fn inspect_room_waves(
    metadata: &[AudioMetadata],
    grains: &[usize],
) -> Result<(String, usize), Box<dyn Error>> {
    let mut output = String::from(
        "path\tchannel\tsample_rate\tbits\traw_samples\tgrain_samples\tcells\tpositive\tnegative\tzero\tsign_changes\ttotal_absolute_current\tmaximum_absolute_current\n",
    );
    let mut total_channels = 0_usize;
    for metadata in metadata {
        let reader = hound::WavReader::open(&metadata.path)?;
        let channels = usize::from(metadata.channels);
        total_channels += channels;
        let mut accumulators = (0..channels)
            .map(|_| {
                grains
                    .iter()
                    .copied()
                    .map(FlowAccumulator::new)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        for (ordinal, sample) in reader.into_samples::<i32>().enumerate() {
            let sample = sample?;
            let channel = ordinal % channels;
            for accumulator in &mut accumulators[channel] {
                accumulator.receive(sample);
            }
        }
        for (channel, channel_accumulators) in accumulators.iter_mut().enumerate() {
            for accumulator in channel_accumulators {
                accumulator.finish();
                writeln!(
                    output,
                    "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                    metadata.path.display(),
                    channel,
                    metadata.sample_rate,
                    metadata.bits_per_sample,
                    metadata.samples_per_channel,
                    accumulator.grain,
                    accumulator.cells,
                    accumulator.positive,
                    accumulator.negative,
                    accumulator.zero,
                    accumulator.sign_changes,
                    accumulator.total_absolute_current,
                    accumulator.maximum_absolute_current
                )?;
            }
        }
    }
    Ok((output, total_channels))
}

fn read_wav_channel(path: &Path, selected_channel: u16) -> Result<Vec<i32>, Box<dyn Error>> {
    let reader = hound::WavReader::open(path)?;
    let channels = reader.spec().channels;
    if selected_channel >= channels {
        return Err(format!(
            "channel {selected_channel} is absent from {}",
            path.display()
        )
        .into());
    }
    let channels = usize::from(channels);
    let selected = usize::from(selected_channel);
    Ok(reader
        .into_samples::<i32>()
        .enumerate()
        .filter_map(|(ordinal, sample)| (ordinal % channels == selected).then_some(sample))
        .collect::<Result<Vec<_>, _>>()?)
}

fn write_text(path: &Path, content: &str) -> Result<(), Box<dyn Error>> {
    let mut writer = BufWriter::new(File::create(path)?);
    writer.write_all(content.as_bytes())?;
    writer.flush()?;
    Ok(())
}
