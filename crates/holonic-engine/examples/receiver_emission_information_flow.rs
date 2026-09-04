//! Co-located speech, transcript, and binaural echo transport through exact
//! receiver-relative emission spectra.
//!
//! A measured stereo room impulse response supplies two co-present returned
//! paths from one emitted impulse.  The production wave law retains them as
//! plural modes, generates both complete coarse target chronologies for an
//! unheard speech occurrence before either return is supplied, and grades
//! each later channel return.  The phase-current law separately preserves
//! the complete impulse returns and compact exact phase/carry spectra for the
//! much larger speech/room product without enumerating every sample pair.

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
    ExactPhaseTransportSpectrum, ExactWavePropagationLaw, ExactWaveSection, PhaseCurrentLineageId,
    PhaseCurrentReceiverId, WaveConditioningEvent, WaveGenerationEvent, WaveInteractionId,
    WaveInteractionSpec, WaveLineageId, WavePredictionReturnEvent, WavePropagationEvent,
    WavePropagationRadiation, WavePropagationSpec, WaveReceiverId, WaveReceiverSpec,
    propagate_phase_current_emission, receive_phase_transport_spectrum,
};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use ron::ser::PrettyConfig;
use serde::{Deserialize, Serialize};

const SOURCE_RECEIVER: WaveReceiverId = WaveReceiverId(100);
const TARGET_RECEIVER: WaveReceiverId = WaveReceiverId(200);
const ROOM_INTERACTION: WaveInteractionId = WaveInteractionId(300);

#[derive(Clone, Debug)]
struct Args {
    speech: PathBuf,
    transcript: PathBuf,
    rir: PathBuf,
    output: PathBuf,
    phase_extent: usize,
    wave_grain: usize,
    workers: NonZeroUsize,
}

impl Args {
    fn parse() -> Result<Self, Box<dyn Error>> {
        let mut args = env::args().skip(1);
        let mut speech = PathBuf::from(
            ".local/runs/information-flow-datasets/source/LibriSpeech/dev-clean/3081/166546/3081-166546-0059.flac",
        );
        let mut transcript = PathBuf::from(
            ".local/runs/information-flow-datasets/source/LibriSpeech/dev-clean/3081/166546/3081-166546.trans.txt",
        );
        let mut rir = PathBuf::from(
            ".local/runs/information-flow-datasets/source/RIRS_NOISES/real_rirs_isotropic_noises/air_type1_air_binaural_aula_carolina_1_7_90_3.wav",
        );
        let mut output =
            PathBuf::from(".local/runs/information-flow-distributions/receiver-emission-aula-carolina");
        let mut phase_extent = 1024_usize;
        let mut wave_grain = 1024_usize;
        let mut workers = std::thread::available_parallelism()?;
        while let Some(argument) = args.next() {
            let mut value = || -> Result<String, Box<dyn Error>> {
                args.next()
                    .ok_or_else(|| format!("missing value after {argument}").into())
            };
            match argument.as_str() {
                "--speech" => speech = PathBuf::from(value()?),
                "--transcript" => transcript = PathBuf::from(value()?),
                "--rir" => rir = PathBuf::from(value()?),
                "--output" => output = PathBuf::from(value()?),
                "--phase-extent" => phase_extent = value()?.parse()?,
                "--wave-grain" => wave_grain = value()?.parse()?,
                "--workers" => {
                    workers = NonZeroUsize::new(value()?.parse()?)
                        .ok_or("worker count must be positive")?
                }
                "--help" | "-h" => {
                    println!(
                        "receiver_emission_information_flow \\\n+  [--speech PATH] [--transcript PATH] [--rir PATH] [--output PATH] \\\n+  [--phase-extent N] [--wave-grain N] [--workers N]"
                    );
                    std::process::exit(0);
                }
                _ => return Err(format!("unknown argument {argument}").into()),
            }
        }
        if phase_extent == 0 || wave_grain == 0 {
            return Err("phase extent and wave grain must be positive".into());
        }
        Ok(Self {
            speech,
            transcript,
            rir,
            output,
            phase_extent,
            wave_grain,
            workers,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CoLocatedReceiverOccurrence {
    schema: String,
    occurrence: u64,
    speech_path: String,
    speech_lineage: PhaseCurrentLineageId,
    transcript_path: String,
    transcript: String,
    room_response_path: String,
    response_lineages: Vec<PhaseCurrentLineageId>,
    response_channels: u16,
    sample_rate: u32,
    bits_per_sample: u16,
    phase_extent: usize,
    wave_grain: usize,
    interpretation: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct BinauralDifferenceReceipt {
    schema: String,
    left_lineage: PhaseCurrentLineageId,
    right_lineage: PhaseCurrentLineageId,
    samples: usize,
    equal_samples: usize,
    differing_samples: usize,
    first_difference: Option<usize>,
    left_current: BigInt,
    right_current: BigInt,
    difference_current: BigInt,
    absolute_difference_current: BigInt,
    differing_phase_bands: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ExperimentManifest {
    schema: String,
    occurrence: CoLocatedReceiverOccurrence,
    impulse_emissions: usize,
    speech_emission_spectra: usize,
    wave_modes: usize,
    generated_before_return: usize,
    exact_return_grades: usize,
    obstructed_return_grades: usize,
    requested_workers: usize,
    interpretation: String,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse()?;
    fs::create_dir_all(&args.output)?;

    let (speech_samples, speech_rate, speech_bits) = read_mono_flac(&args.speech)?;
    let speech_id = args
        .speech
        .file_stem()
        .ok_or("speech path has no file stem")?
        .to_string_lossy()
        .to_string();
    let transcript = read_transcript(&args.transcript, &speech_id)?;
    let (response_channels, response_rate, response_bits) = read_integer_wav(&args.rir)?;
    if response_channels.len() < 2 {
        return Err("the echo membrane requires at least two co-present channels".into());
    }
    if speech_rate != response_rate {
        return Err("speech and room response do not share a native sample rate".into());
    }
    let response_extent = response_channels[0].len();
    if response_channels
        .iter()
        .any(|channel| channel.len() != response_extent)
    {
        return Err("co-present response channels have unequal extents".into());
    }

    let sample_step = Rat::new(BigInt::from(1), BigInt::from(speech_rate));
    let speech = ExactPhaseCurrentSection::from_i32(
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(1),
        Rat::zero(),
        sample_step.clone(),
        args.phase_extent,
        &speech_samples,
    )?;
    let impulse = ExactPhaseCurrentSection::from_i32(
        PhaseCurrentReceiverId(2),
        PhaseCurrentLineageId(2),
        Rat::zero(),
        sample_step.clone(),
        args.phase_extent,
        &[1],
    )?;

    let mut responses = Vec::with_capacity(response_channels.len());
    let mut impulse_emissions = Vec::with_capacity(response_channels.len());
    let mut speech_spectra = Vec::with_capacity(response_channels.len());
    for (channel, samples) in response_channels.iter().enumerate() {
        let channel_u64 = u64::try_from(channel)?;
        let response = ExactPhaseCurrentSection::from_i32(
            PhaseCurrentReceiverId(10 + channel_u64),
            PhaseCurrentLineageId(10 + channel_u64),
            Rat::zero(),
            sample_step.clone(),
            args.phase_extent,
            samples,
        )?;
        impulse_emissions.push(propagate_phase_current_emission(
            &impulse,
            &response,
            PhaseCurrentReceiverId(20 + channel_u64),
            PhaseCurrentLineageId(20 + channel_u64),
            CpuExecutor::multicore(args.workers),
        )?);
        speech_spectra.push(receive_phase_transport_spectrum(
            &speech,
            &response,
            PhaseCurrentReceiverId(30 + channel_u64),
            PhaseCurrentLineageId(30 + channel_u64),
        )?);
        responses.push(response);
    }

    for (channel, emission) in impulse_emissions.iter().enumerate() {
        let expected = &response_channels[channel];
        let actual = emission.propagation.output.flat_values();
        if actual.len() != expected.len()
            || actual
                .iter()
                .zip(expected)
                .any(|(left, right)| left != &BigInt::from(*right))
        {
            return Err("an exact impulse return departed from its measured room channel".into());
        }
    }
    let binaural_difference = compare_binaural(
        &responses[0],
        &responses[1],
        &speech_spectra[0],
        &speech_spectra[1],
    )?;

    let wave_spec = WavePropagationSpec::new(
        [
            WaveReceiverSpec {
                id: SOURCE_RECEIVER,
                name: format!(
                    "emitted signed-current section at {}-sample receiver grain",
                    args.wave_grain
                ),
                channels: 1,
            },
            WaveReceiverSpec {
                id: TARGET_RECEIVER,
                name: "co-present returned room-current section".to_owned(),
                channels: 1,
            },
        ],
        [WaveInteractionSpec {
            id: ROOM_INTERACTION,
            name: "measured binaural room transport".to_owned(),
            source: SOURCE_RECEIVER,
            target: TARGET_RECEIVER,
        }],
    )?;
    let wave_law =
        ExactWavePropagationLaw::new(wave_spec.clone(), CpuExecutor::multicore(args.workers))?;
    let mut world = CausalWorld::new(wave_law.clone(), wave_law.initial_standing());
    let mut transition_receipts = Vec::new();
    let wave_impulse = wave_section(
        SOURCE_RECEIVER,
        1000,
        speech_rate,
        args.wave_grain,
        vec![BigInt::from(1)],
    )?;
    let response_cells = response_extent.div_ceil(args.wave_grain);
    let mut response_kernels = Vec::with_capacity(response_channels.len());
    let mut event = 1_u64;
    for (channel, samples) in response_channels.iter().enumerate() {
        let mut kernel = block_currents(samples, args.wave_grain);
        kernel.resize(response_cells, BigInt::zero());
        let target = wave_section(
            TARGET_RECEIVER,
            1100 + u64::try_from(channel)?,
            speech_rate,
            args.wave_grain,
            kernel.clone(),
        )?;
        transition_receipts.push(world.receive(&WavePropagationEvent::Condition(
            WaveConditioningEvent {
                event: EventId(event),
                interaction: ROOM_INTERACTION,
                source: wave_impulse.clone(),
                target_return: target,
            },
        ))?);
        response_kernels.push(kernel);
        event += 1;
    }

    let wave_source = wave_section(
        SOURCE_RECEIVER,
        2000,
        speech_rate,
        args.wave_grain,
        block_currents(&speech_samples, args.wave_grain),
    )?;
    let mut predictions = Vec::new();
    for _ in 0..response_channels.len() {
        let generation_event = WavePropagationEvent::Generate(WaveGenerationEvent {
            event: EventId(event),
            interaction: ROOM_INTERACTION,
            source: wave_source.clone(),
        });
        let serial = ExactWavePropagationLaw::new(wave_spec.clone(), CpuExecutor::serial())?
            .enact(world.standing(), &generation_event)?;
        let receipt = world.receive(&generation_event)?;
        if serial.standing_after != *world.standing() {
            return Err("serial and multicore generation produced distinct standing".into());
        }
        let WavePropagationRadiation::Generated(generated) = &receipt.radiation[0] else {
            return Err("wave generation emitted the wrong radiation".into());
        };
        predictions.push(generated.prediction);
        transition_receipts.push(receipt);
        event += 1;
    }

    let pending = ron::ser::to_string_pretty(world.standing(), PrettyConfig::default())?;
    let remounted = ron::from_str(&pending)?;
    if remounted != *world.standing() {
        return Err("open generated standing did not remount exactly".into());
    }
    write_text(&args.output.join("pending_standing.ron"), &pending)?;
    let mut world = CausalWorld::new(wave_law, remounted);

    let wave_source_values = block_currents(&speech_samples, args.wave_grain);
    let mut return_rows = String::from(
        "returned_channel\tprediction\tmode\texact\tunresolved\tchart_departure\textent_departure\tresidual_components\tresidual_cells\n",
    );
    let mut exact_return_grades = 0_usize;
    let mut obstructed_return_grades = 0_usize;
    for (channel, prediction) in predictions.into_iter().enumerate() {
        let target_values = convolve_exact(&wave_source_values, &response_kernels[channel]);
        let target = wave_section(
            TARGET_RECEIVER,
            3000 + u64::try_from(channel)?,
            speech_rate,
            args.wave_grain,
            target_values,
        )?;
        let receipt = world.receive(&WavePropagationEvent::Return(WavePredictionReturnEvent {
            event: EventId(event),
            prediction,
            target_return: target,
            condition_after_grade: false,
        }))?;
        let WavePropagationRadiation::Returned(returned) = &receipt.radiation[0] else {
            return Err("wave return emitted the wrong radiation".into());
        };
        for grade in &returned.grades {
            let residual_cells = grade
                .residual_components
                .iter()
                .map(|component| component.last_sample - component.first_sample + 1)
                .sum::<usize>();
            writeln!(
                return_rows,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                channel,
                prediction.0,
                grade.mode.0,
                grade.exact,
                grade.unresolved_prediction,
                grade.chart_departure,
                grade.extent_departure,
                grade.residual_components.len(),
                residual_cells
            )?;
            if grade.exact {
                exact_return_grades += 1;
            } else {
                obstructed_return_grades += 1;
            }
        }
        transition_receipts.push(receipt);
        event += 1;
    }

    write_ron(
        &args.output.join("impulse_emissions.ron"),
        &impulse_emissions,
    )?;
    write_ron(
        &args.output.join("speech_emission_spectra.ron"),
        &speech_spectra,
    )?;
    write_ron(
        &args.output.join("binaural_difference.ron"),
        &binaural_difference,
    )?;
    write_ron(
        &args.output.join("transition_receipts.ron"),
        &transition_receipts,
    )?;
    write_ron(&args.output.join("final_standing.ron"), world.standing())?;
    write_text(&args.output.join("return_grades.tsv"), &return_rows)?;
    write_spectrum_rows(
        &args.output.join("speech_emission_bands.tsv"),
        &speech_spectra,
    )?;

    let occurrence = CoLocatedReceiverOccurrence {
        schema: "holonic-engine.co-located-receiver-occurrence.v1".to_owned(),
        occurrence: 1,
        speech_path: args.speech.display().to_string(),
        speech_lineage: speech.lineage,
        transcript_path: args.transcript.display().to_string(),
        transcript,
        room_response_path: args.rir.display().to_string(),
        response_lineages: responses.iter().map(|response| response.lineage).collect(),
        response_channels: u16::try_from(response_channels.len())?,
        sample_rate: speech_rate,
        bits_per_sample: response_bits,
        phase_extent: args.phase_extent,
        wave_grain: args.wave_grain,
        interpretation: format!(
            "The {}-bit speech ADC section, transcript, and {}-bit two-ear room returns are inherited co-present receiver sections. Shared occurrence is supplied; acoustic transport modes and later return grades are enacted.",
            speech_bits, response_bits
        ),
    };
    let wave_modes = world
        .standing()
        .modes(ROOM_INTERACTION)
        .ok_or("room interaction is absent from final standing")?
        .len();
    let manifest = ExperimentManifest {
        schema: "holonic-engine.receiver-emission-information-flow-manifest.v1".to_owned(),
        occurrence,
        impulse_emissions: impulse_emissions.len(),
        speech_emission_spectra: speech_spectra.len(),
        wave_modes,
        generated_before_return: response_channels.len(),
        exact_return_grades,
        obstructed_return_grades,
        requested_workers: args.workers.get(),
        interpretation: "Emission is the caused current; spectrum is its target phase/carry receiver face; each room channel is a distinct co-present path; return residuals distinguish the paths without averaging them. No FFT, floating threshold, assigned frequency band, or periodic orbit was supplied.".to_owned(),
    };
    write_ron(&args.output.join("manifest.ron"), &manifest)?;

    println!("wrote {}", args.output.display());
    println!(
        "{} speech samples; {} response channels × {} samples; {} phase coordinates",
        speech_samples.len(),
        response_channels.len(),
        response_extent,
        args.phase_extent
    );
    println!(
        "{} learned room modes; {} exact / {} obstructed returned mode grades",
        wave_modes, exact_return_grades, obstructed_return_grades
    );
    Ok(())
}

fn compare_binaural(
    left: &ExactPhaseCurrentSection,
    right: &ExactPhaseCurrentSection,
    left_spectrum: &ExactPhaseTransportSpectrum,
    right_spectrum: &ExactPhaseTransportSpectrum,
) -> Result<BinauralDifferenceReceipt, Box<dyn Error>> {
    if left.sample_step != right.sample_step
        || left.phase_extent != right.phase_extent
        || left.raw_extent() != right.raw_extent()
    {
        return Err("binaural receiver charts do not agree".into());
    }
    let left_values = left.flat_values();
    let right_values = right.flat_values();
    let mut equal_samples = 0_usize;
    let mut first_difference = None;
    let mut left_current = BigInt::zero();
    let mut right_current = BigInt::zero();
    let mut absolute_difference_current = BigInt::zero();
    for (ordinal, (left_value, right_value)) in left_values.iter().zip(&right_values).enumerate() {
        left_current += left_value;
        right_current += right_value;
        if left_value == right_value {
            equal_samples += 1;
        } else {
            first_difference.get_or_insert(ordinal);
            absolute_difference_current += (left_value - right_value).abs();
        }
    }
    let differing_phase_bands = left_spectrum
        .target_bands
        .iter()
        .zip(&right_spectrum.target_bands)
        .filter(|(left_band, right_band)| left_band != right_band)
        .count();
    Ok(BinauralDifferenceReceipt {
        schema: "holonic-engine.binaural-difference-receipt.v1".to_owned(),
        left_lineage: left.lineage,
        right_lineage: right.lineage,
        samples: left_values.len(),
        equal_samples,
        differing_samples: left_values.len() - equal_samples,
        first_difference,
        difference_current: &left_current - &right_current,
        left_current,
        right_current,
        absolute_difference_current,
        differing_phase_bands,
    })
}

fn wave_section(
    receiver: WaveReceiverId,
    lineage: u64,
    sample_rate: u32,
    grain: usize,
    values: Vec<BigInt>,
) -> Result<ExactWaveSection, Box<dyn Error>> {
    Ok(ExactWaveSection::new(
        receiver,
        WaveLineageId(lineage),
        Rat::zero(),
        Rat::new(BigInt::from(grain), BigInt::from(sample_rate)),
        values
            .into_iter()
            .map(|value| vec![Rat::from_integer(value)])
            .collect(),
    )?)
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

fn read_integer_wav(path: &Path) -> Result<(Vec<Vec<i32>>, u32, u16), Box<dyn Error>> {
    let reader = hound::WavReader::open(path)?;
    let spec = reader.spec();
    if spec.sample_format != hound::SampleFormat::Int || spec.channels == 0 {
        return Err(format!("{} is not integer PCM", path.display()).into());
    }
    let channels = usize::from(spec.channels);
    let mut output = vec![Vec::new(); channels];
    for (ordinal, sample) in reader.into_samples::<i32>().enumerate() {
        output[ordinal % channels].push(sample?);
    }
    Ok((output, spec.sample_rate, spec.bits_per_sample))
}

fn read_transcript(path: &Path, speech_id: &str) -> Result<String, Box<dyn Error>> {
    for line in BufReader::new(File::open(path)?).lines() {
        let line = line?;
        let Some((identity, transcript)) = line.split_once(' ') else {
            continue;
        };
        if identity == speech_id {
            return Ok(transcript.to_owned());
        }
    }
    Err(format!("transcript {speech_id} is absent from {}", path.display()).into())
}

fn write_spectrum_rows(
    path: &Path,
    spectra: &[ExactPhaseTransportSpectrum],
) -> Result<(), Box<dyn Error>> {
    let mut output = String::from(
        "channel\ttarget_phase\tcell_carry\tpositive_occurrences\tnegative_occurrences\tpositive_current\tnegative_current\tnet_current\n",
    );
    for (channel, spectrum) in spectra.iter().enumerate() {
        for band in &spectrum.target_bands {
            writeln!(
                output,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                channel,
                band.target_phase,
                band.cell_carry,
                band.population.positive_occurrences,
                band.population.negative_occurrences,
                band.population.positive_current,
                band.population.negative_current,
                band.population.net_current
            )?;
        }
    }
    write_text(path, &output)
}

fn write_ron<T: Serialize + ?Sized>(path: &Path, value: &T) -> Result<(), Box<dyn Error>> {
    write_text(
        path,
        &ron::ser::to_string_pretty(value, PrettyConfig::default())?,
    )
}

fn write_text(path: &Path, content: &str) -> Result<(), Box<dyn Error>> {
    let mut writer = BufWriter::new(File::create(path)?);
    writer.write_all(content.as_bytes())?;
    writer.flush()?;
    Ok(())
}
