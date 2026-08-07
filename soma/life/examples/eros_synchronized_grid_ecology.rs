//! Real synchronized audiovisual speech conditioning over the production Swing.
//!
//! The official GRID MPEG supplies one captured video/audio occurrence. Its
//! word alignment supplies inherited transcript timing and text. This membrane
//! decodes the complete 360x288, 25-frame/s video and one exact 44.1 kHz acoustic
//! receiver channel. It derives ratio/order facets from full-frame temporal
//! topology and from the production exact phase-current spectrum, then sends
//! all receiver sections through `SynchronizedEcology`.
//!
//! Eighty complete utterances condition the ecology. For sixteen held-out
//! utterances, every one of the 51 received vocabulary sections is proposed as
//! a candidate before the actual transcript returns. Audio-only, video-only,
//! and joined fibers are graded without scalar winner selection. The actual
//! six-word transcript then enters once as one complete co-present occurrence.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use body::num::Cog;
use holonic_engine::{
    receive_phase_transport_spectrum, ExactPhaseCurrentSection, PhaseCurrentLineageId,
    PhaseCurrentReceiverId,
};
use life::synchronized_occurrence::{
    relation_atom, ExactClockTransport, ExactSynchronizedOccurrence, SynchronizedCandidateId,
    SynchronizedCellId, SynchronizedCellOrigin, SynchronizedEcology, SynchronizedInteraction,
    SynchronizedPrediction, SynchronizedPredictionAlternative, SynchronizedReceiverId,
    SynchronizedReceiverSection, TimedReceiverCell,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use serde_json::Value;
use sha2::{Digest, Sha256};
use soma_abi::active::ActionCurrent;
use soma_membrane::{LiveCurrentMachine, ReceiverChartIdentity, SparseStandingSurface};

const ALIGNMENT_HZ: u64 = 25_000;
const PHASE_EXTENT: usize = 16;
const FEATURE_GROUPS: usize = 6;
const FEATURE_TRITS: usize = 8;

const AUDIO_RECEIVER: SynchronizedReceiverId = SynchronizedReceiverId(0x4155_4449_4f);
const VIDEO_RECEIVER: SynchronizedReceiverId = SynchronizedReceiverId(0x5649_4445_4f);
const TEXT_RECEIVER: SynchronizedReceiverId = SynchronizedReceiverId(0x5445_5854);
const HORIZON_CHART: u64 = 0x4f43_4355_5252_454e;
const AUDIO_CHART_BASE: u64 = 0x4155_4400;
const VIDEO_CHART_BASE: u64 = 0x5649_4400;
const TEXT_CHART: u64 = 0x5445_5854;

const HELD_OUT: [&str; 16] = [
    "bbwm6p", "bgwo2n", "brwt5s", "bwwuzn", "lbwy8p", "lrae4p", "lwae9s", "pgad8n", "prwx7s",
    "pwwrzp", "sbwo3a", "sgwp8n", "srwi5a", "swwi9s", "bbas3a", "bbbm1s",
];

#[derive(Clone, Debug)]
struct AlignmentWord {
    begin: u64,
    end: u64,
    word: String,
}

#[derive(Clone, Debug)]
struct WordObservation {
    alignment: AlignmentWord,
    audio_begin: u64,
    audio_end: u64,
    video_begin: u64,
    video_end: u64,
    audio_codes: [i64; FEATURE_GROUPS],
    video_codes: [i64; FEATURE_GROUPS],
}

#[derive(Clone, Debug)]
struct ClipObservation {
    stem: String,
    ordinal: u64,
    audio_sample_rate: u64,
    video_rate_num: u64,
    video_rate_den: u64,
    words: Vec<WordObservation>,
}

#[derive(Clone, Debug)]
struct MediaProbe {
    width: usize,
    height: usize,
    video_rate_num: u64,
    video_rate_den: u64,
    audio_sample_rate: u64,
    audio_channels: usize,
}

#[derive(Clone, Copy, Debug)]
enum PredictionFace {
    Audio,
    Video,
    Joined,
}

#[derive(Clone, Debug)]
struct HeldWordResult {
    stem: String,
    word_at: usize,
    actual: SynchronizedCandidateId,
    actual_word: String,
    audio: SynchronizedPrediction,
    video: SynchronizedPrediction,
    joined: SynchronizedPrediction,
}

#[derive(Clone, Copy, Debug, Default)]
struct SupportCensus {
    active_factors: usize,
    causal_nodes: usize,
    cause_edges: usize,
    direct_boundary_entries: usize,
    resolved_boundary_entries: usize,
    native_words: usize,
    maximum_factors: usize,
    maximum_nodes: usize,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .canonicalize()?;
    let dataset = workspace.join("runs/information-flow-datasets/source/GRID");
    let output =
        workspace.join("runs/synchronized-grid-factorized-structural-fiber-information-flow");
    fs::create_dir_all(&output)?;

    let held = HELD_OUT.into_iter().collect::<BTreeSet<_>>();
    let mut stems = fs::read_dir(dataset.join("s1"))?
        .filter_map(Result::ok)
        .filter_map(|entry| {
            entry
                .path()
                .extension()
                .is_some_and(|extension| extension == "mpg")
                .then(|| {
                    entry
                        .path()
                        .file_stem()
                        .unwrap()
                        .to_string_lossy()
                        .into_owned()
                })
        })
        .collect::<Vec<_>>();
    stems.sort();
    if stems.len() != 96 {
        return Err(format!(
            "expected 96 selected GRID occurrences, found {}",
            stems.len()
        )
        .into());
    }
    let train_stems = stems
        .iter()
        .filter(|stem| !held.contains(stem.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    let held_stems = stems
        .iter()
        .filter(|stem| held.contains(stem.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    if train_stems.len() != 80 || held_stems.len() != 16 {
        return Err("the declared 80/16 GRID split is incomplete".into());
    }

    println!(
        "decoding {} complete synchronized GRID occurrences across bounded host workers",
        stems.len()
    );
    let decode_started = Instant::now();
    let observations = parallel_observe(&dataset, &stems, 8)?;
    println!(
        "decoded {} occurrences in {:.3}s",
        observations.len(),
        decode_started.elapsed().as_secs_f64()
    );
    let by_stem = observations
        .into_iter()
        .map(|observation| (observation.stem.clone(), observation))
        .collect::<BTreeMap<_, _>>();

    let vocabulary = derive_vocabulary(by_stem.values())?;
    let token_by_id = vocabulary
        .iter()
        .map(|(word, id)| (*id, word.clone()))
        .collect::<BTreeMap<_, _>>();
    if vocabulary.len() != 51 {
        return Err(format!(
            "expected complete 51-token GRID vocabulary, found {}",
            vocabulary.len()
        )
        .into());
    }

    let action = ActionCurrent::new(Cog::lit(1)).ok_or("nonzero action refused")?;
    let machine = LiveCurrentMachine::new(
        SparseStandingSurface::empty_rank(12)
            .map_err(|error| format!("synchronized standing refused: {error:?}"))?,
    );
    let mut ecology = SynchronizedEcology::new(machine);
    let training_started = Instant::now();
    let mut training_contacts = 0_u64;
    let mut training_rides = 0_u64;
    let mut training_open = 0_u64;
    for (at, stem) in train_stems.iter().enumerate() {
        let observation = &by_stem[stem];
        let occurrence =
            complete_occurrence(observation, &vocabulary, SynchronizedCellOrigin::Inherited)?;
        let radiation = ecology.receive(&occurrence, action)?;
        training_contacts = training_contacts
            .checked_add(u64::try_from(radiation.contacts.len())?)
            .ok_or("training contact count overflow")?;
        training_rides = training_rides
            .checked_add(u64::try_from(
                radiation
                    .contacts
                    .iter()
                    .filter(|contact| contact.formed_ride)
                    .count(),
            )?)
            .ok_or("training ride count overflow")?;
        training_open = training_open
            .checked_add(u64::try_from(
                radiation
                    .contacts
                    .iter()
                    .filter(|contact| contact.open)
                    .count(),
            )?)
            .ok_or("training open count overflow")?;
        if (at + 1) % 10 == 0 {
            println!(
                "conditioned {:>2}/80 occurrences: {} standing constituents, {} indexed relations",
                at + 1,
                ecology.machine().memory().standing_constituents,
                ecology.atlas().relations.len()
            );
        }
    }
    let training_elapsed = training_started.elapsed();
    let established_before_holdout = ecology
        .atlas()
        .relations
        .values()
        .filter(|lineage| lineage.established())
        .count();
    let training_indexed = ecology.atlas().relations.len();
    let training_standing_constituents = ecology.machine().memory().standing_constituents;
    let training_standing_cells = ecology.machine().memory().standing_cells;
    let training_support = support_census(ecology.machine())?;

    let rest = ecology
        .into_rest_image()
        .map_err(|error| format!("synchronized ecology could not rest: {error:?}"))?;
    let remounted = SynchronizedEcology::from_rest_image(rest)
        .map_err(|error| format!("synchronized ecology could not remount: {error:?}"))?;
    ecology = remounted;
    let training_revision = ecology.revision();

    let machine_bytes = ecology
        .machine()
        .rest_image()
        .map_err(|error| format!("machine standing could not rest: {error:?}"))?
        .encode_native_bytes()
        .map_err(|error| format!("machine rest image could not encode: {error:?}"))?;
    let standing_sha256 = hex_digest(&machine_bytes);

    println!(
        "training complete in {:.3}s: {} contacts, {} rides, {} OPEN returns, {} established association fibers",
        training_elapsed.as_secs_f64(),
        training_contacts,
        training_rides,
        training_open,
        established_before_holdout
    );

    let prediction_started = Instant::now();
    let mut held_results = Vec::new();
    let mut return_contacts = 0_u64;
    for (held_at, stem) in held_stems.iter().enumerate() {
        let observation = &by_stem[stem];
        let revision_before = ecology.revision();
        let mut utterance_results = Vec::new();
        for word_at in 0..observation.words.len() {
            let actual_word = observation.words[word_at].alignment.word.clone();
            let actual = SynchronizedCandidateId(vocabulary[&actual_word]);
            let audio = ecology.predict(
                TEXT_RECEIVER,
                &prediction_alternatives(observation, word_at, &vocabulary, PredictionFace::Audio)?,
            )?;
            let video = ecology.predict(
                TEXT_RECEIVER,
                &prediction_alternatives(observation, word_at, &vocabulary, PredictionFace::Video)?,
            )?;
            let joined = ecology.predict(
                TEXT_RECEIVER,
                &prediction_alternatives(
                    observation,
                    word_at,
                    &vocabulary,
                    PredictionFace::Joined,
                )?,
            )?;
            audio.grade(actual)?;
            video.grade(actual)?;
            joined.grade(actual)?;
            utterance_results.push(HeldWordResult {
                stem: stem.clone(),
                word_at,
                actual,
                actual_word,
                audio,
                video,
                joined,
            });
        }
        if ecology.revision() != revision_before {
            return Err("prediction mutated contemporary ecology".into());
        }

        let returned =
            complete_occurrence(observation, &vocabulary, SynchronizedCellOrigin::Inherited)?;
        let radiation = ecology.receive(&returned, action)?;
        return_contacts = return_contacts
            .checked_add(u64::try_from(radiation.contacts.len())?)
            .ok_or("return contact count overflow")?;
        held_results.extend(utterance_results);
        println!(
            "graded and returned {:>2}/16 held occurrences: {}",
            held_at + 1,
            stem
        );
    }
    let prediction_elapsed = prediction_started.elapsed();
    if held_results.len() != 96 {
        return Err("held word population changed".into());
    }
    if ecology.revision() != training_revision + 16 {
        return Err("each complete held utterance must condition exactly once".into());
    }

    let summary = summarize_predictions(&held_results);
    let returned_support = support_census(ecology.machine())?;
    let tsv = prediction_tsv(&held_results, &token_by_id)?;
    fs::write(output.join("heldout-word-fibers.tsv"), tsv)?;
    let best = held_results
        .iter()
        .min_by_key(|result| {
            (
                result.joined.maximal_fiber.len(),
                !result.joined.maximal_fiber.contains(&result.actual),
                result.stem.clone(),
                result.word_at,
            )
        })
        .ok_or("held result population disappeared")?;
    fs::write(
        output.join("heldout-best-fiber.svg"),
        render_prediction_svg(best, &token_by_id)?,
    )?;

    let result_text = format!(
        concat!(
            "# GRID synchronized receiver ecology\n\n",
            "- source: official GRID speaker s1 MPEG and word alignments\n",
            "- retained occurrences: 96 (80 conditioning, 16 held return)\n",
            "- decoded receiver sections: complete 360x288 video, embedded acoustic channel, inherited word alignment/transcript\n",
            "- vocabulary: 51 exact returned token sections\n",
            "- conditioning wall time: {training_seconds:.3}s\n",
            "- training contacts: {training_contacts}\n",
            "- training Swing rides: {training_rides}\n",
            "- training OPEN contacts: {training_open}\n",
            "- training indexed relation signatures: {training_indexed}\n",
            "- established relation signatures before holdout: {established_before_holdout}\n",
            "- training standing constituents: {training_standing_constituents}\n",
            "- training standing cells: {training_standing_cells}\n",
            "- training active support factors: {training_active_factors}\n",
            "- training support DAG nodes / cause edges: {training_causal_nodes} / {training_cause_edges}\n",
            "- training direct / resolved-active boundary entries: {training_direct_boundaries} / {training_resolved_boundaries}\n",
            "- training support native words: {training_support_words}\n",
            "- maximum factors / DAG nodes in one training constituent: {training_maximum_factors} / {training_maximum_nodes}\n",
            "- exact training rest SHA-256: `{standing_sha256}`\n",
            "- return contacts: {return_contacts}\n",
            "- returned indexed relation signatures: {returned_indexed}\n",
            "- returned standing constituents: {returned_standing_constituents}\n",
            "- returned standing cells: {returned_standing_cells}\n",
            "- returned active support factors: {returned_active_factors}\n",
            "- returned support DAG nodes / cause edges: {returned_causal_nodes} / {returned_cause_edges}\n",
            "- returned direct / resolved-active boundary entries: {returned_direct_boundaries} / {returned_resolved_boundaries}\n",
            "- returned support native words: {returned_support_words}\n",
            "- maximum factors / DAG nodes in one returned constituent: {returned_maximum_factors} / {returned_maximum_nodes}\n",
            "- prediction/return wall time: {prediction_seconds:.3}s\n",
            "- audio actual-in-fiber: {audio_admitted}/96; exact singleton: {audio_exact}/96; total fiber population: {audio_population}\n",
            "- video actual-in-fiber: {video_admitted}/96; exact singleton: {video_exact}/96; total fiber population: {video_population}\n",
            "- joined actual-in-fiber: {joined_admitted}/96; exact singleton: {joined_exact}/96; total fiber population: {joined_population}\n",
            "- joined fiber strictly refines both single-receiver fibers: {joined_strict_both}/96\n",
            "- joined fiber refines at least one single-receiver fiber: {joined_refines_one}/96\n",
            "\nThe totals are topology censuses, not a scalar loss or probability estimate. Every fiber member and every established/open evidence section is retained in `heldout-word-fibers.tsv`.\n"
        ),
        training_seconds = training_elapsed.as_secs_f64(),
        training_contacts = training_contacts,
        training_rides = training_rides,
        training_open = training_open,
        training_indexed = training_indexed,
        established_before_holdout = established_before_holdout,
        training_standing_constituents = training_standing_constituents,
        training_standing_cells = training_standing_cells,
        training_active_factors = training_support.active_factors,
        training_causal_nodes = training_support.causal_nodes,
        training_cause_edges = training_support.cause_edges,
        training_direct_boundaries = training_support.direct_boundary_entries,
        training_resolved_boundaries = training_support.resolved_boundary_entries,
        training_support_words = training_support.native_words,
        training_maximum_factors = training_support.maximum_factors,
        training_maximum_nodes = training_support.maximum_nodes,
        standing_sha256 = standing_sha256,
        return_contacts = return_contacts,
        returned_indexed = ecology.atlas().relations.len(),
        returned_standing_constituents = ecology.machine().memory().standing_constituents,
        returned_standing_cells = ecology.machine().memory().standing_cells,
        returned_active_factors = returned_support.active_factors,
        returned_causal_nodes = returned_support.causal_nodes,
        returned_cause_edges = returned_support.cause_edges,
        returned_direct_boundaries = returned_support.direct_boundary_entries,
        returned_resolved_boundaries = returned_support.resolved_boundary_entries,
        returned_support_words = returned_support.native_words,
        returned_maximum_factors = returned_support.maximum_factors,
        returned_maximum_nodes = returned_support.maximum_nodes,
        prediction_seconds = prediction_elapsed.as_secs_f64(),
        audio_admitted = summary.audio_admitted,
        audio_exact = summary.audio_exact,
        audio_population = summary.audio_population,
        video_admitted = summary.video_admitted,
        video_exact = summary.video_exact,
        video_population = summary.video_population,
        joined_admitted = summary.joined_admitted,
        joined_exact = summary.joined_exact,
        joined_population = summary.joined_population,
        joined_strict_both = summary.joined_strict_both,
        joined_refines_one = summary.joined_refines_one,
    );
    fs::write(output.join("RESULTS.md"), &result_text)?;

    println!("{result_text}");
    println!("receipts: {}", output.display());
    Ok(())
}

fn support_census(
    machine: &LiveCurrentMachine,
) -> Result<SupportCensus, Box<dyn std::error::Error>> {
    let mut census = SupportCensus::default();
    for constituent in machine.standing().constituents() {
        let family = constituent.support_family();
        census.active_factors = census
            .active_factors
            .checked_add(family.factor_count())
            .ok_or("support factor census overflow")?;
        census.causal_nodes = census
            .causal_nodes
            .checked_add(family.node_count())
            .ok_or("support node census overflow")?;
        census.cause_edges = census
            .cause_edges
            .checked_add(family.cause_edges())
            .ok_or("support cause census overflow")?;
        census.direct_boundary_entries = census
            .direct_boundary_entries
            .checked_add(family.direct_boundary_entries())
            .ok_or("support direct-boundary census overflow")?;
        census.resolved_boundary_entries = census
            .resolved_boundary_entries
            .checked_add(
                family
                    .resolved_active_boundary_entries()
                    .map_err(|error| format!("support boundary census refused: {error:?}"))?,
            )
            .ok_or("support resolved-boundary census overflow")?;
        census.native_words = census
            .native_words
            .checked_add(
                family
                    .native_word_len()
                    .map_err(|error| format!("support native census refused: {error:?}"))?,
            )
            .ok_or("support native-word census overflow")?;
        census.maximum_factors = census.maximum_factors.max(family.factor_count());
        census.maximum_nodes = census.maximum_nodes.max(family.node_count());
    }
    Ok(census)
}

fn parallel_observe(
    dataset: &Path,
    stems: &[String],
    worker_budget: usize,
) -> Result<Vec<ClipObservation>, Box<dyn std::error::Error>> {
    let workers = worker_budget.max(1).min(stems.len());
    let base = stems.len() / workers;
    let remainder = stems.len() % workers;
    let mut chunks = Vec::new();
    let mut begin = 0_usize;
    for worker in 0..workers {
        let extent = base + usize::from(worker < remainder);
        chunks.push((begin, begin + extent));
        begin += extent;
    }

    let results = std::thread::scope(|scope| {
        let mut handles = Vec::new();
        for (begin, end) in chunks {
            let dataset = dataset.to_path_buf();
            let local = stems[begin..end].to_vec();
            handles.push(scope.spawn(move || {
                local
                    .into_iter()
                    .enumerate()
                    .map(|(offset, stem)| {
                        observe_clip(&dataset, &stem, u64::try_from(begin + offset + 1).unwrap())
                    })
                    .collect::<Result<Vec<_>, String>>()
            }));
        }
        handles
            .into_iter()
            .map(|handle| {
                handle
                    .join()
                    .map_err(|_| "GRID observation worker panicked".to_owned())?
            })
            .collect::<Result<Vec<_>, String>>()
    })?;
    let mut observations = results.into_iter().flatten().collect::<Vec<_>>();
    observations.sort_by(|left, right| left.stem.cmp(&right.stem));
    Ok(observations)
}

fn observe_clip(dataset: &Path, stem: &str, ordinal: u64) -> Result<ClipObservation, String> {
    let media = dataset.join("s1").join(format!("{stem}.mpg"));
    let alignment = dataset.join("alignments/s1").join(format!("{stem}.align"));
    let words = read_alignment(&alignment)?;
    let probe = probe_media(&media)?;
    let audio = decode_audio_channel(&media, probe.audio_channels)?;
    let video = decode_video_gray(&media, probe.width, probe.height)?;
    let frame_extent = probe
        .width
        .checked_mul(probe.height)
        .ok_or_else(|| "video frame extent overflow".to_owned())?;
    if video.len() % frame_extent != 0 {
        return Err(format!("{stem}: raw video extent is not whole frames"));
    }
    let frame_count = video.len() / frame_extent;

    let mut observations = Vec::new();
    for (word_at, word) in words.into_iter().enumerate() {
        let audio_begin = mul_div_floor(word.begin, probe.audio_sample_rate, ALIGNMENT_HZ)?;
        let audio_end = mul_div_ceil(word.end, probe.audio_sample_rate, ALIGNMENT_HZ)?
            .min(u64::try_from(audio.len()).map_err(|_| "audio extent overflow")?);
        let video_denominator = ALIGNMENT_HZ
            .checked_mul(probe.video_rate_den)
            .ok_or_else(|| "video timebase overflow".to_owned())?;
        let video_begin = mul_div_floor(word.begin, probe.video_rate_num, video_denominator)?;
        let video_end = mul_div_ceil(word.end, probe.video_rate_num, video_denominator)?
            .min(u64::try_from(frame_count).map_err(|_| "video extent overflow")?);
        if audio_begin >= audio_end || video_begin >= video_end {
            return Err(format!(
                "{stem}: empty receiver word section {}: alignment=[{},{}), audio=[{audio_begin},{audio_end})/{}, video=[{video_begin},{video_end})/{frame_count}",
                word.word,
                word.begin,
                word.end,
                audio.len()
            ));
        }
        let audio_slice =
            &audio[usize::try_from(audio_begin).unwrap()..usize::try_from(audio_end).unwrap()];
        let audio_codes = audio_phase_codes(
            audio_slice,
            probe.audio_sample_rate,
            ordinal
                .checked_mul(16)
                .and_then(|value| value.checked_add(u64::try_from(word_at).ok()?))
                .ok_or_else(|| "audio lineage overflow".to_owned())?,
        )?;
        let video_codes = video_topology_codes(
            &video,
            probe.width,
            probe.height,
            usize::try_from(video_begin).unwrap(),
            usize::try_from(video_end).unwrap(),
        )?;
        observations.push(WordObservation {
            alignment: word,
            audio_begin,
            audio_end,
            video_begin,
            video_end,
            audio_codes,
            video_codes,
        });
    }
    if observations.len() != 6 {
        return Err(format!("{stem}: expected six spoken words"));
    }
    Ok(ClipObservation {
        stem: stem.to_owned(),
        ordinal,
        audio_sample_rate: probe.audio_sample_rate,
        video_rate_num: probe.video_rate_num,
        video_rate_den: probe.video_rate_den,
        words: observations,
    })
}

fn read_alignment(path: &Path) -> Result<Vec<AlignmentWord>, String> {
    let text = fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))?;
    let mut words = Vec::new();
    for line in text.lines() {
        let fields = line.split_whitespace().collect::<Vec<_>>();
        if fields.len() != 3 {
            return Err(format!("{}: malformed alignment row", path.display()));
        }
        if matches!(fields[2], "sil" | "sp") {
            continue;
        }
        let begin = fields[0]
            .parse::<u64>()
            .map_err(|error| format!("{}: {error}", path.display()))?;
        let end = fields[1]
            .parse::<u64>()
            .map_err(|error| format!("{}: {error}", path.display()))?;
        if begin >= end {
            return Err(format!("{}: nonpositive word interval", path.display()));
        }
        words.push(AlignmentWord {
            begin,
            end,
            word: fields[2].to_owned(),
        });
    }
    Ok(words)
}

fn probe_media(path: &Path) -> Result<MediaProbe, String> {
    let output = Command::new("ffprobe")
        .args([
            "-v",
            "error",
            "-show_entries",
            "stream=codec_type,width,height,avg_frame_rate,sample_rate,channels",
            "-of",
            "json",
        ])
        .arg(path)
        .output()
        .map_err(|error| format!("ffprobe {}: {error}", path.display()))?;
    if !output.status.success() {
        return Err(format!(
            "ffprobe {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let body: Value = serde_json::from_slice(&output.stdout).map_err(|error| error.to_string())?;
    let streams = body["streams"]
        .as_array()
        .ok_or_else(|| "ffprobe omitted streams".to_owned())?;
    let video = streams
        .iter()
        .find(|stream| stream["codec_type"] == "video")
        .ok_or_else(|| "GRID occurrence has no video stream".to_owned())?;
    let audio = streams
        .iter()
        .find(|stream| stream["codec_type"] == "audio")
        .ok_or_else(|| "GRID occurrence has no audio stream".to_owned())?;
    let width = json_usize(video, "width")?;
    let height = json_usize(video, "height")?;
    let rate = video["avg_frame_rate"]
        .as_str()
        .ok_or_else(|| "video frame rate absent".to_owned())?;
    let (video_rate_num, video_rate_den) = parse_rate(rate)?;
    let audio_sample_rate = audio["sample_rate"]
        .as_str()
        .ok_or_else(|| "audio sample rate absent".to_owned())?
        .parse::<u64>()
        .map_err(|error| error.to_string())?;
    let audio_channels = json_usize(audio, "channels")?;
    Ok(MediaProbe {
        width,
        height,
        video_rate_num,
        video_rate_den,
        audio_sample_rate,
        audio_channels,
    })
}

fn json_usize(value: &Value, field: &str) -> Result<usize, String> {
    value[field]
        .as_u64()
        .and_then(|value| usize::try_from(value).ok())
        .ok_or_else(|| format!("ffprobe field {field} absent or out of range"))
}

fn parse_rate(rate: &str) -> Result<(u64, u64), String> {
    let (numerator, denominator) = rate
        .split_once('/')
        .ok_or_else(|| format!("malformed frame rate {rate}"))?;
    let numerator = numerator
        .parse::<u64>()
        .map_err(|error| error.to_string())?;
    let denominator = denominator
        .parse::<u64>()
        .map_err(|error| error.to_string())?;
    if numerator == 0 || denominator == 0 {
        return Err("zero frame rate".to_owned());
    }
    Ok((numerator, denominator))
}

fn decode_audio_channel(path: &Path, channels: usize) -> Result<Vec<i32>, String> {
    let output = Command::new("ffmpeg")
        .args(["-v", "error", "-i"])
        .arg(path)
        .args(["-map", "0:a:0", "-f", "s16le", "-acodec", "pcm_s16le", "-"])
        .output()
        .map_err(|error| format!("ffmpeg audio {}: {error}", path.display()))?;
    if !output.status.success() {
        return Err(format!(
            "ffmpeg audio {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let frame_bytes = channels
        .checked_mul(2)
        .ok_or_else(|| "audio frame width overflow".to_owned())?;
    if channels == 0 || output.stdout.len() % frame_bytes != 0 {
        return Err("decoded audio is not whole sample frames".to_owned());
    }
    Ok(output
        .stdout
        .chunks_exact(frame_bytes)
        .map(|frame| i32::from(i16::from_le_bytes([frame[0], frame[1]])))
        .collect())
}

fn decode_video_gray(path: &Path, width: usize, height: usize) -> Result<Vec<u8>, String> {
    let output = Command::new("ffmpeg")
        .args(["-v", "error", "-i"])
        .arg(path)
        .args(["-map", "0:v:0", "-f", "rawvideo", "-pix_fmt", "gray", "-"])
        .output()
        .map_err(|error| format!("ffmpeg video {}: {error}", path.display()))?;
    if !output.status.success() {
        return Err(format!(
            "ffmpeg video {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let frame_extent = width
        .checked_mul(height)
        .ok_or_else(|| "video frame extent overflow".to_owned())?;
    if frame_extent == 0 || output.stdout.len() % frame_extent != 0 {
        return Err("decoded video is not whole gray frames".to_owned());
    }
    Ok(output.stdout)
}

fn audio_phase_codes(
    samples: &[i32],
    sample_rate: u64,
    lineage: u64,
) -> Result<[i64; FEATURE_GROUPS], String> {
    let step = BigRational::new(BigInt::from(1), BigInt::from(sample_rate));
    let source = ExactPhaseCurrentSection::from_i32(
        PhaseCurrentReceiverId(AUDIO_RECEIVER.0),
        PhaseCurrentLineageId(lineage),
        rational_zero(),
        step.clone(),
        PHASE_EXTENT,
        samples,
    )
    .map_err(|error| error.to_string())?;
    let response = ExactPhaseCurrentSection::from_i32(
        PhaseCurrentReceiverId(0x4449_4646),
        PhaseCurrentLineageId(lineage | (1_u64 << 63)),
        rational_zero(),
        step,
        PHASE_EXTENT,
        &[1, -1],
    )
    .map_err(|error| error.to_string())?;
    let spectrum = receive_phase_transport_spectrum(
        &source,
        &response,
        PhaseCurrentReceiverId(0x4155_444f),
        PhaseCurrentLineageId(lineage),
    )
    .map_err(|error| error.to_string())?;
    let mut trits = Vec::with_capacity(FEATURE_GROUPS * FEATURE_TRITS);
    for phase in 0..PHASE_EXTENT {
        let local = &spectrum.target_bands[phase].population;
        let carried = &spectrum.target_bands[PHASE_EXTENT + phase].population;
        trits.push(order_trit(
            &local.positive_occurrences,
            &local.negative_occurrences,
        ));
        trits.push(order_trit(
            local.net_current.magnitude(),
            carried.net_current.magnitude(),
        ));
        trits.push(order_trit(
            &spectrum.source_phases[phase].positive_current,
            &spectrum.source_phases[phase].negative_current,
        ));
    }
    group_trits(&trits)
}

fn video_topology_codes(
    video: &[u8],
    width: usize,
    height: usize,
    frame_begin: usize,
    frame_end: usize,
) -> Result<[i64; FEATURE_GROUPS], String> {
    let frame_extent = width
        .checked_mul(height)
        .ok_or_else(|| "video frame extent overflow".to_owned())?;
    let frame_count = video.len() / frame_extent;
    if frame_begin >= frame_end || frame_end > frame_count {
        return Err("video word interval outside decoded occurrence".to_owned());
    }

    let mut positive_current = [0_u128; 8];
    let mut negative_current = [0_u128; 8];
    let mut positive_occurrences = [0_u128; 8];
    let mut negative_occurrences = [0_u128; 8];
    let mut horizontal_fronts = [0_u128; 8];
    let mut vertical_fronts = [0_u128; 8];
    let mut previous_signs = vec![0_i8; frame_extent];

    for frame_at in (frame_begin + 1)..frame_end {
        let phase = (frame_at - frame_begin - 1) % 8;
        let previous = &video[(frame_at - 1) * frame_extent..frame_at * frame_extent];
        let current = &video[frame_at * frame_extent..(frame_at + 1) * frame_extent];
        for row in 0..height {
            for column in 0..width {
                let at = row * width + column;
                let difference = i16::from(current[at]) - i16::from(previous[at]);
                let sign = difference.signum() as i8;
                if difference > 0 {
                    positive_current[phase] += difference as u128;
                    positive_occurrences[phase] += 1;
                } else if difference < 0 {
                    negative_current[phase] += (-difference) as u128;
                    negative_occurrences[phase] += 1;
                }
                if column > 0 {
                    let left = previous_signs[at - 1];
                    if sign != 0 && left != 0 && sign != left {
                        horizontal_fronts[phase] += 1;
                    }
                }
                if row > 0 {
                    let above = previous_signs[at - width];
                    if sign != 0 && above != 0 && sign != above {
                        vertical_fronts[phase] += 1;
                    }
                }
                previous_signs[at] = sign;
            }
        }
    }

    let first = &video[frame_begin * frame_extent..(frame_begin + 1) * frame_extent];
    let last = &video[(frame_end - 1) * frame_extent..frame_end * frame_extent];
    let mut signs = vec![0_i8; frame_extent];
    let mut vertices = [0_i128; 2];
    let mut edges = [0_i128; 2];
    let mut faces = [0_i128; 2];
    for at in 0..frame_extent {
        let sign = (i16::from(last[at]) - i16::from(first[at])).signum() as i8;
        signs[at] = sign;
        if sign > 0 {
            vertices[0] += 1;
        } else if sign < 0 {
            vertices[1] += 1;
        }
    }
    for row in 0..height {
        for column in 0..width {
            let at = row * width + column;
            let sign = signs[at];
            if sign == 0 {
                continue;
            }
            let species = usize::from(sign < 0);
            if column + 1 < width && signs[at + 1] == sign {
                edges[species] += 1;
            }
            if row + 1 < height && signs[at + width] == sign {
                edges[species] += 1;
            }
            if column + 1 < width
                && row + 1 < height
                && signs[at + 1] == sign
                && signs[at + width] == sign
                && signs[at + width + 1] == sign
            {
                faces[species] += 1;
            }
        }
    }
    let euler = [
        vertices[0] - edges[0] + faces[0],
        vertices[1] - edges[1] + faces[1],
    ];

    let mut trits = Vec::with_capacity(FEATURE_GROUPS * FEATURE_TRITS);
    for phase in 0..8 {
        trits.push(order_trit(
            &positive_current[phase],
            &negative_current[phase],
        ));
        trits.push(order_trit(
            &positive_occurrences[phase],
            &negative_occurrences[phase],
        ));
        trits.push(order_trit(
            &horizontal_fronts[phase],
            &vertical_fronts[phase],
        ));
        trits.push(order_trit(
            &(positive_current[phase] + negative_current[phase]),
            &(positive_current[(phase + 1) % 8] + negative_current[(phase + 1) % 8]),
        ));
        trits.push(order_trit(
            &positive_current[phase],
            &positive_current[(phase + 1) % 8],
        ));
    }
    trits.extend([
        order_trit(&vertices[0], &vertices[1]),
        order_trit(&edges[0], &edges[1]),
        order_trit(&faces[0], &faces[1]),
        order_trit(&euler[0].unsigned_abs(), &euler[1].unsigned_abs()),
        order_trit(
            &positive_current.iter().sum::<u128>(),
            &negative_current.iter().sum::<u128>(),
        ),
        order_trit(
            &horizontal_fronts.iter().sum::<u128>(),
            &vertical_fronts.iter().sum::<u128>(),
        ),
        order_trit(
            &positive_occurrences.iter().sum::<u128>(),
            &negative_occurrences.iter().sum::<u128>(),
        ),
        order_trit(&(vertices[0] + vertices[1]), &(edges[0] + edges[1])),
    ]);
    group_trits(&trits)
}

fn order_trit<T: Ord>(left: &T, right: &T) -> u8 {
    match left.cmp(right) {
        std::cmp::Ordering::Less => 0,
        std::cmp::Ordering::Equal => 1,
        std::cmp::Ordering::Greater => 2,
    }
}

fn group_trits(trits: &[u8]) -> Result<[i64; FEATURE_GROUPS], String> {
    if trits.len() != FEATURE_GROUPS * FEATURE_TRITS {
        return Err(format!(
            "expected {} receiver trits, found {}",
            FEATURE_GROUPS * FEATURE_TRITS,
            trits.len()
        ));
    }
    let mut codes = [0_i64; FEATURE_GROUPS];
    for (group, chunk) in trits.chunks_exact(FEATURE_TRITS).enumerate() {
        let mut code = 0_i64;
        for trit in chunk {
            code = code
                .checked_mul(3)
                .and_then(|value| value.checked_add(i64::from(*trit)))
                .ok_or_else(|| "feature code overflow".to_owned())?;
        }
        codes[group] = code + 1;
    }
    Ok(codes)
}

fn derive_vocabulary<'a>(
    observations: impl IntoIterator<Item = &'a ClipObservation>,
) -> Result<BTreeMap<String, u64>, String> {
    let words = observations
        .into_iter()
        .flat_map(|observation| {
            observation
                .words
                .iter()
                .map(|word| word.alignment.word.clone())
        })
        .collect::<BTreeSet<_>>();
    words
        .into_iter()
        .enumerate()
        .map(|(at, word)| {
            Ok((
                word,
                u64::try_from(at + 1).map_err(|_| "vocabulary overflow".to_owned())?,
            ))
        })
        .collect()
}

fn complete_occurrence(
    observation: &ClipObservation,
    vocabulary: &BTreeMap<String, u64>,
    text_origin: SynchronizedCellOrigin,
) -> Result<ExactSynchronizedOccurrence, Box<dyn std::error::Error>> {
    let base = observation
        .ordinal
        .checked_mul(10_000)
        .ok_or("cell identity overflow")?;
    let mut audio = Vec::new();
    let mut video = Vec::new();
    let mut text = Vec::new();
    for (word_at, word) in observation.words.iter().enumerate() {
        append_feature_cells(
            &mut audio,
            base,
            word_at,
            0,
            AUDIO_CHART_BASE,
            10_000,
            word.audio_begin,
            word.audio_end,
            &word.audio_codes,
        )?;
        append_feature_cells(
            &mut video,
            base,
            word_at,
            20,
            VIDEO_CHART_BASE,
            20_000,
            word.video_begin,
            word.video_end,
            &word.video_codes,
        )?;
        let token = vocabulary[&word.alignment.word];
        text.push(TimedReceiverCell::new(
            SynchronizedCellId(base + u64::try_from(word_at)? * 100 + 50),
            ReceiverChartIdentity::new(TEXT_CHART),
            TEXT_CHART,
            relation_atom(i64::try_from(30_000 + token)?)?,
            integer(word.alignment.begin),
            integer(word.alignment.end),
            1,
            text_origin,
        )?);
    }
    occurrence_from_sections(
        observation,
        observation.ordinal,
        audio,
        video,
        text,
        PredictionFace::Joined,
        true,
    )
}

fn append_feature_cells(
    output: &mut Vec<TimedReceiverCell>,
    base: u64,
    word_at: usize,
    local_offset: u64,
    chart_base: u64,
    material_base: i64,
    begin: u64,
    end: u64,
    codes: &[i64; FEATURE_GROUPS],
) -> Result<(), Box<dyn std::error::Error>> {
    for (group, code) in codes.iter().enumerate() {
        let group = u64::try_from(group)?;
        output.push(TimedReceiverCell::new(
            SynchronizedCellId(base + u64::try_from(word_at)? * 100 + local_offset + group),
            ReceiverChartIdentity::new(chart_base + group),
            chart_base + group,
            relation_atom(material_base + code)?,
            integer(begin),
            integer(end),
            0,
            SynchronizedCellOrigin::Inherited,
        )?);
    }
    Ok(())
}

fn prediction_alternatives(
    observation: &ClipObservation,
    word_at: usize,
    vocabulary: &BTreeMap<String, u64>,
    face: PredictionFace,
) -> Result<Vec<SynchronizedPredictionAlternative>, Box<dyn std::error::Error>> {
    let word = &observation.words[word_at];
    let base = observation
        .ordinal
        .checked_mul(10_000)
        .ok_or("cell identity overflow")?;
    let mut audio = Vec::new();
    let mut video = Vec::new();
    append_feature_cells(
        &mut audio,
        base,
        word_at,
        0,
        AUDIO_CHART_BASE,
        10_000,
        word.audio_begin,
        word.audio_end,
        &word.audio_codes,
    )?;
    append_feature_cells(
        &mut video,
        base,
        word_at,
        20,
        VIDEO_CHART_BASE,
        20_000,
        word.video_begin,
        word.video_end,
        &word.video_codes,
    )?;

    vocabulary
        .values()
        .copied()
        .map(|token| {
            let text = vec![TimedReceiverCell::new(
                SynchronizedCellId(base + u64::try_from(word_at)? * 100 + 50),
                ReceiverChartIdentity::new(TEXT_CHART),
                TEXT_CHART,
                relation_atom(i64::try_from(30_000 + token)?)?,
                integer(word.alignment.begin),
                integer(word.alignment.end),
                1,
                SynchronizedCellOrigin::Candidate,
            )?];
            Ok(SynchronizedPredictionAlternative {
                candidate: SynchronizedCandidateId(token),
                occurrence: occurrence_from_sections(
                    observation,
                    1_000_000 + observation.ordinal * 10 + u64::try_from(word_at)?,
                    audio.clone(),
                    video.clone(),
                    text,
                    face,
                    false,
                )?,
            })
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn occurrence_from_sections(
    observation: &ClipObservation,
    occurrence: u64,
    audio: Vec<TimedReceiverCell>,
    video: Vec<TimedReceiverCell>,
    text: Vec<TimedReceiverCell>,
    face: PredictionFace,
    include_audio_video: bool,
) -> Result<ExactSynchronizedOccurrence, Box<dyn std::error::Error>> {
    let audio_section = SynchronizedReceiverSection::new(
        AUDIO_RECEIVER,
        ExactClockTransport::new(
            rational_zero(),
            rational_zero(),
            BigRational::new(BigInt::from(1), BigInt::from(observation.audio_sample_rate)),
        )?,
        audio,
    )?;
    let video_section = SynchronizedReceiverSection::new(
        VIDEO_RECEIVER,
        ExactClockTransport::new(
            rational_zero(),
            rational_zero(),
            BigRational::new(
                BigInt::from(observation.video_rate_den),
                BigInt::from(observation.video_rate_num),
            ),
        )?,
        video,
    )?;
    let text_section = SynchronizedReceiverSection::new(
        TEXT_RECEIVER,
        ExactClockTransport::new(
            rational_zero(),
            rational_zero(),
            BigRational::new(BigInt::from(1), BigInt::from(ALIGNMENT_HZ)),
        )?,
        text,
    )?;
    let mut sections = vec![text_section];
    let mut interactions = Vec::new();
    match face {
        PredictionFace::Audio => {
            sections.push(audio_section);
            interactions.push(SynchronizedInteraction::new(AUDIO_RECEIVER, TEXT_RECEIVER)?);
        }
        PredictionFace::Video => {
            sections.push(video_section);
            interactions.push(SynchronizedInteraction::new(VIDEO_RECEIVER, TEXT_RECEIVER)?);
        }
        PredictionFace::Joined => {
            sections.push(audio_section);
            sections.push(video_section);
            interactions.push(SynchronizedInteraction::new(AUDIO_RECEIVER, TEXT_RECEIVER)?);
            interactions.push(SynchronizedInteraction::new(VIDEO_RECEIVER, TEXT_RECEIVER)?);
            if include_audio_video {
                interactions.push(SynchronizedInteraction::new(
                    AUDIO_RECEIVER,
                    VIDEO_RECEIVER,
                )?);
            }
        }
    }
    ExactSynchronizedOccurrence::new(
        occurrence,
        ReceiverChartIdentity::new(HORIZON_CHART),
        relation_atom(1)?,
        2,
        sections,
        interactions,
    )
    .map_err(Into::into)
}

#[derive(Clone, Copy, Debug, Default)]
struct PredictionSummary {
    audio_admitted: usize,
    audio_exact: usize,
    audio_population: usize,
    video_admitted: usize,
    video_exact: usize,
    video_population: usize,
    joined_admitted: usize,
    joined_exact: usize,
    joined_population: usize,
    joined_strict_both: usize,
    joined_refines_one: usize,
}

fn summarize_predictions(results: &[HeldWordResult]) -> PredictionSummary {
    let mut summary = PredictionSummary::default();
    for result in results {
        summary.audio_admitted += usize::from(result.audio.maximal_fiber.contains(&result.actual));
        summary.audio_exact += usize::from(result.audio.invariant == Some(result.actual));
        summary.audio_population += result.audio.maximal_fiber.len();
        summary.video_admitted += usize::from(result.video.maximal_fiber.contains(&result.actual));
        summary.video_exact += usize::from(result.video.invariant == Some(result.actual));
        summary.video_population += result.video.maximal_fiber.len();
        summary.joined_admitted +=
            usize::from(result.joined.maximal_fiber.contains(&result.actual));
        summary.joined_exact += usize::from(result.joined.invariant == Some(result.actual));
        summary.joined_population += result.joined.maximal_fiber.len();
        let strict_audio = result
            .joined
            .maximal_fiber
            .is_subset(&result.audio.maximal_fiber)
            && result.joined.maximal_fiber != result.audio.maximal_fiber;
        let strict_video = result
            .joined
            .maximal_fiber
            .is_subset(&result.video.maximal_fiber)
            && result.joined.maximal_fiber != result.video.maximal_fiber;
        summary.joined_strict_both += usize::from(strict_audio && strict_video);
        summary.joined_refines_one += usize::from(strict_audio || strict_video);
    }
    summary
}

fn prediction_tsv(
    results: &[HeldWordResult],
    token_by_id: &BTreeMap<u64, String>,
) -> Result<String, Box<dyn std::error::Error>> {
    let mut output = String::from(
        "stem\tword_at\tactual\taudio_fiber\tvideo_fiber\tjoined_fiber\taudio_actual\tvideo_actual\tjoined_actual\taudio_invariant\tvideo_invariant\tjoined_invariant\tjoined_established_contacts\tjoined_open_contacts\n",
    );
    for result in results {
        let joined_actual = result
            .joined
            .candidates
            .get(&result.actual)
            .ok_or("actual candidate absent")?;
        writeln!(
            output,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            result.stem,
            result.word_at,
            result.actual_word,
            fiber_words(&result.audio, token_by_id),
            fiber_words(&result.video, token_by_id),
            fiber_words(&result.joined, token_by_id),
            result.audio.maximal_fiber.contains(&result.actual),
            result.video.maximal_fiber.contains(&result.actual),
            result.joined.maximal_fiber.contains(&result.actual),
            result
                .audio
                .invariant
                .and_then(|id| token_by_id.get(&id.0))
                .map_or("-", String::as_str),
            result
                .video
                .invariant
                .and_then(|id| token_by_id.get(&id.0))
                .map_or("-", String::as_str),
            result
                .joined
                .invariant
                .and_then(|id| token_by_id.get(&id.0))
                .map_or("-", String::as_str),
            joined_actual.established_support.len(),
            joined_actual.open_support.len(),
        )?;
    }
    Ok(output)
}

fn fiber_words(prediction: &SynchronizedPrediction, token_by_id: &BTreeMap<u64, String>) -> String {
    prediction
        .maximal_fiber
        .iter()
        .filter_map(|candidate| token_by_id.get(&candidate.0))
        .cloned()
        .collect::<Vec<_>>()
        .join(",")
}

fn render_prediction_svg(
    result: &HeldWordResult,
    token_by_id: &BTreeMap<u64, String>,
) -> Result<String, Box<dyn std::error::Error>> {
    let width = 1400_i64;
    let row_height = 34_i64;
    let candidates = result
        .joined
        .maximal_fiber
        .iter()
        .copied()
        .collect::<Vec<_>>();
    let height = 180_i64
        .checked_add(row_height * i64::try_from(candidates.len().max(12))?)
        .ok_or("SVG extent overflow")?;
    let mut svg = format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\" viewBox=\"0 0 {width} {height}\"><rect width=\"100%\" height=\"100%\" fill=\"#071014\"/><style>text{{font-family:monospace;fill:#dce9e7}}.muted{{fill:#78908d}}.actual{{fill:#ffcc66;font-weight:bold}}.audio{{fill:#45d4ff}}.video{{fill:#9eff6b}}.edge{{stroke:#284842;stroke-width:1}}.live{{stroke:#ffd166;stroke-width:2}}</style>"
    );
    writeln!(
        svg,
        "<text x=\"40\" y=\"42\" font-size=\"24\">narrowest held prediction fiber: {} word {} — returned <tspan class=\"actual\">{}</tspan></text>",
        result.stem, result.word_at, result.actual_word
    )?;
    let admission = if result.joined.maximal_fiber.contains(&result.actual) {
        "returned section admitted"
    } else {
        "RETURNED SECTION OUTSIDE FIBER"
    };
    writeln!(
        svg,
        "<text x=\"40\" y=\"72\" font-size=\"15\" class=\"muted\">audio {} alternatives · video {} · joined {} · {admission}</text>",
        result.audio.maximal_fiber.len(),
        result.video.maximal_fiber.len(),
        result.joined.maximal_fiber.len()
    )?;
    for group in 0..FEATURE_GROUPS {
        let y = 130 + i64::try_from(group)? * 42;
        writeln!(
            svg,
            "<circle cx=\"150\" cy=\"{y}\" r=\"8\" class=\"audio\"/><text x=\"170\" y=\"{}\" font-size=\"14\">acoustic phase/carry facet {group}</text>",
            y + 5
        )?;
        writeln!(
            svg,
            "<circle cx=\"500\" cy=\"{y}\" r=\"8\" class=\"video\"/><text x=\"520\" y=\"{}\" font-size=\"14\">full-frame differential facet {group}</text>",
            y + 5
        )?;
    }
    for (at, candidate) in candidates.iter().enumerate() {
        let y = 120 + i64::try_from(at)? * row_height;
        let word = &token_by_id[&candidate.0];
        let class = if *candidate == result.actual {
            "actual"
        } else {
            ""
        };
        writeln!(
            svg,
            "<line x1=\"700\" y1=\"{y}\" x2=\"1120\" y2=\"{y}\" class=\"edge\"/><circle cx=\"1160\" cy=\"{y}\" r=\"7\" class=\"{class}\"/><text x=\"1180\" y=\"{}\" font-size=\"15\" class=\"{class}\">{word}</text>",
            y + 5
        )?;
    }
    let actual = result
        .joined
        .candidates
        .get(&result.actual)
        .ok_or("actual candidate missing from SVG prediction")?;
    writeln!(
        svg,
        "<text x=\"40\" y=\"{}\" font-size=\"15\" class=\"muted\">returned section support: {} established · {} OPEN; projection is an inspection membrane, not the receiver geometry</text></svg>",
        height - 35,
        actual.established_support.len(),
        actual.open_support.len()
    )?;
    Ok(svg)
}

fn mul_div_floor(value: u64, numerator: u64, denominator: u64) -> Result<u64, String> {
    let product = u128::from(value)
        .checked_mul(u128::from(numerator))
        .ok_or_else(|| "time transport overflow".to_owned())?;
    u64::try_from(product / u128::from(denominator))
        .map_err(|_| "time transport overflow".to_owned())
}

fn mul_div_ceil(value: u64, numerator: u64, denominator: u64) -> Result<u64, String> {
    let product = u128::from(value)
        .checked_mul(u128::from(numerator))
        .ok_or_else(|| "time transport overflow".to_owned())?;
    let denominator = u128::from(denominator);
    u64::try_from(product.div_ceil(denominator)).map_err(|_| "time transport overflow".to_owned())
}

fn integer(value: u64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn rational_zero() -> BigRational {
    BigRational::from_integer(BigInt::from(0))
}

fn hex_digest(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(64);
    for byte in digest {
        write!(output, "{byte:02x}").unwrap();
    }
    output
}
