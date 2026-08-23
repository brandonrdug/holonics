//! N2: text, vision, and raw waveform occurrences cross one receiver-exact native ecology.
//!
//! The unchanged I4 text/vision source receipt is reused by exact closure identity. Four newly
//! caused 16 kHz PCM occurrences cross the exact acoustic source owner and Gemma's authenticated
//! `embed_audio` projection on the RTX card. One three-port rest then returns the shared passage,
//! every local/shared withdrawal, complete fibres, and its still-open foreign interiors from a
//! source-detached process.

#[path = "n2/audio.rs"]
mod audio;

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use holonic_engine::cuda_refine::CudaRefineExecutor;
use holonic_engine::phoenix::heterogeneous_fusion::{
    HeterogeneousFusionRest, ModalityPort, PortDeclaration, SharedWorldGenerator,
    SourcePortResponse,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};

const DEFAULT_OUT: &str =
    "output/the_acoustic_section_crosses_the_inherited_projection_and_three_ports_share_one_native_ecology";
const DEFAULT_MODEL: &str = "/home/b/models/gemma-4-E4B-it";
const I4_SOURCE: &str =
    "output/the_heterogeneous_ports_found_one_shared_phoenix_ecology/00-source-conduct.json";
const I4_MANIFEST: &str =
    "output/the_heterogeneous_ports_found_one_shared_phoenix_ecology/MANIFEST.json";
const REST_SCHEMA: &str = "holonics.n2.rest-directory.v1";

#[derive(Clone, Debug, Deserialize)]
struct PriorSourceConduct {
    source_model_sha256: String,
    responses: Vec<SourcePortResponse>,
    open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ComponentIdentity {
    path: String,
    sha256: String,
    octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RestDirectory {
    schema: String,
    standing: ComponentIdentity,
    decoder: ComponentIdentity,
    fibres: ComponentIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DetachedReturn {
    schema: String,
    component_sha256: BTreeMap<String, String>,
    predecessor_addresses: Vec<u32>,
    successor_addresses: Vec<u32>,
    shared_withdrawn_addresses: Vec<u32>,
    local_withdrawn_addresses: Vec<u32>,
    modality_only_controls: BTreeMap<String, Vec<u32>>,
    every_naturality_square_commutes: bool,
    shared_withdrawal_moves_every_port: bool,
    local_withdrawal_moves_only_its_port: bool,
    source_access_descriptors: Vec<String>,
    forbidden_source_access: Vec<String>,
    cpu_semantic_callbacks_between_fronts: u64,
    apparatus: DetachedApparatus,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DetachedApparatus {
    device: String,
    block_threads: u32,
    active_lanes: u32,
    launches: u64,
    synchronizations: u64,
    host_ingress_octets: u64,
    host_egress_octets: u64,
    resident_octets: u64,
    physical_wall_microseconds: u128,
}

#[derive(Serialize)]
struct N2SourceProduct<'a> {
    schema: &'static str,
    truth_status: &'static str,
    reused_text_vision_receipt: ComponentIdentity,
    prior_source_model_sha256: &'a str,
    prior_responses: &'a [SourcePortResponse],
    audio: &'a audio::AudioSourceConduct,
}

#[derive(Serialize)]
struct N2Dissection<'a> {
    schema: &'static str,
    truth_status: &'static str,
    modality_entry_paths: Vec<Value>,
    shared_junction: &'a SharedWorldGenerator,
    naturality_squares: &'a [holonic_engine::phoenix::heterogeneous_fusion::NaturalitySquare],
    reconstruction_fibres:
        &'a [holonic_engine::phoenix::heterogeneous_fusion::ModalityReconstructionFibre],
    shared_and_local_withdrawals: &'a DetachedReturn,
    open_exterior: &'a [String],
}

#[derive(Serialize)]
struct N2Grade {
    schema: &'static str,
    truth_status: &'static str,
    unchanged_text_and_vision_source_receipt_reused: bool,
    raw_waveforms_are_untranscribed_productive_occurrences: bool,
    exact_pcm_frame_and_sample_incidence_returned: bool,
    inherited_audio_projection_enacted_on_resident_card: bool,
    three_separately_typed_ports_returned: bool,
    complete_port_fibres_and_naturality_returned: bool,
    shared_and_every_local_withdrawal_returned: bool,
    source_detached_remount_returned: bool,
    foreign_audio_tower_interior_retained_as_open_fibre: bool,
    passed: bool,
}

enum Args {
    Produce { model: PathBuf, output: PathBuf },
    Detached { rest: PathBuf, output: PathBuf },
}

fn main() -> Result<(), String> {
    match args()? {
        Args::Produce { model, output } => produce(&model, &output),
        Args::Detached { rest, output } => detached(&rest, &output),
    }
}

fn produce(model: &Path, output: &Path) -> Result<(), String> {
    if output.exists() {
        return Err(format!(
            "N2 output {} already exists; inspect its addressed receipt instead of replaying it",
            output.display()
        ));
    }
    for required in [
        model.join("model.safetensors"),
        model.join("config.json"),
        PathBuf::from(I4_SOURCE),
        PathBuf::from(I4_MANIFEST),
    ] {
        if !required.is_file() {
            return Err(format!(
                "required N2 material {} is absent",
                required.display()
            ));
        }
    }
    fs::create_dir_all(output.join("source-occurrences")).map_err(|error| error.to_string())?;
    let audio_occurrences = synthesize_waveforms(&output.join("source-occurrences"))?;

    let prior_bytes = fs::read(I4_SOURCE).map_err(|error| error.to_string())?;
    let prior: PriorSourceConduct =
        serde_json::from_slice(&prior_bytes).map_err(|error| error.to_string())?;
    let prior_ports = prior
        .responses
        .iter()
        .map(|response| response.port)
        .collect::<BTreeSet<_>>();
    if prior.responses.len() != 8
        || prior_ports
            != [ModalityPort::TextCodeword, ModalityPort::VisionPatch]
                .into_iter()
                .collect()
    {
        return Err(
            "the admitted I4 source receipt is not its complete two-port family".to_owned(),
        );
    }
    let config: Value = serde_json::from_slice(
        &fs::read(model.join("config.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let text_width = u32_field(&config, &["text_config", "hidden_size"])?;
    let vision_width = u32_field(&config, &["vision_config", "hidden_size"])?;
    let audio_width = u32_field(&config, &["audio_config", "output_proj_dims"])?;
    let frame_length = u32_field(
        &config,
        &["audio_config", "audio_feature_extractor", "frame_length"],
    )
    .unwrap_or(320);
    let frame_hop = u32_field(
        &config,
        &["audio_config", "audio_feature_extractor", "hop_length"],
    )
    .unwrap_or(160);
    let audio = audio::conduct(model, &audio_occurrences, frame_length, frame_hop)?;
    if audio.responses.len() != 4
        || audio
            .returns
            .iter()
            .any(|returning| returning.source.sample_rate != 16_000)
    {
        return Err(
            "the N2 audio source family is incomplete or not at the Gemma 16 kHz boundary"
                .to_owned(),
        );
    }

    let mut responses = prior.responses.clone();
    responses.extend(audio.responses.clone());
    let mut open_exterior = prior
        .open_exterior
        .into_iter()
        .filter(|opening| !opening.to_ascii_lowercase().contains("audio"))
        .collect::<Vec<_>>();
    open_exterior.extend(audio.open_exterior.clone());
    open_exterior.push(
        "audio production, video chronology, and wider successor histories remain outside N2"
            .to_owned(),
    );
    let rest = HeterogeneousFusionRest::found(
        prior.source_model_sha256.clone(),
        vec![
            PortDeclaration {
                port: ModalityPort::TextCodeword,
                boundary: format!("admitted I4 tokenizer/codeword source boundary, width {text_width}"),
                source_population: "model.language_model.embed_tokens.weight".to_owned(),
                width: text_width,
                incidence: "UTF-8 byte spans and serial codeword adjacency".to_owned(),
            },
            PortDeclaration {
                port: ModalityPort::VisionPatch,
                boundary: format!("admitted I4 exact RGB patch source boundary, width {vision_width}"),
                source_population: "model.vision_tower.patch_embedder.{input_proj,position_embedding_table}".to_owned(),
                width: vision_width,
                incidence: "two-dimensional patch grid and within-patch channel order".to_owned(),
            },
            PortDeclaration {
                port: ModalityPort::AudioFrame,
                boundary: format!("exact mono PCM chronology → inherited Gemma audio projection, width {audio_width}"),
                source_population: "model.embed_audio.embedding_projection.weight".to_owned(),
                width: audio_width,
                incidence: "sample order, overlapping frame support, frame chronology, and complete PCM reconstruction fibre".to_owned(),
            },
        ],
        responses,
        SharedWorldGenerator {
            name: "oriented-parameter-sign-passage".to_owned(),
            predecessor: 0,
            successor: 1,
            lineage: "the M0 −χ→+χ world occurrence was declared before source conduct; family 0 founds and family 1 tests the same orientation across three ports".to_owned(),
            common_world_receiver: "the native parameter-orientation consequence; transcript equality, filenames, media labels, and projection similarity are excluded".to_owned(),
        },
        vec!["video-temporal-port".to_owned()],
        open_exterior,
    )
    .map_err(|error| error.to_string())?;

    let standing = rest.standing_bytes().map_err(|error| error.to_string())?;
    let decoder = rest.decoder_bytes().map_err(|error| error.to_string())?;
    let fibres = rest.fibre_bytes().map_err(|error| error.to_string())?;
    let rest_root = output.join("native-rest");
    fs::create_dir(&rest_root).map_err(|error| error.to_string())?;
    let rest_directory = RestDirectory {
        schema: REST_SCHEMA.to_owned(),
        standing: component("standing.json", &standing),
        decoder: component("decoder.json", &decoder),
        fibres: component("fibres.json", &fibres),
    };
    write(rest_root.join("standing.json"), &standing)?;
    write(rest_root.join("decoder.json"), &decoder)?;
    write(rest_root.join("fibres.json"), &fibres)?;
    write_json(rest_root.join("manifest.json"), &rest_directory)?;
    let prior_manifest = fs::read(I4_MANIFEST).map_err(|error| error.to_string())?;
    let source_product = N2SourceProduct {
        schema: "holonics.n2.source-product.v1",
        truth_status: "established-bounded",
        reused_text_vision_receipt: component(I4_MANIFEST, &prior_manifest),
        prior_source_model_sha256: &prior.source_model_sha256,
        prior_responses: &prior.responses,
        audio: &audio,
    };
    write_json(output.join("00-source-conduct.json"), &source_product)?;

    let detached_root = output.join("detached-return");
    fs::create_dir(&detached_root).map_err(|error| error.to_string())?;
    run_detached(
        &env::current_exe().map_err(|error| error.to_string())?,
        &rest_root,
        &detached_root,
    )?;
    let detached: DetachedReturn = serde_json::from_slice(
        &fs::read(detached_root.join("return.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let dissection = N2Dissection {
        schema: "holonics.n2.dissection.v1",
        truth_status: "established-bounded",
        modality_entry_paths: rest
            .standing
            .ports
            .iter()
            .map(|port| {
                serde_json::json!({
                    "port": port.port,
                    "boundary": port.boundary,
                    "source_population": port.source_population,
                    "width": port.width,
                    "incidence": port.incidence,
                })
            })
            .collect(),
        shared_junction: &rest.standing.shared_generator,
        naturality_squares: &rest.fibres.naturality_squares,
        reconstruction_fibres: &rest.fibres.fibres,
        shared_and_local_withdrawals: &detached,
        open_exterior: &rest.standing.open_exterior,
    };
    write_json(output.join("01-dissection.json"), &dissection)?;
    let raw_audio = audio.returns.iter().all(|returning| {
        !returning.source.samples.is_empty()
            && !returning.source.frames.is_empty()
            && returning.source.occurrence != returning.source.locator
    });
    let audio_open = rest
        .standing
        .open_exterior
        .iter()
        .any(|opening| opening.contains("twelve-layer foreign audio tower"));
    let mut grade = N2Grade {
        schema: "holonics.n2.grade.v1",
        truth_status: "established-bounded",
        unchanged_text_and_vision_source_receipt_reused: prior_manifest.len() > 64,
        raw_waveforms_are_untranscribed_productive_occurrences: raw_audio,
        exact_pcm_frame_and_sample_incidence_returned: audio.returns.iter().all(|returning| {
            returning
                .source
                .frames
                .iter()
                .all(|frame| frame.sample_from < frame.sample_to)
                && returning.source.incidence_sha256.len() == 64
        }),
        inherited_audio_projection_enacted_on_resident_card: audio
            .apparatus
            .resident_chart
            .contains("NVIDIA")
            && audio.apparatus.exact_multiply_accumulates > 0
            && audio.apparatus.inherited_weight_octets > 0,
        three_separately_typed_ports_returned: rest.standing.ports.len() == 3,
        complete_port_fibres_and_naturality_returned: rest.fibres.fibres.len() == 12
            && rest.fibres.naturality_squares.len() == 6
            && detached.every_naturality_square_commutes,
        shared_and_every_local_withdrawal_returned: detached.shared_withdrawal_moves_every_port
            && detached.local_withdrawal_moves_only_its_port,
        source_detached_remount_returned: detached.forbidden_source_access.is_empty()
            && detached.apparatus.launches == 1
            && detached.apparatus.synchronizations == 1,
        foreign_audio_tower_interior_retained_as_open_fibre: audio_open,
        passed: false,
    };
    grade.passed = grade.unchanged_text_and_vision_source_receipt_reused
        && grade.raw_waveforms_are_untranscribed_productive_occurrences
        && grade.exact_pcm_frame_and_sample_incidence_returned
        && grade.inherited_audio_projection_enacted_on_resident_card
        && grade.three_separately_typed_ports_returned
        && grade.complete_port_fibres_and_naturality_returned
        && grade.shared_and_every_local_withdrawal_returned
        && grade.source_detached_remount_returned
        && grade.foreign_audio_tower_interior_retained_as_open_fibre;
    if !grade.passed {
        return Err("N2 refused its exact three-port grade".to_owned());
    }
    write_json(output.join("02-grade.json"), &grade)?;
    write_json(
        output.join("MANIFEST.json"),
        &serde_json::json!({
            "schema": "holonics.n2.product-manifest.v1",
            "truth_status": "established-bounded",
            "product": "receiver-exact text/vision/audio shared-generator ecology",
            "source_conduct": "00-source-conduct.json",
            "native_rest": "native-rest/manifest.json",
            "detached_return": "detached-return/return.json",
            "dissection": "01-dissection.json",
            "grade": "02-grade.json",
            "open_exterior": rest.standing.open_exterior,
        }),
    )?;
    println!("N2 returned: {}", output.display());
    Ok(())
}

fn detached(rest_root: &Path, output: &Path) -> Result<(), String> {
    let manifest: RestDirectory = serde_json::from_slice(
        &fs::read(rest_root.join("manifest.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    if manifest.schema != REST_SCHEMA {
        return Err("the detached N2 rest schema moved".to_owned());
    }
    let standing = read_component(rest_root, &manifest.standing)?;
    let decoder = read_component(rest_root, &manifest.decoder)?;
    let fibres = read_component(rest_root, &manifest.fibres)?;
    let rest = HeterogeneousFusionRest::read(&standing, &decoder, &fibres)
        .map_err(|error| error.to_string())?;
    if rest.standing.ports.len() != 3 {
        return Err("the detached N2 rest does not carry three ports".to_owned());
    }
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let started = Instant::now();
    let returned = card
        .conduct_heterogeneous_fusion_on_device(
            &rest.standing.successor_action,
            &rest.decoder_addresses(),
            &rest.starts(),
            rest.standing.family_count as usize,
            rest.standing.ports.len(),
        )
        .map_err(|error| error.to_string())?;
    let elapsed = started.elapsed().as_micros();
    let before = rest
        .decoder
        .consequences
        .iter()
        .filter(|consequence| consequence.state == 0)
        .map(|consequence| consequence.address)
        .collect::<Vec<_>>();
    let after = rest
        .decoder
        .consequences
        .iter()
        .filter(|consequence| consequence.state == 1)
        .map(|consequence| consequence.address)
        .collect::<Vec<_>>();
    if returned.predecessor_consequence != before
        || returned.successor_consequence != after
        || returned.shared_ablated_consequence != before
    {
        return Err("the detached N2 GPU consequence disagrees with its rest".to_owned());
    }
    let ports = rest.standing.ports.len();
    let local_exact = (0..ports).all(|withdrawn| {
        (0..before.len()).all(|cell| {
            returned.local_ablated_consequence[cell * ports + withdrawn]
                == if cell % ports == withdrawn {
                    before[cell]
                } else {
                    after[cell]
                }
        })
    });
    let mut modality_only_controls = BTreeMap::new();
    for (kept, port) in rest.standing.ports.iter().enumerate() {
        modality_only_controls.insert(
            format!("{:?}", port.port),
            (0..before.len())
                .map(|cell| {
                    if cell % ports == kept {
                        after[cell]
                    } else {
                        before[cell]
                    }
                })
                .collect(),
        );
    }
    let descriptors = open_descriptors();
    let forbidden = descriptors
        .iter()
        .filter(|path| {
            path.contains("/home/b/Workspaces/holonics")
                || path.contains("/home/b/models")
                || path.contains("model.safetensors")
                || path.contains("00-source-conduct")
                || path.ends_with(".wav")
        })
        .cloned()
        .collect::<Vec<_>>();
    let receipt = DetachedReturn {
        schema: "holonics.n2.detached-return.v1".to_owned(),
        component_sha256: [
            ("standing".to_owned(), manifest.standing.sha256),
            ("decoder".to_owned(), manifest.decoder.sha256),
            ("fibres".to_owned(), manifest.fibres.sha256),
        ]
        .into_iter()
        .collect(),
        predecessor_addresses: returned.predecessor_consequence,
        successor_addresses: returned.successor_consequence,
        shared_withdrawn_addresses: returned.shared_ablated_consequence,
        local_withdrawn_addresses: returned.local_ablated_consequence,
        modality_only_controls,
        every_naturality_square_commutes: rest
            .fibres
            .naturality_squares
            .iter()
            .all(|square| square.commutes),
        shared_withdrawal_moves_every_port: before.iter().zip(&after).all(|(a, b)| a != b),
        local_withdrawal_moves_only_its_port: local_exact,
        source_access_descriptors: descriptors,
        forbidden_source_access: forbidden,
        cpu_semantic_callbacks_between_fronts: 0,
        apparatus: DetachedApparatus {
            device: card.device_name().to_owned(),
            block_threads: returned.block_threads,
            active_lanes: returned.active_lanes,
            launches: returned.launches,
            synchronizations: returned.synchronizations,
            host_ingress_octets: returned.host_ingress_octets,
            host_egress_octets: returned.host_egress_octets,
            resident_octets: returned.resident_octets,
            physical_wall_microseconds: elapsed,
        },
    };
    if !receipt.every_naturality_square_commutes
        || !receipt.shared_withdrawal_moves_every_port
        || !receipt.local_withdrawal_moves_only_its_port
        || !receipt.forbidden_source_access.is_empty()
    {
        return Err("the detached N2 rest did not close its source/withdrawal grade".to_owned());
    }
    write_json(output.join("return.json"), &receipt)
}

fn synthesize_waveforms(root: &Path) -> Result<Vec<(u32, u32, PathBuf)>, String> {
    let fixtures = [
        (0, 0, "chi is negative"),
        (0, 1, "chi is positive"),
        (1, 0, "the parameter chi is less than zero"),
        (1, 1, "the parameter chi is greater than zero"),
    ];
    let mut occurrences = Vec::new();
    for (family, state, phrase) in fixtures {
        let raw = root.join(format!("family-{family}-state-{state}-source.wav"));
        let wave = root.join(format!("family-{family}-state-{state}.wav"));
        let status = Command::new("espeak-ng")
            .args(["-v", "en-us", "-w"])
            .arg(&raw)
            .arg(phrase)
            .status()
            .map_err(|error| error.to_string())?;
        if !status.success() {
            return Err(format!("espeak-ng returned {status}"));
        }
        let status = Command::new("ffmpeg")
            .args(["-y", "-loglevel", "error", "-i"])
            .arg(&raw)
            .args(["-ar", "16000", "-ac", "1", "-c:a", "pcm_s16le"])
            .arg(&wave)
            .status()
            .map_err(|error| error.to_string())?;
        if !status.success() || !wave.is_file() {
            return Err(format!("ffmpeg 16 kHz PCM crossing returned {status}"));
        }
        occurrences.push((family, state, wave));
    }
    Ok(occurrences)
}

fn args() -> Result<Args, String> {
    let mut args = env::args().skip(1);
    let Some(first) = args.next() else {
        return Ok(Args::Produce {
            model: PathBuf::from(DEFAULT_MODEL),
            output: PathBuf::from(DEFAULT_OUT),
        });
    };
    if first == "--detached" {
        let rest = args.next().ok_or("--detached requires a rest path")?;
        let output = args.next().ok_or("--detached requires an output path")?;
        if args.next().is_some() {
            return Err("unexpected N2 detached argument".to_owned());
        }
        return Ok(Args::Detached {
            rest: PathBuf::from(rest),
            output: PathBuf::from(output),
        });
    }
    let output = args
        .next()
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_OUT));
    if args.next().is_some() {
        return Err("usage: example [model] [output] | --detached REST OUTPUT".to_owned());
    }
    Ok(Args::Produce {
        model: PathBuf::from(first),
        output,
    })
}

fn run_detached(executable: &Path, rest: &Path, output: &Path) -> Result<(), String> {
    let executable = executable
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let rest = rest.canonicalize().map_err(|error| error.to_string())?;
    let output = output.canonicalize().map_err(|error| error.to_string())?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--ro-bind", "/sys", "/sys"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"]);
    for library in ["/lib", "/lib64", "/run"] {
        if Path::new(library).exists() {
            command.args(["--ro-bind", library, library]);
        }
    }
    let status = command
        .arg("--ro-bind")
        .arg(executable)
        .arg("/athena-n2")
        .arg("--ro-bind")
        .arg(rest)
        .arg("/rest")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args(["/athena-n2", "--detached", "/rest", "/return"])
        .status()
        .map_err(|error| error.to_string())?;
    if !status.success() {
        return Err(format!("source-detached N2 process returned {status}"));
    }
    Ok(())
}

fn open_descriptors() -> Vec<String> {
    let Ok(entries) = fs::read_dir("/proc/self/fd") else {
        return Vec::new();
    };
    let mut paths = entries
        .filter_map(Result::ok)
        .filter_map(|entry| fs::read_link(entry.path()).ok())
        .map(|path| path.display().to_string())
        .collect::<Vec<_>>();
    paths.sort();
    paths.dedup();
    paths
}

fn u32_field(value: &Value, path: &[&str]) -> Result<u32, String> {
    let mut at = value;
    for field in path {
        at = at
            .get(*field)
            .ok_or_else(|| format!("configuration field {} is absent", path.join(".")))?;
    }
    at.as_u64()
        .and_then(|value| u32::try_from(value).ok())
        .ok_or_else(|| format!("configuration field {} is not u32", path.join(".")))
}

fn component(path: impl Into<String>, bytes: &[u8]) -> ComponentIdentity {
    ComponentIdentity {
        path: path.into(),
        sha256: sha(bytes),
        octets: bytes.len() as u64,
    }
}

fn read_component(root: &Path, component: &ComponentIdentity) -> Result<Vec<u8>, String> {
    let bytes = fs::read(root.join(&component.path)).map_err(|error| error.to_string())?;
    if bytes.len() as u64 != component.octets || sha(&bytes) != component.sha256 {
        return Err(format!(
            "rest component {} changed identity",
            component.path
        ));
    }
    Ok(bytes)
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    write(path, &bytes)
}

fn write(path: PathBuf, bytes: &[u8]) -> Result<(), String> {
    use std::io::Write;
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)
        .map_err(|error| format!("{}: {error}", path.display()))?;
    file.write_all(bytes).map_err(|error| error.to_string())?;
    file.sync_all().map_err(|error| error.to_string())
}

fn sha(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
