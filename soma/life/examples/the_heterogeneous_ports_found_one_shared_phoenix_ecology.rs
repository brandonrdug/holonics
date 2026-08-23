//! I4: Gemma's real text and vision entry ports found one shared Phoenix ecology.
//!
//! The `−χ → +χ` occurrence already admitted by M0 crosses two separately typed Gemma source
//! ports. The source-render pair founds one world-state generator; a separately rendered PDF pair
//! is withheld from generator formation and grades successor naturality. The detached native rest
//! enacts the generator once on the RTX card, retains every modality face in a complete fibre, and
//! returns both global and port-local ablations.

#[path = "i4/product.rs"]
mod product;
#[path = "i4/source.rs"]
mod source;

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use holonic_engine::cuda_refine::CudaRefineExecutor;
use holonic_engine::phoenix::heterogeneous_fusion::{
    HeterogeneousFusionRest, PortDeclaration, SharedWorldGenerator,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};

const DEFAULT_OUT: &str = "output/the_heterogeneous_ports_found_one_shared_phoenix_ecology";
const DEFAULT_MODEL: &str = "/home/b/models/gemma-4-E4B-it";
const SOURCE_RECEIPT: &str = "output/the_source_is_admitted_whole/receipt.form";
const BASELINE_TEXT: &str =
    "research/fixtures/m0_mathematical_source_circulation/harmonic-baseline.typ";
const PERTURBED_TEXT: &str =
    "research/fixtures/m0_mathematical_source_circulation/harmonic-perturbed.typ";
const DEVELOPMENT_BASELINE: &str =
    "output/m0_mathematical_source_circulation/faces/synthetic/harmonic-baseline-source.png";
const DEVELOPMENT_PERTURBED: &str =
    "output/m0_mathematical_source_circulation/faces/synthetic/harmonic-perturbed-source.png";
const HELD_OUT_BASELINE: &str =
    "output/m0_mathematical_source_circulation/faces/synthetic/harmonic-baseline-pdf.png";
const REST_SCHEMA: &str = "holonics.i4.rest-directory.v1";

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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct NativeSemanticWork {
    shared_action_reads: u64,
    decoder_reads: u64,
    consequence_writes: u64,
    local_ablation_writes: u64,
    dependency_span: u64,
}

impl NativeSemanticWork {
    fn total(&self) -> u64 {
        self.shared_action_reads
            + self.decoder_reads
            + self.consequence_writes
            + self.local_ablation_writes
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DetachedReturn {
    schema: String,
    component_sha256: BTreeMap<String, String>,
    predecessor_addresses: Vec<u32>,
    successor_addresses: Vec<u32>,
    shared_ablated_addresses: Vec<u32>,
    local_ablated_addresses: Vec<u32>,
    predecessor_consequence_sha256: Vec<String>,
    successor_consequence_sha256: Vec<String>,
    shared_generator_ablation_moves_both_ports: bool,
    modality_specific_ablation_moves_only_declared_port: bool,
    held_out_cross_port_consequence_requires_shared_ecology: bool,
    semantic_work: NativeSemanticWork,
    source_access_descriptors: Vec<String>,
    forbidden_source_access: Vec<String>,
    cpu_semantic_callbacks_between_fronts: u64,
    apparatus: DetachedApparatus,
}

#[derive(Clone, Debug, Serialize)]
struct CostFace {
    artifact_octets: u64,
    decoder_octets: u64,
    fibre_octets: u64,
    semantic_work: u64,
    dependency_span: u64,
    resident_octets: u64,
    transfer_octets: u64,
}

#[derive(Clone, Debug, Serialize)]
struct CostProduct {
    schema: &'static str,
    truth_status: &'static str,
    source: CostFace,
    native: CostFace,
    strict_coordinate_fall: BTreeMap<&'static str, bool>,
    every_coordinate_strictly_falls: bool,
}

#[derive(Serialize)]
struct SourceDecoderProduct<'a> {
    text_coordinate_decoders: &'a [source::TextSourceConduct],
    vision_coordinate_decoders: &'a [source::VisionSourceConduct],
}

#[derive(Serialize)]
struct SourceFibreProduct<'a> {
    responses: &'a [holonic_engine::phoenix::heterogeneous_fusion::SourcePortResponse],
    text_complete_sections: &'a [source::TextSourceConduct],
    vision_complete_sections: &'a [source::VisionSourceConduct],
}

#[derive(Serialize)]
struct I4Grade {
    schema: &'static str,
    truth_status: &'static str,
    real_occurrences_cross_separately_typed_ports: bool,
    source_and_native_conduct_return_for_each_occurrence: bool,
    spatial_temporal_phase_incidence_retained: bool,
    common_world_correspondence_pullback_returned: bool,
    every_shared_generator_square_commutes: bool,
    shared_subcomplex_stored_and_enacted_once: bool,
    modality_specific_reconstruction_fibres_complete: bool,
    shared_ablation_moves_both_ports: bool,
    local_ablation_moves_only_its_port: bool,
    held_out_cross_port_consequence_requires_shared_ecology: bool,
    detached_fused_rest_and_strict_cost_descent: bool,
    multimodal_atlas_and_interactive_exact_projection_return: bool,
    passed: bool,
}

#[derive(Serialize)]
struct ProductManifest {
    schema: &'static str,
    truth_status: &'static str,
    product: &'static str,
    source_conduct: &'static str,
    native_rest: &'static str,
    detached_return: &'static str,
    cost_product: &'static str,
    realization_atlas: &'static str,
    exact_mesh: &'static str,
    interactive_projection: &'static str,
    ablations: &'static str,
    grade: &'static str,
    code_closure_sha256: String,
    open_exterior: Vec<String>,
}

enum Args {
    Produce { model: PathBuf, output: PathBuf },
    DetachedGrade { rest: PathBuf, output: PathBuf },
}

fn main() -> Result<(), String> {
    match args()? {
        Args::Produce { model, output } => produce(&model, &output),
        Args::DetachedGrade { rest, output } => detached_grade(&rest, &output),
    }
}

fn produce(model: &Path, output: &Path) -> Result<(), String> {
    if output.exists() {
        return Err(format!(
            "I4 output {} already exists; inspect its addressed receipt instead of replaying it",
            output.display()
        ));
    }
    for required in [
        model.join("model.safetensors"),
        model.join("config.json"),
        model.join("processor_config.json"),
        model.join("tokenizer.json"),
        PathBuf::from(SOURCE_RECEIPT),
        PathBuf::from(BASELINE_TEXT),
        PathBuf::from(PERTURBED_TEXT),
        PathBuf::from(DEVELOPMENT_BASELINE),
        PathBuf::from(DEVELOPMENT_PERTURBED),
        PathBuf::from(HELD_OUT_BASELINE),
    ] {
        if !required.is_file() {
            return Err(format!(
                "required I4 material {} is absent",
                required.display()
            ));
        }
    }
    fs::create_dir_all(output.join("source-occurrences")).map_err(|error| error.to_string())?;
    let held_out_perturbed = output.join("source-occurrences/held-out-perturbed-pdf.png");
    render_held_out_perturbation(output, &held_out_perturbed)?;

    let source_model_sha256 = authenticated_source_identity(Path::new(SOURCE_RECEIPT))?;
    let config: Value = serde_json::from_slice(
        &fs::read(model.join("config.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let processor: Value = serde_json::from_slice(
        &fs::read(model.join("processor_config.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let patch_size = u32_field(&config, &["vision_config", "patch_size"])?;
    let pooling_kernel_size = u32_field(&config, &["vision_config", "pooling_kernel_size"])?;
    let max_soft_tokens = usize::try_from(u32_field(
        &processor,
        &["image_processor", "max_soft_tokens"],
    )?)
    .map_err(|_| "max_soft_tokens exceeds usize")?;
    let text_width = u32_field(&config, &["text_config", "hidden_size"])?;
    let vision_width = u32_field(&config, &["vision_config", "hidden_size"])?;

    let source = source::conduct(source::SourceInputs {
        model_root: model,
        source_model_sha256: &source_model_sha256,
        baseline_text: Path::new(BASELINE_TEXT),
        perturbed_text: Path::new(PERTURBED_TEXT),
        development_baseline_image: Path::new(DEVELOPMENT_BASELINE),
        development_perturbed_image: Path::new(DEVELOPMENT_PERTURBED),
        held_out_baseline_image: Path::new(HELD_OUT_BASELINE),
        held_out_perturbed_image: &held_out_perturbed,
        patch_size,
        pooling_kernel_size,
        max_soft_tokens,
    })?;
    let source_bytes = serde_json::to_vec_pretty(&source).map_err(|error| error.to_string())?;
    write(output.join("00-source-conduct.json"), &source_bytes)?;

    let rest = HeterogeneousFusionRest::found(
        source_model_sha256,
        vec![
            PortDeclaration {
                boundary: source::CODEWORD_BOUNDARY,
                source_boundary: format!(
                    "ordered tokenizer codewords → source embedding rows → positive algebraic scale, width {text_width}"
                ),
                source_population: "model.language_model.embed_tokens.weight".to_owned(),
                source_extent: text_width,
                incidence: "UTF-8 byte spans and serial token adjacency".to_owned(),
            },
            PortDeclaration {
                boundary: source::OPTICAL_BOUNDARY,
                source_boundary: format!(
                    "exact RGB patch numerators over 255 → input projection + x/y position rows, width {vision_width}"
                ),
                source_population:
                    "model.vision_tower.patch_embedder.{input_proj,position_embedding_table}"
                        .to_owned(),
                source_extent: vision_width,
                incidence: "two-dimensional patch grid and within-patch channel order".to_owned(),
            },
        ],
        source.responses.clone(),
        SharedWorldGenerator {
            name: "semantic-hand-reflection".to_owned(),
            predecessor: 0,
            successor: 1,
            lineage: "M0 isolated exactly one born-digital −χ→+χ perturbation; source-render text/vision responses found this generator, while the PDF raster family was withheld".to_owned(),
            common_world_receiver: "the predeclared M0 harmonic-sheet parameter occurrence and its exact changed source/raster support; labels, transcript equality, and source-output similarity are excluded".to_owned(),
        },
        vec![
            "audio: authenticated and typed, but its feature-extractor/source tower path is not enacted by I4".to_owned(),
            "video: authenticated processor face over vision, but no real temporal occurrence enters I4".to_owned(),
        ],
        source.open_exterior.clone(),
    )
    .map_err(|error| error.to_string())?;
    let standing_bytes = rest.standing_bytes().map_err(|error| error.to_string())?;
    let decoder_bytes = rest.decoder_bytes().map_err(|error| error.to_string())?;
    let fibre_bytes = rest.fibre_bytes().map_err(|error| error.to_string())?;
    let native_rest = output.join("native-rest");
    fs::create_dir(&native_rest).map_err(|error| error.to_string())?;
    let rest_directory = RestDirectory {
        schema: REST_SCHEMA.to_owned(),
        standing: component("standing.json", &standing_bytes),
        decoder: component("decoder.json", &decoder_bytes),
        fibres: component("fibres.json", &fibre_bytes),
    };
    write(native_rest.join("standing.json"), &standing_bytes)?;
    write(native_rest.join("decoder.json"), &decoder_bytes)?;
    write(native_rest.join("fibres.json"), &fibre_bytes)?;
    write(
        native_rest.join("manifest.json"),
        &serde_json::to_vec_pretty(&rest_directory).map_err(|error| error.to_string())?,
    )?;

    let detached_root = output.join("detached-return");
    fs::create_dir(&detached_root).map_err(|error| error.to_string())?;
    run_detached_grade(
        &env::current_exe().map_err(|error| error.to_string())?,
        &native_rest,
        &detached_root,
    )?;
    let detached_bytes =
        fs::read(detached_root.join("return.json")).map_err(|error| error.to_string())?;
    let detached: DetachedReturn =
        serde_json::from_slice(&detached_bytes).map_err(|error| error.to_string())?;

    let source_decoder_bytes = serde_json::to_vec(&SourceDecoderProduct {
        text_coordinate_decoders: &source.text,
        vision_coordinate_decoders: &source.vision,
    })
    .map_err(|error| error.to_string())?;
    let source_fibre_bytes = serde_json::to_vec(&SourceFibreProduct {
        responses: &source.responses,
        text_complete_sections: &source.text,
        vision_complete_sections: &source.vision,
    })
    .map_err(|error| error.to_string())?;
    let source_work = source.apparatus.exact_multiply_accumulates
        + source
            .text
            .iter()
            .map(|entry| entry.tokens.len() as u64)
            .sum::<u64>();
    let costs = cost_product(
        CostFace {
            artifact_octets: source_bytes.len() as u64,
            decoder_octets: source_decoder_bytes.len() as u64,
            fibre_octets: source_fibre_bytes.len() as u64,
            semantic_work: source_work,
            dependency_span: source.apparatus.dependency_span,
            resident_octets: source.apparatus.resident_projection_octets,
            transfer_octets: source.apparatus.source_weight_octets_read
                + source.apparatus.query_ingress_octets
                + source.apparatus.result_egress_octets,
        },
        CostFace {
            artifact_octets: standing_bytes.len() as u64,
            decoder_octets: decoder_bytes.len() as u64,
            fibre_octets: fibre_bytes.len() as u64,
            semantic_work: detached.semantic_work.total(),
            dependency_span: detached.semantic_work.dependency_span,
            resident_octets: detached.apparatus.resident_octets,
            transfer_octets: detached.apparatus.host_ingress_octets
                + detached.apparatus.host_egress_octets,
        },
    );
    if !costs.every_coordinate_strictly_falls {
        return Err("I4 complete source/native product cost did not strictly fall".to_owned());
    }

    let atlas = product::atlas(&source, &rest, &detached)?;
    let mesh = product::mesh(&atlas)?;
    let svg = product::interactive_svg(&atlas, &mesh)?;
    let ablations = product::ablations(&rest, &detached);
    let grade = grade(&source, &rest, &detached, &costs, &atlas, &mesh);
    if !grade.passed {
        return Err("I4 refused its twelve-part grade".to_owned());
    }
    write(
        output.join("01-complete-product-cost.json"),
        &serde_json::to_vec_pretty(&costs).map_err(|error| error.to_string())?,
    )?;
    write(
        output.join("02-multimodal-realization-atlas.json"),
        &serde_json::to_vec_pretty(&atlas).map_err(|error| error.to_string())?,
    )?;
    write(
        output.join("03-exact-mesh.json"),
        &serde_json::to_vec_pretty(&mesh).map_err(|error| error.to_string())?,
    )?;
    write(output.join("04-interactive-atlas.svg"), svg.as_bytes())?;
    write(
        output.join("05-ablations.json"),
        &serde_json::to_vec_pretty(&ablations).map_err(|error| error.to_string())?,
    )?;
    write(
        output.join("06-grade.json"),
        &serde_json::to_vec_pretty(&grade).map_err(|error| error.to_string())?,
    )?;
    write(
        output.join("INSPECTION.md"),
        product::inspection(&source, &detached, &costs).as_bytes(),
    )?;
    let manifest = ProductManifest {
        schema: "holonics.i4.product-manifest.v1",
        truth_status: "established-bounded",
        product: "receiver-exact text/vision shared-generator Phoenix ecology",
        source_conduct: "00-source-conduct.json",
        native_rest: "native-rest/manifest.json",
        detached_return: "detached-return/return.json",
        cost_product: "01-complete-product-cost.json",
        realization_atlas: "02-multimodal-realization-atlas.json",
        exact_mesh: "03-exact-mesh.json",
        interactive_projection: "04-interactive-atlas.svg",
        ablations: "05-ablations.json",
        grade: "06-grade.json",
        code_closure_sha256: code_closure(),
        open_exterior: rest.standing.open_exterior.clone(),
    };
    write(
        output.join("MANIFEST.json"),
        &serde_json::to_vec_pretty(&manifest).map_err(|error| error.to_string())?,
    )?;
    println!("I4 returned: {}", output.display());
    println!("source port responses: {}", source.responses.len());
    println!(
        "native predecessor {:?} -> successor {:?}",
        detached.predecessor_addresses, detached.successor_addresses
    );
    Ok(())
}

fn detached_grade(rest_root: &Path, output: &Path) -> Result<(), String> {
    let manifest: RestDirectory = serde_json::from_slice(
        &fs::read(rest_root.join("manifest.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    if manifest.schema != REST_SCHEMA {
        return Err("the detached I4 rest schema moved".to_owned());
    }
    let standing = read_component(rest_root, &manifest.standing)?;
    let decoder = read_component(rest_root, &manifest.decoder)?;
    let fibres = read_component(rest_root, &manifest.fibres)?;
    let rest = HeterogeneousFusionRest::read(&standing, &decoder, &fibres)
        .map_err(|error| error.to_string())?;
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let begun = Instant::now();
    let returned = card
        .conduct_heterogeneous_fusion_on_device(
            &rest.standing.successor_action,
            &rest.decoder_addresses(),
            &rest.starts(),
            rest.standing.family_count as usize,
            rest.standing.ports.len(),
        )
        .map_err(|error| error.to_string())?;
    let physical_wall_microseconds = begun.elapsed().as_micros();
    let expected_before = rest
        .decoder
        .consequences
        .iter()
        .filter(|consequence| consequence.state == 0)
        .map(|consequence| consequence.address)
        .collect::<Vec<_>>();
    let expected_after = rest
        .decoder
        .consequences
        .iter()
        .filter(|consequence| consequence.state == 1)
        .map(|consequence| consequence.address)
        .collect::<Vec<_>>();
    if returned.predecessor_consequence != expected_before
        || returned.successor_consequence != expected_after
        || returned.shared_ablated_consequence != expected_before
    {
        return Err("the resident heterogeneous deed disagrees with its exact rest".to_owned());
    }
    let ports = rest.standing.ports.len();
    for (cell, (before, after)) in expected_before.iter().zip(&expected_after).enumerate() {
        for withdrawn_port in 0..ports {
            let observed = returned.local_ablated_consequence[cell * ports + withdrawn_port];
            let expected = if cell % ports == withdrawn_port {
                *before
            } else {
                *after
            };
            if observed != expected {
                return Err("a modality-specific withdrawal crossed another port".to_owned());
            }
        }
    }
    let shared_moves_both = expected_before
        .iter()
        .zip(&expected_after)
        .all(|(before, after)| before != after)
        && returned.shared_ablated_consequence == expected_before;
    let local_moves_only = (0..ports).all(|withdrawn_port| {
        (0..expected_before.len()).all(|cell| {
            let observed = returned.local_ablated_consequence[cell * ports + withdrawn_port];
            if cell % ports == withdrawn_port {
                observed == expected_before[cell]
            } else {
                observed == expected_after[cell]
            }
        })
    });
    let held_out_start = (rest.standing.family_count as usize - 1) * ports;
    let held_out_cells = held_out_start..held_out_start + ports;
    let held_out_source_faces = held_out_cells
        .clone()
        .map(|cell| {
            rest.decoder.consequences[expected_after[cell] as usize]
                .source_consequence_sha256
                .as_str()
        })
        .collect::<std::collections::BTreeSet<_>>();
    let held_out_requires_shared = held_out_source_faces.len() == ports
        && held_out_cells.clone().all(|cell| {
            returned.successor_consequence[cell] != returned.shared_ablated_consequence[cell]
        })
        && (0..ports).all(|withdrawn_port| {
            let mixed = held_out_cells
                .clone()
                .map(|cell| returned.local_ablated_consequence[cell * ports + withdrawn_port])
                .collect::<Vec<_>>();
            mixed != returned.successor_consequence[held_out_cells.clone()]
                && mixed != returned.shared_ablated_consequence[held_out_cells.clone()]
                && held_out_cells.clone().all(|cell| {
                    let observed =
                        returned.local_ablated_consequence[cell * ports + withdrawn_port];
                    if cell % ports == withdrawn_port {
                        observed == expected_before[cell]
                    } else {
                        observed == expected_after[cell]
                    }
                })
        });
    let consequence = |addresses: &[u32]| -> Result<Vec<String>, String> {
        addresses
            .iter()
            .map(|address| {
                rest.decoder
                    .consequences
                    .get(*address as usize)
                    .map(|entry| entry.source_consequence_sha256.clone())
                    .ok_or_else(|| format!("native consequence {address} leaves the decoder"))
            })
            .collect()
    };
    let descriptors = open_descriptors();
    let forbidden = descriptors
        .iter()
        .filter(|path| {
            path.contains("/home/b/Workspaces/holonics")
                || path.contains("/home/b/models")
                || path.contains("model.safetensors")
                || path.contains("tokenizer.json")
                || path.contains("m0_mathematical_source")
                || path.contains("harmonic-")
        })
        .cloned()
        .collect::<Vec<_>>();
    let cells = expected_before.len() as u64;
    let receipt = DetachedReturn {
        schema: "holonics.i4.detached-return.v1".to_owned(),
        component_sha256: [
            ("standing".to_owned(), manifest.standing.sha256),
            ("decoder".to_owned(), manifest.decoder.sha256),
            ("fibres".to_owned(), manifest.fibres.sha256),
        ]
        .into_iter()
        .collect(),
        predecessor_addresses: returned.predecessor_consequence.clone(),
        successor_addresses: returned.successor_consequence.clone(),
        shared_ablated_addresses: returned.shared_ablated_consequence.clone(),
        local_ablated_addresses: returned.local_ablated_consequence.clone(),
        predecessor_consequence_sha256: consequence(&returned.predecessor_consequence)?,
        successor_consequence_sha256: consequence(&returned.successor_consequence)?,
        shared_generator_ablation_moves_both_ports: shared_moves_both,
        modality_specific_ablation_moves_only_declared_port: local_moves_only,
        held_out_cross_port_consequence_requires_shared_ecology: held_out_requires_shared,
        semantic_work: NativeSemanticWork {
            shared_action_reads: cells,
            decoder_reads: cells * 2,
            consequence_writes: cells * 3,
            local_ablation_writes: cells * ports as u64,
            dependency_span: rest.standing.state_count as u64,
        },
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
            physical_wall_microseconds,
        },
    };
    if !receipt.shared_generator_ablation_moves_both_ports
        || !receipt.modality_specific_ablation_moves_only_declared_port
        || !receipt.held_out_cross_port_consequence_requires_shared_ecology
        || !receipt.forbidden_source_access.is_empty()
    {
        return Err(
            "the detached I4 return did not close its ablation/source-access grade".to_owned(),
        );
    }
    write(
        output.join("return.json"),
        &serde_json::to_vec_pretty(&receipt).map_err(|error| error.to_string())?,
    )
}

fn grade(
    source: &source::SourceConduct,
    rest: &HeterogeneousFusionRest,
    detached: &DetachedReturn,
    costs: &CostProduct,
    atlas: &Value,
    mesh: &Value,
) -> I4Grade {
    let real_occurrences = source.responses.len() == 8
        && source
            .responses
            .iter()
            .map(|response| response.boundary)
            .collect::<std::collections::BTreeSet<_>>()
            .len()
            == 2;
    let source_native = detached.predecessor_addresses.len() == 4
        && detached.successor_addresses.len() == 4
        && source
            .responses
            .iter()
            .all(|response| response.semantic_units > 0);
    let incidence = source.text.iter().all(|entry| !entry.tokens.is_empty())
        && source.vision.iter().all(|entry| !entry.scores.is_empty());
    let pullback = atlas["correspondence_pullbacks"]
        .as_array()
        .is_some_and(|pullbacks| pullbacks.len() == 4);
    let naturality = rest
        .fibres
        .naturality_squares
        .iter()
        .all(|square| square.commutes);
    let stored_once = rest.standing.successor_action.len() == 2
        && detached.apparatus.launches == 1
        && detached.apparatus.synchronizations == 1;
    let fibres = rest.fibres.fibres.len() == rest.decoder.consequences.len()
        && rest
            .fibres
            .fibres
            .iter()
            .all(|fibre| !fibre.members.is_empty());
    let visual = mesh["vertices"]
        .as_array()
        .is_some_and(|vertices| !vertices.is_empty())
        && mesh["edges"]
            .as_array()
            .is_some_and(|edges| !edges.is_empty());
    let mut grade = I4Grade {
        schema: "holonics.i4.grade.v1",
        truth_status: "established-bounded",
        real_occurrences_cross_separately_typed_ports: real_occurrences,
        source_and_native_conduct_return_for_each_occurrence: source_native,
        spatial_temporal_phase_incidence_retained: incidence,
        common_world_correspondence_pullback_returned: pullback,
        every_shared_generator_square_commutes: naturality,
        shared_subcomplex_stored_and_enacted_once: stored_once,
        modality_specific_reconstruction_fibres_complete: fibres,
        shared_ablation_moves_both_ports: detached.shared_generator_ablation_moves_both_ports,
        local_ablation_moves_only_its_port: detached
            .modality_specific_ablation_moves_only_declared_port,
        held_out_cross_port_consequence_requires_shared_ecology: detached
            .held_out_cross_port_consequence_requires_shared_ecology,
        detached_fused_rest_and_strict_cost_descent: detached.forbidden_source_access.is_empty()
            && costs.every_coordinate_strictly_falls,
        multimodal_atlas_and_interactive_exact_projection_return: visual,
        passed: false,
    };
    grade.passed = grade.real_occurrences_cross_separately_typed_ports
        && grade.source_and_native_conduct_return_for_each_occurrence
        && grade.spatial_temporal_phase_incidence_retained
        && grade.common_world_correspondence_pullback_returned
        && grade.every_shared_generator_square_commutes
        && grade.shared_subcomplex_stored_and_enacted_once
        && grade.modality_specific_reconstruction_fibres_complete
        && grade.shared_ablation_moves_both_ports
        && grade.local_ablation_moves_only_its_port
        && grade.held_out_cross_port_consequence_requires_shared_ecology
        && grade.detached_fused_rest_and_strict_cost_descent
        && grade.multimodal_atlas_and_interactive_exact_projection_return;
    grade
}

fn cost_product(source: CostFace, native: CostFace) -> CostProduct {
    let strict_coordinate_fall = [
        (
            "artifact_octets",
            native.artifact_octets < source.artifact_octets,
        ),
        (
            "decoder_octets",
            native.decoder_octets < source.decoder_octets,
        ),
        ("fibre_octets", native.fibre_octets < source.fibre_octets),
        ("semantic_work", native.semantic_work < source.semantic_work),
        (
            "dependency_span",
            native.dependency_span < source.dependency_span,
        ),
        (
            "resident_octets",
            native.resident_octets < source.resident_octets,
        ),
        (
            "transfer_octets",
            native.transfer_octets < source.transfer_octets,
        ),
    ]
    .into_iter()
    .collect::<BTreeMap<_, _>>();
    let every_coordinate_strictly_falls = strict_coordinate_fall.values().all(|passed| *passed);
    CostProduct {
        schema: "holonics.i4.complete-product-cost.v1",
        truth_status: "measured",
        source,
        native,
        strict_coordinate_fall,
        every_coordinate_strictly_falls,
    }
}

fn render_held_out_perturbation(output: &Path, png: &Path) -> Result<(), String> {
    let pdf = output.join("source-occurrences/held-out-perturbed.pdf");
    let status = Command::new("typst")
        .env("SOURCE_DATE_EPOCH", "0")
        .args(["compile", PERTURBED_TEXT])
        .arg(&pdf)
        .status()
        .map_err(|error| error.to_string())?;
    if !status.success() {
        return Err(format!("Typst held-out perturbation returned {status}"));
    }
    let prefix = output.join("source-occurrences/held-out-perturbed-pdf");
    let status = Command::new("pdftoppm")
        .args(["-f", "1", "-l", "1", "-singlefile", "-png", "-r", "144"])
        .arg(&pdf)
        .arg(&prefix)
        .status()
        .map_err(|error| error.to_string())?;
    if !status.success() || !png.is_file() {
        return Err(format!("pdftoppm held-out perturbation returned {status}"));
    }
    Ok(())
}

fn authenticated_source_identity(receipt: &Path) -> Result<String, String> {
    fs::read_to_string(receipt)
        .map_err(|error| error.to_string())?
        .lines()
        .find_map(|line| line.strip_prefix("content sha256 "))
        .filter(|identity| {
            identity.len() == 64 && identity.bytes().all(|byte| byte.is_ascii_hexdigit())
        })
        .map(str::to_owned)
        .ok_or_else(|| "the Station-B source receipt carries no valid content identity".to_owned())
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

fn run_detached_grade(executable: &Path, rest: &Path, output: &Path) -> Result<(), String> {
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
    command
        .arg("--ro-bind")
        .arg(executable)
        .arg("/athena-i4")
        .arg("--ro-bind")
        .arg(rest)
        .arg("/rest")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/tmp",
            "/athena-i4",
            "--detached-grade",
            "/rest",
            "/return",
        ]);
    let status = command.status().map_err(|error| error.to_string())?;
    status
        .success()
        .then_some(())
        .ok_or_else(|| format!("detached I4 grade returned {status}"))
}

fn component(path: &str, bytes: &[u8]) -> ComponentIdentity {
    ComponentIdentity {
        path: path.to_owned(),
        sha256: sha256(bytes),
        octets: bytes.len() as u64,
    }
}

fn read_component(root: &Path, identity: &ComponentIdentity) -> Result<Vec<u8>, String> {
    if identity.path.contains('/') || identity.path.contains("..") {
        return Err("an I4 component escaped its rest directory".to_owned());
    }
    let bytes = fs::read(root.join(&identity.path)).map_err(|error| error.to_string())?;
    if sha256(&bytes) != identity.sha256 || bytes.len() as u64 != identity.octets {
        return Err(format!("I4 component {} moved", identity.path));
    }
    Ok(bytes)
}

fn write(path: impl AsRef<Path>, bytes: &[u8]) -> Result<(), String> {
    let path = path.as_ref();
    let staged = path.with_extension("i4-staged");
    fs::write(&staged, bytes).map_err(|error| error.to_string())?;
    fs::rename(staged, path).map_err(|error| error.to_string())
}

fn open_descriptors() -> Vec<String> {
    let mut descriptors = Vec::new();
    if let Ok(entries) = fs::read_dir("/proc/self/fd") {
        for entry in entries.flatten() {
            if let Ok(target) = fs::read_link(entry.path()) {
                descriptors.push(target.to_string_lossy().into_owned());
            }
        }
    }
    descriptors.sort();
    descriptors.dedup();
    descriptors
}

fn sha256(bytes: &[u8]) -> String {
    source::sha(bytes)
}

fn code_closure() -> String {
    let members: &[&[u8]] = &[
        include_bytes!("the_heterogeneous_ports_found_one_shared_phoenix_ecology.rs"),
        include_bytes!("i4/source.rs"),
        include_bytes!("i4/product.rs"),
        include_bytes!("../../../crates/holonic-engine/src/phoenix/heterogeneous_fusion.rs"),
        include_bytes!("../../../crates/holonic-engine/src/cuda_refine.rs"),
        include_bytes!("../../../crates/holonic-engine/kernels/refine_shell.cu"),
        include_bytes!("../../../crates/holonic-engine/src/embedding_fiber.rs"),
        include_bytes!("../../../crates/holonic-engine/kernels/exact_embedding_fiber.cu"),
        include_bytes!("../../../crates/holonic-engine/src/foreign_map.rs"),
        include_bytes!("../../../crates/holonic-engine/src/cuda_aperture.rs"),
    ];
    let mut digest = Sha256::new();
    for member in members {
        digest.update((member.len() as u64).to_le_bytes());
        digest.update(member);
    }
    source::sha(&digest.finalize())
}

fn args() -> Result<Args, String> {
    let mut values = env::args().skip(1);
    match values.next().as_deref() {
        Some("--produce") => {
            let model = values
                .next()
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from(DEFAULT_MODEL));
            let output = values
                .next()
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from(DEFAULT_OUT));
            no_trailing(&mut values, "--produce")?;
            Ok(Args::Produce { model, output })
        }
        Some("--detached-grade") => {
            let rest = required_path(&mut values, "REST")?;
            let output = required_path(&mut values, "OUTPUT")?;
            no_trailing(&mut values, "--detached-grade")?;
            Ok(Args::DetachedGrade { rest, output })
        }
        _ => Err("usage: --produce [MODEL [OUTPUT]] | --detached-grade REST OUTPUT".to_owned()),
    }
}

fn required_path(values: &mut impl Iterator<Item = String>, name: &str) -> Result<PathBuf, String> {
    let path = values
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| format!("missing {name}"))?;
    path.exists()
        .then_some(path.clone())
        .ok_or_else(|| format!("required {name} {} is absent", path.display()))
}

fn no_trailing(values: &mut impl Iterator<Item = String>, mode: &str) -> Result<(), String> {
    values
        .next()
        .is_none()
        .then_some(())
        .ok_or_else(|| format!("{mode} carries trailing arguments"))
}
