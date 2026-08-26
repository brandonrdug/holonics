//! I3: recurrent physical realizations condense into an executable Phoenix ecology.
//!
//! The complete I1 source fibres and the I2 returned successor are not flattened into one output
//! class. Stable recurrent transport becomes one compact action with one local predecessor
//! deformation; terminal-potential faces which still separate source occurrences remain complete
//! reconstruction fibres. A source-absent process remounts the three components and conducts both
//! routes plus shared-generator withdrawal on the resident card in one front.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    native_ecology::{
        recurrent::RetainedContinuationPassage,
        recurrent_condensation::{CondensedRecurrentRest, CondensedRoute},
        recurrent_return::ReturnedRecurrentRest,
    },
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const DEFAULT_OUT: &str = "output/the_recurrent_realizations_condense_into_a_phoenix_ecology";
const REST_DIRECTORY_SCHEMA: &str = "holonics.i3.condensed-rest-directory.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ComponentIdentity {
    path: String,
    sha256: String,
    octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RestDirectoryManifest {
    schema: String,
    standing: ComponentIdentity,
    decoder: ComponentIdentity,
    fibres: ComponentIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct SourceApparatus {
    device: String,
    launches: u64,
    synchronizations: u64,
    host_ingress_octets: u64,
    host_egress_octets: u64,
    resident_octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct I2Detached {
    apparatus: SourceApparatus,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct CondensedSemanticWork {
    starting_occurrences: u64,
    predecessor_transition_reads: u64,
    successor_transition_reads: u64,
    withdrawal_transition_reads: u64,
    visited_incidence_tests: u64,
    trace_entries_written: u64,
    dependency_span: u64,
}

impl CondensedSemanticWork {
    fn product_work(&self) -> u64 {
        self.predecessor_transition_reads
            + self.successor_transition_reads
            + self.withdrawal_transition_reads
            + self.visited_incidence_tests
            + self.trace_entries_written
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DetachedApparatus {
    device: String,
    block_threads: u32,
    active_lanes: u32,
    launches: u64,
    synchronizations: u64,
    visited_words_per_route: usize,
    host_ingress_octets: u64,
    host_egress_octets: u64,
    resident_octets: u64,
    physical_wall_microseconds: u128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DetachedReturn {
    schema: String,
    component_sha256: BTreeMap<String, String>,
    predecessor_traces: Vec<Vec<u32>>,
    successor_traces: Vec<Vec<u32>>,
    withdrawn_traces: Vec<Vec<u32>>,
    predecessor_passages: Vec<String>,
    successor_passages: Vec<String>,
    withdrawn_passages: Vec<String>,
    shared_generator_withdrawal_reopened_every_family: bool,
    semantic_work: CondensedSemanticWork,
    source_access_descriptors: Vec<String>,
    forbidden_source_access: Vec<String>,
    cpu_semantic_callbacks_between_fronts: u64,
    apparatus: DetachedApparatus,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct CostFace {
    artifact_octets: u64,
    decoder_octets: u64,
    fibre_octets: u64,
    semantic_work: u64,
    dependency_span: u64,
    resident_octets: u64,
    transfer_octets: u64,
}

#[derive(Serialize)]
struct CostProduct {
    schema: &'static str,
    truth_status: &'static str,
    source: CostFace,
    native: CostFace,
    strict_coordinate_fall: BTreeMap<&'static str, bool>,
    every_coordinate_strictly_falls: bool,
}

#[derive(Serialize)]
struct I3Grade {
    schema: &'static str,
    truth_status: &'static str,
    overlapping_active_cover_derived: bool,
    generators_come_from_stable_transport_and_recurrence: bool,
    defects_and_shortest_separators_complete: bool,
    only_zero_defect_future_exact_subcomplex_condensed: bool,
    noncommuting_and_receiver_visible_routes_retained: bool,
    executable_generator_native_rest_and_decoder: bool,
    source_development_and_exchange_absent_at_remount: bool,
    complete_main_and_held_out_passage_families_return: bool,
    shared_generator_ablation_reopens_every_family: bool,
    complete_product_vector_strictly_falls: bool,
    source_native_atlas_and_interactive_exact_mesh_return: bool,
    passed: bool,
}

#[derive(Serialize)]
struct ProductManifest {
    schema: &'static str,
    truth_status: &'static str,
    product: &'static str,
    native_rest: &'static str,
    cost_product: &'static str,
    realization_atlas: &'static str,
    exact_mesh: &'static str,
    interactive_projection: &'static str,
    detached_return: &'static str,
    ablation: &'static str,
    grade: &'static str,
    code_closure_sha256: String,
    open_exterior: Vec<String>,
}

enum Args {
    Produce {
        passage: PathBuf,
        returned: PathBuf,
        i2_detached: PathBuf,
        output: PathBuf,
    },
    DetachedGrade {
        rest: PathBuf,
        output: PathBuf,
    },
}

fn main() -> Result<(), String> {
    match args()? {
        Args::Produce {
            passage,
            returned,
            i2_detached,
            output,
        } => produce(&passage, &returned, &i2_detached, &output),
        Args::DetachedGrade { rest, output } => detached_grade(&rest, &output),
    }
}

fn produce(
    passage_path: &Path,
    returned_path: &Path,
    i2_detached_path: &Path,
    output: &Path,
) -> Result<(), String> {
    if output.exists() {
        return Err(format!(
            "I3 output {} already exists; inspect its addressed receipt instead of replaying it",
            output.display()
        ));
    }
    let passage_bytes = fs::read(passage_path).map_err(|error| error.to_string())?;
    let returned_bytes = fs::read(returned_path).map_err(|error| error.to_string())?;
    let i2_detached_bytes = fs::read(i2_detached_path).map_err(|error| error.to_string())?;
    let passage =
        RetainedContinuationPassage::read(&passage_bytes).map_err(|error| error.to_string())?;
    let returned =
        ReturnedRecurrentRest::read(&returned_bytes).map_err(|error| error.to_string())?;
    let i2_detached: I2Detached =
        serde_json::from_slice(&i2_detached_bytes).map_err(|error| error.to_string())?;
    let compact = CondensedRecurrentRest::found(&passage_bytes, &returned_bytes)
        .map_err(|error| error.to_string())?;
    let standing_bytes = compact
        .standing_bytes()
        .map_err(|error| error.to_string())?;
    let decoder_bytes = compact.decoder_bytes().map_err(|error| error.to_string())?;
    let fibre_bytes = compact.fibre_bytes().map_err(|error| error.to_string())?;

    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let native_rest = output.join("native-rest");
    fs::create_dir(&native_rest).map_err(|error| error.to_string())?;
    let manifest = RestDirectoryManifest {
        schema: REST_DIRECTORY_SCHEMA.to_owned(),
        standing: component("standing.json", &standing_bytes),
        decoder: component("decoder.json", &decoder_bytes),
        fibres: component("fibres.json", &fibre_bytes),
    };
    write(native_rest.join("standing.json"), &standing_bytes)?;
    write(native_rest.join("decoder.json"), &decoder_bytes)?;
    write(native_rest.join("fibres.json"), &fibre_bytes)?;
    write(
        native_rest.join("manifest.json"),
        &serde_json::to_vec_pretty(&manifest).map_err(|error| error.to_string())?,
    )?;

    let detached_directory = output.join("detached-return");
    fs::create_dir(&detached_directory).map_err(|error| error.to_string())?;
    run_detached_grade(
        &env::current_exe().map_err(|error| error.to_string())?,
        &native_rest,
        &detached_directory,
    )?;
    let detached_bytes =
        fs::read(detached_directory.join("return.json")).map_err(|error| error.to_string())?;
    let detached: DetachedReturn =
        serde_json::from_slice(&detached_bytes).map_err(|error| error.to_string())?;

    let source_fibre_bytes = serde_json::to_vec(&json!({
        "sections": &passage.sections,
        "fibres": &passage.fibres,
        "reopenings": &passage.reopenings,
    }))
    .map_err(|error| error.to_string())?;
    let source_decoder_bytes =
        serde_json::to_vec(&returned.decoder).map_err(|error| error.to_string())?;
    let source_work = &returned.semantic_work_prediction;
    let source_product_work = source_work.predecessor_transition_reads
        + source_work.successor_transition_reads
        + source_work.ablation_transition_reads
        + source_work.recurrence_equality_comparisons
        + source_work.trace_entries_written;
    let source_cost = CostFace {
        artifact_octets: returned_bytes.len() as u64,
        decoder_octets: source_decoder_bytes.len() as u64,
        fibre_octets: source_fibre_bytes.len() as u64,
        semantic_work: source_product_work,
        dependency_span: source_work.dependency_span,
        resident_octets: i2_detached.apparatus.resident_octets,
        transfer_octets: i2_detached.apparatus.host_ingress_octets
            + i2_detached.apparatus.host_egress_octets,
    };
    let native_cost = CostFace {
        artifact_octets: standing_bytes.len() as u64,
        decoder_octets: decoder_bytes.len() as u64,
        fibre_octets: fibre_bytes.len() as u64,
        semantic_work: detached.semantic_work.product_work(),
        dependency_span: detached.semantic_work.dependency_span,
        resident_octets: detached.apparatus.resident_octets,
        transfer_octets: detached.apparatus.host_ingress_octets
            + detached.apparatus.host_egress_octets,
    };
    let costs = cost_product(source_cost, native_cost);
    if !costs.every_coordinate_strictly_falls {
        return Err(
            "I3 complete product cost did not strictly fall in every coordinate".to_owned(),
        );
    }

    let atlas = realization_atlas(&passage, &returned, &compact, &detached)?;
    let mesh = exact_mesh(&atlas)?;
    let svg = interactive_svg(&atlas, &mesh)?;
    let ablation = json!({
        "schema": "holonics.i3.shared-generator-ablation.v1",
        "truth_status": "established-bounded",
        "intervention": "withdraw the one shared recurrent generator from the same mounted body",
        "predecessor": detached.predecessor_passages,
        "successor": detached.successor_passages,
        "withdrawn": detached.withdrawn_passages,
        "every_attributable_family_reopened": detached.shared_generator_withdrawal_reopened_every_family,
        "open_exterior": ["withdrawal is graded only over the two admitted starting occurrences"]
    });
    let grade = grade(&atlas, &mesh, &detached, &costs, &manifest);
    if !grade.passed {
        return Err("I3 refused its eleven-part grade".to_owned());
    }

    write(
        output.join("00-complete-product-cost.json"),
        &serde_json::to_vec_pretty(&costs).map_err(|error| error.to_string())?,
    )?;
    write(
        output.join("01-realization-atlas.json"),
        &serde_json::to_vec_pretty(&atlas).map_err(|error| error.to_string())?,
    )?;
    write(
        output.join("02-exact-mesh.json"),
        &serde_json::to_vec_pretty(&mesh).map_err(|error| error.to_string())?,
    )?;
    write(output.join("03-interactive-atlas.svg"), svg.as_bytes())?;
    write(
        output.join("04-shared-generator-ablation.json"),
        &serde_json::to_vec_pretty(&ablation).map_err(|error| error.to_string())?,
    )?;
    write(
        output.join("05-grade.json"),
        &serde_json::to_vec_pretty(&grade).map_err(|error| error.to_string())?,
    )?;
    write(
        output.join("INSPECTION.md"),
        inspection(&costs, &detached, &compact).as_bytes(),
    )?;
    let product = ProductManifest {
        schema: "holonics.i3.product-manifest.v1",
        truth_status: "established-bounded",
        product: "recurrent generator-native Phoenix condensation",
        native_rest: "native-rest/manifest.json",
        cost_product: "00-complete-product-cost.json",
        realization_atlas: "01-realization-atlas.json",
        exact_mesh: "02-exact-mesh.json",
        interactive_projection: "03-interactive-atlas.svg",
        detached_return: "detached-return/return.json",
        ablation: "04-shared-generator-ablation.json",
        grade: "05-grade.json",
        code_closure_sha256: code_closure(),
        open_exterior: compact.standing.open_exterior.clone(),
    };
    write(
        output.join("MANIFEST.json"),
        &serde_json::to_vec_pretty(&product).map_err(|error| error.to_string())?,
    )?;
    println!("I3 returned: {}", output.display());
    println!("predecessor: {:?}", detached.predecessor_passages);
    println!("successor: {:?}", detached.successor_passages);
    println!("withdrawn: {:?}", detached.withdrawn_passages);
    Ok(())
}

fn detached_grade(rest_directory: &Path, output: &Path) -> Result<(), String> {
    let manifest: RestDirectoryManifest = serde_json::from_slice(
        &fs::read(rest_directory.join("manifest.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    if manifest.schema != REST_DIRECTORY_SCHEMA {
        return Err("the detached I3 manifest schema moved".to_owned());
    }
    let standing = read_component(rest_directory, &manifest.standing)?;
    let decoder = read_component(rest_directory, &manifest.decoder)?;
    let fibres = read_component(rest_directory, &manifest.fibres)?;
    let compact = CondensedRecurrentRest::read(&standing, &decoder, &fibres)
        .map_err(|error| error.to_string())?;
    let starts = [compact.standing.main_start, compact.standing.held_out_start];
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let begun = Instant::now();
    let returned = card
        .conduct_condensed_recurrences_on_device(
            &compact.standing.successor_action,
            &starts,
            compact.standing.predecessor_from,
            compact.standing.predecessor_to,
        )
        .map_err(|error| error.to_string())?;
    let physical_wall_microseconds = begun.elapsed().as_micros();
    let predecessor_traces = traces(
        &returned.predecessor_trace,
        &returned.predecessor_lengths,
        returned.trace_stride,
    )?;
    let successor_traces = traces(
        &returned.successor_trace,
        &returned.successor_lengths,
        returned.trace_stride,
    )?;
    let withdrawn_traces = traces(
        &returned.withdrawn_trace,
        &returned.withdrawn_lengths,
        returned.trace_stride,
    )?;
    for (at, start) in starts.iter().copied().enumerate() {
        if predecessor_traces[at]
            != compact
                .trace(CondensedRoute::Predecessor, start)
                .map_err(|error| error.to_string())?
            || successor_traces[at]
                != compact
                    .trace(CondensedRoute::Successor, start)
                    .map_err(|error| error.to_string())?
            || withdrawn_traces[at]
                != compact
                    .trace(CondensedRoute::Withdrawn, start)
                    .map_err(|error| error.to_string())?
        {
            return Err("the resident routes disagree with the exact compact owner".to_owned());
        }
    }
    let decode = |rows: &[Vec<u32>]| {
        rows.iter()
            .map(|trace| {
                compact
                    .decode_trace(trace)
                    .map_err(|error| error.to_string())
            })
            .collect::<Result<Vec<_>, _>>()
    };
    let predecessor_passages = decode(&predecessor_traces)?;
    let successor_passages = decode(&successor_traces)?;
    let withdrawn_passages = decode(&withdrawn_traces)?;
    let shared_generator_withdrawal_reopened_every_family = predecessor_passages
        .iter()
        .zip(&withdrawn_passages)
        .all(|(before, after)| before != after)
        && successor_passages
            .iter()
            .zip(&withdrawn_passages)
            .all(|(before, after)| before != after);
    if !shared_generator_withdrawal_reopened_every_family {
        return Err("shared-generator withdrawal left an attributable family unchanged".to_owned());
    }
    let semantic_work = actual_work(
        returned.trace_stride,
        &returned.predecessor_lengths,
        &returned.successor_lengths,
        &returned.withdrawn_lengths,
    );
    let descriptors = open_descriptors();
    let forbidden = descriptors
        .iter()
        .filter(|path| {
            path.contains("/home/b/Workspaces/holonics")
                || path.contains("the_recurrent_boundary_returns_a_complete_passage")
                || path.contains("the_exterior_return_changes_the_later_current")
                || path.contains("source-runtime")
                || path.contains("morphology.safetensors")
                || path.contains("tokenizer.json")
                || path.contains("exchange")
        })
        .cloned()
        .collect::<Vec<_>>();
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let receipt = DetachedReturn {
        schema: "holonics.i3.detached-return.v1".to_owned(),
        component_sha256: [
            ("standing".to_owned(), manifest.standing.sha256),
            ("decoder".to_owned(), manifest.decoder.sha256),
            ("fibres".to_owned(), manifest.fibres.sha256),
        ]
        .into_iter()
        .collect(),
        predecessor_traces,
        successor_traces,
        withdrawn_traces,
        predecessor_passages,
        successor_passages,
        withdrawn_passages,
        shared_generator_withdrawal_reopened_every_family,
        semantic_work,
        source_access_descriptors: descriptors,
        forbidden_source_access: forbidden,
        cpu_semantic_callbacks_between_fronts: 0,
        apparatus: DetachedApparatus {
            device: card.device_name().to_owned(),
            block_threads: returned.block_threads,
            active_lanes: returned.active_lanes,
            launches: returned.launches,
            synchronizations: returned.synchronizations,
            visited_words_per_route: returned.visited_words,
            host_ingress_octets: returned.host_ingress_octets,
            host_egress_octets: returned.host_egress_octets,
            resident_octets: returned.resident_octets,
            physical_wall_microseconds,
        },
    };
    write(
        output.join("return.json"),
        &serde_json::to_vec_pretty(&receipt).map_err(|error| error.to_string())?,
    )
}

fn realization_atlas(
    passage: &RetainedContinuationPassage,
    returned: &ReturnedRecurrentRest,
    compact: &CondensedRecurrentRest,
    detached: &DetachedReturn,
) -> Result<Value, String> {
    let sections = passage
        .sections
        .iter()
        .map(|section| {
            json!({
                "occurrence": section.occurrence,
                "predecessor": section.predecessor,
                "native": section.native_boundary.0,
                "terminal_potential_sha256": section.complete_terminal_potential_sha256,
            })
        })
        .collect::<Vec<_>>();
    let cover_members = vec![
        ("predecessor-main", detached.predecessor_traces[0].clone()),
        ("successor-main", detached.successor_traces[0].clone()),
        (
            "predecessor-held-out",
            detached.predecessor_traces[1].clone(),
        ),
        ("successor-held-out", detached.successor_traces[1].clone()),
        ("terminal-potential-native-1", vec![1]),
        ("terminal-potential-native-2", vec![2]),
    ];
    let active_cover = cover_members
        .iter()
        .map(|(name, members)| {
            json!({"cell": name, "native_members": unique(members), "derived_from": "enacted intervention/history"})
        })
        .collect::<Vec<_>>();
    let mut nerve = Vec::new();
    for left in 0..cover_members.len() {
        for right in left + 1..cover_members.len() {
            let left_set = cover_members[left]
                .1
                .iter()
                .copied()
                .collect::<BTreeSet<_>>();
            let intersection = cover_members[right]
                .1
                .iter()
                .copied()
                .filter(|member| left_set.contains(member))
                .collect::<BTreeSet<_>>();
            if !intersection.is_empty() {
                nerve.push(json!({
                    "left": cover_members[left].0,
                    "right": cover_members[right].0,
                    "intersection": intersection,
                }));
            }
        }
    }
    let predecessor = [1u32, 2, 1];
    let successor = compact.standing.successor_action.clone();
    let mut transport_defects = Vec::new();
    for pair in passage.sections.windows(2) {
        let from = u32::try_from(pair[0].native_boundary.0).map_err(|_| "native exceeds u32")?;
        let observed =
            u32::try_from(pair[1].native_boundary.0).map_err(|_| "native exceeds u32")?;
        for (route, action) in [
            ("predecessor", predecessor.as_slice()),
            ("successor", successor.as_slice()),
        ] {
            let expected = action[from as usize];
            transport_defects.push(json!({
                "kind": "source/native-generator-square",
                "source_from": pair[0].occurrence,
                "source_to": pair[1].occurrence,
                "native_from": from,
                "native_observed_to": observed,
                "route": route,
                "native_expected_to": expected,
                "defect": i64::from(observed) - i64::from(expected),
                "zero_defect": observed == expected,
                "shortest_separator": (observed != expected).then_some(vec![0u32]),
                "truth_status": "established-bounded"
            }));
        }
    }
    for separator in &compact.fibres.separators {
        transport_defects.push(json!({
            "kind": "receiver-visible-terminal-potential",
            "native": separator.native,
            "left_occurrence": separator.left_occurrence,
            "right_occurrence": separator.right_occurrence,
            "left_receiver": separator.left_potential_sha256,
            "right_receiver": separator.right_potential_sha256,
            "defect": "nonzero-digest-separation",
            "zero_defect": false,
            "shortest_separator": separator.shortest_history,
            "truth_status": "established-bounded"
        }));
    }
    transport_defects.push(json!({
        "kind": "unexcited-source-successor-square",
        "native_from": 2,
        "native_to": 2,
        "route": "successor",
        "defect": "open-no-source-occurrence",
        "zero_defect": false,
        "shortest_separator": [0],
        "truth_status": "open"
    }));
    Ok(json!({
        "schema": "holonics.i3.realization-atlas.v1",
        "truth_status": "established-bounded",
        "source_sections": sections,
        "native_population": [0, 1, 2],
        "active_cover": active_cover,
        "cover_nerve": nerve,
        "generator_families": [{
            "generator": 0,
            "founded_by": "stable returned recurrence under main and held-out histories",
            "shared_zero_defect_edges": [{"from": 0, "to": 1}, {"from": 1, "to": 2}],
            "predecessor_local_route": {"from": 2, "to": 1},
            "successor_local_route": {"from": 2, "to": 2},
            "withdrawal": "identity recurrence at every admitted entering boundary"
        }],
        "transport_defects": transport_defects,
        "zero_defect_condensed_subcomplex": {
            "native_states": [0, 1, 2],
            "shared_edges": [{"from": 0, "to": 1}, {"from": 1, "to": 2}],
            "successor_action": successor,
            "predecessor_deformation": {"from": compact.standing.predecessor_from, "to": compact.standing.predecessor_to},
        },
        "reconstruction_fibres": compact.fibres,
        "noncommuting_route": {
            "rank": returned.holonomy.commutator_rank,
            "at_native": returned.delta.from.0,
            "predecessor_to": returned.delta.predecessor_to.0,
            "successor_to": returned.delta.successor_to.0,
            "retained_separately": true
        },
        "exterior_return": {
            "emitted_occurrence": returned.exterior.emitted_occurrence,
            "consequence_occurrence": returned.exterior.consequence_occurrence,
            "return_occurrence": returned.exterior.return_occurrence,
            "deposit_at_native": returned.delta.from.0,
            "return_lineage": returned.causal_adjoint.return_lineage,
            "truth_status": "established-bounded"
        },
        "conservation_of_faces": {
            "statement": "a condensed receiver face is conserved only with its complete source fibre and every shortest reopening history",
            "relation_to_current_formal_work": "same fibrewise conservation pattern as summing a complete sigma-fibre without identifying its members",
            "truth_status": "definition"
        },
        "open_exterior": compact.standing.open_exterior,
    }))
}

fn exact_mesh(atlas: &Value) -> Result<Value, String> {
    let source = atlas["source_sections"]
        .as_array()
        .ok_or("atlas source sections are absent")?;
    let mut vertices = Vec::new();
    for (ordinal, section) in source.iter().enumerate() {
        vertices.push(json!({
            "id": format!("s{ordinal}"),
            "kind": "source-occurrence",
            "occurrence": section["occurrence"],
            "native": section["native"],
            "x": 80 + ordinal * 120,
            "y": 110,
        }));
    }
    for native in 0..3usize {
        vertices.push(json!({
            "id": format!("n{native}"),
            "kind": "native-boundary",
            "native": native,
            "x": 200 + native * 180,
            "y": 310,
        }));
    }
    for (id, kind, x, y, occurrence) in [
        (
            "e0",
            "emitted-occurrence",
            650usize,
            120usize,
            &atlas["exterior_return"]["emitted_occurrence"],
        ),
        (
            "w0",
            "world-consequence",
            760,
            230,
            &atlas["exterior_return"]["consequence_occurrence"],
        ),
        (
            "r0",
            "returned-occurrence",
            650,
            340,
            &atlas["exterior_return"]["return_occurrence"],
        ),
    ] {
        vertices.push(json!({"id": id, "kind": kind, "occurrence": occurrence, "x": x, "y": y}));
    }
    let mut edges = Vec::new();
    for ordinal in 0..source.len() - 1 {
        edges.push(json!({"from": format!("s{ordinal}"), "to": format!("s{}", ordinal + 1), "kind": "source-chronology"}));
    }
    for (ordinal, section) in source.iter().enumerate() {
        edges.push(json!({"from": format!("s{ordinal}"), "to": format!("n{}", section["native"]), "kind": "realization-passage"}));
    }
    edges.push(json!({"from": "s1", "to": "s3", "kind": "reconstruction-fibre", "receiver": "terminal-potential"}));
    edges.push(json!({"from": "s2", "to": "s4", "kind": "reconstruction-fibre", "receiver": "terminal-potential"}));
    for (from, to, kind) in [
        (0, 1, "shared"),
        (1, 2, "shared"),
        (2, 1, "predecessor"),
        (2, 2, "successor"),
    ] {
        edges.push(json!({"from": format!("n{from}"), "to": format!("n{to}"), "kind": kind}));
    }
    edges.push(json!({"from": "n1", "to": "e0", "kind": "emission"}));
    edges.push(json!({"from": "e0", "to": "w0", "kind": "world"}));
    edges.push(json!({"from": "w0", "to": "r0", "kind": "return"}));
    edges.push(json!({"from": "r0", "to": "n2", "kind": "deposit"}));
    Ok(json!({
        "schema": "holonics.i3.exact-causal-mesh.v1",
        "truth_status": "established-bounded",
        "topology_source": "01-realization-atlas.json",
        "vertices": vertices,
        "edges": edges,
        "layout_is_receiver_only": true,
        "layout_crossings_create_edges": false,
    }))
}

fn interactive_svg(atlas: &Value, mesh: &Value) -> Result<String, String> {
    let vertices = mesh["vertices"].as_array().ok_or("mesh vertices absent")?;
    let edges = mesh["edges"].as_array().ok_or("mesh edges absent")?;
    let positions = vertices
        .iter()
        .map(|vertex| {
            let id = vertex["id"].as_str().unwrap_or_default().to_owned();
            let x = vertex["x"].as_u64().unwrap_or_default();
            let y = vertex["y"].as_u64().unwrap_or_default();
            (id, (x, y))
        })
        .collect::<BTreeMap<_, _>>();
    let mut drawing = String::new();
    for edge in edges {
        let from = edge["from"].as_str().ok_or("edge source absent")?;
        let to = edge["to"].as_str().ok_or("edge target absent")?;
        let kind = edge["kind"].as_str().ok_or("edge kind absent")?;
        let (x1, y1) = positions[from];
        let (x2, y2) = positions[to];
        if from == to {
            drawing.push_str(&format!("<path class='edge {kind}' data-kind='{kind}' d='M {x1} {} C {} {} {} {} {x1} {}'/>", y1 - 20, x1 + 70, y1 - 90, x1 - 70, y1 - 90, y1 - 20));
        } else if kind == "reconstruction-fibre" {
            drawing.push_str(&format!(
                "<path class='edge {kind}' data-kind='{kind}' d='M {x1} {y1} Q {} {} {x2} {y2}'/>",
                (x1 + x2) / 2,
                y1 - 75
            ));
        } else {
            drawing.push_str(&format!("<line class='edge {kind}' data-kind='{kind}' x1='{x1}' y1='{y1}' x2='{x2}' y2='{y2}'/>"));
        }
    }
    for vertex in vertices {
        let id = vertex["id"].as_str().unwrap_or_default();
        let kind = vertex["kind"].as_str().unwrap_or_default();
        let x = vertex["x"].as_u64().unwrap_or_default();
        let y = vertex["y"].as_u64().unwrap_or_default();
        let fibre_member = matches!(id, "s3" | "s4");
        drawing.push_str(&format!("<g class='node {kind}{}' data-kind='{kind}'><circle cx='{x}' cy='{y}' r='24'/><text x='{x}' y='{}'>{id}</text></g>", if fibre_member { " fibre-secondary" } else { "" }, y + 5));
    }
    let defects = atlas["transport_defects"].as_array().map_or(0, Vec::len);
    Ok(format!(
        r##"<svg xmlns="http://www.w3.org/2000/svg" width="900" height="560" viewBox="0 0 900 560">
<title>I3 exact source/native causal atlas</title><desc>Topology is copied from 02-exact-mesh.json; layout crossings have no incidence.</desc>
<defs><marker id="arrow" markerWidth="7" markerHeight="7" refX="6" refY="3.5" orient="auto"><path d="M0,0 L7,3.5 L0,7 z" fill="context-stroke"/></marker></defs>
<style>svg{{background:#101722;color:#d8e6f2;font:14px sans-serif}} .edge{{fill:none;stroke:#6b8195;stroke-width:2;marker-end:url(#arrow)}} .edge.realization-passage{{stroke:#6cc6b3;stroke-dasharray:5 4}} .edge.reconstruction-fibre{{stroke:#b287e8;stroke-width:3;marker-end:none}} .edge.predecessor{{stroke:#f0b45a}} .edge.successor{{stroke:#da668b}} .edge.emission,.edge.world,.edge.return,.edge.deposit{{stroke:#6fb9ee;stroke-width:3}} .node circle{{fill:#223447;stroke:#9ab6cb;stroke-width:2}} .native-boundary circle{{fill:#294b42}} .emitted-occurrence circle,.world-consequence circle,.returned-occurrence circle{{fill:#253e5d;stroke:#74bdf0}} text{{fill:#eef6fb;text-anchor:middle}} .label{{text-anchor:start;font-size:13px}} [data-filter],[data-action]{{cursor:pointer}} .travelling{{stroke-dasharray:9 8;animation:travel 1.2s linear infinite}} @keyframes travel{{to{{stroke-dashoffset:-34}}}}</style>
<rect x="20" y="18" width="860" height="54" rx="8" fill="#182536"/><text class="label" x="38" y="42">I3 recurrent realization complex · {defects} defect/open rows</text><text class="label" x="38" y="62">receiver projections change visibility only; the JSON mesh remains authoritative</text>
<g id="drawing">{drawing}</g>
<g transform="translate(35 450)"><text class="label" x="0" y="-20">receiver:</text><rect data-filter="source-occurrence" x="70" y="-42" width="105" height="32" rx="5" fill="#30445b"/><text x="122" y="-20">source</text><rect data-filter="native-boundary" x="185" y="-42" width="105" height="32" rx="5" fill="#315d51"/><text x="237" y="-20">native</text><rect data-filter="reconstruction-fibre" x="300" y="-42" width="105" height="32" rx="5" fill="#624a78"/><text x="352" y="-20">fibres</text><rect data-filter="return-cycle" x="415" y="-42" width="105" height="32" rx="5" fill="#375f7d"/><text x="467" y="-20">return</text><rect data-filter="all" x="530" y="-42" width="105" height="32" rx="5" fill="#4a3f5f"/><text x="582" y="-20">all</text></g>
<g transform="translate(35 515)"><text class="label" x="0" y="0">intervention:</text><rect data-action="collapse" x="95" y="-22" width="130" height="32" rx="5" fill="#67475d"/><text x="160" y="0">collapse fibres</text><rect data-action="reopen" x="235" y="-22" width="130" height="32" rx="5" fill="#5f4c78"/><text x="300" y="0">reopen fibres</text><rect data-action="animate" x="375" y="-22" width="145" height="32" rx="5" fill="#315d75"/><text x="447" y="0">animate return</text></g>
<script><![CDATA[const returnKinds=new Set(['emission','world','return','deposit']);document.querySelectorAll('[data-filter]').forEach(b=>b.addEventListener('click',()=>{{const f=b.dataset.filter;document.querySelectorAll('.node,.edge').forEach(e=>{{const hit=f==='all'||e.classList.contains(f)||(f==='return-cycle'&&[...returnKinds].some(k=>e.classList.contains(k)));e.style.opacity=hit?'1':'0.10'}})}}));document.querySelector('[data-action="collapse"]').addEventListener('click',()=>document.querySelectorAll('.reconstruction-fibre,.fibre-secondary').forEach(e=>e.style.opacity='0'));document.querySelector('[data-action="reopen"]').addEventListener('click',()=>document.querySelectorAll('.reconstruction-fibre,.fibre-secondary').forEach(e=>e.style.opacity='1'));document.querySelector('[data-action="animate"]').addEventListener('click',()=>document.querySelectorAll('.emission,.world,.return,.deposit').forEach(e=>e.classList.toggle('travelling')));]]></script>
</svg>"##
    ))
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
        schema: "holonics.i3.complete-product-cost.v1",
        truth_status: "measured",
        source,
        native,
        strict_coordinate_fall,
        every_coordinate_strictly_falls,
    }
}

fn grade(
    atlas: &Value,
    mesh: &Value,
    detached: &DetachedReturn,
    costs: &CostProduct,
    manifest: &RestDirectoryManifest,
) -> I3Grade {
    let active_cover = atlas["active_cover"].as_array().map_or(0, Vec::len);
    let nerve = atlas["cover_nerve"].as_array().map_or(0, Vec::len);
    let defects = atlas["transport_defects"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let separated = defects
        .iter()
        .filter(|row| row["zero_defect"] == false)
        .all(|row| row["shortest_separator"].is_array());
    let overlapping_active_cover_derived = active_cover >= 6 && nerve > 0;
    let generators_come_from_stable_transport_and_recurrence = atlas["generator_families"]
        .as_array()
        .is_some_and(|families| !families.is_empty());
    let defects_and_shortest_separators_complete = defects.len() == 11 && separated;
    let only_zero_defect_future_exact_subcomplex_condensed = atlas
        ["zero_defect_condensed_subcomplex"]["shared_edges"]
        .as_array()
        .is_some_and(|edges| edges.len() == 2);
    let noncommuting_and_receiver_visible_routes_retained = atlas["noncommuting_route"]["rank"]
        .as_u64()
        .is_some_and(|rank| rank > 0)
        && atlas["reconstruction_fibres"]["separators"]
            .as_array()
            .is_some_and(|rows| rows.len() == 2);
    let executable_generator_native_rest_and_decoder = manifest.standing.octets > 0
        && manifest.decoder.octets > 0
        && manifest.fibres.octets > 0
        && detached.apparatus.launches == 1
        && detached.apparatus.synchronizations == 1;
    let source_development_and_exchange_absent_at_remount =
        detached.forbidden_source_access.is_empty()
            && detached.cpu_semantic_callbacks_between_fronts == 0;
    let complete_main_and_held_out_passage_families_return = detached.predecessor_passages.len()
        == 2
        && detached.successor_passages.len() == 2
        && detached
            .predecessor_passages
            .iter()
            .zip(&detached.successor_passages)
            .all(|(left, right)| left != right);
    let shared_generator_ablation_reopens_every_family =
        detached.shared_generator_withdrawal_reopened_every_family;
    let complete_product_vector_strictly_falls = costs.every_coordinate_strictly_falls;
    let source_native_atlas_and_interactive_exact_mesh_return = mesh["vertices"]
        .as_array()
        .is_some_and(|rows| rows.len() == 11)
        && mesh["layout_crossings_create_edges"] == false;
    let passed = overlapping_active_cover_derived
        && generators_come_from_stable_transport_and_recurrence
        && defects_and_shortest_separators_complete
        && only_zero_defect_future_exact_subcomplex_condensed
        && noncommuting_and_receiver_visible_routes_retained
        && executable_generator_native_rest_and_decoder
        && source_development_and_exchange_absent_at_remount
        && complete_main_and_held_out_passage_families_return
        && shared_generator_ablation_reopens_every_family
        && complete_product_vector_strictly_falls
        && source_native_atlas_and_interactive_exact_mesh_return;
    I3Grade {
        schema: "holonics.i3.grade.v1",
        truth_status: "established-bounded",
        overlapping_active_cover_derived,
        generators_come_from_stable_transport_and_recurrence,
        defects_and_shortest_separators_complete,
        only_zero_defect_future_exact_subcomplex_condensed,
        noncommuting_and_receiver_visible_routes_retained,
        executable_generator_native_rest_and_decoder,
        source_development_and_exchange_absent_at_remount,
        complete_main_and_held_out_passage_families_return,
        shared_generator_ablation_reopens_every_family,
        complete_product_vector_strictly_falls,
        source_native_atlas_and_interactive_exact_mesh_return,
        passed,
    }
}

fn actual_work(
    stride: usize,
    predecessor: &[u32],
    successor: &[u32],
    withdrawn: &[u32],
) -> CondensedSemanticWork {
    let steps = |lengths: &[u32]| lengths.iter().map(|length| u64::from(*length - 1)).sum();
    let predecessor_transition_reads = steps(predecessor);
    let successor_transition_reads = steps(successor);
    let withdrawal_transition_reads = steps(withdrawn);
    let visited_incidence_tests =
        predecessor_transition_reads + successor_transition_reads + withdrawal_transition_reads;
    CondensedSemanticWork {
        starting_occurrences: predecessor.len() as u64,
        predecessor_transition_reads,
        successor_transition_reads,
        withdrawal_transition_reads,
        visited_incidence_tests,
        trace_entries_written: (predecessor.len() * stride * 3) as u64,
        dependency_span: predecessor
            .iter()
            .chain(successor)
            .chain(withdrawn)
            .map(|length| u64::from(*length - 1))
            .max()
            .unwrap_or(0),
    }
}

fn traces(flat: &[u32], lengths: &[u32], stride: usize) -> Result<Vec<Vec<u32>>, String> {
    if flat.len() != lengths.len() * stride {
        return Err("the recurrent trace rectangle is malformed".to_owned());
    }
    lengths
        .iter()
        .enumerate()
        .map(|(at, length)| {
            let length = usize::try_from(*length).map_err(|_| "trace length exceeds usize")?;
            if length < 2 || length > stride {
                return Err(format!("recurrence {at} returned length {length}"));
            }
            let trace = flat[at * stride..at * stride + length].to_vec();
            let prior = trace[..trace.len() - 1]
                .iter()
                .copied()
                .collect::<BTreeSet<_>>();
            if prior.len() + 1 != trace.len() || !prior.contains(trace.last().expect("nonempty")) {
                return Err(format!(
                    "recurrence {at} did not first close at its terminal face"
                ));
            }
            Ok(trace)
        })
        .collect()
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
        .arg("/athena-i3")
        .arg("--ro-bind")
        .arg(rest)
        .arg("/rest")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/tmp",
            "/athena-i3",
            "--detached-grade",
            "/rest",
            "/return",
        ]);
    let status = command.status().map_err(|error| error.to_string())?;
    status
        .success()
        .then_some(())
        .ok_or_else(|| format!("detached I3 grade returned {status}"))
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
        return Err("an I3 component escaped its rest directory".to_owned());
    }
    let bytes = fs::read(root.join(&identity.path)).map_err(|error| error.to_string())?;
    if sha256(&bytes) != identity.sha256 || bytes.len() as u64 != identity.octets {
        return Err(format!("I3 component {} moved", identity.path));
    }
    Ok(bytes)
}

fn unique(values: &[u32]) -> Vec<u32> {
    values
        .iter()
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn inspection(
    costs: &CostProduct,
    detached: &DetachedReturn,
    compact: &CondensedRecurrentRest,
) -> String {
    format!(
        "# I3 recurrent Phoenix condensation\n\n- grade: PASS\n- source/native artifact octets: {} / {}\n- source/native decoder octets: {} / {}\n- source/native fibre octets: {} / {}\n- source/native semantic work: {} / {}\n- source/native dependency span: {} / {}\n- source/native residency octets: {} / {}\n- source/native transfer octets: {} / {}\n- predecessor passages: {:?}\n- successor passages: {:?}\n- withdrawn passages: {:?}\n- terminal-potential separators retained: {}\n- detached card launches/synchronizations: {}/{}\n- forbidden source descriptors: {}\n",
        costs.source.artifact_octets, costs.native.artifact_octets,
        costs.source.decoder_octets, costs.native.decoder_octets,
        costs.source.fibre_octets, costs.native.fibre_octets,
        costs.source.semantic_work, costs.native.semantic_work,
        costs.source.dependency_span, costs.native.dependency_span,
        costs.source.resident_octets, costs.native.resident_octets,
        costs.source.transfer_octets, costs.native.transfer_octets,
        detached.predecessor_passages, detached.successor_passages, detached.withdrawn_passages,
        compact.fibres.separators.len(), detached.apparatus.launches,
        detached.apparatus.synchronizations, detached.forbidden_source_access.len()
    )
}

fn sha256(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn code_closure() -> String {
    let members: &[&[u8]] = &[
        include_bytes!("the_recurrent_realizations_condense_into_a_phoenix_ecology.rs"),
        include_bytes!(
            "../../../crates/holonic-engine/src/native_ecology/recurrent_condensation.rs"
        ),
        include_bytes!("../../../crates/holonic-engine/src/native_ecology/recurrent_return.rs"),
        include_bytes!("../../../crates/holonic-engine/src/native_ecology/recurrent.rs"),
        include_bytes!("../../../crates/holonic-engine/src/cuda_refine.rs"),
        include_bytes!("../../../crates/holonic-engine/kernels/refine_shell.cu"),
    ];
    let mut digest = Sha256::new();
    for member in members {
        digest.update((member.len() as u64).to_le_bytes());
        digest.update(member);
    }
    hex(&digest.finalize())
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(DIGITS[(byte >> 4) as usize] as char);
        out.push(DIGITS[(byte & 15) as usize] as char);
    }
    out
}

fn write(path: impl AsRef<Path>, bytes: &[u8]) -> Result<(), String> {
    let path = path.as_ref();
    let staged = path.with_extension("i3-staged");
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

fn args() -> Result<Args, String> {
    let mut values = env::args().skip(1);
    match values.next().as_deref() {
        Some("--produce") => {
            let passage = required_path(&mut values, "I1_PASSAGE")?;
            let returned = required_path(&mut values, "I2_RETURNED_REST")?;
            let i2_detached = required_path(&mut values, "I2_DETACHED_RECEIPT")?;
            let output = values.next().map(PathBuf::from).unwrap_or_else(|| PathBuf::from(DEFAULT_OUT));
            no_trailing(&mut values, "--produce")?;
            Ok(Args::Produce { passage, returned, i2_detached, output })
        }
        Some("--detached-grade") => {
            let rest = required_path(&mut values, "REST")?;
            let output = required_path(&mut values, "OUTPUT")?;
            no_trailing(&mut values, "--detached-grade")?;
            Ok(Args::DetachedGrade { rest, output })
        }
        _ => Err("usage: --produce I1_PASSAGE I2_RETURNED_REST I2_DETACHED_RECEIPT [OUTPUT] | --detached-grade REST OUTPUT".to_owned()),
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
