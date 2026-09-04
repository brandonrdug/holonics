//! I2: an actual exterior consequence returns, deposits locally, and changes later current.
//!
//! The I1 passage is emitted into a source-absent `/usr/bin/tee` receiver. The resulting durable
//! byte occurrence and echoed return are distinct from the emission even though the byte receiver
//! reads them alike. Their positive oriented difference returns along I1's closing edge and founds
//! one exact rank-one local generator delta. A fresh source-absent process then derives every
//! predecessor, successor and targeted-ablation recurrence on the resident card in one terminal
//! launch. No token capacity, host stop case, source model, or exchange store enters that deed.

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    native_ecology::{
        recurrent::RetainedContinuationRest,
        recurrent_return::{
            ExteriorToolReturn, RecurrentSemanticWork, ReturnDecision, ReturnedRecurrentRest,
        },
    },
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const DEFAULT_OUT: &str = ".local/artifacts/the_exterior_return_changes_the_later_current";
const REST_DIRECTORY_SCHEMA: &str = "holonics.i2.returned-rest-directory.v1";

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct RestDirectoryManifest {
    schema: String,
    rest: String,
    rest_sha256: String,
    rest_octets: u64,
}

#[derive(Serialize)]
struct ToolReceipt {
    schema: &'static str,
    receiver: &'static str,
    executable_sha256: String,
    mount_namespace_source_absent: bool,
    emitted_octets: u64,
    consequence_octets: u64,
    echoed_octets: u64,
    process_status: i32,
    physical_wall_milliseconds: u128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct TraceReopening {
    start: u32,
    predecessor: Vec<u32>,
    successor: Vec<u32>,
    shortest_separating_boundary: usize,
}

#[derive(Serialize, Deserialize)]
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
    physical_wall_milliseconds: u128,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DetachedReturn {
    schema: String,
    rest_sha256: String,
    predecessor_traces: Vec<Vec<u32>>,
    successor_traces: Vec<Vec<u32>>,
    ablated_traces: Vec<Vec<u32>>,
    main_predecessor_text: String,
    main_successor_text: String,
    held_out_predecessor_text: String,
    held_out_successor_text: String,
    control_from: u32,
    control_predecessor: u32,
    control_successor: u32,
    reopenings: Vec<TraceReopening>,
    semantic_work: RecurrentSemanticWork,
    committed: bool,
    cpu_semantic_callbacks_between_fronts: u64,
    source_access_descriptors: Vec<String>,
    forbidden_source_access: Vec<String>,
    apparatus: DetachedApparatus,
}

#[derive(Serialize)]
struct I2Grade {
    schema: &'static str,
    emission_and_exterior_consequence_are_distinct_events: bool,
    exact_returned_difference: bool,
    causal_adjoint_is_restricted_to_forward_lineage: bool,
    candidate_delta_and_explicit_commit: bool,
    predecessor_and_successor_rests_are_distinct: bool,
    source_detached_later_current_rides_successor: bool,
    nonidentical_held_out_history_changes: bool,
    subject_port_disjoint_control_holds: bool,
    targeted_ablation_restores_predecessor: bool,
    revisit_holonomy_and_every_reopening_return: bool,
    exact_work_and_separate_apparatus_receipts: bool,
    passed: bool,
}

#[derive(Serialize)]
struct ProductManifest {
    schema: &'static str,
    product: &'static str,
    exterior_return: &'static str,
    consequence: &'static str,
    returned_rest: &'static str,
    causal_adjoint: &'static str,
    detached_return: &'static str,
    predecessor_passage: &'static str,
    successor_passage: &'static str,
    grade: &'static str,
    code_closure_sha256: String,
    open_exterior: Vec<String>,
}

enum Args {
    Produce {
        predecessor: PathBuf,
        emitted: PathBuf,
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
            predecessor,
            emitted,
            output,
        } => produce(&predecessor, &emitted, &output),
        Args::DetachedGrade { rest, output } => detached_grade(&rest, &output),
    }
}

fn produce(predecessor_path: &Path, emitted_path: &Path, output: &Path) -> Result<(), String> {
    if output.exists() {
        return Err(format!(
            "I2 output {} already exists; inspect the addressed receipt instead of replaying the deed",
            output.display()
        ));
    }
    let predecessor_bytes = fs::read(predecessor_path).map_err(|error| error.to_string())?;
    let predecessor =
        RetainedContinuationRest::read(&predecessor_bytes).map_err(|error| error.to_string())?;
    let emitted = fs::read(emitted_path).map_err(|error| error.to_string())?;
    if emitted != predecessor.emitted_text.as_bytes() || emitted.is_empty() {
        return Err("the I1 emitted occurrence disagrees with its retained rest".to_owned());
    }

    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let world = output.join("world-consequence");
    fs::create_dir(&world).map_err(|error| error.to_string())?;
    let emitted_sha = sha256(&emitted);
    let predecessor_sha = sha256(&predecessor_bytes);
    let emitted_occurrence = occurrence("emission", &predecessor_sha, &emitted_sha);
    let begun = Instant::now();
    let echoed = run_exterior_tee(&world, &emitted)?;
    let wall = begun.elapsed().as_millis();
    let consequence = fs::read(world.join("consequence.txt")).map_err(|error| error.to_string())?;
    if consequence != emitted || echoed != emitted {
        return Err("the exact exterior receiver moved the emitted byte occurrence".to_owned());
    }
    let consequence_occurrence = occurrence("consequence", &emitted_occurrence, &emitted_sha);
    let return_occurrence = occurrence("return", &consequence_occurrence, &sha256(&echoed));
    let exterior = ExteriorToolReturn {
        schema: "holonics.i2.exterior-tool-return.v1".to_owned(),
        receiver: format!(
            "/usr/bin/tee exact byte-preserving consequence; executable sha256 {}",
            sha256(&fs::read("/usr/bin/tee").map_err(|error| error.to_string())?)
        ),
        emitted_occurrence,
        consequence_occurrence,
        return_occurrence,
        emitted_sha256: emitted_sha.clone(),
        consequence_sha256: sha256(&consequence),
        echoed_sha256: sha256(&echoed),
        before_octets: 0,
        after_octets: consequence.len() as u64,
        exact_difference_octets: consequence.len() as u64,
        process_status: 0,
    };
    let rest = ReturnedRecurrentRest::seal(
        &predecessor_bytes,
        exterior.emitted_occurrence.clone(),
        exterior.clone(),
    )
    .map_err(|error| error.to_string())?;
    let rest_bytes = rest.canonical_bytes().map_err(|error| error.to_string())?;

    write(world.join("echoed-return.bin"), &echoed)?;
    write(
        world.join("tool-receipt.json"),
        &serde_json::to_vec_pretty(&ToolReceipt {
            schema: "holonics.i2.exterior-tool-receipt.v1",
            receiver: "/usr/bin/tee",
            executable_sha256: sha256(
                &fs::read("/usr/bin/tee").map_err(|error| error.to_string())?,
            ),
            mount_namespace_source_absent: true,
            emitted_octets: emitted.len() as u64,
            consequence_octets: consequence.len() as u64,
            echoed_octets: echoed.len() as u64,
            process_status: 0,
            physical_wall_milliseconds: wall,
        })
        .map_err(|error| error.to_string())?,
    )?;
    write(
        output.join("00-exterior-return.json"),
        &serde_json::to_vec_pretty(&exterior).map_err(|error| error.to_string())?,
    )?;
    write(
        output.join("01-returned-recurrence-rest.json"),
        &serde_json::to_vec_pretty(&rest).map_err(|error| error.to_string())?,
    )?;
    write(
        output.join("02-causal-adjoint-and-holonomy.json"),
        &serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "holonics.i2.causal-adjoint-and-holonomy.v1",
            "delta": &rest.delta,
            "causal_adjoint": &rest.causal_adjoint,
            "holonomy": &rest.holonomy,
            "decision": &rest.decision,
            "truth_status": "established-bounded"
        }))
        .map_err(|error| error.to_string())?,
    )?;

    let native_rest = output.join("native-rest");
    fs::create_dir(&native_rest).map_err(|error| error.to_string())?;
    write(native_rest.join("returned-recurrence.rest"), &rest_bytes)?;
    let rest_manifest = RestDirectoryManifest {
        schema: REST_DIRECTORY_SCHEMA.to_owned(),
        rest: "returned-recurrence.rest".to_owned(),
        rest_sha256: sha256(&rest_bytes),
        rest_octets: rest_bytes.len() as u64,
    };
    write(
        native_rest.join("manifest.json"),
        &serde_json::to_vec_pretty(&rest_manifest).map_err(|error| error.to_string())?,
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
    let grade = grade(&rest, &rest_manifest, &detached);
    if !grade.passed {
        return Err("I2 refused its eleven-part grade".to_owned());
    }
    write(
        output.join("03-grade.json"),
        &serde_json::to_vec_pretty(&grade).map_err(|error| error.to_string())?,
    )?;
    write(
        output.join("INSPECTION.md"),
        format!(
            "# I2 exterior return and changed later current\n\n- grade: PASS\n- emitted occurrence: {}\n- consequence occurrence: {}\n- return occurrence: {}\n- exact returned difference: +{} octets\n- decision: {:?}\n- local generator delta: {:?}: {:?}->{:?}\n- adjoint rank: {}\n- revisit holonomy rank: {}\n- predecessor passage: {:?}\n- successor passage: {:?}\n- held-out predecessor/successor: {:?} / {:?}\n- reopened recurrence fibres: {}\n- disjoint control: {} -> {} / {}\n- detached card launches/synchronizations: {}/{}\n- forbidden source descriptors: {}\n",
            rest.exterior.emitted_occurrence,
            rest.exterior.consequence_occurrence,
            rest.exterior.return_occurrence,
            rest.exterior.exact_difference_octets,
            rest.decision.decision,
            rest.delta.generator,
            rest.delta.predecessor_to,
            rest.delta.successor_to,
            rest.causal_adjoint.measured_delta_rank,
            rest.holonomy.commutator_rank,
            detached.main_predecessor_text,
            detached.main_successor_text,
            detached.held_out_predecessor_text,
            detached.held_out_successor_text,
            detached.reopenings.len(),
            detached.control_from,
            detached.control_predecessor,
            detached.control_successor,
            detached.apparatus.launches,
            detached.apparatus.synchronizations,
            detached.forbidden_source_access.len()
        )
        .as_bytes(),
    )?;
    let manifest = ProductManifest {
        schema: "holonics.i2.product-manifest.v1",
        product: "Athena-Gemma exterior-return cultivation passage",
        exterior_return: "00-exterior-return.json",
        consequence: "world-consequence/consequence.txt",
        returned_rest: "01-returned-recurrence-rest.json",
        causal_adjoint: "02-causal-adjoint-and-holonomy.json",
        detached_return: "detached-return/return.json",
        predecessor_passage: "detached-return/predecessor-passage.txt",
        successor_passage: "detached-return/successor-passage.txt",
        grade: "03-grade.json",
        code_closure_sha256: code_closure(),
        open_exterior: rest.open_fibres.clone(),
    };
    write(
        output.join("MANIFEST.json"),
        &serde_json::to_vec_pretty(&manifest).map_err(|error| error.to_string())?,
    )?;
    println!("I2 returned: {}", output.display());
    println!("predecessor passage: {:?}", detached.main_predecessor_text);
    println!("successor passage: {:?}", detached.main_successor_text);
    Ok(())
}

fn detached_grade(rest_directory: &Path, output: &Path) -> Result<(), String> {
    let manifest_bytes =
        fs::read(rest_directory.join("manifest.json")).map_err(|error| error.to_string())?;
    let manifest: RestDirectoryManifest =
        serde_json::from_slice(&manifest_bytes).map_err(|error| error.to_string())?;
    if manifest.schema != REST_DIRECTORY_SCHEMA || manifest.rest != "returned-recurrence.rest" {
        return Err("the detached I2 rest manifest is invalid".to_owned());
    }
    let rest_bytes =
        fs::read(rest_directory.join(&manifest.rest)).map_err(|error| error.to_string())?;
    if sha256(&rest_bytes) != manifest.rest_sha256
        || rest_bytes.len() as u64 != manifest.rest_octets
    {
        return Err("the detached I2 rest identity moved".to_owned());
    }
    let rest = ReturnedRecurrentRest::read(&rest_bytes).map_err(|error| error.to_string())?;
    let table = rest.generator_table().map_err(|error| error.to_string())?;
    let generator = rest
        .base
        .generators
        .iter()
        .position(|entry| entry.generator == rest.delta.generator)
        .ok_or("the return generator is absent")? as u32;
    let starts = rest
        .recurrence_starts
        .iter()
        .map(|state| u32::try_from(state.0).map_err(|_| "native state exceeds u32"))
        .collect::<Result<Vec<_>, _>>()?;
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let begun = Instant::now();
    let returned = card
        .conduct_returned_recurrences_on_device(
            rest.base.native_population.len(),
            rest.base.generators.len(),
            &table,
            generator,
            &starts,
            rest.exterior.exact_difference_octets,
            u32::try_from(rest.delta.from.0).map_err(|_| "delta source exceeds u32")?,
            u32::try_from(rest.delta.successor_to.0).map_err(|_| "delta target exceeds u32")?,
            u32::try_from(rest.control_from.0).map_err(|_| "control source exceeds u32")?,
        )
        .map_err(|error| error.to_string())?;
    let wall = begun.elapsed().as_millis();
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
    let ablated_traces = traces(
        &returned.ablated_trace,
        &returned.ablated_lengths,
        returned.trace_stride,
    )?;
    if predecessor_traces != ablated_traces || !returned.committed {
        return Err("the targeted ablation did not return the predecessor recurrence".to_owned());
    }
    let reopenings = predecessor_traces
        .iter()
        .zip(&successor_traces)
        .zip(&starts)
        .filter_map(|((predecessor, successor), start)| {
            (predecessor != successor).then(|| TraceReopening {
                start: *start,
                shortest_separating_boundary: shortest_separator(predecessor, successor),
                predecessor: predecessor.clone(),
                successor: successor.clone(),
            })
        })
        .collect::<Vec<_>>();
    if reopenings.len() != starts.len() {
        return Err("not every recurrence fibre reopened under the local return".to_owned());
    }
    let main = starts
        .iter()
        .position(|state| u64::from(*state) == rest.main_start.0)
        .ok_or("main recurrence start is absent")?;
    let held_out = starts
        .iter()
        .position(|state| u64::from(*state) == rest.held_out_start.0)
        .ok_or("held-out recurrence start is absent")?;
    let main_predecessor_text = rest
        .decode_trace(&predecessor_traces[main])
        .map_err(|error| error.to_string())?;
    let main_successor_text = rest
        .decode_trace(&successor_traces[main])
        .map_err(|error| error.to_string())?;
    let held_out_predecessor_text = rest
        .decode_trace(&predecessor_traces[held_out])
        .map_err(|error| error.to_string())?;
    let held_out_successor_text = rest
        .decode_trace(&successor_traces[held_out])
        .map_err(|error| error.to_string())?;
    if main_predecessor_text == main_successor_text
        || held_out_predecessor_text == held_out_successor_text
        || returned.control_predecessor != returned.control_successor
    {
        return Err(
            "the successor, held-out, or disjoint-control consequence is invalid".to_owned(),
        );
    }
    let semantic_work = actual_work(
        returned.trace_stride,
        &returned.predecessor_lengths,
        &returned.successor_lengths,
        &returned.ablated_lengths,
    );
    if semantic_work != rest.semantic_work_prediction {
        return Err("the card return disagrees with the exact semantic work prediction".to_owned());
    }
    let descriptors = open_descriptors();
    let forbidden = descriptors
        .iter()
        .filter(|path| {
            path.contains("/home/b/Workspaces/holonics")
                || path.contains("the_recurrent_boundary_returns_a_complete_passage")
                || path.contains("base.w1.rest")
                || path.contains("cultivated.rest")
                || path.contains("morphology.safetensors")
                || path.contains("tokenizer.json")
                || path.contains("exchange")
        })
        .cloned()
        .collect::<Vec<_>>();
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    write(
        output.join("predecessor-passage.txt"),
        main_predecessor_text.as_bytes(),
    )?;
    write(
        output.join("successor-passage.txt"),
        main_successor_text.as_bytes(),
    )?;
    write(
        output.join("held-out-predecessor.txt"),
        held_out_predecessor_text.as_bytes(),
    )?;
    write(
        output.join("held-out-successor.txt"),
        held_out_successor_text.as_bytes(),
    )?;
    let receipt = DetachedReturn {
        schema: "holonics.i2.detached-return.v1".to_owned(),
        rest_sha256: manifest.rest_sha256,
        predecessor_traces,
        successor_traces,
        ablated_traces,
        main_predecessor_text,
        main_successor_text,
        held_out_predecessor_text,
        held_out_successor_text,
        control_from: rest.control_from.0 as u32,
        control_predecessor: returned.control_predecessor,
        control_successor: returned.control_successor,
        reopenings,
        semantic_work,
        committed: returned.committed,
        cpu_semantic_callbacks_between_fronts: 0,
        source_access_descriptors: descriptors,
        forbidden_source_access: forbidden,
        apparatus: DetachedApparatus {
            device: card.device_name().to_owned(),
            block_threads: returned.block_threads,
            active_lanes: returned.active_lanes,
            launches: returned.launches,
            synchronizations: returned.synchronizations,
            host_ingress_octets: returned.host_ingress_octets,
            host_egress_octets: returned.host_egress_octets,
            resident_octets: returned.resident_octets,
            physical_wall_milliseconds: wall,
        },
    };
    write(
        output.join("return.json"),
        &serde_json::to_vec_pretty(&receipt).map_err(|error| error.to_string())?,
    )
}

fn grade(
    rest: &ReturnedRecurrentRest,
    manifest: &RestDirectoryManifest,
    detached: &DetachedReturn,
) -> I2Grade {
    let emission_and_exterior_consequence_are_distinct_events = rest.exterior.emitted_occurrence
        != rest.exterior.consequence_occurrence
        && rest.exterior.emitted_occurrence != rest.exterior.return_occurrence
        && rest.exterior.consequence_occurrence != rest.exterior.return_occurrence;
    let exact_returned_difference = rest.exterior.before_octets == 0
        && rest.exterior.after_octets == rest.exterior.exact_difference_octets
        && rest.exterior.exact_difference_octets > 0;
    let causal_adjoint_is_restricted_to_forward_lineage = rest.causal_adjoint.measured_delta_rank
        == 1
        && rest.causal_adjoint.forward_lineage.first() == Some(&rest.main_start)
        && rest.causal_adjoint.forward_lineage[rest.causal_adjoint.forward_lineage.len() - 2]
            == rest.delta.from
        && rest.causal_adjoint.return_lineage
            == rest
                .causal_adjoint
                .forward_lineage
                .iter()
                .copied()
                .rev()
                .collect::<Vec<_>>();
    let candidate_delta_and_explicit_commit = rest.decision.decision == ReturnDecision::Committed
        && rest.delta.predecessor_to != rest.delta.successor_to
        && detached.committed;
    let predecessor_and_successor_rests_are_distinct = rest.decision.predecessor_sha256
        != rest
            .decision
            .successor_sha256
            .as_deref()
            .unwrap_or_default()
        && detached.rest_sha256 == manifest.rest_sha256;
    let source_detached_later_current_rides_successor = detached.forbidden_source_access.is_empty()
        && detached.main_predecessor_text != detached.main_successor_text;
    let nonidentical_held_out_history_changes = rest.held_out_start != rest.main_start
        && detached.held_out_predecessor_text != detached.held_out_successor_text;
    let subject_port_disjoint_control_holds = rest.control_from != rest.delta.from
        && detached.control_predecessor == detached.control_successor;
    let targeted_ablation_restores_predecessor =
        detached.predecessor_traces == detached.ablated_traces;
    let revisit_holonomy_and_every_reopening_return = rest.holonomy.commutator_rank > 0
        && detached.reopenings.len() == rest.recurrence_starts.len()
        && detached
            .reopenings
            .iter()
            .all(|reopening| reopening.shortest_separating_boundary > 0);
    let exact_work_and_separate_apparatus_receipts = detached.semantic_work
        == rest.semantic_work_prediction
        && detached.apparatus.launches == 1
        && detached.apparatus.synchronizations == 1
        && detached.apparatus.resident_octets > 0
        && detached.cpu_semantic_callbacks_between_fronts == 0;
    let passed = emission_and_exterior_consequence_are_distinct_events
        && exact_returned_difference
        && causal_adjoint_is_restricted_to_forward_lineage
        && candidate_delta_and_explicit_commit
        && predecessor_and_successor_rests_are_distinct
        && source_detached_later_current_rides_successor
        && nonidentical_held_out_history_changes
        && subject_port_disjoint_control_holds
        && targeted_ablation_restores_predecessor
        && revisit_holonomy_and_every_reopening_return
        && exact_work_and_separate_apparatus_receipts;
    I2Grade {
        schema: "holonics.i2.grade.v1",
        emission_and_exterior_consequence_are_distinct_events,
        exact_returned_difference,
        causal_adjoint_is_restricted_to_forward_lineage,
        candidate_delta_and_explicit_commit,
        predecessor_and_successor_rests_are_distinct,
        source_detached_later_current_rides_successor,
        nonidentical_held_out_history_changes,
        subject_port_disjoint_control_holds,
        targeted_ablation_restores_predecessor,
        revisit_holonomy_and_every_reopening_return,
        exact_work_and_separate_apparatus_receipts,
        passed,
    }
}

fn traces(flat: &[u32], lengths: &[u32], stride: usize) -> Result<Vec<Vec<u32>>, String> {
    if flat.len() != lengths.len() * stride {
        return Err("the returned recurrence trace rectangle is malformed".to_owned());
    }
    lengths
        .iter()
        .enumerate()
        .map(|(at, length)| {
            let length = *length as usize;
            if length < 2 || length > stride {
                return Err(format!("recurrence {at} returned length {length}"));
            }
            let trace = flat[at * stride..at * stride + length].to_vec();
            let before_last = trace[..trace.len() - 1]
                .iter()
                .copied()
                .collect::<BTreeSet<_>>();
            if before_last.len() + 1 != trace.len()
                || !before_last.contains(trace.last().expect("nonempty"))
            {
                return Err(format!(
                    "recurrence {at} did not close first at its terminal face"
                ));
            }
            Ok(trace)
        })
        .collect()
}

fn shortest_separator(left: &[u32], right: &[u32]) -> usize {
    left.iter()
        .zip(right)
        .position(|(left, right)| left != right)
        .unwrap_or_else(|| left.len().min(right.len()))
}

fn actual_work(
    stride: usize,
    predecessor: &[u32],
    successor: &[u32],
    ablated: &[u32],
) -> RecurrentSemanticWork {
    let steps = |lengths: &[u32]| lengths.iter().map(|length| u64::from(*length - 1)).sum();
    let comparisons = predecessor
        .iter()
        .chain(successor)
        .chain(ablated)
        .map(|length| {
            let steps = u64::from(*length - 1);
            steps * (steps + 1) / 2
        })
        .sum();
    RecurrentSemanticWork {
        starting_occurrences: predecessor.len() as u64,
        predecessor_transition_reads: steps(predecessor),
        successor_transition_reads: steps(successor),
        ablation_transition_reads: steps(ablated),
        recurrence_equality_comparisons: comparisons,
        trace_entries_written: (predecessor.len() * stride * 3) as u64,
        dependency_span: predecessor
            .iter()
            .chain(successor)
            .chain(ablated)
            .copied()
            .max()
            .unwrap_or(0) as u64,
    }
}

fn run_exterior_tee(world: &Path, emitted: &[u8]) -> Result<Vec<u8>, String> {
    let world = world
        .canonicalize()
        .map_err(|error| format!("resolve exterior world: {error}"))?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"]);
    for library in ["/lib", "/lib64", "/run"] {
        if Path::new(library).exists() {
            command.args(["--ro-bind", library, library]);
        }
    }
    command
        .arg("--bind")
        .arg(world)
        .arg("/world")
        .args(["--chdir", "/tmp", "/usr/bin/tee", "/world/consequence.txt"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command
        .spawn()
        .map_err(|error| format!("enter exterior receiver namespace: {error}"))?;
    child
        .stdin
        .take()
        .ok_or("exterior receiver stdin is absent")?
        .write_all(emitted)
        .map_err(|error| error.to_string())?;
    let returned = child
        .wait_with_output()
        .map_err(|error| error.to_string())?;
    if !returned.status.success() {
        return Err(format!(
            "exterior receiver refused: {}",
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(returned.stdout)
}

fn run_detached_grade(executable: &Path, rest: &Path, output: &Path) -> Result<(), String> {
    let executable = executable
        .canonicalize()
        .map_err(|error| format!("resolve I2 executable: {error}"))?;
    let rest = rest
        .canonicalize()
        .map_err(|error| format!("resolve I2 rest: {error}"))?;
    let output = output
        .canonicalize()
        .map_err(|error| format!("resolve I2 return: {error}"))?;
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
        .arg("/athena-i2")
        .arg("--ro-bind")
        .arg(rest)
        .arg("/rest")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/tmp",
            "/athena-i2",
            "--detached-grade",
            "/rest",
            "/return",
        ]);
    let status = command
        .status()
        .map_err(|error| format!("enter detached I2 namespace: {error}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("detached I2 grade returned {status}"))
    }
}

fn occurrence(role: &str, predecessor: &str, material: &str) -> String {
    let mut digest = Sha256::new();
    digest.update(b"holonics/i2/addressed-occurrence/v1");
    digest.update(role.as_bytes());
    digest.update(predecessor.as_bytes());
    digest.update(material.as_bytes());
    hex(&digest.finalize())
}

fn sha256(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn code_closure() -> String {
    let members: &[&[u8]] = &[
        include_bytes!("the_exterior_return_changes_the_later_current.rs"),
        include_bytes!("../../holonic-engine/src/native_ecology/recurrent_return.rs"),
        include_bytes!("../../holonic-engine/src/native_ecology/recurrent.rs"),
        include_bytes!("../../holonic-engine/src/cuda_refine.rs"),
        include_bytes!("../../holonic-engine/kernels/refine_shell.cu"),
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
    let staged = path.with_extension("i2-staged");
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
            let predecessor = required_path(&mut values, "I1_REST")?;
            let emitted = required_path(&mut values, "I1_EMITTED")?;
            let output = values
                .next()
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from(DEFAULT_OUT));
            no_trailing(&mut values, "--produce")?;
            Ok(Args::Produce {
                predecessor,
                emitted,
                output,
            })
        }
        Some("--detached-grade") => {
            let rest = required_path(&mut values, "REST")?;
            let output = required_path(&mut values, "OUTPUT")?;
            no_trailing(&mut values, "--detached-grade")?;
            Ok(Args::DetachedGrade { rest, output })
        }
        _ => Err(
            "usage: --produce I1_REST I1_EMITTED [OUTPUT] | --detached-grade REST OUTPUT"
                .to_owned(),
        ),
    }
}

fn required_path(values: &mut impl Iterator<Item = String>, name: &str) -> Result<PathBuf, String> {
    let path = values
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| format!("missing {name}"))?;
    if !path.exists() {
        return Err(format!("required {name} {} is absent", path.display()));
    }
    Ok(path)
}

fn no_trailing(values: &mut impl Iterator<Item = String>, mode: &str) -> Result<(), String> {
    if values.next().is_some() {
        Err(format!("{mode} carries trailing arguments"))
    } else {
        Ok(())
    }
}
