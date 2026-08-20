//! W2: structural condensation of the complete W1 deed family.
//!
//! This is an exterior grader, not a second runtime.  It mounts only the authenticated W1 rest,
//! groups its source-operation occurrences by their declared deed, and asks the existing pure W2
//! owner whether the declared receiver family factors.  No source model, byte count, tensor norm,
//! or name-based byte quotient is consulted.

#[path = "phoenix/lifted_condensation.rs"]
mod lifted_condensation;

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::PathBuf;

use holonic_engine::native_rest::MountedNativeRest;
use holonic_engine::operation_correspondence::SourceOperationOccurrence;
use lifted_condensation::{
    CondensationInput, CondensationState, ReceiverSignature, SharingDeclaration, StructureKind,
    SuccessorSignature, condense,
};
use sha2::{Digest, Sha256};

const EXPECTED_DEEDS: usize = 45;

#[derive(Debug)]
struct Args {
    rest: PathBuf,
    h5_receipt: PathBuf,
    h5_equality: PathBuf,
    out: PathBuf,
}

fn args() -> Args {
    let mut result = Args {
        rest: PathBuf::from(
            "output/the_whole_foreign_map_crosses_into_native_rest/gemma_native_rest.bin",
        ),
        h5_receipt: PathBuf::from(
            "output/the_dissection_shares_its_prefixes/native-w1/receipt.form",
        ),
        h5_equality: PathBuf::from(
            "output/the_dissection_shares_its_prefixes/native-w1/equality-against-the-committed-artifact.tsv",
        ),
        out: PathBuf::from(
            "output/the_lifted_body_condenses_only_where_future_receivers_factor/condensation.json",
        ),
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--native-rest" => {
                result.rest = PathBuf::from(it.next().expect("--native-rest <path>"))
            }
            "--h5-receipt" => {
                result.h5_receipt = PathBuf::from(it.next().expect("--h5-receipt <path>"))
            }
            "--h5-equality" => {
                result.h5_equality = PathBuf::from(it.next().expect("--h5-equality <path>"))
            }
            "--out" => result.out = PathBuf::from(it.next().expect("--out <path>")),
            other => panic!("unknown argument {other}"),
        }
    }
    result
}

#[derive(Clone, Debug)]
struct ReceiverAtlas {
    receiver: ReceiverSignature,
    /// Exact ordinal ↔ full signature strings. The ordinal is only the finite receiver's
    /// observation; the atlas retains the complete reconstruction fibre and never hashes it.
    atlas: BTreeMap<u64, String>,
}

fn exact_receiver(name: &str, signatures: BTreeMap<String, String>) -> ReceiverAtlas {
    let mut unique = signatures.values().cloned().collect::<Vec<_>>();
    unique.sort();
    unique.dedup();
    let atlas = unique
        .into_iter()
        .enumerate()
        .map(|(ordinal, signature)| (ordinal as u64, signature))
        .collect::<BTreeMap<_, _>>();
    let reverse = atlas
        .iter()
        .map(|(ordinal, signature)| (signature, *ordinal))
        .collect::<BTreeMap<_, _>>();
    ReceiverAtlas {
        receiver: ReceiverSignature {
            name: name.to_owned(),
            values: signatures
                .into_iter()
                .map(|(state, signature)| (state, reverse[&signature]))
                .collect(),
        },
        atlas,
    }
}

fn state_order(deed: &str) -> usize {
    deed.strip_prefix("layer-")
        .and_then(|value| value.parse::<usize>().ok())
        .map_or(
            match deed {
                "final-boundary" => 42,
                "modality-vision" => 43,
                "modality-audio" => 44,
                _ => usize::MAX,
            },
            |layer| layer,
        )
}

fn grouped_states(
    operations: &[SourceOperationOccurrence],
) -> Result<Vec<CondensationState>, String> {
    let mut grouped = BTreeMap::<String, Vec<String>>::new();
    for operation in operations {
        grouped
            .entry(operation.deed.clone())
            .or_default()
            .push(operation.id.clone());
    }
    if grouped.len() != EXPECTED_DEEDS {
        return Err(format!(
            "W1 deed closure has {} groups, expected {EXPECTED_DEEDS}",
            grouped.len()
        ));
    }
    let mut rows = grouped
        .into_iter()
        .map(|(id, mut source_members)| {
            source_members.sort();
            CondensationState { id, source_members }
        })
        .collect::<Vec<_>>();
    rows.sort_by_key(|state| state_order(&state.id));
    if rows.iter().any(|state| state.source_members.is_empty()) {
        return Err("W1 contains an empty deed state".to_owned());
    }
    if rows
        .iter()
        .any(|state| state_order(&state.id) == usize::MAX)
    {
        return Err("W1 contains an unrecognized deed state".to_owned());
    }
    if rows
        .iter()
        .map(|state| state_order(&state.id))
        .collect::<BTreeSet<_>>()
        != (0..EXPECTED_DEEDS).collect()
    {
        return Err("W1 deed states do not form the 0..44 ordered family".to_owned());
    }
    Ok(rows)
}

fn h5_rows(path: &PathBuf) -> Result<(String, Vec<String>), String> {
    let text = fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))?;
    if !text
        .lines()
        .next()
        .is_some_and(|line| line.contains("native W1"))
        || !text.contains("source identity: native W1")
        || !text
            .contains("168 committed cells compared across the base line and 16 taxa; 0 drifted")
    {
        return Err(format!(
            "{} is not the authenticated native-W1 H5 receipt",
            path.display()
        ));
    }
    for evidence in [
        "Q/K contact permuted: matched true",
        "V/O transport permuted: matched true",
        "KV reuse (the reuse, not the weights): matched true",
    ] {
        if !text.contains(evidence) {
            return Err(format!("{} lacks H5 evidence {evidence:?}", path.display()));
        }
    }
    let rows = text
        .lines()
        .filter(|line| line.contains("shortest separating history"))
        .map(str::to_owned)
        .collect::<Vec<_>>();
    if rows.is_empty() {
        return Err(format!(
            "{} has no shortest-separation rows",
            path.display()
        ));
    }
    Ok((text, rows))
}

fn equality_rows(path: &PathBuf) -> Result<(usize, usize), String> {
    let text = fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))?;
    let mut lines = text.lines();
    let header = lines.next().unwrap_or_default();
    if header != "taxon\tcolumn\tcommitted\treturned\tverdict" {
        return Err(format!(
            "{} has no authenticated H5 equality header",
            path.display()
        ));
    }
    let mut unchanged = 0usize;
    let mut apparatus = 0usize;
    for line in lines.filter(|line| !line.trim().is_empty()) {
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 5 {
            return Err(format!("{} has malformed equality row", path.display()));
        }
        match fields[4] {
            "UNCHANGED" => unchanged += 1,
            "APPARATUS" => apparatus += 1,
            verdict => {
                return Err(format!(
                    "{} has unadmitted equality verdict {verdict:?}",
                    path.display()
                ));
            }
        }
    }
    if unchanged != 168 || apparatus != 1 {
        return Err(format!(
            "{} has {unchanged} UNCHANGED and {apparatus} APPARATUS rows; expected 168 and 1",
            path.display()
        ));
    }
    Ok((unchanged, apparatus))
}

fn matches_state(state: &str, row: &str) -> bool {
    match state {
        "final-boundary" => row.contains("potential section") || row.contains("output boundary"),
        "modality-vision" => row.contains("vision"),
        "modality-audio" => row.contains("audio"),
        _ => state
            .strip_prefix("layer-")
            .is_some_and(|layer| row.contains(&format!("layer {layer} "))),
    }
}

fn h5_receiver(states: &[CondensationState], rows: &[String]) -> ReceiverAtlas {
    let signatures = states
        .iter()
        .map(|state| {
            let material = rows
                .iter()
                .filter(|row| matches_state(&state.id, row))
                .map(String::as_str)
                .collect::<Vec<_>>();
            let signature = if material.is_empty() {
                "evidence=unexcited".to_owned()
            } else {
                material.join("|")
            };
            (state.id.clone(), signature)
        })
        .collect();
    exact_receiver("h5-shortest-separation-site-count", signatures)
}

fn structural_receivers(
    states: &[CondensationState],
    by_id: &BTreeMap<&str, &SourceOperationOccurrence>,
    rest: &MountedNativeRest,
) -> Result<Vec<ReceiverAtlas>, String> {
    let mut receivers = Vec::new();
    for (name, projection) in [
        ("source-authenticated-family", 0usize),
        ("source-authenticated-species", 1),
        ("source-authenticated-kv-role", 2),
        ("source-shape-port-class", 3),
    ] {
        let mut values = BTreeMap::new();
        for state in states {
            let mut pieces = Vec::new();
            for source_id in &state.source_members {
                let operation = by_id
                    .get(source_id.as_str())
                    .ok_or_else(|| format!("W1 source operation {source_id} is absent"))?;
                let piece = match projection {
                    0 => operation.family.clone(),
                    1 => format!("{:?}", operation.species),
                    2 => operation
                        .parameters
                        .get("kv_role")
                        .cloned()
                        .unwrap_or_else(|| "not-declared".to_owned()),
                    _ => {
                        let mut carrier_faces = Vec::new();
                        if let Some(carrier) = &operation.carrier {
                            let extent = rest
                                .population_extent(carrier)
                                .map_err(|error| format!("{carrier}: {error}"))?;
                            carrier_faces
                                .push(format!("dtype={};shape={:?}", extent.dtype, extent.shape));
                        }
                        format!(
                            "{};inputs={:?};outputs={:?}",
                            carrier_faces.join("|"),
                            operation.inputs,
                            operation.outputs
                        )
                    }
                };
                pieces.push(piece);
            }
            pieces.sort();
            values.insert(state.id.clone(), pieces.join("|"));
        }
        receivers.push(exact_receiver(name, values));
    }
    Ok(receivers)
}

fn tower_successor(states: &[CondensationState]) -> SuccessorSignature {
    let mut next = BTreeMap::new();
    for state in states {
        let order = state_order(&state.id);
        // The text tower's causal successor ends at its final boundary. Modalities are terminal
        // projection states, not a fabricated vision→audio serial path.
        if order < 42 {
            next.insert(state.id.clone(), states[order + 1].id.clone());
        }
    }
    SuccessorSignature {
        input: "tower-step".to_owned(),
        next,
    }
}

fn sharing(
    states: &[CondensationState],
    by_id: &BTreeMap<&str, &SourceOperationOccurrence>,
    receipt: &str,
) -> Result<Vec<SharingDeclaration>, String> {
    let layers = states
        .iter()
        .filter(|state| state.id.starts_with("layer-"))
        .map(|state| state.id.clone())
        .collect::<Vec<_>>();
    let selected = |state_predicate: &dyn Fn(&str) -> bool,
                    operation_names: &[&str]|
     -> Result<Vec<String>, String> {
        let selected_members = states
            .iter()
            .filter(|state| state_predicate(&state.id))
            .flat_map(|state| state.source_members.iter())
            .filter(|member| {
                by_id.get(member.as_str()).is_some_and(|operation| {
                    operation_names.contains(&operation.operation.as_str())
                })
            })
            .cloned()
            .collect::<Vec<_>>();
        Ok(selected_members)
    };
    let layer = |id: &str| id.starts_with("layer-");
    let qk_names = [
        "receiver projection",
        "receiver head rebase",
        "receiver chronology",
        "presented projection",
        "presented head rebase",
        "presented chronology",
        "contact and carried construction",
    ];
    let ov_names = [
        "carried projection",
        "carried head rebase, no gain",
        "contact and carried construction",
        "contact returns",
        "post-attention rebase",
    ];
    let producer_names = [
        "presented projection",
        "carried projection",
        "presented head rebase",
        "carried head rebase, no gain",
        "presented chronology",
    ];
    let shared_names = ["shared presented standing", "shared carried standing"];
    let qk = selected(&layer, &qk_names)?;
    let ov = selected(&layer, &ov_names)?;
    let sliding_states = |id: &str| {
        matches!(
            id,
            "layer-22"
                | "layer-24"
                | "layer-26"
                | "layer-28"
                | "layer-30"
                | "layer-32"
                | "layer-34"
                | "layer-36"
                | "layer-38"
                | "layer-40"
        )
    };
    let full_states = |id: &str| {
        matches!(
            id,
            "layer-23"
                | "layer-25"
                | "layer-27"
                | "layer-29"
                | "layer-31"
                | "layer-33"
                | "layer-35"
                | "layer-37"
                | "layer-39"
                | "layer-41"
        )
    };
    let sliding = selected(&sliding_states, &producer_names)?
        .into_iter()
        .chain(selected(
            &|id| sliding_states(id) && id != "layer-22",
            &shared_names,
        )?)
        .collect::<Vec<_>>();
    let full = selected(&full_states, &producer_names)?
        .into_iter()
        .chain(selected(
            &|id| full_states(id) && id != "layer-23",
            &shared_names,
        )?)
        .collect::<Vec<_>>();
    if qk.len() != 240 || ov.len() != 174 || sliding.len() != 23 || full.len() != 23 {
        return Err(format!(
            "W1 role selections drifted: QK {} (expected 240), OV {} (expected 174), KV sliding {} (expected 23), KV full {} (expected 23)",
            qk.len(),
            ov.len(),
            sliding.len(),
            full.len()
        ));
    }
    if !receipt.contains("Q/K contact permuted: matched true")
        || !receipt.contains("V/O transport permuted: matched true")
        || !receipt.contains("KV reuse (the reuse, not the weights): matched true")
    {
        return Err("H5 does not authenticate all QK/OV/KV sharing sites".to_owned());
    }
    Ok(vec![
        SharingDeclaration {
            family: "w1-layer-qk-family".to_owned(),
            kind: StructureKind::Qk,
            states: layers.clone(),
            source_members: qk,
        },
        SharingDeclaration {
            family: "w1-layer-ov-family".to_owned(),
            kind: StructureKind::Ov,
            states: layers.clone(),
            source_members: ov,
        },
        SharingDeclaration {
            family: "w1-layer-kv-family".to_owned(),
            kind: StructureKind::Kv,
            states: vec![
                "layer-22".to_owned(),
                "layer-24".to_owned(),
                "layer-26".to_owned(),
                "layer-28".to_owned(),
                "layer-30".to_owned(),
                "layer-32".to_owned(),
                "layer-34".to_owned(),
                "layer-36".to_owned(),
                "layer-38".to_owned(),
                "layer-40".to_owned(),
            ],
            source_members: sliding,
        },
        SharingDeclaration {
            family: "w1-layer-kv-full-family".to_owned(),
            kind: StructureKind::Kv,
            states: vec![
                "layer-23".to_owned(),
                "layer-25".to_owned(),
                "layer-27".to_owned(),
                "layer-29".to_owned(),
                "layer-31".to_owned(),
                "layer-33".to_owned(),
                "layer-35".to_owned(),
                "layer-37".to_owned(),
                "layer-39".to_owned(),
                "layer-41".to_owned(),
            ],
            source_members: full,
        },
    ])
}

fn write_receipts(
    out: &PathBuf,
    result: &lifted_condensation::CondensationResult,
    equality_counts: (usize, usize),
    receiver_atlases: &[ReceiverAtlas],
    state_cover: &serde_json::Value,
    successor: &BTreeMap<String, String>,
    lineage: &serde_json::Value,
) -> Result<(), String> {
    if let Some(parent) = out.parent() {
        fs::create_dir_all(parent).map_err(|error| error.to_string())?;
    }
    let json = serde_json::json!({
        "schema": result.schema,
        "source_operations": result.source_operations,
        "candidate_count": result.candidates.len(),
        "candidates": result.candidates,
        "reconstruction": result.reconstruction,
        "no_factor": result.no_factor,
        "open_source_operations": result.open_source_operations,
        "structures": result.structures,
        "state_source_member_cover": state_cover,
        "receiver_atlases": receiver_atlases.iter().map(|atlas| serde_json::json!({
            "name": atlas.receiver.name,
            "state_values": atlas.receiver.values,
            "ordinal_to_signature": atlas.atlas,
        })).collect::<Vec<_>>(),
        "successors": { "tower-step": successor },
        "h5_equality_unchanged": equality_counts.0,
        "h5_equality_apparatus": equality_counts.1,
        "lineage": lineage,
        "byte_factor": null,
    });
    fs::write(
        out,
        serde_json::to_vec_pretty(&json).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let tsv = out.with_extension("tsv");
    let mut text =
        String::from("candidate\tstatus\tfactorization_holds\tmembers\tconduct_blocks\n");
    for candidate in &result.candidates {
        text.push_str(&format!(
            "{}\t{:?}\t{}\t{}\t{}\n",
            candidate.members.join("+"),
            candidate.status,
            candidate.factorization.holds,
            candidate.members.len(),
            candidate.conduct_blocks.len()
        ));
    }
    fs::write(tsv, text).map_err(|error| error.to_string())
}

fn main() -> Result<(), String> {
    let args = args();
    let rest = MountedNativeRest::open(&args.rest).map_err(|error| error.to_string())?;
    let correspondence = rest.correspondence();
    correspondence
        .validate()
        .map_err(|error| error.to_string())?;
    let states = grouped_states(&correspondence.source_operations)?;
    let (h5_receipt, h5) = h5_rows(&args.h5_receipt)?;
    let equality_counts = equality_rows(&args.h5_equality)?;
    let by_id = correspondence
        .source_operations
        .iter()
        .map(|operation| (operation.id.as_str(), operation))
        .collect::<BTreeMap<_, _>>();
    let mut receiver_atlases = vec![h5_receiver(&states, &h5)];
    receiver_atlases.extend(structural_receivers(&states, &by_id, &rest)?);
    let receivers = receiver_atlases
        .iter()
        .map(|atlas| atlas.receiver.clone())
        .collect::<Vec<_>>();
    let sharing = sharing(&states, &by_id, &h5_receipt)?;
    let successor = tower_successor(&states);
    let state_cover = serde_json::json!(
        states
            .iter()
            .map(|state| serde_json::json!({
                "id": state.id,
                "source_members": state.source_members,
            }))
            .collect::<Vec<_>>()
    );
    let successor_map = successor.next.clone();
    let input = CondensationInput {
        seal: correspondence,
        states,
        receivers,
        successors: vec![successor],
        sharing,
    };
    let result = condense(input).map_err(|error| error.to_string())?;
    let h5_equality_bytes = fs::read(&args.h5_equality)
        .map_err(|error| format!("{}: {error}", args.h5_equality.display()))?;
    let lineage = serde_json::json!({
        "native_graph_keys": rest.graphs().iter().map(|graph| graph.key.as_str()).collect::<Vec<_>>(),
        "native_codebook_sha256": rest.codebook().codebook_sha256.as_str(),
        "foreign_source_content_sha256": rest.source().container_content_sha256.as_deref(),
        "h5_receipt_sha256": format!("{:x}", Sha256::digest(h5_receipt.as_bytes())),
        "h5_equality_sha256": format!("{:x}", Sha256::digest(&h5_equality_bytes)),
    });
    write_receipts(
        &args.out,
        &result,
        equality_counts,
        &receiver_atlases,
        &state_cover,
        &successor_map,
        &lineage,
    )?;
    println!(
        "W2 CONDENSATION RETURN: {} one-shot candidates, {} reconstruction fibres, {} no-factor remainders; no byte factor quoted",
        result.candidates.len(),
        result.reconstruction.len(),
        result.no_factor.len()
    );
    Ok(())
}
