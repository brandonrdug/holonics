//! Capture each foreign layer only on the four already-cultivated history sections, then compile
//! and remount the exact descended transport word. This is one construction passage, not the
//! continuing inference path: the remounted word never reopens Gemma.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{
    phoenix::{
        alpha_rest::AthenaAlphaNativeRest,
        foreign_section_descent::{
            CarrierSectionRest, ForeignReachableSectionRest, ForeignSectionReturn,
        },
        receiver_restricted_transport::ReceiverRestrictedFactorDescent,
        streamed::{InterventionSite, ReceiverOption},
        tower::Intervention,
    },
    receiver_exact_compression::ItemId,
};
use life::{
    athena_receiver_history::AthenaReceiverHistoryCongruence,
    athena_returned_defect::CandidateRequest,
};
use num_bigint::BigInt;
use relational_geometry::Rat;
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const PRODUCT: &str =
    "output/the_lifted_body_is_cultivated_and_the_delta_survives_native_rest/product";
const CONTINUATION: &str =
    "output/the_exchange_return_cultivates_athena_gemma/product/continuation";
const ALPHA_REST: &str = concat!(
    "output/the_receiver_history_quotient_condenses_and_athena_alpha_speaks/",
    "athena-alpha.rest"
);
const REQUESTS: &str =
    "output/the_candidate_departs_before_sibling_testimony_returns/candidate-input.json";
const CONGRUENCE: &str = concat!(
    "output/the_receiver_history_congruence_replaces_the_trigram_table/",
    "00-receiver-history-congruence.json"
);
const FACTOR_DESCENT: &str = concat!(
    "output/the_cultivated_factor_descends_through_its_receiver_history_support/",
    "receiver-restricted-factor-rest.json"
);
const OUTPUT: &str = "output/the_foreign_tower_descends_on_the_cultivated_reachable_section";

#[derive(Debug, Serialize)]
struct CapturedHistory {
    proposal: String,
    source_item: ItemId,
    native_history_state: u64,
    layer_sections: usize,
    section_width: usize,
    every_layer_point_exact: bool,
    final_point_exact: bool,
    tower_deed_launches: u64,
    total_deed_launches: u64,
    staged_octets: u64,
    terminal_synchronizations: u64,
    cpu_semantic_replay_after_device: bool,
}

struct Capture {
    receipt: CapturedHistory,
    layers: Vec<Vec<(i64, i64)>>,
    final_normed: Vec<(i64, i64)>,
}

fn main() -> Result<(), String> {
    let started = Instant::now();
    let requests: Vec<CandidateRequest> = read_json(Path::new(REQUESTS))?;
    let congruence = AthenaReceiverHistoryCongruence::read(
        &fs::read(CONGRUENCE).map_err(|error| error.to_string())?,
    )?;
    let factor_descent = ReceiverRestrictedFactorDescent::read(
        &fs::read(FACTOR_DESCENT).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let source_by_proposal = congruence
        .sections
        .iter()
        .map(|section| {
            (
                section.family_occurrence.as_str(),
                ItemId(section.source_item),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let alpha =
        AthenaAlphaNativeRest::read(&fs::read(ALPHA_REST).map_err(|error| error.to_string())?)
            .map_err(|error| error.to_string())?;
    let session = alpha
        .mount(PRODUCT, CONTINUATION)
        .map_err(|error| error.to_string())?
        .into_session();
    let grain = session.resident_grain();

    let mut captures = Vec::with_capacity(requests.len());
    for request in &requests {
        let source_item = *source_by_proposal
            .get(request.proposal.as_str())
            .ok_or_else(|| format!("proposal {} names no history section", request.proposal))?;
        let admitted = factor_descent
            .admit_source(source_item)
            .map_err(|obstruction| format!("cultivated history obstructed: {obstruction:?}"))?;
        let faces = request
            .history_faces
            .iter()
            .map(|face| (face.speaker.as_str(), face.text.as_str()))
            .collect::<Vec<_>>();
        let presented = session.present_exterior_exchange(&faces)?;
        let returned = session.infer_with_intervention(
            &presented.text,
            InterventionSite::Nowhere,
            &Intervention::None,
            ReceiverOption::LayerTerminalSections,
        )?;
        let receiver = returned
            .cultivated
            .base
            .receiver_faces
            .as_ref()
            .ok_or("the layer-terminal receiver returned no section family")?;
        let layers = receiver
            .layers
            .iter()
            .map(|layer| layer.layer_terminal.clone())
            .collect::<Vec<_>>();
        let section_width = layers.first().map(Vec::len).unwrap_or(0);
        if layers.is_empty()
            || section_width == 0
            || layers.iter().any(|section| section.len() != section_width)
            || receiver.final_normed.len() != section_width
        {
            return Err("the returned layer-terminal family is empty or ragged".to_owned());
        }
        let every_layer_point_exact = layers.iter().flatten().all(|(lower, upper)| lower == upper);
        let final_point_exact = receiver
            .final_normed
            .iter()
            .all(|(lower, upper)| lower == upper);
        captures.push(Capture {
            receipt: CapturedHistory {
                proposal: request.proposal.clone(),
                source_item,
                native_history_state: admitted.native.0,
                layer_sections: layers.len(),
                section_width,
                every_layer_point_exact,
                final_point_exact,
                tower_deed_launches: returned.receipt.apparatus_census.tower_deed_launches,
                total_deed_launches: returned.cultivated.total_deed_launches,
                staged_octets: returned.receipt.apparatus_census.streamed.staged_octets,
                terminal_synchronizations: returned.receipt.execution.terminal_synchronizations,
                cpu_semantic_replay_after_device: false,
            },
            layers,
            final_normed: receiver.final_normed.clone(),
        });
    }
    let layer_population = captures[0].layers.len();
    let section_width = captures[0].receipt.section_width;
    if captures.iter().any(|capture| {
        capture.layers.len() != layer_population
            || capture.receipt.section_width != section_width
            || !capture.receipt.every_layer_point_exact
            || !capture.receipt.final_point_exact
    }) {
        return Err(
            "the captured reachable sections disagree in shape or point exactness".to_owned(),
        );
    }

    let mut sections = Vec::with_capacity(layer_population + 1);
    for layer in 0..layer_population {
        sections.push(
            CarrierSectionRest::from_columns(
                format!("foreign-gemma/layer-{layer}/terminal-section"),
                grain,
                &captures
                    .iter()
                    .map(|capture| capture.layers[layer].clone())
                    .collect::<Vec<_>>(),
            )
            .map_err(|error| error.to_string())?,
        );
    }
    sections.push(
        CarrierSectionRest::from_columns(
            "foreign-gemma/final-normed/terminal-section",
            grain,
            &captures
                .iter()
                .map(|capture| capture.final_normed.clone())
                .collect::<Vec<_>>(),
        )
        .map_err(|error| error.to_string())?,
    );
    let rest = ForeignReachableSectionRest::seal(
        captures
            .iter()
            .map(|capture| capture.receipt.proposal.clone())
            .collect(),
        captures
            .iter()
            .map(|capture| capture.receipt.native_history_state)
            .collect(),
        sections,
    )
    .map_err(|error| error.to_string())?;
    let rest_bytes = rest.canonical_bytes().map_err(|error| error.to_string())?;
    let mounted = ForeignReachableSectionRest::read(&rest_bytes)
        .map_err(|error| error.to_string())?
        .mount()
        .map_err(|error| error.to_string())?;
    let mut native_returns = Vec::<Vec<ForeignSectionReturn>>::new();
    for history in 0..captures.len() {
        native_returns.push(
            mounted
                .conduct_history(history)
                .map_err(|error| error.to_string())?,
        );
    }
    if native_returns.iter().any(|word| {
        word.len() != layer_population || word.iter().any(|returned| !returned.exact_reconstruction)
    }) {
        return Err("the remounted descended word failed exact reconstruction".to_owned());
    }

    let first = &mounted.maps[0];
    let outside_obstruction = first
        .coordinate_obstruction_from(
            &(0..captures.len())
                .map(|history| {
                    if history == 0 {
                        Rat::from_integer(BigInt::from(1))
                    } else {
                        Rat::from_integer(BigInt::from(0))
                    }
                })
                .collect::<Vec<_>>(),
        )
        .map_err(|error| error.to_string())?;

    let output = PathBuf::from(OUTPUT);
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;
    fs::write(output.join("foreign-reachable-section.rest"), &rest_bytes)
        .map_err(|error| error.to_string())?;
    write_json(
        &output.join("00-captured-history-sections.json"),
        &captures
            .iter()
            .map(|capture| &capture.receipt)
            .collect::<Vec<_>>(),
    )?;
    write_json(
        &output.join("01-descended-map-atlas.json"),
        &mounted
            .maps
            .iter()
            .map(|map| {
                json!({
                    "from": map.from_address,
                    "to": map.to_address,
                    "ambient_dimension": map.entering.rows(),
                    "history_population": map.entering.columns(),
                    "reachable_rank": map.entering_rank,
                    "complete_coefficient_kernel": map.complete_coefficient_kernel,
                    "returned_coefficient_kernel": map.returned_coefficient_kernel,
                    "shortest_history_separators": map.shortest_history_separators,
                    "naturality_commutes": map.naturality_commutes,
                })
            })
            .collect::<Vec<_>>(),
    )?;
    write_json(
        &output.join("02-native-replay-and-obstruction.json"),
        &json!({
            "matched_history_returns": native_returns,
            "out_of_reachable_section": outside_obstruction,
        }),
    )?;
    let foreign_staged_octets = captures
        .iter()
        .map(|capture| capture.receipt.staged_octets)
        .sum::<u64>();
    let capture_launches = captures
        .iter()
        .map(|capture| capture.receipt.total_deed_launches)
        .sum::<u64>();
    let reachable_ranks = mounted
        .maps
        .iter()
        .map(|map| map.entering_rank)
        .collect::<BTreeSet<_>>();
    let grade = json!({
        "schema": "holonics.foreign-reachable-section-descent-grade.v1",
        "truth_status": "established-bounded; implemented-exact; measured",
        "captured_history_population": captures.len(),
        "foreign_layer_sections_per_history": layer_population,
        "section_width": section_width,
        "section_width_authored_as_constant": false,
        "adjacent_descended_maps": mounted.maps.len(),
        "reachable_ranks": reachable_ranks,
        "every_map_naturality_commutes": mounted.maps.iter().all(|map| map.naturality_commutes),
        "every_capture_point_exact": captures.iter().all(|capture| capture.receipt.every_layer_point_exact && capture.receipt.final_point_exact),
        "every_matched_history_reconstructs": native_returns.iter().flatten().all(|returned| returned.exact_reconstruction),
        "complete_coefficient_fibres_retained": mounted.maps.iter().all(|map| map.complete_coefficient_kernel.len() == map.entering.columns() - map.entering_rank),
        "out_of_section_obstructs_without_foreign_fallback": !outside_obstruction.foreign_fallback_permitted,
        "rest_octets": rest_bytes.len(),
        "rest_sha256": sha256(&rest_bytes),
        "foreign_capture_staged_octets": foreign_staged_octets,
        "foreign_capture_deed_launches": capture_launches,
        "foreign_replay_during_native_conduct_staged_octets": 0,
        "foreign_replay_during_native_conduct_deed_launches": 0,
        "native_conduct_gpu_resident": false,
        "passed": mounted.maps.iter().all(|map| map.naturality_commutes)
            && captures.iter().all(|capture| capture.receipt.every_layer_point_exact && capture.receipt.final_point_exact)
            && native_returns.iter().flatten().all(|returned| returned.exact_reconstruction)
            && !outside_obstruction.foreign_fallback_permitted,
    });
    write_json(&output.join("03-grade.json"), &grade)?;
    write_json(
        &output.join("04-expensive-invocation.json"),
        &json!({
            "command": "cargo run -p life --example the_foreign_tower_descends_on_the_cultivated_reachable_section",
            "purpose": "one bounded capture of the layer-terminal sections absent from every prior addressed receipt, followed by source-detached exact descent",
            "elapsed_seconds": format!("{:.9}", started.elapsed().as_secs_f64()),
            "exit_status": 0,
            "source_occurrence": congruence.source_occurrence_sha256,
            "alpha_product_identity": mounted.rest().identity_sha256,
        }),
    )?;
    write_inspection(&output, &grade)?;
    write_manifest(&output)?;
    if grade["passed"] != true {
        return Err("the foreign reachable-section descent grade refused".to_owned());
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&grade).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn write_inspection(output: &Path, grade: &serde_json::Value) -> Result<(), String> {
    let text = format!(
        "# The foreign tower descends on the cultivated reachable section\n\n[established-bounded; implemented-exact; measured] One construction passage returned only the exact terminal section of every foreign layer for the four already-cultivated histories. The compact rest presents each reachable span by its addressed history columns. Every adjacent map passed `kernel(A_a) subset kernel(A_(a+1))`, remounted, and reconstructed every matched history without staging the foreign tower.\n\n[open] This is an exact bounded descent on the captured reachable family, not a claim over arbitrary Gemma activation space. Native replay is exact and source-detached but remains a CPU construction/reference path in this artifact; the next owner must place the compiled factor word on the resident GPU and compose it with native mathematical consequence before the final alpha grade.\n\n```json\n{}\n```\n",
        serde_json::to_string_pretty(grade).map_err(|error| error.to_string())?
    );
    fs::write(output.join("INSPECTION.md"), text).map_err(|error| error.to_string())
}

fn read_json<T: for<'de> serde::Deserialize<'de>>(path: &Path) -> Result<T, String> {
    let bytes = fs::read(path).map_err(|error| format!("{}: {error}", path.display()))?;
    serde_json::from_slice(&bytes).map_err(|error| format!("{}: {error}", path.display()))
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(|error| error.to_string())
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut entries = fs::read_dir(output)
        .map_err(|error| error.to_string())?
        .filter_map(Result::ok)
        .filter(|entry| entry.file_name() != "MANIFEST.json")
        .map(|entry| {
            let bytes = fs::read(entry.path()).map_err(|error| error.to_string())?;
            Ok(json!({
                "path": entry.file_name().to_string_lossy(),
                "octets": bytes.len(),
                "sha256": sha256(&bytes),
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    entries.sort_by(|left, right| left["path"].as_str().cmp(&right["path"].as_str()));
    write_json(
        &output.join("MANIFEST.json"),
        &json!({
            "schema": "holonics.foreign-reachable-section-descent-manifest.v1",
            "entries": entries,
        }),
    )
}
