//! Descend the twelve addressed coefficient occurrences through Athena's own receiver/history
//! family. The complete foreign carrier quotient remains reconstruction testimony and never enters
//! the native class key.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    native_anatomy::NativeAnatomyRest,
    phoenix::{
        foreign_potential_rest::ForeignPotentialComplexRest,
        foreign_section_descent::ForeignReachableSectionRest,
        receiver_restricted_transport::{AnatomicalOccurrence, NativeAnatomyDescentReturn},
    },
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const SECTION: &str = concat!(
    "output/the_second_emitted_frontier_grows_the_parametron_coefficient_lattice/",
    "expanded-reachable-section.rest"
);
const POTENTIAL: &str = concat!(
    "output/the_second_successor_receiver_and_support_faces_glue_",
    "the_twelve_node_parametron/expanded-potential.rest"
);
const FIRST_SUPPORT: &str = concat!(
    "output/the_eight_node_parametron_rest_returns_athena_alpha/product/successor/",
    "support-passage.json"
);
const SECOND_SUPPORT: &str = concat!(
    "output/the_twelve_node_parametron_rest_returns_athena_alpha/product/successor/",
    "support-passage.json"
);
const INTERVENTION: &str =
    "output/the_factor_complex_changes_the_same_body/08-composite-grade.json";
const OUTPUT: &str = "output/the_foreign_receiver_descends_into_athena_native_anatomy_k1";

/// Historical support testimony is read as exterior evidence. It is not remounted as the current
/// native schema and no compatibility route is installed in the engine.
#[derive(Debug, Deserialize)]
struct SupportEvidence {
    occurrences: Vec<SupportOccurrenceEvidence>,
}

#[derive(Debug, Deserialize)]
struct SupportOccurrenceEvidence {
    occurrence: String,
    predecessor_occurrence: String,
    realization_addresses: BTreeSet<String>,
}

#[derive(Debug, Serialize)]
struct FileReceipt {
    octets: u64,
    sha256: String,
}

fn main() -> Result<(), String> {
    let output = PathBuf::from(OUTPUT);
    if output.exists() {
        return Err(format!(
            "preserve existing station output {}",
            output.display()
        ));
    }
    let started = Instant::now();
    let section =
        ForeignReachableSectionRest::read(&fs::read(SECTION).map_err(display)?).map_err(display)?;
    let foreign = section.coefficient_receiver_quotient().map_err(display)?;
    let potential = ForeignPotentialComplexRest::read(&fs::read(POTENTIAL).map_err(display)?)
        .map_err(display)?;
    if section.history_addresses != potential.history_addresses
        || section.native_history_states != potential.native_history_states
        || potential.receiver_certificates.len() != section.history_addresses.len()
    {
        return Err("foreign section and terminal potential do not share one lineage".to_owned());
    }

    let first: SupportEvidence = read_json(Path::new(FIRST_SUPPORT))?;
    let second: SupportEvidence = read_json(Path::new(SECOND_SUPPORT))?;
    let mut support_by_occurrence = BTreeMap::<String, BTreeSet<String>>::new();
    for carried in first.occurrences.iter().chain(&second.occurrences) {
        insert_equal(
            &mut support_by_occurrence,
            carried.occurrence.clone(),
            carried.realization_addresses.clone(),
        )?;
        insert_equal(
            &mut support_by_occurrence,
            carried.predecessor_occurrence.clone(),
            carried.realization_addresses.clone(),
        )?;
    }

    let occurrences = section
        .history_addresses
        .iter()
        .enumerate()
        .map(|(node, occurrence)| {
            let certificate = &potential.receiver_certificates[node];
            let [emitted_native_address] =
                certificate.cultivated_selected_native_addresses.as_slice()
            else {
                return Err(format!(
                    "occurrence {occurrence} has an unresolved terminal receiver fibre"
                ));
            };
            if certificate.history_address != *occurrence
                || certificate.native_history_state != section.native_history_states[node]
            {
                return Err("terminal certificate left its addressed occurrence".to_owned());
            }
            Ok(AnatomicalOccurrence {
                occurrence: occurrence.clone(),
                predecessor_occurrence: predecessor(occurrence),
                coefficient_node: node,
                inherited_history_state: section.native_history_states[node],
                foreign_receiver_class: foreign.history_to_class[node],
                emitted_native_address: *emitted_native_address,
                emitted_surface: potential
                    .decode(*emitted_native_address)
                    .map_err(display)?
                    .to_owned(),
                realization_addresses: support_by_occurrence.get(occurrence).cloned().ok_or_else(
                    || format!("occurrence {occurrence} has no returned support face"),
                )?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;

    let mut card = CudaRefineExecutor::new().map_err(display)?;
    let descent = NativeAnatomyDescentReturn::found_on_device(occurrences, &foreign, &mut card)
        .map_err(display)?;
    let anatomy = descent.native;
    let exterior = descent.exterior;
    let bytes = anatomy.canonical_bytes().map_err(display)?;
    let exterior_bytes = exterior.canonical_bytes(&anatomy).map_err(display)?;
    let remounted = NativeAnatomyRest::read(&bytes).map_err(display)?;
    if remounted != anatomy {
        return Err("source-detached anatomical rest changed during remount".to_owned());
    }

    let intervention: Value = read_json(Path::new(INTERVENTION))?;
    let repetition_caustics = exterior
        .classes
        .iter()
        .filter(|class| class.successor_classes.contains(&class.native))
        .map(|class| {
            json!({
                "native":class.native.0,
                "surface":class.emitted_surface,
                "occurrences":class.occurrences,
            })
        })
        .collect::<Vec<_>>();
    let anatomy_atlas = json!({
        "schema":"holonics.athena-native-anatomy-atlas.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "native_classes":anatomy.classes,
        "exterior_classes":exterior.classes,
        "foreign_to_native":exterior.foreign_to_native,
        "foreign_only_distinctions":exterior.foreign_only_distinctions,
        "analogous_sections":exterior.analogous_sections,
        "homologous_sections":exterior.homologous_sections,
        "receivers":exterior.receivers,
        "partial_successor_squares":exterior.quotient.generators,
        "pathology":{
            "foreign_identity_overreach":exterior.foreign_only_distinctions,
            "repetition_caustics":repetition_caustics,
            "malignant_morphology_witnesses":[],
            "malignancy_not_inferred_from_activation_or_coordinate_difference":true,
        },
        "intervention_testimony":{
            "source":INTERVENTION,
            "passed":intervention["passed"],
            "same_non_cloned_product_session":intervention["same_non_cloned_product_session"],
            "targeted_ablation_returned":intervention["targeted_ablation_returned"],
            "exact_ordered_prefix_withdrawal_returned":intervention["exact_ordered_prefix_withdrawal_returned"],
            "path_ordered_holonomy_returned":intervention["path_ordered_holonomy_returned"],
            "disjoint_interchange_returned":intervention["disjoint_interchange_returned"],
        },
        "apparatus":exterior.apparatus,
    });
    let native_classes = anatomy.native_population.len();
    let foreign_classes = foreign.classes.len();
    let exact_foreign_factor = exterior.foreign_to_native.len() == foreign_classes;
    let passed = native_classes < foreign_classes
        && exact_foreign_factor
        && !exterior.foreign_only_distinctions.is_empty()
        && exterior
            .classes
            .iter()
            .all(|class| !class.occurrences.is_empty())
        && exterior.apparatus.cpu_device_partition_equal
        && !exterior.apparatus.cpu_semantic_replay_after_device
        && intervention["targeted_ablation_returned"] == true
        && intervention["exact_ordered_prefix_withdrawal_returned"] == true;
    let grade = json!({
        "schema":"holonics.foreign-receiver-to-native-anatomy-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "addressed_occurrence_population":exterior.occurrences.len(),
        "foreign_carrier_class_population":foreign_classes,
        "native_anatomy_class_population":native_classes,
        "foreign_coordinate_classes_determine_native_population":false,
        "foreign_to_native_factor_is_functional_and_complete":exact_foreign_factor,
        "foreign_only_distinction_population":exterior.foreign_only_distinctions.len(),
        "complete_native_occurrence_fibres":exterior.classes.iter().map(|class| class.occurrences.len()).collect::<Vec<_>>(),
        "partial_successor_generator_population":exterior.quotient.generators.len(),
        "analogous_pair_population":exterior.analogous_sections.len(),
        "homologous_pair_population":exterior.homologous_sections.len(),
        "repetition_caustic_population":repetition_caustics.len(),
        "resident_device":exterior.apparatus.device,
        "resident_quotient_launches":exterior.apparatus.launches,
        "cpu_semantic_replay_after_device":false,
        "native_anatomy_rest_octets":bytes.len(),
        "native_anatomy_rest_sha256":sha(&bytes),
        "exterior_anatomy_witness_octets":exterior_bytes.len(),
        "exterior_anatomy_witness_sha256":sha(&exterior_bytes),
        "foreign_tower_staged_octets":0,
        "foreign_tower_deed_launches":0,
    });

    fs::create_dir_all(&output).map_err(display)?;
    fs::write(output.join("native-anatomy.rest"), &bytes).map_err(display)?;
    fs::write(output.join("exterior-anatomy.witness"), &exterior_bytes).map_err(display)?;
    write_json(output.join("00-anatomy-atlas.json"), &anatomy_atlas)?;
    write_json(output.join("01-grade.json"), &grade)?;
    write_json(
        output.join("02-expensive-invocation.json"),
        &json!({
            "schema":"holonics.expensive-invocation.v1",
            "command":"cargo run --release -p life --example the_foreign_receiver_descends_into_athena_native_anatomy",
            "purpose":"found the resident exact native anatomical quotient and the foreign-to-native reconstruction map over the existing twelve addressed occurrences",
            "elapsed_seconds":format!("{:.9}",started.elapsed().as_secs_f64()),
            "exit_status":if passed {0} else {1},
            "foreign_capture_replayed":false,
        }),
    )?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# The foreign receiver descends into Athena native anatomy\n\n[established-bounded; implemented-exact; measured] The twelve addressed occurrences descended from {foreign_classes} foreign-carrier classes into {native_classes} native receiver/history classes. The complete foreign distinctions remain reconstruction testimony; they did not enter the native class key. Resident and exact reference quotients agreed, partial termini remained explicit, and the prior same-body ablation/withdrawal testimony was attached without replaying the foreign organ.\n\n```json\n{}\n```\n",
            serde_json::to_string_pretty(&grade).map_err(display)?
        ),
    )
    .map_err(display)?;
    write_manifest(&output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("the native-anatomy grade refused".to_owned())
    }
}

fn predecessor(occurrence: &str) -> Option<String> {
    occurrence
        .rsplit_once("/emission/")
        .map(|(predecessor, _)| predecessor.to_owned())
}

fn insert_equal(
    standing: &mut BTreeMap<String, BTreeSet<String>>,
    occurrence: String,
    support: BTreeSet<String>,
) -> Result<(), String> {
    if let Some(existing) = standing.insert(occurrence.clone(), support.clone()) {
        if existing != support {
            return Err(format!(
                "support changed without a returned passage at {occurrence}"
            ));
        }
    }
    Ok(())
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(display)?).map_err(display)
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut files = BTreeMap::new();
    for entry in fs::read_dir(output).map_err(display)? {
        let entry = entry.map_err(display)?;
        if entry.file_type().map_err(display)?.is_file() && entry.file_name() != "MANIFEST.json" {
            let bytes = fs::read(entry.path()).map_err(display)?;
            files.insert(
                entry.file_name().to_string_lossy().into_owned(),
                FileReceipt {
                    octets: bytes.len() as u64,
                    sha256: sha(&bytes),
                },
            );
        }
    }
    write_json(
        output.join("MANIFEST.json"),
        &json!({
            "schema":"holonics.output-manifest.v1",
            "files":files,
        }),
    )
}

fn sha(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
