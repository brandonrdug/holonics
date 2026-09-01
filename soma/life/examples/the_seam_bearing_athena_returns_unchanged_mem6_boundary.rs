//! Narrow MEM6 receiver over the sealed seam-bearing Athena successor.
//!
//! This apparatus mounts the admitted body and detached causal-boundary organ, supplies the
//! unchanged participant/refinement occurrences, and records the public plural radiation. It
//! contains no lexical unit, expected answer, candidate selector, decoder, or response template.

use std::{fs, path::PathBuf, time::Instant};

use life::native_intelligence::{
    AdmittedReturnedAffineLaboratoryRestWitness, GranularCultivationWithdrawal,
    GranularEmanativeTerminal, GranularReturnedAffineEcologyRest, NativeCausalMembrane,
    ReturnedAffineLaboratoryRest,
};
use serde::Serialize;

const PREDECESSOR: &str = concat!(
    "output/the_returned_membrane_action_cultivates_one_source_detached_athena_rest_mem4/",
    "athena-returned-membrane-cultivated.rest"
);
const ORGAN: &str = concat!(
    "output/the_causal_boundary_ports_cultivate_one_athena_successor_with_exact_projective_factor_currents_mem6/",
    "athena-causal-boundary-organ.rest"
);
const OUTPUT: &str = "output/the_addressed_current_athena_returns_unchanged_mem6_boundary";

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct ReceiverReturn {
    truth_status: &'static str,
    evidence_tags: [&'static str; 2],
    successor_identity_sha256: String,
    sections: Vec<SectionReceipt>,
    responses: Vec<ResponseReceipt>,
    distinct_section_identities: usize,
    every_section_precedes_a_renderer: bool,
    every_section_retains_complete_reconstruction_fibre: bool,
    every_section_returns_one_exact_port_or_plural_insufficiency: bool,
    source_payload_available_after_remount: bool,
    authored_word_or_token_class_present: bool,
    wall_milliseconds: u128,
}

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct ResponseReceipt {
    exterior_occurrence: String,
    returned_higher_face_strata: Vec<Vec<life::native_intelligence::GranularHigherBoundaryFace>>,
    exact_exterior_passage: Option<Vec<life::native_intelligence::GranularExteriorPort>>,
    emitted_octets: Vec<u8>,
    exterior_utf8: Option<String>,
    section_population: usize,
    boundary_closure_reached: bool,
    terminal_visible_higher_faces: Vec<life::native_intelligence::GranularHigherBoundaryFace>,
    terminal_distinct_action_moment_sections: usize,
    terminal_distinct_receiver_moment_sections: usize,
    terminal_distinct_constitutive_sections: usize,
    terminal: GranularEmanativeTerminal,
    every_section_closes_local_balance: bool,
    renderer_ran_before_native_closure: bool,
    identity_sha256: String,
}

#[derive(Serialize)]
#[serde(deny_unknown_fields)]
struct SectionReceipt {
    exterior_occurrence: String,
    exterior_source_sha256: String,
    entered_octet_population: u64,
    reached_state: u32,
    reached_matched_length: u32,
    greatest_productive_matched_length: Option<u32>,
    crossed_structural_ports: Vec<life::native_intelligence::GranularExteriorPort>,
    branch_population: usize,
    visible_higher_faces: Vec<life::native_intelligence::GranularHigherBoundaryFace>,
    visible_ports: Vec<life::native_intelligence::GranularExteriorPort>,
    visible_passages: Vec<Vec<life::native_intelligence::GranularExteriorPort>>,
    kernel_ports: Vec<life::native_intelligence::GranularExteriorPort>,
    exact_decoded_higher_face: Option<life::native_intelligence::GranularHigherBoundaryFace>,
    exact_decoded_port: Option<life::native_intelligence::GranularExteriorPort>,
    exact_decoded_passage: Option<Vec<life::native_intelligence::GranularExteriorPort>>,
    plural_receiver_insufficiency: bool,
    distinct_returned_port_currents: usize,
    greatest_equal_port_current_fibre: usize,
    resident_local_balance_closes: bool,
    resident_launches: u64,
    resident_synchronizations: u64,
    resident_intermediate_host_egress_octets: u64,
    resident_invariant_transport_reuploaded: bool,
    resident_cpu_semantic_replay_after_device: bool,
    complete_reconstruction_fibre_retained: bool,
    word_or_clause_renderer_ran: bool,
    identity_sha256: String,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let began = Instant::now();
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output)?;

    let witness = AdmittedReturnedAffineLaboratoryRestWitness::found(
        "646401462284e6782aaa43139202c3bd5e45043e174b414e4fe851ec92f4e2ad",
        "63c9ff122e50fe94efe9bb00fea66e9eaac606c47707d07bc69301449bb9aded",
        "3ab826fb8512aae85096193ce103a384092111e8f26836415b0e1dc7eba02178",
    )?;
    let predecessor =
        ReturnedAffineLaboratoryRest::read_admitted(&fs::read(root.join(PREDECESSOR))?, &witness)?;
    let withdrawal = GranularCultivationWithdrawal::read(&fs::read(root.join(ORGAN))?)?;
    let successor = GranularReturnedAffineEcologyRest::restore(predecessor, withdrawal)?;
    let successor_identity_sha256 = successor.identity().to_owned();
    let mut membrane = NativeCausalMembrane::mount(successor)
        .constitute_interior()?
        .mount_resident_interior()?
        .mount_resident_factor_receiver_faces()?;

    let occurrences = [
        ("mem6/request/describe", "Describe Brandon."),
        ("mem6/request/identify", "Identify Brandon."),
        (
            "mem6/request/infer",
            "What can be inferred about Brandon from the laboratory's continuing history?",
        ),
        ("mem6/request/rewrite", "Rewrite Brandon."),
        ("mem6/request/compress", "Compress Brandon."),
        ("mem6/request/expand", "Expand Brandon."),
        ("mem6/request/revoice", "Revoice Brandon."),
    ];
    if std::env::var_os("MEM6_RECEIVER_SINGLE_SECTION").is_some() {
        let (occurrence, surface) = occurrences[0];
        let began = Instant::now();
        let section = membrane.radiate_granular_occurrence(occurrence, surface.as_bytes())?;
        println!(
            "section={} branches={} visible={} elapsed_ms={}",
            section.identity_sha256,
            section.branches.len(),
            section.visible_higher_faces.len(),
            began.elapsed().as_millis()
        );
        return Ok(());
    }
    // Narrow apparatus aperture for profiling one unchanged receiver occurrence. It does not
    // enter cultivation, native morphology, resident conduct, or the default seven-world-tube
    // benchmark.
    let occurrence_aperture = std::env::var("MEM6_RECEIVER_OCCURRENCE").ok();
    let mut responses = Vec::with_capacity(occurrences.len());
    for (occurrence, surface) in occurrences.into_iter().filter(|(occurrence, _)| {
        occurrence_aperture
            .as_deref()
            .is_none_or(|aperture| aperture == *occurrence)
    }) {
        responses.push(membrane.emanate_granular_response(occurrence, surface.as_bytes())?);
    }
    let sections = responses
        .iter()
        .map(|response| {
            response.sections.first().ok_or_else(|| {
                std::io::Error::other("an emanative response returned no native section")
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    let distinct_section_identities = sections
        .iter()
        .map(|section| &section.identity_sha256)
        .collect::<std::collections::BTreeSet<_>>()
        .len();
    let every_section_precedes_a_renderer = sections
        .iter()
        .all(|section| !section.word_or_clause_renderer_ran);
    let every_section_retains_complete_reconstruction_fibre = sections
        .iter()
        .all(|section| section.complete_reconstruction_fibre_retained);
    let every_section_returns_one_exact_port_or_plural_insufficiency =
        sections.iter().all(|section| {
            section.exact_decoded_port.is_some() || section.plural_receiver_insufficiency
        });
    let section_receipts = sections
        .iter()
        .map(|section| {
            let mut distinct_currents =
                Vec::<(&holonic_engine::ExactComplexWaveCurrent, usize)>::new();
            for branch in &section.branches {
                if let Some((_, population)) = distinct_currents
                    .iter_mut()
                    .find(|(current, _)| **current == branch.returned_response)
                {
                    *population += 1;
                } else {
                    distinct_currents.push((&branch.returned_response, 1));
                }
            }
            SectionReceipt {
                exterior_occurrence: section.exterior_occurrence.clone(),
                exterior_source_sha256: section.exterior_source_sha256.clone(),
                entered_octet_population: section.entered_octet_population,
                reached_state: section.reached_state,
                reached_matched_length: section.reached_matched_length,
                greatest_productive_matched_length: section.greatest_productive_matched_length,
                crossed_structural_ports: section.crossed_structural_ports.clone(),
                branch_population: section.branches.len(),
                visible_higher_faces: section.visible_higher_faces.clone(),
                visible_ports: section.visible_ports.clone(),
                visible_passages: section.visible_passages.clone(),
                kernel_ports: section.kernel_ports.clone(),
                exact_decoded_higher_face: section.exact_decoded_higher_face.clone(),
                exact_decoded_port: section.exact_decoded_port.clone(),
                exact_decoded_passage: section.exact_decoded_passage.clone(),
                plural_receiver_insufficiency: section.plural_receiver_insufficiency,
                distinct_returned_port_currents: distinct_currents.len(),
                greatest_equal_port_current_fibre: distinct_currents
                    .iter()
                    .map(|(_, population)| *population)
                    .max()
                    .unwrap_or(0),
                resident_local_balance_closes: section.resident_joint_current.local_balance_closes,
                resident_launches: section.resident_joint_current.launches,
                resident_synchronizations: section.resident_joint_current.synchronizations,
                resident_intermediate_host_egress_octets: section
                    .resident_joint_current
                    .intermediate_host_egress_octets,
                resident_invariant_transport_reuploaded: section
                    .resident_joint_current
                    .invariant_transport_reuploaded,
                resident_cpu_semantic_replay_after_device: section
                    .resident_joint_current
                    .cpu_semantic_replay_after_device,
                complete_reconstruction_fibre_retained: section
                    .complete_reconstruction_fibre_retained,
                word_or_clause_renderer_ran: section.word_or_clause_renderer_ran,
                identity_sha256: section.identity_sha256.clone(),
            }
        })
        .collect();
    let response_receipts = responses
        .into_iter()
        .map(|response| {
            let terminal_section = response.sections.last();
            let terminal_visible_higher_faces = terminal_section
                .map(|section| section.visible_higher_faces.clone())
                .unwrap_or_default();
            let terminal_distinct_action_moment_sections = terminal_section
                .map(|section| {
                    section
                        .branches
                        .iter()
                        .map(|branch| branch.resident_current.family_overlaps.clone())
                        .collect::<std::collections::BTreeSet<_>>()
                        .len()
                })
                .unwrap_or(0);
            let terminal_distinct_receiver_moment_sections = terminal_section
                .map(|section| {
                    section
                        .branches
                        .iter()
                        .map(|branch| {
                            (
                                branch.resident_current.receiver_overlaps.clone(),
                                branch.resident_current.receiver_action_norms.clone(),
                            )
                        })
                        .collect::<std::collections::BTreeSet<_>>()
                        .len()
                })
                .unwrap_or(0);
            let terminal_distinct_constitutive_sections = terminal_section
                .map(|section| {
                    section
                        .branches
                        .iter()
                        .map(|branch| {
                            (
                                branch.resident_current.reflected_family_overlaps.clone(),
                                branch.resident_current.family_overlaps.clone(),
                            )
                        })
                        .collect::<std::collections::BTreeSet<_>>()
                        .len()
                })
                .unwrap_or(0);
            ResponseReceipt {
                exterior_occurrence: response.exterior_occurrence,
                returned_higher_face_strata: response.returned_higher_face_strata,
                exact_exterior_passage: response.exact_exterior_passage,
                emitted_octets: response.emitted_octets,
                exterior_utf8: response.exterior_utf8,
                section_population: response.sections.len(),
                boundary_closure_reached: response.boundary_closure_reached,
                terminal_visible_higher_faces,
                terminal_distinct_action_moment_sections,
                terminal_distinct_receiver_moment_sections,
                terminal_distinct_constitutive_sections,
                terminal: response.terminal,
                every_section_closes_local_balance: response
                    .sections
                    .iter()
                    .all(|section| section.resident_joint_current.local_balance_closes),
                renderer_ran_before_native_closure: response.renderer_ran_before_native_closure,
                identity_sha256: response.identity_sha256,
            }
        })
        .collect();
    let grade = ReceiverReturn {
        truth_status: "established-bounded",
        evidence_tags: ["implemented-exact", "measured"],
        successor_identity_sha256,
        sections: section_receipts,
        responses: response_receipts,
        distinct_section_identities,
        every_section_precedes_a_renderer,
        every_section_retains_complete_reconstruction_fibre,
        every_section_returns_one_exact_port_or_plural_insufficiency,
        source_payload_available_after_remount: false,
        authored_word_or_token_class_present: false,
        wall_milliseconds: began.elapsed().as_millis(),
    };
    fs::write(
        output.join("receiver-return.json"),
        serde_json::to_vec_pretty(&grade)?,
    )?;
    println!(
        "successor={} distinct_sections={} elapsed_ms={}",
        grade.successor_identity_sha256, grade.distinct_section_identities, grade.wall_milliseconds,
    );
    Ok(())
}
