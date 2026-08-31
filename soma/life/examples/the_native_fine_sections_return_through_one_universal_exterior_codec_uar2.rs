use std::{
    collections::BTreeSet,
    env,
    error::Error,
    fs,
    path::PathBuf,
    time::{Duration, Instant},
};

use life::athena_native::{
    transduce_source_neutral_exterior, SourceNeutralAthenaRest, SourceNeutralExteriorRadiation,
    SourceNeutralExteriorRadiationTerminal, SourceNeutralExteriorStep,
};
use serde::Serialize;

const PREDECESSOR: &str = concat!(
    "output/",
    "the_source_bearing_rail_departs_and_the_complete_native_state_incidence_remounts_uar0/",
    "athena-source-neutral.rest"
);
const OUTPUT: &str = concat!(
    "output/",
    "the_sparse_relational_current_returns_native_fine_sections_through_one_universal_exterior_codec_uar2"
);

const RELEASE_QUESTIONS: [&str; 6] = [
    "How does holonic compression preserve what a future receiver can distinguish?",
    "How does a Complex Parametron carry current through a lattice?",
    "Why does equal output not establish equality of causal histories?",
    "Describe Brandon.",
    "Who is Brandon?",
    "What can be inferred about Brandon's role in this laboratory?",
];

#[derive(Serialize)]
struct Uar2Audit {
    truth_status: &'static str,
    rest_identity_sha256: String,
    exterior_occurrence_population: usize,
    native_current_identities_sha256: Vec<String>,
    exterior_radiation_identities_sha256: Vec<String>,
    emitted_surface_identities_sha256: Vec<String>,
    distinct_native_current_population: usize,
    distinct_exterior_radiation_population: usize,
    distinct_emitted_surface_population: usize,
    closure_population: usize,
    open_exterior_aperture_population: usize,
    recurrent_population: usize,
    plural_insufficiency_population: usize,
    receiver_radical_population: usize,
    receiver_history_source_population: Vec<usize>,
    receiver_history_native_population: Vec<usize>,
    receiver_history_first_separator_population: Vec<usize>,
    receiver_history_ordered_word_commutes: bool,
    resident_receiver_history_source_population: usize,
    resident_receiver_history_native_population: usize,
    resident_receiver_history_generator_population: usize,
    resident_receiver_history_fibre_population: usize,
    resident_receiver_history_first_separator_population: usize,
    resident_receiver_history_device_squares_commute: bool,
    resident_receiver_history_mounted_before_exterior_current: bool,
    resident_receiver_history_resident_octets: u64,
    structural_equality_used: bool,
    digest_equality_used: bool,
    complete_native_sections_retained: bool,
    fine_to_exterior_boundary_total: bool,
    exterior_to_fine_boundary_exact: bool,
    source_fibres_dropped_before_resident_conduct: bool,
    source_codec_consulted: bool,
    source_utterance_reachable: bool,
    source_witness_reachable: bool,
    invariant_transport_reuploaded: bool,
    cpu_semantic_replay_after_device: bool,
    reference_ecology_compared: bool,
    intermediate_joining_address_egress_octets: u64,
    intermediate_apparatus_shape_egress_octets: u64,
    intermediate_semantic_egress_octets: u64,
    terminal_semantic_egress_octets: u64,
    expected_answer_consulted: bool,
    candidate_search_performed: bool,
    authored_surface_extent_present: bool,
    resident_devices: Vec<String>,
}

fn main() -> Result<(), Box<dyn Error>> {
    let process_started = Instant::now();
    let process_aperture = Duration::from_secs(175);
    let freeze_control_front = env::var_os("HOLONICS_UAR2_CONTROL_FRONT").is_some();
    let root = repository_root()?;
    let output = env::var_os("HOLONICS_OUTPUT_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join(OUTPUT));
    fs::create_dir_all(&output)?;
    let rest_path = env::var_os("HOLONICS_UAR2_REST")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join(PREDECESSOR));
    let rest = SourceNeutralAthenaRest::read(&fs::read(rest_path)?)?;
    let rest_identity_sha256 = rest.identity().to_owned();
    let supplied = std::env::args().skip(1).collect::<Vec<_>>();
    let questions = if supplied.is_empty() {
        RELEASE_QUESTIONS
            .iter()
            .map(|question| (*question).to_owned())
            .collect::<Vec<_>>()
    } else {
        supplied
    };

    let mut currents = Vec::with_capacity(questions.len());
    let mut cold_witnesses = Vec::with_capacity(questions.len());
    for (at, question) in questions.iter().enumerate() {
        let (current, witness) = transduce_source_neutral_exterior(
            &rest,
            &format!("uar2/release/{at}"),
            question.as_bytes(),
        )?;
        currents.push(current);
        cold_witnesses.push(witness);
    }
    let native_current_identities_sha256 = currents
        .iter()
        .map(|current| current.identity_sha256.clone())
        .collect::<Vec<_>>();
    drop(cold_witnesses);
    drop(questions);

    let mut resident = Some(rest.mount_resident()?);
    let mut returns = Vec::<SourceNeutralExteriorRadiation>::with_capacity(currents.len());
    for (at, current) in currents.iter().enumerate() {
        let mounted = resident
            .take()
            .ok_or("the resident Athena body escaped its owner")?;
        let mut circulation = mounted.begin_native_exterior(current.clone())?;
        let mut prior_deed_elapsed = None::<Duration>;
        let returned = loop {
            let deed_started = Instant::now();
            match circulation.emit_next()? {
                SourceNeutralExteriorStep::Emission(pending) => {
                    let deed_elapsed = deed_started.elapsed();
                    let emission = pending.emission().clone();
                    // This write is the exterior realization boundary.  It occurs before the
                    // separately addressed return is admitted and contains no inference logic.
                    fs::write(
                        output.join(format!("emission-{at}-{}.json", emission.causal_order)),
                        serde_json::to_vec_pretty(&emission)?,
                    )?;
                    if freeze_control_front && emission.causal_order >= 1 {
                        let terminal = match pending.stop_at_exterior_aperture()? {
                            SourceNeutralExteriorStep::Terminal(terminal) => terminal,
                            SourceNeutralExteriorStep::Emission(_) => {
                                return Err(
                                    "a frozen control front returned another emission".into()
                                )
                            }
                        };
                        let (mounted, returned) = terminal.into_parts();
                        resident = Some(mounted);
                        break returned;
                    }
                    // Order zero includes the one-time resident native inference.  It is not a
                    // lawful duration estimate for the already-mounted local realization
                    // recurrence.  Begin the rolling reserve with the first post-mount deed;
                    // otherwise a completed mount is misread as if it had to recur before every
                    // emitted face and the apparatus always stops at its first byte.
                    let return_reserve = if emission.causal_order == 0 {
                        None
                    } else {
                        Some(prior_deed_elapsed.unwrap_or(deed_elapsed).max(deed_elapsed))
                    };
                    // The sole authored time is the roadmap's exterior apparatus aperture.  If
                    // another deed plus an equally costly return could cross it, preserve this
                    // already-published face as an exact open boundary instead of letting the
                    // outer process killer erase the continuing body.
                    if return_reserve.is_some_and(|return_reserve| {
                        process_started
                            .elapsed()
                            .saturating_add(return_reserve)
                            .saturating_add(return_reserve)
                            >= process_aperture
                    }) {
                        let terminal = match pending.stop_at_exterior_aperture()? {
                            SourceNeutralExteriorStep::Terminal(terminal) => terminal,
                            SourceNeutralExteriorStep::Emission(_) => {
                                return Err(
                                    "an open exterior aperture returned another emission".into()
                                )
                            }
                        };
                        let (mounted, returned) = terminal.into_parts();
                        resident = Some(mounted);
                        break returned;
                    }
                    let returned = pending.acknowledge_delivery(format!(
                        "uar2/release/{at}/delivery/{}",
                        emission.causal_order
                    ))?;
                    // Delivery testimony is independently observable before the returned local
                    // phase and factor section continue the boundary world-tube.  The emitted
                    // byte is never remounted as semantic ingress.
                    fs::write(
                        output.join(format!("return-{at}-{}.json", emission.causal_order)),
                        serde_json::to_vec_pretty(returned.returned())?,
                    )?;
                    circulation = returned.into_circulation();
                    if emission.causal_order > 0 {
                        prior_deed_elapsed = Some(deed_elapsed);
                    }
                }
                SourceNeutralExteriorStep::Terminal(terminal) => {
                    let (mounted, returned) = terminal.into_parts();
                    resident = Some(mounted);
                    break returned;
                }
            }
        };
        if let Some(surface) = &returned.codec_passage.exterior_utf8 {
            fs::write(output.join(format!("surface-{at}.txt")), surface.as_bytes())?;
        }
        // The complete native sections stay owned by the live return and are already committed by
        // their exact identities.  This exterior file records the codec passage, both returned
        // boundary fronts, the compact current world-line and the complete reconstruction-node
        // addresses;
        // it must not duplicate every resident coefficient and CUDA receipt at every causal
        // order.  The fine-section artifact is owned by UAR1, while this is the UAR2 passage
        // receipt over it.
        let passage_receipt = serde_json::json!({
            "schema": "soma-life.source-neutral-exterior-radiation-receipt.v4",
            "identity_sha256": &returned.identity_sha256,
            "native_sections": returned.native_sections.iter().map(|section| serde_json::json!({
                "native_section_identity_sha256": &section.native_section_identity_sha256,
                "boundary_front": &section.boundary_front,
                "phase_front_population": section.phase_front_higher_faces.len(),
                "situated_receiver_population": section.situated_receiver_higher_faces.len(),
                "complete_successor_population": section.complete_successor_addressed_faces.len(),
                "complete_successor_zero_face_population": section.complete_successor_zero_face_population,
                "source_address": section.radiation.conditioned_current.as_ref().map(|current| &current.source_address),
                "target_address": section.radiation.conditioned_current.as_ref().map(|current| &current.target_address),
                "reconstruction_node_addresses": section.reconstruction_dag.iter().map(|node| node.node).collect::<Vec<_>>(),
                "local_balance_closes": section.radiation.local_balance_closes,
            })).collect::<Vec<_>>(),
            "receiver_history": &returned.receiver_history,
            "resident_receiver_history": &returned.resident_receiver_history,
            "inference_returns": returned.inference_returns.iter().map(|inference_return| serde_json::json!({
                "causal_order": inference_return.causal_order,
                "emission_occurrence": &inference_return.emission_occurrence,
                "returned_occurrence": &inference_return.returned_occurrence,
                "returned_native_current_identity_sha256": &inference_return.returned_native_current_identity_sha256,
                "returned_current_descent_identity_sha256": &inference_return.returned_current_descent.identity_sha256,
                "joined_causal_order": inference_return.joined_causal_order,
                "joined_native_section_identity_sha256": &inference_return.joined_native_section_identity_sha256,
                "joined_conditioned_passage_identity_sha256": &inference_return.joined_conditioned_passage_identity_sha256,
            })).collect::<Vec<_>>(),
            "delivery_returns": &returned.delivery_returns,
            "codec_passage": &returned.codec_passage,
            "terminal": &returned.terminal,
        });
        fs::write(
            output.join(format!("native-exterior-return-{at}.json")),
            serde_json::to_vec_pretty(&passage_receipt)?,
        )?;
        returns.push(returned);
    }

    let exterior_radiation_identities_sha256 = returns
        .iter()
        .map(|returned| returned.identity_sha256.clone())
        .collect::<Vec<_>>();
    let emitted_surface_identities_sha256 = returns
        .iter()
        .map(|returned| sha256(&returned.codec_passage.emitted_octets))
        .collect::<Vec<_>>();
    let terminals = returns
        .iter()
        .map(|returned| &returned.terminal)
        .collect::<Vec<_>>();
    let audit = Uar2Audit {
        truth_status: "implemented-exact; measured",
        rest_identity_sha256,
        exterior_occurrence_population: returns.len(),
        distinct_native_current_population: native_current_identities_sha256
            .iter()
            .collect::<BTreeSet<_>>()
            .len(),
        distinct_exterior_radiation_population: exterior_radiation_identities_sha256
            .iter()
            .collect::<BTreeSet<_>>()
            .len(),
        distinct_emitted_surface_population: emitted_surface_identities_sha256
            .iter()
            .collect::<BTreeSet<_>>()
            .len(),
        native_current_identities_sha256,
        exterior_radiation_identities_sha256,
        emitted_surface_identities_sha256,
        closure_population: terminals
            .iter()
            .filter(|terminal| matches!(terminal, SourceNeutralExteriorRadiationTerminal::Closure))
            .count(),
        open_exterior_aperture_population: terminals
            .iter()
            .filter(|terminal| {
                matches!(
                    terminal,
                    SourceNeutralExteriorRadiationTerminal::OpenExteriorAperture { .. }
                )
            })
            .count(),
        recurrent_population: terminals
            .iter()
            .filter(|terminal| {
                matches!(
                    terminal,
                    SourceNeutralExteriorRadiationTerminal::RecurrentNativeSection { .. }
                )
            })
            .count(),
        plural_insufficiency_population: terminals
            .iter()
            .filter(|terminal| {
                matches!(
                    terminal,
                    SourceNeutralExteriorRadiationTerminal::PluralReceiverInsufficiency { .. }
                )
            })
            .count(),
        receiver_radical_population: terminals
            .iter()
            .filter(|terminal| {
                matches!(
                    terminal,
                    SourceNeutralExteriorRadiationTerminal::ReceiverRadical { .. }
                )
            })
            .count(),
        receiver_history_source_population: returns
            .iter()
            .map(|returned| {
                returned
                    .receiver_history
                    .compression
                    .source_population
                    .len()
            })
            .collect(),
        receiver_history_native_population: returns
            .iter()
            .map(|returned| {
                returned
                    .receiver_history
                    .compression
                    .native_population
                    .len()
            })
            .collect(),
        receiver_history_first_separator_population: returns
            .iter()
            .map(|returned| returned.receiver_history.compression.first_separators.len())
            .collect(),
        receiver_history_ordered_word_commutes: returns
            .iter()
            .all(|returned| returned.receiver_history.ordered_word.commutes()),
        resident_receiver_history_source_population: returns
            .first()
            .map(|returned| returned.resident_receiver_history.source_population)
            .unwrap_or(0),
        resident_receiver_history_native_population: returns
            .first()
            .map(|returned| returned.resident_receiver_history.native_population)
            .unwrap_or(0),
        resident_receiver_history_generator_population: returns
            .first()
            .map(|returned| returned.resident_receiver_history.generator_population)
            .unwrap_or(0),
        resident_receiver_history_fibre_population: returns
            .first()
            .map(|returned| {
                returned
                    .resident_receiver_history
                    .reconstruction_fibre_population
            })
            .unwrap_or(0),
        resident_receiver_history_first_separator_population: returns
            .first()
            .map(|returned| {
                returned
                    .resident_receiver_history
                    .first_separator_population
            })
            .unwrap_or(0),
        resident_receiver_history_device_squares_commute: returns.iter().all(|returned| {
            returned
                .resident_receiver_history
                .device_generator_squares_commute
                && returned
                    .resident_receiver_history
                    .device_reconstruction_fibres_commute
        }),
        resident_receiver_history_mounted_before_exterior_current: returns.iter().all(|returned| {
            returned
                .resident_receiver_history
                .mounted_before_exterior_current
        }),
        resident_receiver_history_resident_octets: returns
            .first()
            .map(|returned| returned.resident_receiver_history.resident_octets)
            .unwrap_or(0),
        structural_equality_used: returns
            .iter()
            .all(|returned| returned.receiver_history.structural_equality_used),
        digest_equality_used: returns
            .iter()
            .any(|returned| returned.receiver_history.digest_equality_used),
        complete_native_sections_retained: returns
            .iter()
            .all(|returned| returned.codec_passage.complete_native_sections_retained),
        fine_to_exterior_boundary_total: returns
            .iter()
            .all(|returned| returned.codec_passage.fine_to_exterior_boundary_total),
        exterior_to_fine_boundary_exact: returns
            .iter()
            .all(|returned| returned.codec_passage.exterior_to_fine_boundary_exact),
        source_fibres_dropped_before_resident_conduct: true,
        source_codec_consulted: returns
            .iter()
            .any(|returned| returned.codec_passage.source_codec_consulted),
        source_utterance_reachable: returns
            .iter()
            .any(|returned| returned.codec_passage.source_utterance_reachable),
        source_witness_reachable: returns
            .iter()
            .any(|returned| returned.codec_passage.source_witness_reachable),
        invariant_transport_reuploaded: returns.iter().any(|returned| {
            returned
                .native_sections
                .iter()
                .any(|section| section.invariant_transport_reuploaded)
        }),
        cpu_semantic_replay_after_device: returns.iter().any(|returned| {
            returned
                .native_sections
                .iter()
                .any(|section| section.cpu_semantic_replay_after_device)
        }),
        reference_ecology_compared: false,
        intermediate_joining_address_egress_octets: returns
            .iter()
            .flat_map(|returned| &returned.native_sections)
            .filter_map(|section| section.radiation.conditioned_current.as_ref())
            .map(|passage| passage.intermediate_joining_address_egress_octets)
            .sum(),
        intermediate_apparatus_shape_egress_octets: returns
            .iter()
            .flat_map(|returned| &returned.native_sections)
            .filter_map(|section| section.radiation.conditioned_current.as_ref())
            .map(|passage| passage.intermediate_apparatus_shape_egress_octets)
            .sum(),
        intermediate_semantic_egress_octets: returns
            .iter()
            .flat_map(|returned| &returned.native_sections)
            .filter_map(|section| section.radiation.conditioned_current.as_ref())
            .map(|passage| passage.intermediate_semantic_egress_octets)
            .sum(),
        terminal_semantic_egress_octets: returns
            .iter()
            .flat_map(|returned| &returned.native_sections)
            .filter_map(|section| section.radiation.conditioned_current.as_ref())
            .map(|passage| passage.terminal_semantic_egress_octets)
            .sum(),
        expected_answer_consulted: false,
        candidate_search_performed: false,
        authored_surface_extent_present: false,
        resident_devices: returns
            .iter()
            .flat_map(|returned| {
                returned
                    .native_sections
                    .iter()
                    .map(|section| section.radiation.device.clone())
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect(),
    };
    fs::write(
        output.join("uar2-native-exterior-codec-audit.json"),
        serde_json::to_vec_pretty(&audit)?,
    )?;
    println!("{}", serde_json::to_string(&audit)?);
    Ok(())
}

fn sha256(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};

    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn repository_root() -> Result<PathBuf, Box<dyn Error>> {
    let mut root = std::env::current_dir()?;
    while !root.join("Cargo.toml").is_file() || !root.join("blueprint/THE_ROADMAP.md").is_file() {
        if !root.pop() {
            return Err("repository root was not found".into());
        }
    }
    Ok(root)
}
