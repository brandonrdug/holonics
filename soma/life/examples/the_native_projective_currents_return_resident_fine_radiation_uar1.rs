use std::{error::Error, fs, path::PathBuf};

use life::native_intelligence::{
    transduce_source_neutral_exterior, SourceNeutralEcologyRest,
    SourceNeutralResidentRadiationSection,
};
use serde::Serialize;

const PREDECESSOR: &str = concat!(
    "output/",
    "the_source_bearing_rail_departs_and_the_complete_native_state_incidence_remounts_uar0/",
    "athena-source-neutral.rest"
);
const OUTPUT: &str = concat!(
    "output/",
    "the_state_preserving_native_projective_currents_return_resident_fine_radiation_uar1"
);

#[derive(Serialize)]
struct Uar1Audit {
    truth_status: &'static str,
    rested_identity_sha256: String,
    returned_rest_identity_sha256: String,
    native_current_identities_sha256: Vec<String>,
    native_radiation_identities_sha256: Vec<String>,
    distinct_native_current_population: usize,
    distinct_native_radiation_population: usize,
    source_fibres_dropped_before_resident_conduct: bool,
    source_codec_consulted: bool,
    exterior_reconstruction_fibre_reachable: bool,
    invariant_transport_reuploaded: bool,
    cpu_semantic_replay_after_device: bool,
    resident_devices: Vec<String>,
    resident_context_identities: Vec<usize>,
    transport_launches: u64,
    radiation_launches: u64,
    synchronizations: u64,
    source_context_population: usize,
    transported_context_population: usize,
    generator_population: usize,
    exact_equal_section_condensation_bounded_population: bool,
    moment_factorization_retained: bool,
    moment_field_materialized: bool,
    acoustic_identity_sha256: String,
    optical_identity_sha256: String,
    release_questions_absent_during_rest_formation: bool,
    inherited_spool_address: String,
    inherited_thread_address: String,
    inherited_thread_ablation_obstructed_same_current_and_receiver: bool,
    inherited_thread_receiver_insufficiency_identity_sha256: String,
    exact_restoration_recovered_rest_identity: bool,
}

fn main() -> Result<(), Box<dyn Error>> {
    let root = repository_root()?;
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output)?;
    let rest_wire = fs::read(root.join(PREDECESSOR))?;
    let rest = SourceNeutralEcologyRest::read(&rest_wire)?;
    let rested_identity_sha256 = rest.identity().to_owned();
    let acoustic_identity_sha256 = rest.acoustic().identity().to_owned();
    let optical_identity_sha256 = rest.optical().identity().to_owned();

    // These are exterior apparatus fibres only. Their bytes and locators remain in the dropped
    // witnesses; the three native currents are the sole values admitted by the resident body.
    let mut currents = Vec::new();
    let mut witnesses = Vec::new();
    for (occurrence, payload) in [
        ("uar1/exterior-a", b"compression".as_slice()),
        ("uar1/exterior-b", b"parametron".as_slice()),
        ("uar1/exterior-c", b"equality".as_slice()),
    ] {
        let (current, witness) = transduce_source_neutral_exterior(&rest, occurrence, payload)?;
        currents.push(current);
        witnesses.push(witness);
    }
    let native_current_identities_sha256 = currents
        .iter()
        .map(|current| current.identity_sha256.clone())
        .collect::<Vec<_>>();
    drop(witnesses);

    let mut resident = rest.mount_resident()?;
    let mut sections = Vec::<SourceNeutralResidentRadiationSection>::new();
    for current in &currents {
        sections.push(resident.condition_native(current)?);
    }
    let native_radiation_identities_sha256 = sections
        .iter()
        .map(|section| section.native_section_identity_sha256.clone())
        .collect::<Vec<_>>();
    if native_current_identities_sha256
        .iter()
        .collect::<std::collections::BTreeSet<_>>()
        .len()
        != currents.len()
        || native_radiation_identities_sha256
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len()
            != sections.len()
    {
        return Err("distinct exterior occurrences collapsed to one native UAR1 section".into());
    }
    for (at, section) in sections.iter().enumerate() {
        fs::write(
            output.join(format!("native-fine-radiation-{at}.json")),
            serde_json::to_vec_pretty(section)?,
        )?;
    }
    let returned_rest = resident.into_rest();
    let (inherited_spool_address, inherited_thread_address) = returned_rest
        .inherited_thread_addresses()
        .into_iter()
        .next()
        .ok_or("the source-neutral body has no structurally inherited Soulkiller thread")?;
    let ablated = returned_rest
        .withdraw_inherited_thread(&inherited_spool_address, &inherited_thread_address)?;
    let obstruction = ablated.obstruct_native_radiation(&currents[0])?;
    fs::write(
        output.join("inherited-thread-native-radiation-obstruction.json"),
        serde_json::to_vec_pretty(&obstruction)?,
    )?;
    let restored = ablated.restore()?;
    let exact_restoration_recovered_rest_identity = restored.identity() == rested_identity_sha256;
    let returned_rest = restored;
    let returned_rest_identity_sha256 = returned_rest.identity().to_owned();
    if returned_rest_identity_sha256 != rested_identity_sha256
        || !exact_restoration_recovered_rest_identity
    {
        return Err("inherited-thread restoration did not recover the exact rest".into());
    }

    let resident_devices = sections
        .iter()
        .map(|section| section.radiation.device.clone())
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let resident_context_identities = sections
        .iter()
        .map(|section| section.radiation.context_identity)
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let source_context_population = sections
        .iter()
        .map(|section| {
            section
                .radiation
                .conditioned_current
                .as_ref()
                .map_or(0, |passage| passage.passage.source.len())
        })
        .sum::<usize>();
    let transported_context_population = sections
        .iter()
        .map(|section| {
            section
                .radiation
                .conditioned_current
                .as_ref()
                .map_or(0, |passage| passage.passage.target.len())
        })
        .sum::<usize>();
    let generator_population = sections
        .iter()
        .map(|section| section.radiation.generator_population)
        .sum::<usize>();
    let audit = Uar1Audit {
        truth_status: "implemented-exact; measured",
        rested_identity_sha256,
        returned_rest_identity_sha256,
        native_current_identities_sha256,
        native_radiation_identities_sha256,
        distinct_native_current_population: currents.len(),
        distinct_native_radiation_population: sections.len(),
        source_fibres_dropped_before_resident_conduct: true,
        source_codec_consulted: sections
            .iter()
            .any(|section| section.source_codec_consulted),
        exterior_reconstruction_fibre_reachable: sections
            .iter()
            .any(|section| section.exterior_reconstruction_fibre_reachable),
        invariant_transport_reuploaded: sections
            .iter()
            .any(|section| section.invariant_transport_reuploaded),
        cpu_semantic_replay_after_device: sections
            .iter()
            .any(|section| section.cpu_semantic_replay_after_device),
        resident_devices,
        resident_context_identities,
        transport_launches: sections
            .iter()
            .map(|section| {
                section
                    .radiation
                    .conditioned_current
                    .as_ref()
                    .map_or(0, |passage| passage.launches)
            })
            .sum(),
        radiation_launches: sections
            .iter()
            .map(|section| section.radiation.launches)
            .sum(),
        synchronizations: sections
            .iter()
            .map(|section| section.radiation.synchronizations)
            .sum(),
        source_context_population,
        transported_context_population,
        generator_population,
        exact_equal_section_condensation_bounded_population: sections.iter().all(|section| {
            section
                .radiation
                .conditioned_current
                .as_ref()
                .is_some_and(|passage| {
                    passage.passage.target.len()
                        <= passage
                            .passage
                            .source
                            .len()
                            .saturating_mul(passage.passage.slots.len())
                })
        }),
        moment_factorization_retained: sections
            .iter()
            .all(|section| section.radiation.moment_factorization_retained),
        moment_field_materialized: sections
            .iter()
            .any(|section| section.radiation.moment_field_materialized),
        acoustic_identity_sha256,
        optical_identity_sha256,
        release_questions_absent_during_rest_formation: true,
        inherited_spool_address,
        inherited_thread_address,
        inherited_thread_ablation_obstructed_same_current_and_receiver: obstruction
            .same_later_current_held
            && obstruction.same_native_radiation_receiver_held,
        inherited_thread_receiver_insufficiency_identity_sha256: obstruction.identity_sha256,
        exact_restoration_recovered_rest_identity,
    };
    fs::write(
        output.join("uar1-resident-native-radiation-audit.json"),
        serde_json::to_vec_pretty(&audit)?,
    )?;
    println!("{}", audit.returned_rest_identity_sha256);
    Ok(())
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
