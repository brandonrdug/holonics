use std::{error::Error, fs, path::PathBuf};

use life::athena_native::{
    sever_source_bearing_athena_rest, transduce_source_neutral_exterior, SourceNeutralAthenaRest,
    SourceNeutralSeveringReceipt,
};
use serde::Serialize;

const PREDECESSOR: &str = concat!(
    "output/",
    "the_one_athena_alpha_body_circulates_every_admitted_organ_and_cultivates_alp4/",
    "athena-sens6-cultivated.rest"
);
const OUTPUT: &str = concat!(
    "output/",
    "the_source_bearing_rail_departs_and_the_complete_native_state_incidence_remounts_uar0"
);

#[derive(Serialize)]
struct SourceAbsenceAudit {
    truth_status: &'static str,
    predecessor_wire_octets: usize,
    successor_wire_octets: usize,
    successor_to_predecessor_per_million: u64,
    predecessor_identity_sha256: String,
    successor_identity_sha256: String,
    remounted_identity_sha256: String,
    forbidden_octet_sequences: Vec<String>,
    forbidden_sequence_hits: Vec<u64>,
    source_surface_atlas_reachable: bool,
    source_codec_reachable: bool,
    source_clause_decoder_reachable: bool,
    cold_witness_absent_during_remount: bool,
    hot_rest_contains_only_native_ecology_and_reusable_organs: bool,
    renamed_exterior_occurrences_return_same_native_current: bool,
    renamed_exterior_occurrences_retain_distinct_cold_fibres: bool,
    exterior_fibres_dropped_before_hot_conduct: bool,
    detached_remount_returns_native_conduct: bool,
    hot_rest_identity_unchanged_by_transient_conduct: bool,
    native_current_identity_sha256: String,
    native_conduct_identity_sha256: String,
    source_neutral_relational_identity_sha256: String,
    source_neutral_relational_face_population: usize,
    source_neutral_relational_cell_population: usize,
    causal_grain_population: usize,
    boundary_port_population: usize,
}

fn main() -> Result<(), Box<dyn Error>> {
    let root = repository_root()?;
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output)?;
    if std::env::var_os("HOLONICS_UAR0_VERIFY_EXISTING").is_some() {
        return verify_existing_successor(&root, &output);
    }
    let predecessor_wire = fs::read(root.join(PREDECESSOR))?;
    eprintln!(
        "uar0-stage=predecessor-read octets={}",
        predecessor_wire.len()
    );
    let predecessor_wire_octets = u64::try_from(predecessor_wire.len())?;
    let (successor, witness, receipt) = sever_source_bearing_athena_rest(&predecessor_wire)?;
    eprintln!("uar0-stage=source-severed");
    let predecessor_identity_sha256 = receipt.predecessor_rest_identity_sha256.clone();
    let successor_wire = successor.canonical_bytes()?;
    eprintln!(
        "uar0-stage=successor-serialized octets={}",
        successor_wire.len()
    );
    let successor_identity_sha256 = successor.identity().to_owned();
    let witness_wire = witness.canonical_bytes()?;

    fs::write(output.join("athena-source-neutral.rest"), &successor_wire)?;
    fs::write(
        output.join("exterior-relational-witness.json"),
        witness_wire,
    )?;
    fs::write(
        output.join("source-neutral-severing-receipt.json"),
        serde_json::to_vec_pretty(&receipt)?,
    )?;

    // The cold witness and contaminated predecessor are not supplied to this remount.
    drop(predecessor_wire);
    drop(witness);
    let remounted = SourceNeutralAthenaRest::read(&successor_wire)?;
    eprintln!("uar0-stage=successor-remounted");
    let forbidden = [
        "Brandon",
        "surface_variants",
        "founding_delivery_order",
        "founding_clause_order",
        "NativeRelationalCodec",
        "source_occurrence_identity_sha256",
        "occurrence_population_identity_sha256",
        "source_action_identity_sha256",
        "source_square_identity_sha256",
        "material_occurrence_population",
        "material_octet_population",
        "material_port_population",
        "predecessor_wire_sha256",
        "ExteriorParticipantReceiverChart",
        "ExteriorRelationReceiverChart",
        "soma-life.native-relational-codec",
    ];
    let hits = occurrence_populations(&successor_wire, &forbidden.map(str::as_bytes));
    if hits.iter().any(|hits| *hits != 0)
        || remounted.identity() != successor_identity_sha256
        || remounted.acoustic().ordered_ports() != remounted.optical().ordered_ports()
    {
        return Err("the detached native remount retained a forbidden developmental face".into());
    }
    let (native_left, exterior_left) =
        transduce_source_neutral_exterior(&remounted, "exterior-apparatus/left", b"a")?;
    let (native_right, exterior_right) =
        transduce_source_neutral_exterior(&remounted, "exterior-apparatus/right", b"a")?;
    let renamed_exterior_occurrences_return_same_native_current = native_left == native_right;
    let renamed_exterior_occurrences_retain_distinct_cold_fibres =
        exterior_left.identity_sha256 != exterior_right.identity_sha256;
    let native_current_identity_sha256 = native_left.identity_sha256.clone();
    drop(exterior_left);
    drop(exterior_right);
    let rest_identity_before_conduct = remounted.identity().to_owned();
    let mut resident = remounted.mount_resident()?;
    eprintln!("uar0-stage=first-resident-mounted");
    let native_conduct = resident.condition_native(&native_left)?;
    let remounted = resident.into_rest();
    if !renamed_exterior_occurrences_return_same_native_current
        || !renamed_exterior_occurrences_retain_distinct_cold_fibres
        || remounted.identity() != rest_identity_before_conduct
    {
        return Err(
            "the source-neutral quotient depended on an exterior locator or changed hot rest"
                .into(),
        );
    }
    let ratio = u64::try_from(successor_wire.len())?
        .checked_mul(1_000_000)
        .and_then(|scaled| scaled.checked_div(predecessor_wire_octets))
        .ok_or("wire ratio overflow")?;
    let audit = SourceAbsenceAudit {
        truth_status: "implemented-exact; measured",
        predecessor_wire_octets: usize::try_from(predecessor_wire_octets)?,
        successor_wire_octets: successor_wire.len(),
        successor_to_predecessor_per_million: ratio,
        predecessor_identity_sha256,
        successor_identity_sha256: successor_identity_sha256.clone(),
        remounted_identity_sha256: remounted.identity().to_owned(),
        forbidden_octet_sequences: forbidden.iter().map(|value| (*value).to_owned()).collect(),
        forbidden_sequence_hits: hits,
        source_surface_atlas_reachable: false,
        source_codec_reachable: false,
        source_clause_decoder_reachable: false,
        cold_witness_absent_during_remount: true,
        hot_rest_contains_only_native_ecology_and_reusable_organs: true,
        renamed_exterior_occurrences_return_same_native_current,
        renamed_exterior_occurrences_retain_distinct_cold_fibres,
        exterior_fibres_dropped_before_hot_conduct: true,
        detached_remount_returns_native_conduct: true,
        hot_rest_identity_unchanged_by_transient_conduct: true,
        native_current_identity_sha256,
        native_conduct_identity_sha256: native_conduct.native_section_identity_sha256,
        source_neutral_relational_identity_sha256: remounted.relational().identity().to_owned(),
        source_neutral_relational_face_population: remounted.relational().face_population(),
        source_neutral_relational_cell_population: remounted.relational().cell_population(),
        causal_grain_population: remounted.granular().causal_grain_population(),
        boundary_port_population: remounted.granular().boundary_port_population(),
    };
    fs::write(
        output.join("source-absence-and-detached-remount-audit.json"),
        serde_json::to_vec_pretty(&audit)?,
    )?;
    println!("{successor_identity_sha256}");
    Ok(())
}

fn verify_existing_successor(root: &PathBuf, output: &PathBuf) -> Result<(), Box<dyn Error>> {
    let successor_wire = fs::read(output.join("athena-source-neutral.rest"))?;
    let receipt: SourceNeutralSeveringReceipt = serde_json::from_slice(&fs::read(
        output.join("source-neutral-severing-receipt.json"),
    )?)?;
    let predecessor_wire_octets = fs::metadata(root.join(PREDECESSOR))?.len();
    let predecessor_identity_sha256 = receipt.predecessor_rest_identity_sha256.clone();
    let remounted = SourceNeutralAthenaRest::read(&successor_wire)?;
    let successor_identity_sha256 = remounted.identity().to_owned();
    if successor_identity_sha256 != receipt.native_successor_identity_sha256 {
        return Err("the written UAR0 successor escaped its severing receipt".into());
    }
    let forbidden = [
        "Brandon",
        "surface_variants",
        "founding_delivery_order",
        "founding_clause_order",
        "NativeRelationalCodec",
        "source_occurrence_identity_sha256",
        "occurrence_population_identity_sha256",
        "source_action_identity_sha256",
        "source_square_identity_sha256",
        "material_occurrence_population",
        "material_octet_population",
        "material_port_population",
        "predecessor_wire_sha256",
        "ExteriorParticipantReceiverChart",
        "ExteriorRelationReceiverChart",
        "soma-life.native-relational-codec",
    ];
    let hits = occurrence_populations(&successor_wire, &forbidden.map(str::as_bytes));
    if hits.iter().any(|hits| *hits != 0) {
        return Err("the written UAR0 successor retained a forbidden developmental face".into());
    }
    let (native_left, exterior_left) =
        transduce_source_neutral_exterior(&remounted, "exterior-apparatus/left", b"a")?;
    let (native_right, exterior_right) =
        transduce_source_neutral_exterior(&remounted, "exterior-apparatus/right", b"a")?;
    let renamed_exterior_occurrences_return_same_native_current = native_left == native_right;
    let renamed_exterior_occurrences_retain_distinct_cold_fibres =
        exterior_left.identity_sha256 != exterior_right.identity_sha256;
    let native_current_identity_sha256 = native_left.identity_sha256.clone();
    drop(exterior_left);
    drop(exterior_right);
    let rest_identity_before_conduct = remounted.identity().to_owned();
    let mut resident = remounted.mount_resident()?;
    let native_conduct = resident.condition_native(&native_left)?;
    let remounted = resident.into_rest();
    if !renamed_exterior_occurrences_return_same_native_current
        || !renamed_exterior_occurrences_retain_distinct_cold_fibres
        || remounted.identity() != rest_identity_before_conduct
    {
        return Err("the written UAR0 successor failed detached native conduct".into());
    }
    let ratio = u64::try_from(successor_wire.len())?
        .checked_mul(1_000_000)
        .and_then(|scaled| scaled.checked_div(predecessor_wire_octets))
        .ok_or("wire ratio overflow")?;
    let audit = SourceAbsenceAudit {
        truth_status: "implemented-exact; measured",
        predecessor_wire_octets: usize::try_from(predecessor_wire_octets)?,
        successor_wire_octets: successor_wire.len(),
        successor_to_predecessor_per_million: ratio,
        predecessor_identity_sha256,
        successor_identity_sha256: successor_identity_sha256.clone(),
        remounted_identity_sha256: remounted.identity().to_owned(),
        forbidden_octet_sequences: forbidden.iter().map(|value| (*value).to_owned()).collect(),
        forbidden_sequence_hits: hits,
        source_surface_atlas_reachable: false,
        source_codec_reachable: false,
        source_clause_decoder_reachable: false,
        cold_witness_absent_during_remount: true,
        hot_rest_contains_only_native_ecology_and_reusable_organs: true,
        renamed_exterior_occurrences_return_same_native_current,
        renamed_exterior_occurrences_retain_distinct_cold_fibres,
        exterior_fibres_dropped_before_hot_conduct: true,
        detached_remount_returns_native_conduct: true,
        hot_rest_identity_unchanged_by_transient_conduct: true,
        native_current_identity_sha256,
        native_conduct_identity_sha256: native_conduct.native_section_identity_sha256,
        source_neutral_relational_identity_sha256: remounted.relational().identity().to_owned(),
        source_neutral_relational_face_population: remounted.relational().face_population(),
        source_neutral_relational_cell_population: remounted.relational().cell_population(),
        causal_grain_population: remounted.granular().causal_grain_population(),
        boundary_port_population: remounted.granular().boundary_port_population(),
    };
    fs::write(
        output.join("source-absence-and-detached-remount-audit.json"),
        serde_json::to_vec_pretty(&audit)?,
    )?;
    println!("{successor_identity_sha256}");
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

fn occurrence_populations(haystack: &[u8], needles: &[&[u8]]) -> Vec<u64> {
    let mut by_first: [Vec<usize>; 256] = std::array::from_fn(|_| Vec::new());
    for (needle_at, needle) in needles.iter().enumerate() {
        if let Some(first) = needle.first() {
            by_first[*first as usize].push(needle_at);
        }
    }
    let mut populations = vec![0_u64; needles.len()];
    for (at, first) in haystack.iter().copied().enumerate() {
        for needle_at in &by_first[first as usize] {
            if haystack[at..].starts_with(needles[*needle_at]) {
                populations[*needle_at] = populations[*needle_at].saturating_add(1);
            }
        }
    }
    populations
}
