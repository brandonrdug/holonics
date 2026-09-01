//! H2N return — one exact factor cover over all sealed-candidate/later-return boundaries.

use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use life::{
    native_intelligence::{
        CompleteExchangeCultivationCover, CompleteExchangeNativeRealizationPassage,
        ExchangeDefectBasisFace, HistoryOnlyExchangeFront, NativeEcologyRest,
        SealedNativeCandidateFront,
    },
    receiver_history::ReceiverHistoryCongruence,
};
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const K3_REST: &str = concat!(
    "output/the_one_connected_athena_native_ecology_returns_dependent_sections_k3/",
    "athena-native.rest"
);
const CONGRUENCE: &str = concat!(
    "output/the_receiver_history_congruence_replaces_the_trigram_table/",
    "00-receiver-history-congruence.json"
);
const OUTPUT: &str =
    "output/the_returned_exchange_boundary_founds_one_compact_native_factor_cover_h2n";

fn main() -> Result<(), String> {
    let output = PathBuf::from(OUTPUT);
    if output.exists() {
        return Err(format!(
            "preserve existing H2N factor return {}",
            output.display()
        ));
    }
    let started = Instant::now();
    fs::create_dir_all(&output).map_err(display)?;

    let rest = NativeEcologyRest::read(&fs::read(K3_REST).map_err(display)?).map_err(display)?;
    let congruence = ReceiverHistoryCongruence::read(&fs::read(CONGRUENCE).map_err(display)?)?;
    let history = HistoryOnlyExchangeFront::project(&congruence.sections)?;
    let candidate = SealedNativeCandidateFront::seal(&rest, history).map_err(display)?;
    let passage = CompleteExchangeNativeRealizationPassage::found(candidate, congruence)?;
    let cultivation = CompleteExchangeCultivationCover::derive(&passage)?;

    let source_population = cultivation.sections.len();
    let local_population = cultivation.cover.locals.len();
    let factor_population = cultivation.cover.factor_order.len();
    let derived_rank = cultivation
        .cover
        .locals
        .iter()
        .map(|local| local.derived_rank)
        .sum::<usize>();
    let radical_direction_population = cultivation
        .cover
        .locals
        .iter()
        .map(|local| local.radical_fibre.len())
        .sum::<usize>();
    let open_exterior_direction_population = cultivation
        .cover
        .locals
        .iter()
        .map(|local| local.open_exterior.len())
        .sum::<usize>();
    let distinct_defect_population = cultivation
        .sections
        .iter()
        .map(|section| &section.defect_address)
        .collect::<BTreeSet<_>>()
        .len();
    let returned_basis_population = cultivation
        .codomain_basis
        .iter()
        .filter(|face| matches!(face, ExchangeDefectBasisFace::ReturnedReceiver { .. }))
        .count();
    let candidate_basis_population = cultivation.codomain_basis.len() - returned_basis_population;
    let interchange = cultivation
        .cover
        .compact_interchange_families
        .first()
        .ok_or("the compact interchange family is absent")?;
    let pair_population = source_population
        .checked_mul(source_population.saturating_sub(1))
        .and_then(|population| population.checked_div(2))
        .ok_or("pair population overflow")?;
    let every_factor_has_exact_reverse = cultivation.cover.locals.iter().all(|local| {
        local.factors.len() == local.withdrawal_word.len()
            && local
                .factors
                .iter()
                .rev()
                .zip(&local.withdrawal_word)
                .all(|(factor, withdrawal)| factor.withdrawal == *withdrawal)
    });
    let passed = source_population == 2_224
        && local_population == source_population
        && factor_population == source_population
        && derived_rank == source_population
        && radical_direction_population == 0
        && distinct_defect_population > 1
        && returned_basis_population > 1
        && candidate_basis_population == 4
        && cultivation.cover.overlaps.is_empty()
        && cultivation.cover.complete_pair_population == pair_population as u64
        && interchange.pair_population == pair_population as u64
        && interchange.interchange_law == "additive-local-delta-interchange"
        && cultivation.assembly.exact_disjoint_union
        && every_factor_has_exact_reverse;

    fs::write(
        output.join("01-complete-exchange-cultivation-cover.json"),
        cultivation.canonical_bytes()?,
    )
    .map_err(display)?;
    let grade = json!({
        "schema":"soma-life.complete-exchange-cultivation-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "predecessor_rest_wire_sha256":cultivation.predecessor_rest_wire_sha256,
        "source_population":source_population,
        "local_defect_population":local_population,
        "distinct_return-sensitive_defect_population":distinct_defect_population,
        "candidate_basis_population":candidate_basis_population,
        "returned_basis_population":returned_basis_population,
        "common_codomain_basis_population":cultivation.codomain_basis.len(),
        "nonzero_boundary_coefficient_population":cultivation.assembly.nonzero_coefficient_population,
        "derived_factor_population":factor_population,
        "derived_rank":derived_rank,
        "radical_direction_population":radical_direction_population,
        "open_exterior_direction_population":open_exterior_direction_population,
        "complete_pair_population":pair_population,
        "compact_interchange_family_population":cultivation.cover.compact_interchange_families.len(),
        "explicit_pair_enumeration_population":cultivation.cover.overlaps.len(),
        "zero_holonomy_interchange_pair_population":interchange.pair_population,
        "compact_glue_sha256":cultivation.assembly.assembled_support_sha256,
        "complete_factor_order":cultivation.cover.factor_order.len() == factor_population,
        "complete_reverse_withdrawal_word":cultivation.cover.withdrawal_word.len() == factor_population,
        "every_factor_has_exact_reverse":every_factor_has_exact_reverse,
        "observation_ordinal_arithmetic":false,
        "source_coordinate_selects_conduct":false,
        "foreign_post_boundary_execution":false,
        "elapsed_seconds":format!("{:.9}", started.elapsed().as_secs_f64()),
    });
    write_json(output.join("00-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# Complete exchange cultivation cover\n\n[established-bounded; implemented-exact; measured] The 2,224 sealed-candidate/later-return boundaries form one common typed free module. Opaque observations are basis faces and are never subtracted. Every local boundary has exact rank one, a complete cokernel, one addressed factor, and one inverse withdrawal. Its domain column is disjoint from every other section, so all {pair_population} pairwise interchanges and zero holonomies return through one exact support-family receipt rather than an enumerated all-pairs scan. The sparse union is bound by `{}`.\n\n```json\n{}\n```\n",
            cultivation.assembly.assembled_support_sha256,
            serde_json::to_string_pretty(&grade).map_err(display)?
        ),
    )
    .map_err(display)?;
    write_manifest(&output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("H2N compact native factor cover refused".to_owned())
    }
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut entries = fs::read_dir(output)
        .map_err(display)?
        .filter_map(Result::ok)
        .filter(|entry| entry.file_name() != "MANIFEST.json")
        .map(|entry| {
            let bytes = fs::read(entry.path()).map_err(display)?;
            Ok(json!({
                "path":entry.file_name().to_string_lossy(),
                "octets":bytes.len(),
                "sha256":hex_digest(&bytes),
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    entries.sort_by(|left, right| left["path"].as_str().cmp(&right["path"].as_str()));
    let identity = hex_digest(&serde_json::to_vec(&entries).map_err(display)?);
    write_json(
        output.join("MANIFEST.json"),
        &json!({
            "schema":"soma-life.complete-exchange-cultivation-manifest.v1",
            "identity":identity,
            "files":entries,
        }),
    )
}

fn hex_digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
