//! L2 apparatus: cultivate the complete situated-difference population into one native rest.
//!
//! This driver only mounts the admitted K3 and L1 artifacts, invokes the public cultivation and
//! resident owners, performs move-owned ablations/restorations, and writes receipts after every
//! exact and qualitative phase condition has passed.

use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use life::native_intelligence::{
    ExchangeSituatedProduct, NativeEcologyRest, SituatedCultivatedConductReturn,
    SituatedCultivatedEcologyRest,
};
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const K3_REST: &str = concat!(
    "output/the_one_connected_athena_native_ecology_returns_dependent_sections_k3/",
    "athena-native.rest"
);
const L1_PRODUCT: &str = concat!(
    "output/the_exchange_receiver_histories_cross_actual_k3_pullbacks_l1/",
    "01-exchange-situated-product.rest"
);
const OUTPUT: &str = "output/the_causal_adjoint_cultivates_one_source_detached_athena_rest_l2";

fn main() -> Result<(), String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .ok_or("cannot locate the repository root")?
        .to_path_buf();
    let output = root.join(OUTPUT);
    if output.exists() {
        return Err(format!("preserve existing L2 return {}", output.display()));
    }
    let started = Instant::now();

    let k3_bytes = fs::read(root.join(K3_REST)).map_err(display)?;
    let product_bytes = fs::read(root.join(L1_PRODUCT)).map_err(display)?;
    let predecessor = NativeEcologyRest::read(&k3_bytes).map_err(display)?;
    let predecessor_wire_sha256 = predecessor.wire_sha256().map_err(display)?;
    let predecessor_section_population = predecessor.realization.sections.len();
    let product = ExchangeSituatedProduct::read(&product_bytes).map_err(display)?;
    eprintln!("L2 admitted K3 and L1; cultivating the complete returned population");
    let cultivated =
        SituatedCultivatedEcologyRest::cultivate(predecessor, product).map_err(display)?;
    let cultivated_identity_sha256 = cultivated.identity().to_owned();
    let cultivated_bytes = cultivated.canonical_bytes().map_err(display)?;
    let cultivated_wire_sha256 = sha256(&cultivated_bytes);
    let cultivated_section_population = cultivated.realization().sections.len();
    let cultivated_branch_population = cultivated.branches().len();
    let cultivated_mixed_population = cultivated.ecology().mixed_constitutive_families().len();
    let exact_fibre_population = cultivated.ecology().exact_reconstruction_fibres().len();
    drop(cultivated);
    drop(k3_bytes);
    drop(product_bytes);

    // The only input to the hot continuation from here onward is the sealed native wire.
    let remounted = SituatedCultivatedEcologyRest::read(&cultivated_bytes).map_err(display)?;
    let source_detached_identity_preserved = remounted.identity() == cultivated_identity_sha256;
    let mut resident = remounted.mount().map_err(display)?;
    let full = resident.conduct().map_err(display)?;
    let full_rest = resident.into_rest();
    let full_factor_addresses = factor_addresses(&full);
    let source_detached_later_conduct_changed = cultivated_section_population
        > predecessor_section_population
        && full.factors.len() == cultivated_branch_population + cultivated_mixed_population
        && full.factors.iter().all(|factor| !factor.current.is_zero());
    eprintln!("L2 source-detached coupled current returned; applying targeted withdrawal");

    let target_thread = full_rest
        .branches()
        .first()
        .ok_or("the cultivated ecology has no target branch")?
        .thread_address
        .clone();
    let expected_removed = full
        .factors
        .iter()
        .filter(|factor| factor.incident_threads.contains(&target_thread))
        .map(|factor| factor.address.clone())
        .collect::<BTreeSet<_>>();
    let (target_ablated, target_withdrawal) = full_rest.withdraw_branch(0).map_err(display)?;
    let target_ablated_identity_sha256 = target_ablated.identity().to_owned();
    let mut target_resident = target_ablated.mount().map_err(display)?;
    let target_return = target_resident.conduct().map_err(display)?;
    let target_ablated = target_resident.into_rest();
    let target_addresses = factor_addresses(&target_return);
    let targeted_ablation_exact = expected_removed.contains(&target_thread)
        && !expected_removed.is_empty()
        && target_addresses
            == full_factor_addresses
                .difference(&expected_removed)
                .cloned()
                .collect::<BTreeSet<_>>();
    let restored = target_ablated
        .restore_branch(target_withdrawal)
        .map_err(display)?;
    let target_restoration_identity_exact = restored.identity() == cultivated_identity_sha256;
    let target_restoration_wire_exact =
        restored.canonical_bytes().map_err(display)? == cultivated_bytes;
    let mut restored_resident = restored.mount().map_err(display)?;
    let restored_return = restored_resident.conduct().map_err(display)?;
    let target_restoration_conduct_exact = restored_return.factors == full.factors;
    let restored = restored_resident.into_rest();
    let restored_mixed_population = restored.ecology().mixed_constitutive_families().len();
    let target_restoration_mixed_exact = restored_mixed_population == cultivated_mixed_population;

    eprintln!("L2 targeted route restored; applying exact receiver-radical control");
    let (fibre_address, radical_position) = restored
        .ecology()
        .exact_reconstruction_fibres()
        .iter()
        .find(|fibre| !fibre.radical.is_empty())
        .map(|fibre| (fibre.address.clone(), 0usize))
        .ok_or("the exact causal-adjoint population has no receiver-radical direction")?;
    let (radical_ablated, radical_withdrawal) = restored
        .withdraw_radical_direction(&fibre_address, radical_position)
        .map_err(display)?;
    let radical_ablated_identity_sha256 = radical_ablated.identity().to_owned();
    let mut radical_resident = radical_ablated.mount().map_err(display)?;
    let radical_return = radical_resident.conduct().map_err(display)?;
    let radical_ablated = radical_resident.into_rest();
    let support_disjoint_conduct_preserved = radical_return.factors == full.factors;
    let radical_restored = radical_ablated
        .restore_radical_direction(radical_withdrawal)
        .map_err(display)?;
    let radical_restoration_identity_exact =
        radical_restored.identity() == cultivated_identity_sha256;
    let radical_restoration_wire_exact =
        radical_restored.canonical_bytes().map_err(display)? == cultivated_bytes;

    let reverse = radical_restored.withdraw_all().map_err(display)?;
    let complete_reverse_exact = reverse.complete_reverse_word_applied
        && reverse.predecessor_wire_sha256 == predecessor_wire_sha256
        && reverse
            .restored_predecessor
            .wire_sha256()
            .map_err(display)?
            == predecessor_wire_sha256;

    let wire_lower = String::from_utf8(cultivated_bytes.clone())
        .map_err(display)?
        .to_ascii_lowercase();
    let forbidden_hot_faces = [
        "exchange-situated-product",
        "source_reconstruction_fibre",
        "source_ordinal",
        "response_interior",
        "candidate_seal",
        "codec_label",
        "checker",
        "soulkiller",
        "phoenix",
        "gemma",
        "q_proj",
        "k_proj",
        "v_proj",
    ];
    let retained_forbidden_hot_faces = forbidden_hot_faces
        .into_iter()
        .filter(|face| wire_lower.contains(face))
        .collect::<Vec<_>>();
    let hot_dependency_closure_source_neutral = retained_forbidden_hot_faces.is_empty();

    let exact_apparatus = full.apparatus.device.contains("RTX 4080 SUPER")
        && full.apparatus.limb_count >= 7
        && full.apparatus.dyadic_exponent.is_some()
        && !full.apparatus.invariant_transport_reuploaded
        && !full.apparatus.cpu_semantic_replay_after_device
        && !full.apparatus.binary_receiver_taken;
    let passed = source_detached_identity_preserved
        && source_detached_later_conduct_changed
        && targeted_ablation_exact
        && support_disjoint_conduct_preserved
        && target_restoration_identity_exact
        && target_restoration_wire_exact
        && target_restoration_conduct_exact
        && target_restoration_mixed_exact
        && radical_restoration_identity_exact
        && radical_restoration_wire_exact
        && complete_reverse_exact
        && hot_dependency_closure_source_neutral
        && exact_apparatus;
    if !passed {
        return Err("L2 exact or qualitative cultivation gate refused advancement".to_owned());
    }

    fs::create_dir_all(&output).map_err(display)?;
    fs::write(
        output.join("athena-situated-cultivated.rest"),
        &cultivated_bytes,
    )
    .map_err(display)?;
    write_json(output.join("01-source-detached-coupled-return.json"), &full)?;
    write_json(
        output.join("02-targeted-withdrawal-and-restoration.json"),
        &json!({
            "schema":"soma-life.situated-targeted-ablation-receipt.v1",
            "truth_status":"established-bounded; implemented-exact; measured",
            "target_thread":target_thread,
            "expected_removed_factor_addresses":expected_removed,
            "target_ablated_factor_addresses":target_addresses,
            "target_ablated_identity_sha256":target_ablated_identity_sha256,
            "targeted_ablation_exact":targeted_ablation_exact,
            "restoration_identity_exact":target_restoration_identity_exact,
            "restoration_wire_exact":target_restoration_wire_exact,
            "restoration_conduct_exact":target_restoration_conduct_exact,
            "restoration_mixed_exact":target_restoration_mixed_exact,
        }),
    )?;
    write_json(
        output.join("03-receiver-radical-control.json"),
        &json!({
            "schema":"soma-life.situated-radical-control-receipt.v1",
            "truth_status":"established-bounded; implemented-exact; measured",
            "fibre_address":fibre_address,
            "radical_position":radical_position,
            "radical_ablated_identity_sha256":radical_ablated_identity_sha256,
            "support_disjoint_conduct_preserved":support_disjoint_conduct_preserved,
            "restoration_identity_exact":radical_restoration_identity_exact,
            "restoration_wire_exact":radical_restoration_wire_exact,
        }),
    )?;
    write_json(
        output.join("04-complete-reverse-word.json"),
        &json!({
            "schema":"soma-life.situated-complete-reverse-receipt.v1",
            "truth_status":"implemented-exact; measured",
            "predecessor_wire_sha256":predecessor_wire_sha256,
            "cultivated_identity_sha256":cultivated_identity_sha256,
            "withdrawn_deposit_population":reverse.withdrawn_deposits.len(),
            "complete_reverse_exact":complete_reverse_exact,
        }),
    )?;
    write_json(
        output.join("05-hot-dependency-closure-audit.json"),
        &json!({
            "schema":"soma-life.situated-hot-dependency-audit.v1",
            "truth_status":"implemented-exact; measured",
            "source_detached_remount":true,
            "retained_forbidden_hot_faces":retained_forbidden_hot_faces,
            "source_exchange_absent":hot_dependency_closure_source_neutral,
            "hot_inputs":["athena-situated-cultivated.rest", "resident active-factor aperture"],
        }),
    )?;
    write_json(
        output.join("06-l2-primary-grade.json"),
        &json!({
            "schema":"soma-life.situated-cultivation-grade.v1",
            "truth_status":"established-bounded; implemented-exact; measured",
            "phase":"L2",
            "passed":passed,
            "elapsed_milliseconds":started.elapsed().as_millis(),
            "predecessor_wire_sha256":predecessor_wire_sha256,
            "cultivated_identity_sha256":cultivated_identity_sha256,
            "cultivated_wire_sha256":cultivated_wire_sha256,
            "cultivated_wire_octets":cultivated_bytes.len(),
            "predecessor_section_population":predecessor_section_population,
            "cultivated_section_population":cultivated_section_population,
            "branch_population":cultivated_branch_population,
            "mixed_family_population":cultivated_mixed_population,
            "exact_reconstruction_fibre_population":exact_fibre_population,
            "source_detached_later_conduct_changed":source_detached_later_conduct_changed,
            "targeted_ablation_exact":targeted_ablation_exact,
            "support_disjoint_radical_ablation_preserved_conduct":support_disjoint_conduct_preserved,
            "exact_restoration_recovered_identity_wire_conduct_and_mixed":target_restoration_identity_exact && target_restoration_wire_exact && target_restoration_conduct_exact && target_restoration_mixed_exact,
            "complete_reverse_exact":complete_reverse_exact,
            "hot_dependency_closure_source_neutral":hot_dependency_closure_source_neutral,
            "device":full.apparatus.device,
            "derived_limb_count":full.apparatus.limb_count,
            "common_denominator":full.apparatus.common_denominator,
            "dyadic_exponent":full.apparatus.dyadic_exponent,
            "resident_invariant_octets":full.apparatus.resident_invariant_octets,
            "successor_ingress_octets":full.apparatus.successor_host_ingress_octets,
            "successor_egress_octets":full.apparatus.successor_host_egress_octets,
            "invariant_transport_reuploaded":full.apparatus.invariant_transport_reuploaded,
            "cpu_semantic_replay_after_device":full.apparatus.cpu_semantic_replay_after_device,
            "binary_receiver_taken":full.apparatus.binary_receiver_taken,
            "shortest_open_fibre":"receiver/successor histories outside the L1 admitted family remain open",
        }),
    )?;
    eprintln!("L2 passed in {} ms", started.elapsed().as_millis());
    Ok(())
}

fn factor_addresses(returned: &SituatedCultivatedConductReturn) -> BTreeSet<String> {
    returned
        .factors
        .iter()
        .map(|factor| factor.address.clone())
        .collect()
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
