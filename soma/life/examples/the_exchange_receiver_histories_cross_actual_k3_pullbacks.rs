//! L1 apparatus: cross the complete exchange receiver/history return with actual K3 pullbacks.
//!
//! This driver only mounts admitted artifacts, invokes the public L1 owner, introduces one
//! addressed later-return control, and writes receipts.  It does not select support, construct a
//! semantic route, or author a local factor.

use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{
    derived_factor_cover::OverlapKind, receiver_exact_compression::ItemId,
    receiver_history_compression::ReceiverHistoryCompression, EventId,
};
use life::native_intelligence::{
    ExchangeCandidateLineage, ExchangeProductMaterial, ExchangeSituatedProduct, NativeEcologyRest,
    ReturnedExchangeSection,
};
use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const K3_REST: &str = concat!(
    "output/the_one_connected_athena_native_ecology_returns_dependent_sections_k3/",
    "athena-native.rest"
);
const EXCHANGE_RETURN: &str = concat!(
    "output/the_complete_exchange_enters_one_athena_ecology_before_returns_open_h2n/",
    "03-complete-native-realization.json"
);
const OUTPUT: &str = "output/the_exchange_receiver_histories_cross_actual_k3_pullbacks_l1";

fn main() -> Result<(), String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .ok_or("cannot locate the repository root")?
        .to_path_buf();
    let output = root.join(OUTPUT);
    if output.exists() {
        return Err(format!("preserve existing L1 return {}", output.display()));
    }
    fs::create_dir_all(&output).map_err(display)?;
    let started = Instant::now();

    let rest = NativeEcologyRest::read(&fs::read(root.join(K3_REST)).map_err(display)?)
        .map_err(display)?;
    let material = read_exchange_material(&root.join(EXCHANGE_RETURN))?;
    eprintln!("L1 mount complete; founding the exchange/K3 dependent product");
    let product = ExchangeSituatedProduct::found(&rest, material).map_err(display)?;
    eprintln!("L1 product founded; deriving the later-return intervention");

    let source = product
        .native_covers
        .first()
        .and_then(|cover| cover.source_reconstruction_fibre.iter().next())
        .copied()
        .ok_or("the L1 product returned no reconstruction member")?;
    let replacement_return = fresh_event(&product)?;
    let intervention = product
        .intervene_return_event(source, replacement_return)
        .map_err(display)?;
    eprintln!("L1 intervention returned; writing the exact artifact population");

    let local_population = product
        .native_covers
        .iter()
        .map(|cover| cover.locals.len())
        .sum::<usize>();
    let overlap_population = product
        .native_covers
        .iter()
        .map(|cover| cover.cover.overlaps.len())
        .sum::<usize>();
    let every_overlap_has_both_restrictions = product.native_covers.iter().all(|cover| {
        cover.cover.overlaps.iter().all(|overlap| {
            overlap.patch.as_ref().is_some_and(|patch| {
                !patch.rows.is_empty()
                    && !patch.columns.is_empty()
                    && patch.left.rows() == patch.right.rows()
                    && patch.left.columns() == patch.right.columns()
            })
        })
    });
    let overlap_kinds = product
        .native_covers
        .iter()
        .flat_map(|cover| cover.cover.overlaps.iter())
        .fold(
            (0usize, 0usize, 0usize, 0usize),
            |(glue, cocycle, holonomy, open), overlap| match &overlap.kind {
                OverlapKind::CompatibleGlue { .. } => (glue + 1, cocycle, holonomy, open),
                OverlapKind::CommutingCocycle { .. } => (glue, cocycle + 1, holonomy, open),
                OverlapKind::ConstitutiveCocycle { .. } => (glue, cocycle + 1, holonomy, open),
                OverlapKind::PathOrderedHolonomy { .. } => (glue, cocycle, holonomy + 1, open),
                OverlapKind::Open { .. } | OverlapKind::DisjointInterchange { .. } => {
                    (glue, cocycle, holonomy, open + 1)
                }
            },
        );
    let generator_square_population = product
        .native_covers
        .iter()
        .flat_map(|cover| &cover.locals)
        .map(|local| local.generator_squares.len())
        .sum::<usize>();
    let every_generator_square_commutes = product
        .native_covers
        .iter()
        .flat_map(|cover| &cover.locals)
        .flat_map(|local| &local.generator_squares)
        .all(|square| square.exchange_square_commutes && square.k3_pullback_word_admitted);
    let every_local_reconstructs = product.native_covers.iter().all(|cover| {
        cover.locals.len() == cover.cover.locals.len()
            && cover.cover.locals.iter().all(|factor| {
                factor.reconstructed_defect == factor.section.supported
                    && cover.locals.iter().any(|local| {
                        factor.section.address
                            == format!(
                                "exchange-k3-local/{}/{}",
                                local.address.native.0, local.address.branch
                            )
                    })
            })
    });
    let nonzero_mixed_population = product
        .mixed_interactions
        .iter()
        .filter(|interaction| {
            interaction.mixed_remainder != holonic_engine::ExactComplexWaveCurrent::zero()
        })
        .count();
    let finite_leibniz_exact = product.mixed_interactions.iter().all(|interaction| {
        interaction
            .candidate_product
            .add(&interaction.source_linear_terms)
            .add(&interaction.mixed_remainder)
            == interaction.returned_product
    });
    let candidate_unchanged_and_loss_changed = intervention.sealed_candidate_unchanged
        && intervention.affected_locals.iter().all(|local| {
            local.candidate_event_before == local.candidate_event_after
                && local.complete_situated_difference_changed
        });
    let branch_population = product.k3_branches.len();
    let expected_local_population = product
        .native_action
        .native_population
        .len()
        .checked_mul(branch_population)
        .ok_or("local population overflow")?;
    let expected_overlap_population = product
        .native_action
        .native_population
        .len()
        .checked_mul(
            branch_population
                .checked_mul(branch_population.saturating_sub(1))
                .and_then(|value| value.checked_div(2))
                .ok_or("overlap population overflow")?,
        )
        .ok_or("overlap population overflow")?;
    let passed = local_population == expected_local_population
        && overlap_population == expected_overlap_population
        && every_local_reconstructs
        && every_overlap_has_both_restrictions
        && overlap_kinds.3 == 0
        && every_generator_square_commutes
        && generator_square_population > 0
        && nonzero_mixed_population > 0
        && finite_leibniz_exact
        && candidate_unchanged_and_loss_changed;

    let product_bytes = product.canonical_bytes().map_err(display)?;
    fs::write(
        output.join("01-exchange-situated-product.rest"),
        &product_bytes,
    )
    .map_err(display)?;
    write_json(
        output.join("02-overlap-generator-and-constitutive-ledger.json"),
        &json!({
            "schema":"soma-life.exchange-situated-overlap-ledger.v1",
            "truth_status":"established-bounded; implemented-exact; measured",
            "k3_pullback_branch_population":branch_population,
            "native_receiver_history_population":product.native_action.native_population.len(),
            "local_population":local_population,
            "overlap_population":overlap_population,
            "compatible_glue_population":overlap_kinds.0,
            "commuting_cocycle_population":overlap_kinds.1,
            "path_ordered_holonomy_population":overlap_kinds.2,
            "open_or_private_interchange_population":overlap_kinds.3,
            "generator_square_population":generator_square_population,
            "every_generator_square_commutes":every_generator_square_commutes,
            "receiver_constitutive_rank":product.constitutive_form.factorization.rank,
            "receiver_constitutive_radical":product.constitutive_form.factorization.kernel,
            "mutual_constitutive_response_population":product.constitutive_form.mutual_responses.len(),
            "mixed_interaction_family_population":product.mixed_interactions.len(),
            "nonzero_mixed_interaction_family_population":nonzero_mixed_population,
            "finite_leibniz_exact":finite_leibniz_exact,
        }),
    )?;
    write_json(
        output.join("03-later-return-intervention.json"),
        &intervention,
    )?;
    write_json(
        output.join("04-mixed-finite-leibniz-families.json"),
        &product.mixed_interactions,
    )?;
    write_json(
        output.join("05-source-neutral-support-control.json"),
        &json!({
            "schema":"soma-life.exchange-source-neutral-support-control.v1",
            "truth_status":"implemented-exact; measured",
            "source":source,
            "source_is_reconstruction_lineage_only":true,
            "support_address_components":["receiver_history_native_fibre", "actual_k3_pullback_branch", "receiver_constitutive_form"],
            "forbidden_support_components":["source_ordinal", "equal_text", "collection_membership", "equal_endpoint"],
            "unaffected_native_support_identity_sha256":intervention.unaffected_native_support_identity_sha256,
        }),
    )?;
    let product_sha256 = sha256(&product_bytes);
    let grade = json!({
        "schema":"soma-life.exchange-situated-product-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "phase":"L1",
        "passed":passed,
        "predecessor_rest_wire_sha256":product.predecessor_rest_wire_sha256,
        "exchange_situated_product_sha256":product_sha256,
        "exchange_situated_product_octets":product_bytes.len(),
        "k3_pullback_branch_population":branch_population,
        "receiver_history_native_population":product.native_action.native_population.len(),
        "source_reconstruction_population":product.native_action.source_population.len(),
        "local_population":local_population,
        "every_local_reconstructs":every_local_reconstructs,
        "overlap_population":overlap_population,
        "every_overlap_has_both_restrictions":every_overlap_has_both_restrictions,
        "open_or_private_interchange_population":overlap_kinds.3,
        "generator_square_population":generator_square_population,
        "every_generator_square_commutes":every_generator_square_commutes,
        "nonzero_mixed_interaction_family_population":nonzero_mixed_population,
        "finite_leibniz_exact":finite_leibniz_exact,
        "intervened_source":source,
        "sealed_candidate_unchanged":intervention.sealed_candidate_unchanged,
        "changed_complete_loss_local_population":intervention.affected_locals.iter().filter(|local| local.complete_situated_difference_changed).count(),
        "factor_projection_unchanged_under_lineage_intervention":intervention.affected_locals.iter().all(|local| local.factor_projection_unchanged),
        "source_ordinal_enters_support_law":false,
        "equal_text_enters_support_law":false,
        "morphology_deposited":false,
        "shortest_open_fibre":"the exact causal-adjoint population has not yet been deposited into the one K3 continuing morphology",
        "elapsed_seconds":format!("{:.9}", started.elapsed().as_secs_f64()),
    });
    write_json(output.join("00-grade.json"), &grade)?;
    if !passed {
        return Err("the L1 qualitative or exact return did not pass".to_owned());
    }
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    Ok(())
}

fn read_exchange_material(path: &Path) -> Result<ExchangeProductMaterial, String> {
    let value: Value =
        serde_json::from_slice(&fs::read(path).map_err(display)?).map_err(display)?;
    let predecessor_rest_wire_sha256 = value
        .pointer("/candidate/predecessor_rest_wire_sha256")
        .and_then(Value::as_str)
        .ok_or("the exchange artifact lacks its predecessor rest")?
        .to_owned();
    let native: ReceiverHistoryCompression = serde_json::from_value(
        value
            .get("native")
            .cloned()
            .ok_or("the exchange artifact lacks its native quotient")?,
    )
    .map_err(display)?;
    let returned: Vec<ReturnedExchangeSection> = serde_json::from_value(
        value
            .get("returned")
            .cloned()
            .ok_or("the exchange artifact lacks its later return")?,
    )
    .map_err(display)?;
    let candidate_lineage = value
        .pointer("/candidate/sections")
        .and_then(Value::as_array)
        .ok_or("the exchange artifact lacks its sealed candidates")?
        .iter()
        .map(|section| {
            let source = section
                .pointer("/history/source")
                .and_then(Value::as_u64)
                .ok_or("one sealed candidate lacks its source lineage")?;
            let seal_sha256 = section
                .get("seal_sha256")
                .and_then(Value::as_str)
                .ok_or("one sealed candidate lacks its seal")?
                .to_owned();
            Ok(ExchangeCandidateLineage {
                source: ItemId(source),
                seal_sha256,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let open_exterior = serde_json::from_value(
        value
            .get("open_exterior")
            .cloned()
            .ok_or("the exchange artifact lacks its open exterior")?,
    )
    .map_err(display)?;
    let material = ExchangeProductMaterial {
        predecessor_rest_wire_sha256,
        native,
        candidate_lineage,
        returned,
        open_exterior,
    };
    material.validate()?;
    Ok(material)
}

fn fresh_event(product: &ExchangeSituatedProduct) -> Result<EventId, String> {
    let used = product
        .native_covers
        .iter()
        .flat_map(|cover| &cover.locals)
        .flat_map(|local| {
            local
                .returned_native
                .members
                .iter()
                .flat_map(|member| [member.candidate_event, member.return_event])
        })
        .collect::<BTreeSet<_>>();
    let next = used
        .iter()
        .map(|event| event.0)
        .max()
        .and_then(|event| event.checked_add(1))
        .ok_or("cannot found a fresh later-return occurrence")?;
    Ok(EventId(next))
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(value).map_err(display)?;
    fs::write(path, bytes).map_err(display)
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
