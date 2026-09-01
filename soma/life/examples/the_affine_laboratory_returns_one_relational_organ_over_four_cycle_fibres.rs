//! Repaired L5 construction receiver.
//!
//! This apparatus mounts the complete exchange only during cultivation, returns one affine
//! relational organ over the four already-owned L2 fibres, separates an equal-count source
//! intervention, and verifies detached remount plus move-owned withdrawal/restoration.  It does
//! not claim the complete L5 grade before the resident participant receiver returns.

use std::{
    env, fs,
    path::{Path, PathBuf},
    time::Instant,
};

use life::{
    exchange_world_tube::{
        remount_visible_message_projection, ContinuationAperture, Digest32, MessageAddress,
        VisibleMessageProjection,
    },
    native_intelligence::{
        AffineLaboratoryCultivatedRest, ExchangeSituatedProduct, SituatedCultivatedEcologyRest,
    },
};
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const L2_REST: &str = concat!(
    "output/the_causal_adjoint_cultivates_one_source_detached_athena_rest_l2/",
    "athena-situated-cultivated.rest"
);
const L1_PRODUCT: &str = concat!(
    "output/the_exchange_receiver_histories_cross_actual_k3_pullbacks_l1/",
    "01-exchange-situated-product.rest"
);
const EXCHANGE_APERTURE: &str = concat!(
    "output/the_complete_laboratory_exchange_returns_for_athena_alpha/",
    "04-continuation-aperture.json"
);
const EXCHANGE_WORLD: &str = concat!(
    "output/the_complete_laboratory_exchange_returns_for_athena_alpha/",
    "exchange-world-tube.ewtb"
);
const OUTPUT: &str =
    "output/the_affine_laboratory_returns_one_relational_organ_over_four_cycle_fibres_l5_repair";

fn main() -> Result<(), String> {
    let arguments = env::args().collect::<Vec<_>>();
    if arguments
        .get(1)
        .is_some_and(|argument| argument == "--output")
    {
        return found(Some(PathBuf::from(
            arguments.get(2).ok_or("output path absent")?,
        )));
    }
    if arguments
        .get(1)
        .is_some_and(|argument| argument == "--detached")
    {
        return detached(
            Path::new(arguments.get(2).ok_or("detached rest path absent")?),
            Path::new(arguments.get(3).ok_or("detached receipt path absent")?),
        );
    }
    if arguments
        .get(1)
        .is_some_and(|argument| argument == "--intervention")
    {
        return intervention(
            Path::new(arguments.get(2).ok_or("baseline rest path absent")?),
            Path::new(arguments.get(3).ok_or("intervention receipt path absent")?),
        );
    }
    found(None)
}

fn found(output_override: Option<PathBuf>) -> Result<(), String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .ok_or("cannot locate repository root")?
        .to_path_buf();
    let output = output_override.unwrap_or_else(|| root.join(OUTPUT));
    if output.exists() {
        return Err(format!(
            "preserve existing repaired L5 return {}",
            output.display()
        ));
    }
    fs::create_dir_all(&output).map_err(display)?;
    let started = Instant::now();

    eprintln!("repair L5: remounting exterior exchange projection");
    let aperture: ContinuationAperture =
        serde_json::from_slice(&fs::read(root.join(EXCHANGE_APERTURE)).map_err(display)?)
            .map_err(display)?;
    let world = remount_visible_message_projection(&root.join(EXCHANGE_WORLD))?;
    eprintln!("repair L5: reading L2 rest and L1 fibre correspondence");
    let l2_bytes = fs::read(root.join(L2_REST)).map_err(display)?;
    let product_bytes = fs::read(root.join(L1_PRODUCT)).map_err(display)?;
    let predecessor = SituatedCultivatedEcologyRest::read(&l2_bytes).map_err(display)?;
    let predecessor_identity = predecessor.identity().to_owned();
    let product = ExchangeSituatedProduct::read(&product_bytes).map_err(display)?;
    eprintln!("repair L5: cultivating one affine relational organ");
    let (rest, receipt) =
        AffineLaboratoryCultivatedRest::cultivate(predecessor, product, &aperture, &world)
            .map_err(display)?;
    eprintln!("repair L5: serializing returned source-detached rest");
    let rest_identity = rest.identity().to_owned();
    let rest_bytes = rest.canonical_bytes().map_err(display)?;
    let rest_path = output.join("athena-affine-laboratory-cultivated.rest");
    fs::write(&rest_path, &rest_bytes).map_err(display)?;
    write_json(output.join("00-cultivation-receipt.json"), &receipt)?;

    let affine_support = rest
        .affine_cells()
        .iter()
        .map(|cell| {
            json!({
                "cell_address": cell.cell_address,
                "landmark_population": cell.landmark_factors.len(),
                "occurrence_population": cell.occurrence_multiplicities.iter().sum::<u64>(),
                "barycentric_sum": cell.barycentric_weights.iter().map(ToString::to_string).collect::<Vec<_>>(),
                "source_occurrence_population": cell.source_occurrence_identities_sha256.len(),
            })
        })
        .take(64)
        .collect::<Vec<_>>();
    write_json(
        output.join("01-affine-support-sample.json"),
        &json!({
            "complete_cell_population": rest.affine_cells().len(),
            "sample_is_receiver_projection_only": true,
            "sample": affine_support,
        }),
    )?;

    let (returned_l2, withdrawal) = rest.withdraw_relational_organ().map_err(display)?;
    let withdrawal_exact = returned_l2.identity() == predecessor_identity;
    let restored =
        AffineLaboratoryCultivatedRest::restore_relational_organ(returned_l2, withdrawal)
            .map_err(display)?;
    let restoration_exact = restored.identity() == rest_identity
        && restored.canonical_bytes().map_err(display)? == rest_bytes;
    drop(restored);
    let construction_returned = withdrawal_exact
        && restoration_exact
        && receipt.cycle_coordinate_population_per_factor == 4
        && receipt.additional_winding_thread_population == 0
        && receipt.aggregate_count_coordinate_population == 0;
    write_json(
        output.join("02-repaired-l5-baseline-construction-grade.json"),
        &json!({
            "schema": "soma-life.affine-laboratory-l5-repair-construction-grade.v1",
            "truth_status": if construction_returned { "implemented-exact-measured" } else { "counterexample" },
            "construction_returned": construction_returned,
            "complete_l5_grade_claimed": false,
            "complete_l5_blocker": "source-detached and equal-count controls are separate bounded receivers; resident participant/deed contact remains open",
            "rest_identity_sha256": rest_identity,
            "rest_octets": rest_bytes.len(),
            "rank_four_fibre_per_landmark": receipt.cycle_coordinate_population_per_factor == 4,
            "fifth_winding_axis_absent": receipt.additional_winding_thread_population == 0,
            "aggregate_count_condensation_absent": receipt.aggregate_count_coordinate_population == 0,
            "withdrawal_exact": withdrawal_exact,
            "restoration_exact": restoration_exact,
            "later_target_is_not_a_cultivation_input": true,
            "wall_milliseconds": started.elapsed().as_millis(),
        }),
    )?;
    if !construction_returned {
        return Err("the repaired L5 affine construction did not return".to_owned());
    }
    println!(
        "repaired L5 baseline returned affine rest {} in {} ms; detached, intervention and resident participant receivers remain",
        rest_identity,
        started.elapsed().as_millis()
    );
    Ok(())
}

fn intervention(baseline_path: &Path, output_path: &Path) -> Result<(), String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .ok_or("cannot locate repository root")?
        .to_path_buf();
    let started = Instant::now();
    eprintln!("repair L5 control: reading baseline affine rest");
    let baseline = AffineLaboratoryCultivatedRest::read(&fs::read(baseline_path).map_err(display)?)
        .map_err(display)?;
    let baseline_identity = baseline.identity().to_owned();
    let baseline_cell_addresses = baseline
        .affine_cells()
        .iter()
        .map(|cell| cell.cell_address.clone())
        .collect::<Vec<_>>();
    let baseline_factor_population = baseline.correspondences().len();
    drop(baseline);

    eprintln!("repair L5 control: remounting and intervening one source occurrence");
    let aperture: ContinuationAperture =
        serde_json::from_slice(&fs::read(root.join(EXCHANGE_APERTURE)).map_err(display)?)
            .map_err(display)?;
    let world = remount_visible_message_projection(&root.join(EXCHANGE_WORLD))?;
    let (intervened_aperture, intervened_world, source_intervention) =
        equal_count_source_intervention(&aperture, &world)?;
    let predecessor =
        SituatedCultivatedEcologyRest::read(&fs::read(root.join(L2_REST)).map_err(display)?)
            .map_err(display)?;
    let product = ExchangeSituatedProduct::read(&fs::read(root.join(L1_PRODUCT)).map_err(display)?)
        .map_err(display)?;
    eprintln!("repair L5 control: cultivating intervened affine rest");
    let (intervened, receipt) = AffineLaboratoryCultivatedRest::cultivate(
        predecessor,
        product,
        &intervened_aperture,
        &intervened_world,
    )
    .map_err(display)?;
    let intervened_cell_addresses = intervened
        .affine_cells()
        .iter()
        .map(|cell| cell.cell_address.clone())
        .collect::<Vec<_>>();
    let equal_counts = baseline_factor_population == receipt.addressed_factor_population
        && aperture.families.len() == intervened_aperture.families.len()
        && aperture.complete_response_message_population
            == intervened_aperture.complete_response_message_population;
    let separated = equal_counts
        && intervened.identity() != baseline_identity
        && intervened_cell_addresses != baseline_cell_addresses;
    write_json(
        output_path.to_path_buf(),
        &json!({
            "schema": "soma-life.affine-laboratory-equal-count-source-separator.v1",
            "truth_status": if separated { "implemented-exact-measured" } else { "counterexample" },
            "source_intervention": source_intervention,
            "exchange_family_population_equal": aperture.families.len() == intervened_aperture.families.len(),
            "response_message_population_equal": aperture.complete_response_message_population == intervened_aperture.complete_response_message_population,
            "factor_population_equal": baseline_factor_population == receipt.addressed_factor_population,
            "baseline_rest_identity_sha256": baseline_identity,
            "intervened_rest_identity_sha256": intervened.identity(),
            "rest_identity_separated": intervened.identity() != baseline_identity,
            "native_cell_sections_separated": intervened_cell_addresses != baseline_cell_addresses,
            "equal_count_separator": separated,
            "wall_milliseconds": started.elapsed().as_millis(),
        }),
    )?;
    if !separated {
        return Err("the equal-count source intervention collapsed".to_owned());
    }
    Ok(())
}

fn detached(rest_path: &Path, output_path: &Path) -> Result<(), String> {
    let bytes = fs::read(rest_path).map_err(display)?;
    let rest = AffineLaboratoryCultivatedRest::read(&bytes).map_err(display)?;
    let identity = rest.identity().to_owned();
    let factor_population = rest.correspondences().len();
    let affine_cell_population = rest.affine_cells().len();
    let native_face_population = rest.native_face_population();
    let native_cell_population = rest.native_cell_population();
    let (body, withdrawal) = rest.withdraw_relational_organ().map_err(display)?;
    let mut resident = body.mount().map_err(display)?;
    let returned = resident.conduct().map_err(display)?;
    let body = resident.into_rest();
    let restored = AffineLaboratoryCultivatedRest::restore_relational_organ(body, withdrawal)
        .map_err(display)?;
    let exact_gpu_l2_conduct = returned.rest_identity_sha256 == restored.body().identity()
        && !returned.apparatus.invariant_transport_reuploaded
        && !returned.apparatus.cpu_semantic_replay_after_device
        && !returned.apparatus.binary_receiver_taken;
    write_json(
        output_path.to_path_buf(),
        &json!({
            "schema": "soma-life.affine-laboratory-source-detached-remount.v1",
            "truth_status": if exact_gpu_l2_conduct { "implemented-exact-measured" } else { "counterexample" },
            "rest_identity_sha256": identity,
            "wire_octets": bytes.len(),
            "addressed_factor_population": factor_population,
            "native_face_population": native_face_population,
            "native_cell_population": native_cell_population,
            "affine_cell_population": affine_cell_population,
            "exact_gpu_l2_conduct": exact_gpu_l2_conduct,
            "source_dependencies_opened": Vec::<String>::new(),
            "restoration_exact": restored.identity() == identity,
        }),
    )
}

fn equal_count_source_intervention(
    aperture: &ContinuationAperture,
    world: &VisibleMessageProjection,
) -> Result<
    (
        ContinuationAperture,
        VisibleMessageProjection,
        serde_json::Value,
    ),
    String,
> {
    let mut aperture = aperture.clone();
    let mut world = world.clone();
    let target = aperture
        .families
        .iter()
        .find_map(|family| family.later_operator_return.as_ref())
        .or_else(|| aperture.families.first().map(|family| &family.prompt))
        .ok_or("the exchange aperture has no intervenable occurrence")?
        .clone();
    let message = world
        .messages
        .get_mut(usize::try_from(target.visible_index).map_err(display)?)
        .ok_or("the intervention target escaped the visible projection")?;
    let before = message.text_sha256;
    message
        .text
        .push_str(" The returned source occurrence changes here.");
    let after = Digest32::of(message.text.as_bytes());
    message.text_sha256 = after;
    for family in &mut aperture.families {
        update_address(&mut family.prompt, target.visible_index, after);
        for address in &mut family.history {
            update_address(address, target.visible_index, after);
        }
        for address in &mut family.response {
            update_address(address, target.visible_index, after);
        }
        if let Some(address) = &mut family.later_operator_return {
            update_address(address, target.visible_index, after);
        }
    }
    let changed_source = Digest32::of(
        &[
            aperture.source_occurrence_sha256.octets().as_slice(),
            target.occurrence.as_bytes(),
            after.octets().as_slice(),
        ]
        .concat(),
    );
    aperture.source_occurrence_sha256 = changed_source;
    world.source_occurrence_sha256 = changed_source;
    Ok((
        aperture,
        world,
        json!({
            "visible_index": target.visible_index,
            "occurrence": target.occurrence,
            "content_sha256_before": before.render(),
            "content_sha256_after": after.render(),
            "population_or_membership_changed": false,
        }),
    ))
}

fn update_address(address: &mut MessageAddress, target: u64, digest: Digest32) {
    if address.visible_index == target {
        address.content_sha256 = digest;
    }
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(display)?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(display)
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}

#[allow(dead_code)]
fn sha256(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(64);
    for octet in Sha256::digest(bytes) {
        out.push(HEX[(octet >> 4) as usize] as char);
        out.push(HEX[(octet & 15) as usize] as char);
    }
    out
}
