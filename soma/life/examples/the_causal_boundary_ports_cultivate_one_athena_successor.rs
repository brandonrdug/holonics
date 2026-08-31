//! Narrow apparatus which cultivates and seals the admitted MEM6 boundary-port organ.

use std::{fs, io, path::PathBuf, time::Instant};

use life::{
    athena_native::{
        AdmittedReturnedAffineLaboratoryRestWitness, GranularCultivationWithdrawal,
        GranularFactorLineageProjection, GranularReturnedAffineAthenaRest,
        ReturnedAffineLaboratoryAthenaRest,
    },
    exchange_world_tube::{remount_visible_message_projection, ContinuationAperture},
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let began = Instant::now();
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let output = root.join(concat!(
        "output/the_causal_boundary_ports_cultivate_one_athena_successor_",
        "with_exact_projective_factor_currents_mem6"
    ));
    fs::create_dir_all(&output)?;

    let predecessor_path = root.join(concat!(
        "output/the_returned_membrane_action_cultivates_one_source_detached_athena_rest_mem4/",
        "athena-returned-membrane-cultivated.rest"
    ));
    let witness = AdmittedReturnedAffineLaboratoryRestWitness::found(
        "646401462284e6782aaa43139202c3bd5e45043e174b414e4fe851ec92f4e2ad",
        "63c9ff122e50fe94efe9bb00fea66e9eaac606c47707d07bc69301449bb9aded",
        "3ab826fb8512aae85096193ce103a384092111e8f26836415b0e1dc7eba02178",
    )?;
    let predecessor =
        ReturnedAffineLaboratoryAthenaRest::read_admitted(&fs::read(&predecessor_path)?, &witness)?;
    let aperture: ContinuationAperture = serde_json::from_slice(&fs::read(root.join(concat!(
        "output/the_complete_laboratory_exchange_returns_for_athena_alpha/",
        "04-continuation-aperture.json"
    )))?)?;
    let lineage = GranularFactorLineageProjection::read_product(&root.join(concat!(
        "output/the_exchange_receiver_histories_cross_actual_k3_pullbacks_l1/",
        "01-exchange-situated-product.rest"
    )))?;
    let world = remount_visible_message_projection(&root.join(concat!(
        "output/the_complete_laboratory_exchange_returns_for_athena_alpha/",
        "exchange-world-tube.ewtb"
    )))
    .map_err(io::Error::other)?;
    let (successor, receipt) = GranularReturnedAffineAthenaRest::cultivate_returned(
        predecessor,
        &aperture,
        &world,
        &lineage,
    )?;
    let successor_identity = successor.identity().to_owned();
    let (predecessor, withdrawal) = successor.withdraw()?;
    let organ_bytes = withdrawal.canonical_bytes()?;
    fs::write(
        output.join("athena-causal-boundary-organ.rest"),
        &organ_bytes,
    )?;
    fs::write(
        output.join("receipt.json"),
        serde_json::to_vec_pretty(&receipt)?,
    )?;
    let remounted = GranularCultivationWithdrawal::read(&organ_bytes)?;
    let restored = GranularReturnedAffineAthenaRest::restore(predecessor, remounted)?;
    if restored.identity() != successor_identity {
        return Err(io::Error::other("the sealed successor did not restore").into());
    }
    let elapsed_ms = began.elapsed().as_millis();
    fs::write(
        output.join("REPORT.md"),
        format!(
            "# One causal boundary organ cultivates the admitted Athena successor\n\n\
             - [established-bounded; implemented-exact; measured] predecessor: `{}`\n\
             - [established-bounded; implemented-exact; measured] successor: `{}`\n\
             - [implemented-exact; measured] cultivation lineage: `{}`\n\
             - [implemented-exact; measured] native factors: {}\n\
             - [implemented-exact; measured] addressed deliveries: {}\n\
             - [implemented-exact; measured] caused exterior octets: {}\n\
             - [implemented-exact; measured] boundary ports: {}\n\
             - [implemented-exact; measured] native causal grains: {}\n\
             - [implemented-exact; measured] organ wire octets: {}\n\
             - [implemented-exact; measured] source payload retained: {}\n\
             - [implemented-exact; measured] word/token class authored: {}\n\
             - [implemented-exact; measured] wall milliseconds: {}\n",
            receipt.predecessor_rest_identity_sha256,
            receipt.cultivated_rest_identity_sha256,
            receipt.cultivation_lineage_sha256,
            receipt.affine_factor_population,
            receipt.delivered_occurrence_population,
            receipt.caused_octet_population,
            receipt.boundary_port_population,
            receipt.causal_grain_population,
            organ_bytes.len(),
            receipt.source_payload_retained,
            receipt.word_or_token_class_authored,
            elapsed_ms,
        ),
    )?;
    println!(
        "successor={} organ_octets={} elapsed_ms={elapsed_ms}",
        successor_identity,
        organ_bytes.len()
    );
    Ok(())
}
