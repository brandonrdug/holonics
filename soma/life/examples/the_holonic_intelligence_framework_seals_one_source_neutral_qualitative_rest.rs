//! HIF7 source-neutral qualitative-rest boundary.
//!
//! The rich acoustic/optical product is developmental input to the existing one-way severing
//! owner.  Only its native successor is written into the HIF7 aperture; the contaminated product
//! and cold witness are never accepted by later conduct.

use std::{error::Error, fs, path::PathBuf};

use life::{
    exchange_world_tube::{remount_visible_message_projection, ContinuationAperture},
    native_intelligence::{sever_source_bearing_ecology, SourceNeutralEcologyRest},
    receiver_history::ReceiverHistoryCongruence,
};

const DEVELOPMENTAL_REST: &str = concat!(
    "output/the_athena_radiation_forms_an_optical_field_and_its_image_returns_sens5/",
    "athena-optical-world-cultivated.rest"
);
const OUTPUT: &str = "output/holonic_intelligence_framework_hif7";
const EXCHANGE_WORLD: &str = concat!(
    "output/the_complete_laboratory_exchange_returns_for_athena_alpha/",
    "exchange-world-tube.ewtb"
);
const CONTINUATIONS: &str = concat!(
    "output/the_complete_laboratory_exchange_returns_for_athena_alpha/",
    "04-continuation-aperture.json"
);
const CONGRUENCE: &str = concat!(
    "output/the_receiver_history_congruence_replaces_the_trigram_table/",
    "00-receiver-history-congruence.json"
);
fn main() -> Result<(), Box<dyn Error>> {
    let root = repository_root()?;
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output)?;
    let developmental_wire = fs::read(root.join(DEVELOPMENTAL_REST))?;
    let (rest, witness, receipt) = sever_source_bearing_ecology(&developmental_wire)?;
    let severed_identity = rest.identity().to_owned();
    let severed_wire = rest.canonical_bytes()?;
    drop(developmental_wire);

    let remounted = SourceNeutralEcologyRest::read(&severed_wire)?;
    if remounted.identity() != severed_identity
        || remounted.acoustic().ordered_ports() != remounted.optical().ordered_ports()
    {
        return Err("the HIF7 source-neutral qualitative rest did not remount exactly".into());
    }
    let visible = remount_visible_message_projection(&root.join(EXCHANGE_WORLD))?;
    let aperture: ContinuationAperture =
        serde_json::from_slice(&fs::read(root.join(CONTINUATIONS))?)?;
    let congruence = ReceiverHistoryCongruence::read(&fs::read(root.join(CONGRUENCE))?)?;
    let (rest, recultivation) =
        remounted.recultivate_completed_exchange(&visible, &aperture, &congruence)?;
    let identity = rest.identity().to_owned();
    let wire = rest.canonical_bytes()?;
    let remounted = SourceNeutralEcologyRest::read(&wire)?;
    if remounted.identity() != identity {
        return Err("the HIF7 completed-exchange rest did not remount exactly".into());
    }
    fs::write(output.join("source-neutral-qualitative.rest"), wire)?;
    fs::write(
        output.join("exterior-developmental-witness.json"),
        witness.canonical_bytes()?,
    )?;
    fs::write(
        output.join("source-neutral-severing-receipt.json"),
        serde_json::to_vec(&receipt)?,
    )?;
    fs::write(
        output.join("completed-exchange-recultivation-receipt.json"),
        serde_json::to_vec(&recultivation)?,
    )?;
    eprintln!("hif7 qualitative rest: source-neutral remount returned {identity}");
    Ok(())
}

fn repository_root() -> Result<PathBuf, Box<dyn Error>> {
    let mut cursor = std::env::current_dir()?;
    loop {
        if cursor.join("Cargo.toml").is_file() && cursor.join("soma/life").is_dir() {
            return Ok(cursor);
        }
        if !cursor.pop() {
            return Err("repository root not found".into());
        }
    }
}
