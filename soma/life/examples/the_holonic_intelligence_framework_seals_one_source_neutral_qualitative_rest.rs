//! HIF7 source-neutral qualitative-rest boundary.
//!
//! The rich acoustic/optical product is developmental input to the existing one-way severing
//! owner.  Only its native successor is written into the HIF7 aperture; the contaminated product
//! and cold witness are never accepted by later conduct.

use std::{error::Error, fs, path::PathBuf};

use life::native_intelligence::{sever_source_bearing_ecology, SourceNeutralEcologyRest};

const DEVELOPMENTAL_REST: &str = concat!(
    "output/the_athena_radiation_forms_an_optical_field_and_its_image_returns_sens5/",
    "athena-optical-world-cultivated.rest"
);
const OUTPUT: &str = "output/holonic_intelligence_framework_hif7";

fn main() -> Result<(), Box<dyn Error>> {
    let root = repository_root()?;
    let output = root.join(OUTPUT);
    fs::create_dir_all(&output)?;
    let developmental_wire = fs::read(root.join(DEVELOPMENTAL_REST))?;
    let (rest, witness, receipt) = sever_source_bearing_ecology(&developmental_wire)?;
    let identity = rest.identity().to_owned();
    let wire = rest.canonical_bytes()?;
    drop(developmental_wire);

    let remounted = SourceNeutralEcologyRest::read(&wire)?;
    if remounted.identity() != identity
        || remounted.acoustic().ordered_ports() != remounted.optical().ordered_ports()
    {
        return Err("the HIF7 source-neutral qualitative rest did not remount exactly".into());
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
