//! Narrow UAR2 apparatus: one unchanged technical occurrence crosses the complete cultivated cell
//! field of the admitted ALP5 body and returns its native causal front.

use std::{fs, path::PathBuf, time::Instant};

use life::native_intelligence::{EmanationDeed, OpticalProductRest};

const REST: &str = concat!(
    ".local/artifacts/the_one_holonics_hna_body_circulates_every_admitted_organ_and_cultivates_alp4/",
    "athena-sens6-cultivated.rest"
);
const EXPECTED_ALP5_IDENTITY: &str =
    "916710c5e7e5f79c602e8e4b6e0e3a74c7a5334d1b50df9e63bf1a127e8b67f5";

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let began = Instant::now();
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let rest = OpticalProductRest::read(&fs::read(root.join(REST))?)?;
    if rest.identity() != EXPECTED_ALP5_IDENTITY {
        return Err("the probe did not receive the admitted ALP5 body".into());
    }
    eprintln!("UAR2 probe rest read in {} ms", began.elapsed().as_millis());
    let current = rest
        .body()
        .body()
        .granular_potential()
        .reflect_exterior_projective_current(
            "uar2/probe/holonic-compression",
            b"How does holonic compression preserve future consequences?",
        )?;
    let mut product = rest.mount_product()?;
    eprintln!(
        "UAR2 probe resident body mounted in {} ms",
        began.elapsed().as_millis()
    );
    let returned = product.emanate_situated_current(&current, false, EmanationDeed::Infer, None)?;
    println!(
        "rest={} current={} contexts={} selected={} surface={:?} elapsed_ms={}",
        returned.rest_identity_sha256,
        returned.exterior_current_identity_sha256,
        returned.apparatus.context_population,
        returned.selected_cell_addresses.len(),
        returned.surface,
        began.elapsed().as_millis(),
    );
    Ok(())
}
