//! R0: one rich mathematical inquiry crosses every boundary the unchanged I5 ecology admits.
//!
//! This is a diagnostic product driver, not a new intake, inference, mathematics, or scheduling
//! owner. It mounts the operator occurrence through A1/M0, authenticates the already-returned
//! M1/M6 boundaries, conducts canonical I5 once on the resident card, and returns the complete
//! dependency-minimal obstruction antichain without repairing it.

#[path = "r0/i5.rs"]
mod i5;
#[path = "r0/product.rs"]
mod product;
#[path = "r0/source.rs"]
mod source;

use std::path::PathBuf;

const OUTPUT: &str = "output/the_rich_mathematical_inquiry_returns_the_i5_baseline_boundary";

fn main() -> Result<(), String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    let output = root.join(OUTPUT);
    let source = source::mount(&root)?;
    let baseline = i5::conduct(&root)?;
    product::write(&output, &source, &baseline)?;
    println!("R0 returned: {}", output.display());
    println!(
        "actual unchanged I5 emission: {:?}",
        baseline.selected_passages
    );
    println!("R1 is authorized only by 07-minimal-absence-antichain.json");
    Ok(())
}
