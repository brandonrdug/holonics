//! R2 — derive recurrence extent from the R1 operation world-tube, return every compatible
//! receiver product or its exact unfinished frontier, and close the exterior constraint passage.

#[path = "r2/artifact.rs"]
mod artifact;
#[path = "r2/detached.rs"]
mod detached;
#[path = "r2/product.rs"]
mod product;
#[path = "r1/intake.rs"]
mod r1_intake;

use std::env;
use std::path::{Path, PathBuf};

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    if let [flag, rest, receipt] = arguments.as_slice() {
        if flag == "--detached" {
            return detached::conduct(Path::new(rest), Path::new(receipt));
        }
    }
    if !arguments.is_empty() {
        return Err("usage: R2 driver [--detached REST RECEIPT]".to_owned());
    }
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    product::construct(&root, product::DEFAULT_OUT)
}
