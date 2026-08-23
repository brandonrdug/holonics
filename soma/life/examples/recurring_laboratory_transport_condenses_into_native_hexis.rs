//! L2 — condense the recurring L1 fixed-section families into one generator-native hexis while
//! retaining carrier charts, complete fibres, exact defects, and richer future separators.

#[path = "l2/artifact.rs"]
mod artifact;
#[path = "l2/detached.rs"]
mod detached;
#[path = "l2/product.rs"]
mod product;
#[path = "l2/rest.rs"]
mod rest;

use std::env;
use std::path::{Path, PathBuf};

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    if let [flag, output] = arguments.as_slice() {
        if flag == "--manifest" {
            artifact::manifest(Path::new(output))?;
            return Ok(());
        }
    }
    if let [flag, standing, decoder, fibres, inquiry, output] = arguments.as_slice() {
        if flag == "--infer" {
            return detached::conduct(
                Path::new(standing),
                Path::new(decoder),
                Path::new(fibres),
                Path::new(inquiry),
                Path::new(output),
            );
        }
    }
    if !arguments.is_empty() {
        return Err(
            "usage: L2 driver [--infer STANDING DECODER FIBRES INQUIRY OUTPUT | --manifest OUTPUT]"
                .to_owned(),
        );
    }
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    product::construct(&root)
}
