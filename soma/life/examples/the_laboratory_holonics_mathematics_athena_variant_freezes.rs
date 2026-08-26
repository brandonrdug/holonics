//! L4 — freeze the admitted L3 ecology as the laboratory's canonical holonics/mathematics Athena
//! variant and return its application entry, complete anatomy, controls, and manifest.

#[path = "l3/artifact.rs"]
mod artifact;
#[path = "l3/detached.rs"]
mod detached;
#[path = "l4/product.rs"]
mod product;
#[path = "l4/rest.rs"]
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
            "usage: L4 Athena [--infer STANDING DECODER FIBRES INQUIRY OUTPUT | --manifest OUTPUT]"
                .to_owned(),
        );
    }
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    product::construct(&root)
}
