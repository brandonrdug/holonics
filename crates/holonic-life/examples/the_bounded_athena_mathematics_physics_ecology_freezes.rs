//! R6 — freeze the first bounded Athena mathematics/physics production ecology and execute one
//! new rich inquiry through fresh-process decline, world return, committed later conduct, and
//! exact withdrawal.

#[path = "r6/artifact.rs"]
mod artifact;
#[path = "r6/detached.rs"]
mod detached;
#[path = "r6/product.rs"]
mod product;
#[path = "r6/render.rs"]
mod render;
#[path = "r6/rest.rs"]
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
            "usage: R6 driver [--infer STANDING DECODER FIBRES INQUIRY OUTPUT | --manifest OUTPUT]"
                .to_owned(),
        );
    }
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    product::construct(&root)
}
