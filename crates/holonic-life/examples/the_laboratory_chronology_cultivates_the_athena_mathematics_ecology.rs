//! L0 — circulate one frozen committed laboratory chronology through the admitted Athena ecology,
//! accept a genuine Lean return, cultivate one reusable quadratic-section route, and prove its
//! held-out conduct, obstruction, ablation, source-detached remount, and exact withdrawal.

#[path = "l0/artifact.rs"]
mod artifact;
#[path = "l0/detached.rs"]
mod detached;
#[path = "l0/product.rs"]
mod product;
#[path = "l0/render.rs"]
mod render;
#[path = "l0/rest.rs"]
mod rest;
#[path = "l0/source.rs"]
mod source;

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
            "usage: L0 driver [--infer STANDING DECODER FIBRES INQUIRY OUTPUT | --manifest OUTPUT]"
                .to_owned(),
        );
    }
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    product::construct(&root)
}
