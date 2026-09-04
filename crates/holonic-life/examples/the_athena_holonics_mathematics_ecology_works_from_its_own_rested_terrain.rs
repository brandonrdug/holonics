//! L3 — mount only the L2 native rest, receive one genuine mathematical world return, and show
//! its attributable later conduct, revisitation, ablation, and exact predecessor withdrawal.

#[path = "l3/artifact.rs"]
mod artifact;
#[path = "l3/detached.rs"]
mod detached;
#[path = "l3/product.rs"]
mod product;
#[path = "l3/rest.rs"]
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
            "usage: L3 driver [--infer STANDING DECODER FIBRES INQUIRY OUTPUT | --manifest OUTPUT]"
                .to_owned(),
        );
    }
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    product::construct(&root)
}
