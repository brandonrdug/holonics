//! R5 — retain mathematical notation, vector geometry, and raster vision at separately typed
//! ports; found their common-world pullback; and return a held-out joint consequence on the card.

#[path = "r5/artifact.rs"]
mod artifact;
#[path = "r5/detached.rs"]
mod detached;
#[path = "r5/grade.rs"]
mod grade;
#[path = "r5/product.rs"]
mod product;
#[path = "r5/render.rs"]
mod render;
#[path = "r5/source.rs"]
mod source;

use std::env;
use std::path::{Path, PathBuf};

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    if let [flag, standing, decoder, fibres, inquiry, receipt] = arguments.as_slice() {
        if flag == "--detached" {
            return detached::conduct(
                Path::new(standing),
                Path::new(decoder),
                Path::new(fibres),
                Path::new(inquiry),
                Path::new(receipt),
            );
        }
    }
    if !arguments.is_empty() {
        return Err(
            "usage: R5 driver [--detached STANDING DECODER FIBRES INQUIRY RECEIPT]".to_owned(),
        );
    }
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    product::construct(&root, product::DEFAULT_OUT)
}
