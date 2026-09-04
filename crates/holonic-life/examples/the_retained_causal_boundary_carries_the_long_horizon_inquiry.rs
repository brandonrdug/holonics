//! R4 — compactify addressed long-horizon histories only through their lawful future-receiver
//! boundary, reopen the exact interior under a richer return, and remount the cultivated passage.

#[path = "r4/artifact.rs"]
mod artifact;
#[path = "r4/detached.rs"]
mod detached;
#[path = "r4/grade.rs"]
mod grade;
#[path = "r4/product.rs"]
mod product;
#[path = "r4/render.rs"]
mod render;
#[path = "r4/source.rs"]
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
            "usage: R4 driver [--detached STANDING DECODER FIBRES INQUIRY RECEIPT]".to_owned(),
        );
    }
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    product::construct(&root, product::DEFAULT_OUT)
}
