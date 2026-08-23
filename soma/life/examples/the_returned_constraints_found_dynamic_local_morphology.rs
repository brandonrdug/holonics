//! R3 — return distinct world constraints through their exact receiver adjoint, let the card
//! commit or decline one local action change, remount the successor, and withdraw it exactly.

#[path = "r3/artifact.rs"]
mod artifact;
#[path = "r3/detached.rs"]
mod detached;
#[path = "r3/product.rs"]
mod product;

use std::env;
use std::path::{Path, PathBuf};

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    if let [flag, rest, held_out, receipt] = arguments.as_slice() {
        if flag == "--detached" {
            return detached::conduct(Path::new(rest), Path::new(held_out), Path::new(receipt));
        }
    }
    if !arguments.is_empty() {
        return Err("usage: R3 driver [--detached REST HELD_OUT RECEIPT]".to_owned());
    }
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    product::construct(&root, product::DEFAULT_OUT)
}
