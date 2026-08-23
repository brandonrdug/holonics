//! R1 — bind the rich inquiry's separately situated faces into one M1 operation boundary and
//! return its complete pullback through every unchanged I5 start on the resident card.

#[path = "r1/i5.rs"]
mod i5;
#[path = "r1/intake.rs"]
mod intake;
#[path = "r1/product.rs"]
mod product;

use std::path::PathBuf;

fn main() -> Result<(), String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    product::construct(&root, product::DEFAULT_OUT)
}
