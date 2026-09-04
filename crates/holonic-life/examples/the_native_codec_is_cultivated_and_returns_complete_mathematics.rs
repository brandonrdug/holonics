//! M4 — one returned receiver difference cultivates the M3 native codec and a held-out exact
//! mathematical passage returns through the detached morphology.

#[path = "m4/artifact.rs"]
mod artifact;
#[path = "m4/native.rs"]
mod native;
#[path = "m4/quadric.rs"]
mod quadric;
#[path = "m4/resident.rs"]
mod resident;
#[path = "m4/visual.rs"]
mod visual;

use std::path::PathBuf;

use holonic_engine::receiver_history_cultivation::CultivatedReceiverHistoryRest;

fn main() -> Result<(), String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    let native = native::mount(&root)?;
    let product = quadric::cultivate(&native)?;
    // The later current receives only the cultivated bytes, the M3 native predecessor and its own
    // exact input.  M2 evidence and the Lean source are not arguments to this remount or GPU deed.
    let mounted = CultivatedReceiverHistoryRest::mount(&product.rest_bytes, &native.rest_bytes)
        .map_err(|error| error.to_string())?;
    let returned = resident::conduct(&mounted, &product.mathematical)?;
    let visual = visual::produce(&product)?;
    artifact::write(&root, &native, &product, &returned, &visual, mounted)
}
