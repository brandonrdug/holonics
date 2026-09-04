//! M3 — recover a generator-native, receiver/history-exact codec from the M2 active cover.

#[path = "m3/active_cover.rs"]
mod active_cover;
#[path = "m3/artifact.rs"]
mod artifact;
#[path = "m3/native.rs"]
mod native;
#[path = "m3/swing.rs"]
mod swing;

use std::path::PathBuf;

fn main() -> Result<(), String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    let recovery = active_cover::recover(&root)?;
    println!(
        "M3 mounted {} source states from {} without reading an exact-cell digest as equality",
        recovery.states.len(),
        recovery.source_path.display()
    );
    let deed = native::conduct(&recovery)?;
    let swing = swing::calibrate(&deed.source_states)?;
    artifact::write(&root, &recovery, &deed, &swing)
}
