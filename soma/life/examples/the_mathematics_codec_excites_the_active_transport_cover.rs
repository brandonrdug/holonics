//! M2 — M1 mathematical particles excite a receiver-indexed active transport cover in the frozen
//! source-detached Gemma lift.

#[path = "m1/particle.rs"]
mod particle;
#[path = "m1/particle_operation.rs"]
mod particle_operation;
#[path = "m1/particle_relations.rs"]
mod particle_relations;
#[path = "m1/particle_typing.rs"]
mod particle_typing;
#[path = "m1/resident_affine.rs"]
mod resident_affine;
#[path = "m1/source_material.rs"]
mod source_material;

#[path = "m2/artifact.rs"]
mod artifact;
#[path = "m2/deed.rs"]
mod deed;
#[path = "m2/excitation.rs"]
mod excitation;
#[path = "m2/panel.rs"]
mod panel;

use std::path::PathBuf;

fn main() -> Result<(), String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    let construction = particle::construct(&root)?;
    let returned = deed::run(&root, &construction)?;
    artifact::write(&root, &returned)
}
