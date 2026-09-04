//! M1 — return one addressed mathematical particle and its compact, validated receipt.

#[path = "m1/artifact.rs"]
mod artifact;
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

use std::path::PathBuf;

const DEFAULT_OUT: &str = ".local/artifacts/the_mathematical_particle_is_an_addressed_passage";

fn main() -> Result<(), String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| format!("resolve workspace root: {error}"))?;
    let construction = particle::construct(&root)?;
    artifact::write(&root, DEFAULT_OUT, &construction)
}
