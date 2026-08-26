//! Thin example consumer of the source-detached resident circulation.
pub use holonic_engine::phoenix::streamed::*;

#[path = "foreign_material.rs"]
#[allow(dead_code)]
mod foreign_material;
#[allow(unused_imports)]
pub use foreign_material::ForeignMaterialSource;
