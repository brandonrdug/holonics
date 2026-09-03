//! Athena alpha: one exterior application of the neutral live-circulation API.
//!
//! Product naming stops at this crate. Routing, morphology, cultivation, diffusion, persistence,
//! and ABI conduct remain owned by `life`, `holonic-engine`, and `holonics-circulation-abi`.

mod apertures;
mod application;
mod diffusion;
mod material_codec;
mod receivers;
mod recurrent_operator;
mod world_application;

pub use apertures::addressed_ingress;
pub use application::{AthenaAlphaAdmission, AthenaAlphaApplication, AthenaAlphaError};
pub use diffusion::declared_diffusion_law;
pub use material_codec::{
    AthenaMaterialArtifact, AthenaMaterialCodecError, render_material_artifact,
};
pub use receivers::{AthenaAlphaCycleReceipt, inspect_cycle};
pub use recurrent_operator::{
    AthenaRecurrentApplicationError, AthenaRenderedTokenFace, AthenaTextOccurrenceApplication,
    AthenaTokenApplication, AthenaVocabularyFace,
};
pub use world_application::{
    ApplicationWorldError, ApplicationWorldReturn, ExactReadbackWorld, ProcessArtifactWorld,
};

pub const ATHENA_ALPHA_APPLICATION_SCHEMA: &str = "org.holonics.athena-alpha.application.v1";
pub const BASE_CONFIGURATION: &str = include_str!("../configurations/base.json");
