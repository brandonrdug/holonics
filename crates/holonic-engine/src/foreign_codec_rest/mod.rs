//! Source-detached exterior codebook rest.

mod schema;
mod validation;
mod wire;

pub use schema::{
    CodebookEntry, CoverageSummary, ExteriorCodecArtifact, ExteriorCodecDescriptor, OpenFibre,
    RestError, SourceAssetIdentity,
};
pub use wire::{ExteriorCodebookRest, NativeRead};

#[cfg(test)]
#[path = "../foreign_codec_rest_tests.rs"]
mod tests;
