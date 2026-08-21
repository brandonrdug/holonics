//! W3 material admission at the W1 exterior-codec boundary.
//!
//! The implementation is routed through owner-local `types`, `hashing`, and `admission` modules;
//! this path remains the stable Phoenix module and retains the existing external test inclusion.

#[path = "cultivation_material/admission.rs"]
mod admission;
#[path = "cultivation_material/codec.rs"]
mod codec;
#[path = "cultivation_material/hashing.rs"]
mod hashing;
#[path = "cultivation_material/types.rs"]
mod types;

#[cfg(test)]
pub use admission::admit_text;
pub use admission::{TokenizedMaterial, admit_tokenized};
#[allow(unused_imports)]
pub use codec::{
    AddSpecialTokens, CodecEquivalenceReceipt, CodecPathPassage, CodecPathRefusal,
    pretokenized_codebook_surface_path, recover_codec_paths, tokenized_codec_variant,
    tokenizer_json_path,
};
pub use hashing::material_identity;
#[cfg(test)]
pub use hashing::surface_rebase_identity;
pub use types::*;

#[cfg(test)]
#[path = "cultivation_material_tests.rs"]
mod cultivation_material_tests;
