//! Exact word layouts shared by host code and the detached no_std CUDA kernel.
//!
//! These modules define row layouts and checked word conversions only. They do not choose
//! launch geometry, own allocation, or interpret a world. Keep host codecs and device entries on
//! these same definitions so their word contracts cannot drift.

pub mod contact;
pub mod emission;
pub mod live_event_cuda;
pub mod material_shadow_cuda;
pub mod morphological_condition_cuda;
pub mod morphological_conduct_cuda;
pub mod recurrent_law_cuda;
pub mod register;
pub mod returned_contact_cuda;
pub mod text_restrict_cuda;

#[cfg(test)]
mod tests;
