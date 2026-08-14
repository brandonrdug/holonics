#![no_std]

//! Substrate-neutral word records at Soma's execution membrane.
//!
//! This crate owns layouts which must be exact across host staging, CUDA entry shells,
//! other card substrates, and exact gates. It owns no carriage law, allocation, launch sizing,
//! sharding, world policy, persistence, or observer interpretation.

/// Native execution mouth for relation atoms, event/current extents, sparse cuts, and incidence.
pub mod active;
/// Allocation-free conduct of one validated native current.
pub mod conduct;
/// Transient cooperative REGISTER-contact sheet.
pub mod contact;
/// Fixed word transport for the consequence of one live event.
// `cuda_execution` was removed 2026-08-10. It defined `EventContactRow` / `EVENT_CONTACT_WORDS`
// with a full pack/validate/unpack round trip, 272 lines, and **nothing on either side of the
// membrane referenced it** — not the PTX kernel crate, not the host executor, not a driver.
// `CLAUDE.md` §13 rule 3: superseded production machinery fails closed. It is removed rather than
// deprecated, and git history is the recovery surface.
/// One substrate-neutral active event row.
pub mod current;
/// Accepted body deeds partitioned at native event boundaries.
pub mod emission;
/// One receiver-relative swept construction over shared presentation cuts.
pub mod holon;
/// One contemporary live-current event at the CUDA execution seam.
pub mod live_event_cuda;
/// One raw-material recurrence shadow at the CUDA execution seam.
pub mod material_shadow_cuda;
/// Resident generalized-suffix and question-prefix conditioning mouths.
pub mod morphological_condition_cuda;
/// One morphological candidate/deposit attachment at the CUDA execution seam.
pub mod morphological_conduct_cuda;
/// One world presentation without a world-specific object model.
pub mod presentation;
/// Exact recurrent transformation-law founding and evaluation at the CUDA execution seam.
pub mod recurrent_law_cuda;
/// Exact REGISTER status, lane, and entry rows.
pub mod register;
/// Exact returned-contact grouping at the CUDA execution seam.
pub mod returned_contact_cuda;
/// Sparse exact text-section restriction at the CUDA execution seam.
pub mod text_restrict_cuda;

#[cfg(test)]
mod tests;
