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
pub mod cuda_execution;
/// One substrate-neutral active event row.
pub mod current;
/// Accepted body deeds partitioned at native event boundaries.
pub mod emission;
/// One receiver-relative swept construction over shared presentation cuts.
pub mod holon;
/// One contemporary live-current event at the CUDA execution seam.
pub mod live_event_cuda;
/// One world presentation without a world-specific object model.
pub mod presentation;
/// Exact REGISTER status, lane, and entry rows.
pub mod register;
/// Sparse exact text-section restriction at the CUDA execution seam.
pub mod text_restrict_cuda;

#[cfg(test)]
mod tests;
