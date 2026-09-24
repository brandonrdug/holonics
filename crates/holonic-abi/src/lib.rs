#![no_std]

//! Substrate-neutral event schemas retained for separate disposition.
//!
//! `current`, `holon`, and `presentation` remain here until their separate owner decisions land.
//! Shared host/device rows now live in `holonics-portable::wire`, the no_std source both native
//! crates and the detached NVPTX kernel can compile without introducing a dependency cycle.

/// One substrate-neutral active event row.
pub mod current;
/// One receiver-relative swept construction over shared presentation cuts.
pub mod holon;
/// One world presentation without a world-specific object model.
pub mod presentation;

#[cfg(test)]
mod tests;
