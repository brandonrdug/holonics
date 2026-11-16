//! Athena's commands (THE_CONSOLIDATION §7, C6 of #603): the store line's live commands (`store`), its live reading (`ruler`), their parity (`parity`) and the
//! exterior's reads and writes they share (`exterior`). The binary (`main.rs`) dispatches them on the card.

#![allow(clippy::disallowed_methods, clippy::disallowed_types, reason = "the exterior: a command's files, processes and printed lines")]

pub mod exterior;
pub mod parity;
pub mod ruler;
pub mod store;
pub mod world;
