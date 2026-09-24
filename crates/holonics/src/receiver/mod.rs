//! Receiver-specific constructions over the shared Holon laws.
//!
//! [`law::receiver`](crate::law::receiver) remains the owner of passive linear readings, widths
//! and release vocabulary. [`causal_chord`] is the specialized exact linear-response and pole
//! receiver. Joint active reception and its receipt are separate construction work.

pub mod causal_chord;
pub mod native;
pub mod release;
pub mod standing;
