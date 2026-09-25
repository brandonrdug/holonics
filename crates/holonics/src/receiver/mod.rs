//! **The receiver: a role of a participating Holon, and what it returns.**
//!
//! A receiver is a Holon joined at ports ([object](../../../../docs/ELEMENTARY_OBJECTS.md#10-receipt)).
//! Reception changes both participants and returns a face with its receipt. The present owners:
//!
//! - [`reception`]: joint reception, `interact -> InteractionReturn` on a solved step of the joint
//!   law, with `HolonLaw::receive` its zero-storage specialization;
//! - [`receipt`]: receipts over regions in their own frames and clocks, and the receipt ratio
//!   `between`, compared after the common transport;
//! - [`face`]: the passive coholon, the active receiver with its power, and the exact faces a
//!   reading returns (width, horizon, relation rung);
//! - [`release`]: width over a compatible family, and release at a declared tolerance;
//! - [`standing`]: standing as the future-sufficient retention quotient, memory and extinction;
//! - [`causal_chord`]: the exact transfer object `C(sI − A)⁻¹B` of a linearization and its poles.
//!
//! Lean: `Holarchy/{Reception,Receipt}`, `Foundation/{Receiver,ReceiverRelease,Standing,CausalChord}`,
//! `Holon/Law`.

pub mod causal_chord;
pub mod face;
pub mod receipt;
pub mod reception;
pub mod release;
pub mod standing;
