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
//! - [`release`]: width over a compatible family, and the one decision law with its arms;
//! - [`population`]: the egg population, a receiver's Bayesian mixture over declared navigator
//!   families (the discrete replicator), each family's death at zero likelihood, and survivor
//!   filtering over a terrain's key spaces.
//!
//! [definition] The causal chord (the transfer object `C(sI − A)⁻¹B` of a linearization and its
//! poles) has no owner here: its law is Lean `Foundation/CausalChord`, and the laws only its Rust
//! realization carried are in [RECEIVER_HOLARCHY](../../../../docs/RECEIVER_HOLARCHY.md#the-causal-chord)
//! (retired at U3's second loop, September 28, with no library caller; history at `c10acca9`).
//!
//! [definition; agent-inferred, U2] Retention (the standing law, Lean `Foundation/Standing`) has no
//! owner here: each collapse certifies it through its own carrier (the [retention
//! contract](../../../../docs/ELEMENTARY_OBJECTS.md#the-retention-contract)).
//!
//! Lean: `Holarchy/{Reception,Receipt}`, `Foundation/{Receiver,ReceiverRelease,Standing}`,
//! `Holon/Law`, `Compression/Landmark/Context/Population`.

pub mod face;
pub mod population;
pub mod receipt;
pub mod reception;
pub mod release;
