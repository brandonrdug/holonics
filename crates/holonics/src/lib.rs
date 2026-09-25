//! **Holonics: the Holon law and its operators, exact over ℚ.**
//!
//! A Holon is the law and its ports, not its state
//! ([object](../../../docs/ELEMENTARY_OBJECTS.md#the-holon-as-one-object)):
//!
//! ```text
//! H = (K, ∂_A;  Π;  𝒟;  𝓔;  G;  π)
//! ```
//!
//! The library is ten modules, each implementing rows of the
//! [operator contract](../../../docs/ELEMENTARY_OBJECTS.md#operator-contract):
//!
//! - [`ratio`]: one per two. The exact rational, rings, the exponentiated/log chart, surprisal,
//!   and the exact linear carrier whose inversion keeps its nonunit fibre.
//! - [`geometry`]: the complex, frames and exact carriers, the screw and pair charts, winding and
//!   carry, cell holonomy and the Swing.
//! - [`holon`]: the law and its facets — ports, Dirac structure, elements, restrictions (tube,
//!   tower, fibre, descent), deposition, reaction — with the helical pair [`holon::contact`] and the
//!   ring [`holon::parametron`].
//! - [`navigator`]: transport with an initial configuration and its own clock, phase lift, address
//!   words and lock addresses, trace faces and the dynamical zeta, the reflective continuation.
//! - [`receiver`]: roles and faces, width and release, standing as the retention quotient, the
//!   causal chord, joint reception and the receipt ratio.
//! - [`holarchy`]: what `Holon::interconnect` returns — the joined whole with its constituents,
//!   typed gluing (or a gluing defect) and parametric orientation, and its receiver-relative
//!   `view`/`count`/`refine`.
//! - [`aeon`]: aeon, epoch and cycle — clock readings with carry, epochs and their towers at a
//!   receiver's section with the oriented flux, two-clock locks, the Hodge split of a clock,
//!   production, the dynamical zeta and the first law of learning.
//! - [`compression`]: compression is intelligence is navigation — a navigator family's face map
//!   against terrain, whose kernel quotient is retention and whose cokernel is the residual; the
//!   resonating/emanating split of a drive; the cost `Kt` against the literal; and locating keys
//!   by loop closure.
//! - [`hnn`]: the HNN law over aeons — closing rotor rings joined by pair contacts, the change that
//!   opens at zero and propagates one contact per tick, deposition, retention at the aeon
//!   boundary, and the exact host reference of the execution port.
//! - [`physics`]: the physical instances — fluid, wave, thermal, spacetime and the information
//!   port — each with its constitutive equations, clocks, balances and participating receiver.
//!
//! Every law computes over exact rationals; no float enters a law. Each module header names its
//! Lean owner relative to the Lean library root.

pub mod aeon;
pub mod compression;
pub mod geometry;
pub mod hnn;
pub mod holarchy;
pub mod holon;
pub mod navigator;
pub mod physics;
pub mod ratio;
pub mod receiver;
