//! **Holonics: the Holon law and its operators, exact over ℚ.**
//!
//! A Holon is the law and its ports, not its state
//! ([object](../../../docs/ELEMENTARY_OBJECTS.md#the-holon-as-one-object)):
//!
//! ```text
//! H = (K, ∂_A;  Π;  𝒟;  𝓔;  G;  π)
//! ```
//!
//! The library is five operator modules, each implementing rows of the
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
//! - [`receiver`]: roles and faces, width and release, standing as the retention quotient, and the
//!   causal chord.
//!
//! Every law computes over exact rationals; no float enters a law. Each module header names its
//! Lean owner relative to the Lean library root.

pub mod geometry;
pub mod holon;
pub mod navigator;
pub mod ratio;
pub mod receiver;
