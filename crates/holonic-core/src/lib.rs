//! **The Holon core: one object, the law and its ports.**
//!
//! [project-postulate] Brandon, September 22: the Holon is the foundational class of the Rust
//! codebase ([plan](../../../docs/plans/THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md),
//! [object](../../../docs/ELEMENTARY_OBJECTS.md#the-holon-as-one-object)). A Holon is
//!
//! ```text
//! H = (K, ∂_A;  Π;  𝒟;  𝓔;  G;  π)
//! ```
//!
//! and a state is a point on it. The modules below mirror the Lean foundation
//! `formal/elementary-holonics/ElementaryHolonics/Holon/` (namespace
//! `Soma.Holonics.HolonCore`) facet by facet; each module header names its Lean owner, and the
//! engine's `lean_citations` test checks those citations.
//!
//! [definition] This crate depends only on `relational-geometry` and numeric/serde crates. It
//! builds without CUDA. It is exposed as `holonics::core` and is never glob-re-exported into the
//! engine.
//!
//! **The exact base** (phase 2): the exact rational linear carrier [`exact_linear::ExactRatMatrix`]
//! with its certified prime-image reading ([`prime_image_algebra`], computing in
//! `holonic_words::ModularWords`, the device's own ring, over the declared [`hardware_cover`]),
//! symmetric forms and their [`inertia`], the integer Smith reduction ([`rebase_invariants`]),
//! [`exact_value`], [`exact_work`], [`rational_polynomial`] and [`primality`]. They moved here from
//! `holonic-engine`, which re-exports every item at its existing path; behaviour, work receipts and
//! wire formats are unchanged.
//!
//! **The facets** (phase 3a): [`port`] (bonds, power, units), [`dirac`] (kernel-form Dirac
//! structures, composition, interconnection, pushforward), [`complex`] (validated cell complexes,
//! connection incidence and curvature), [`element`] (storage, certified resistance, source, active,
//! pump), [`generator`] (transport, initial configuration, clock, phase lift), [`restriction`] (port
//! maps, scale square, Kron), [`holon`] (the port Holon, the medium, the Holon and its state),
//! [`law`] (`HolonLaw`, `EnergyBalance`, the exact reference motion), [`deposition`] (commit
//! balance, deposit ledger, exact passive projection) and [`conformance`]. Everything computes over
//! `Rat`; the engine consumers adopt them in the later phases.

pub mod exact_linear;
pub mod exact_value;
pub mod exact_work;
pub mod hardware_cover;
pub mod inertia;
pub mod primality;
pub mod prime_image_algebra;
pub mod rational_polynomial;
pub mod rebase_invariants;

pub mod complex;
pub mod conformance;
pub mod deposition;
pub mod dirac;
pub mod element;
pub mod generator;
pub mod holon;
pub mod law;
pub mod port;
pub mod reaction;
pub mod restriction;
pub mod scalar;
