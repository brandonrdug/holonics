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
//! Phase 2 (the core base) creates the facet modules empty. Their types arrive in phase 3 and
//! later, from the existing owners the plan's facet survey names.

pub mod complex;
pub mod conformance;
pub mod dirac;
pub mod element;
pub mod generator;
pub mod holon;
pub mod law;
pub mod port;
pub mod restriction;
pub mod scalar;
