//! Production-owned structural carriers for exact holonic computation.
//!
//! These types encapsulate the few administrative data structures which recurring causal
//! machinery actually needs. Their hidden allocation substrate is not ontology: page size,
//! directory position, and contiguous row offsets never become source identity, chronology, or
//! receiver testimony.
//!
//! The crate deliberately does not define a universal event, scalar state, modality, or wire
//! format. [`CausalMembrane`] instead preserves each application's typed occurrence and return
//! while giving both reference laws and live machines one atomic receiving contract.
//!
//! # The discipline was only half of one until 2026-08-15
//!
//! Everything above is a **negative** discipline: it stops a substrate container from becoming
//! ontology. It never supplied the geometry that should have been there instead, and the cost was
//! measurable — the traversal carriers addressed by **index** while `crates/holonic-body/src/arrow.rs`, one
//! floor down, already addressed by **turn**. [`BranchLineage`] is the proof: a genuinely holonic
//! ancestry whose link is a raw pointer and a count.
//!
//! [`Relating`], [`Chain`] and [`Face`] are the positive half. A link carries a reach that **weighs**
//! and a hand that **gates**; a chain has both ends open and retains what did not connect; an index
//! is a scalar face whose relation stays askable. Plan:
//! `archive/plans/THE_TRAVERSIBLE_CHAIN.md`.

#![no_std]

extern crate alloc;
#[cfg(test)]
extern crate std;

mod branch_lineage;
mod chain;
mod face;
mod gauge;
mod junction;
mod keyed_atlas;
mod local_population;
mod local_sequence;
mod membrane;
mod ordinal_atlas;
mod relating;
mod relation_atlas;

pub use branch_lineage::{BranchForkReceipt, BranchLineage, BranchLineageIter};
pub use chain::{Chain, ChainEnd, Disposition, Unconnected};
pub use face::Face;
pub use gauge::{DeclaredGauge, TrivialGauge};
pub use junction::CountedCrossing;
pub use keyed_atlas::{
    GrowingKeyAtlas, KeyAtlasError, KeyAtlasIter, KeyAtlasKeys, KeyAtlasMemory, KeyAtlasValues,
};
pub use local_population::{
    LocalQueue, LocalSet, LocalSetIntersection, LocalSetIter, LocalStructureError,
};
pub use local_sequence::LocalSequence;
pub use membrane::CausalMembrane;
pub use ordinal_atlas::{
    OrdinalAtlasError, OrdinalAtlasIter, OrdinalAtlasMemory, OrdinalAtlasValues, SparseOrdinalAtlas,
};
pub use relating::{Composes, Hand, Relating};
pub use relation_atlas::{
    FrozenRelationAtlas, FrozenRelationBuilder, FrozenRelationIter, LocalRelationIter,
    LocalRelations, LocalRelationsIntoIter, RelationAtlasError, RelationSpan,
};
