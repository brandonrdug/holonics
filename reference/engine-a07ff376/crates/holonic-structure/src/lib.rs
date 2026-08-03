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

#![no_std]

extern crate alloc;
#[cfg(test)]
extern crate std;

mod branch_lineage;
mod keyed_atlas;
mod local_population;
mod local_sequence;
mod membrane;
mod ordinal_atlas;
mod relation_atlas;

pub use branch_lineage::{BranchForkReceipt, BranchLineage, BranchLineageIter};
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
pub use relation_atlas::{
    FrozenRelationAtlas, FrozenRelationBuilder, FrozenRelationIter, LocalRelationIter,
    LocalRelations, LocalRelationsIntoIter, RelationAtlasError, RelationSpan,
};
