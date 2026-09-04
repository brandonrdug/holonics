//! R5's exact joint-media boundary over M0, I4, and the retained causal predecessor.
//!
//! The standing stores one shared port/world subcomplex and only the future-visible candidate
//! multiplicities of the held-out occurrence. Exact modality interiors and complete candidate
//! fibres depart into decoder/fibre owners and can be reopened without their source files.

mod rest;
mod types;
mod validation;
mod wire;

pub use rest::MultimodalTransportRest;
pub use types::{
    AnchorSection, ExactMediaAxis, ExactSpatialDeclaration, FamilyCorrespondenceFibre,
    JointMediaDecoder, JointMediaFibres, JointMediaStanding, MathematicalMediaPort,
    MediaCandidatePair, MediaNaturalitySquare, MediaPortDeclaration, MediaSourceFamily,
    MediaSourceInterior, NativeMediaConsequence, NativeMediaFibre, ProductLineage,
    SharedMediaContact, SharedMediaHigherCell, SharedMediaSubcomplex, SharedMediaVertex,
    UnmatchedMediaMember, JOINT_MEDIA_DECODER_SCHEMA, JOINT_MEDIA_FIBRES_SCHEMA,
    JOINT_MEDIA_STANDING_SCHEMA,
};
pub use validation::MultimodalTransportRefusal;

#[cfg(test)]
mod tests;
