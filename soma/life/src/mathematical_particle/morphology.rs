//! Returned world constraints founding one attributable local derivation morphology.
//!
//! R2 owns the source-detached finite recurrence. This relation consumes that standing, composes
//! the exact receiver adjoint, and offers one local action change to the resident apparatus. A
//! decline gives the predecessor back; withdrawal consumes a successor and returns that exact
//! predecessor. It adds no solver, trainer, route label, or second ecology.

mod algebra;
mod candidate;
mod rest;
mod types;

pub use types::{
    CausingForwardLineage, ConstitutiveActionChange, ConstraintReceiver, CultivationHolonomy,
    DynamicMorphologyCandidate, DynamicMorphologyError, DynamicMorphologyRest,
    ExactSupportSubcomplex, ExactWithdrawal, LocalMorphologyDelta, MorphologyCompatibilityReceipt,
    MorphologyDecision, ReconstructionFibreChange, ReturnedConstraintOccurrence,
    ReturnedReceiverAdjoint, WithdrawalReceipt,
};

pub const DYNAMIC_MORPHOLOGY_SCHEMA: &str = "holonics.r3.dynamic-local-morphology-rest.v1";

#[cfg(test)]
mod tests;
