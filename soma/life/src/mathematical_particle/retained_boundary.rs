//! R4's retained causal boundary over addressed mathematical inquiry histories.
//!
//! Receiver/history refinement and native transport already belong to `holonic-engine`.  This
//! module adds only the absent consequence: exact historical interiors depart from hot standing
//! into a complete reconstruction fibre while every admitted future receiver and generator still
//! factors through the native boundary.  A richer later receiver may reopen that fibre.

mod rest;
mod system;
mod types;
mod validation;

#[cfg(test)]
mod tests;

pub use system::AddressedHistorySystem;
pub use types::{
    BoundaryRecurrence, CultivatedActionLineage, HistoricalInterior, HistoricalSourceMember,
    LongHorizonBoundaryError, LongHorizonRetainedBoundary, OrderedBoundaryHolonomy,
    RetainedBoundaryDecoder, RetainedBoundaryFibres, RetainedBoundaryStanding,
    RicherReceiverReopening, LONG_HORIZON_DECODER_SCHEMA, LONG_HORIZON_FIBRES_SCHEMA,
    LONG_HORIZON_STANDING_SCHEMA,
};
