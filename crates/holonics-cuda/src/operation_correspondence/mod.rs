//! Complete source/native operation correspondence for Phoenix W1.

mod errors;
mod schema;
mod validation;

#[cfg(test)]
mod tests;

pub use errors::{CorrespondenceRefusal, CoverageReceipt};
pub use schema::{
    NativeGraphIdentity, NativeOperationBinding, OpenRemainder, OperationCorrespondence,
    OperationCorrespondenceSeal, OperationResolution, PopulationCorrespondence,
    PopulationResolution, PortCorrespondence, SourceOperationOccurrence, topology_identity,
};
