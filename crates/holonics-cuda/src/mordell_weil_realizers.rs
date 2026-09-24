//! Supported realizer populations on an elliptic quartic, exactly, with a float-free independence
//! certificate. The implementation is partitioned by its established construction owners.

mod curve;
mod foundation;
mod receivers;
mod sections;

pub use curve::{ExactCurve, IndependenceCertificate, QuarticChart, independence_certificate};
pub use foundation::{
    IntegralQuartic, MinimalModel, RealizerSextuple, RemainderQuartic, SextupleRefusal,
    elementary_symmetric, minimalise, primes_upto,
};
pub use receivers::{
    ReceiverPartition, ResidualReceivers, RolledWheel, WHEEL_APERTURE, WheelPreparation,
    cell_of_trace, complete_to_sextuple, height_ceiling_from_published_log, is_negation_symmetric,
    partitions_from_traces,
};
pub use sections::LinearSection;

#[cfg(test)]
pub(crate) use sections::is_perfect_square_for_test;

#[cfg(test)]
mod tests;
