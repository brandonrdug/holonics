use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::{
    native_spool::NativeTransportScaffold, receiver_history_compression::NativeStateId, EventId,
};
use life::native_intelligence::{NativeDiffusionLaw, NativeSessionError};
use num_rational::BigRational as Rat;

/// Admit one exact application-declared diffusion realization over native incidence.
pub fn declared_diffusion_law(
    morphology: &NativeTransportScaffold,
    spool: &str,
    capacities: BTreeMap<NativeStateId, Rat>,
    conductances: BTreeMap<EventId, Rat>,
    boundary: BTreeSet<NativeStateId>,
) -> Result<NativeDiffusionLaw, NativeSessionError> {
    NativeDiffusionLaw::found(morphology, spool, capacities, conductances, boundary)
}
