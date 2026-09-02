use std::collections::BTreeSet;

use holonic_engine::{
    native_ecology::holonic_intelligence::NativeEmissionAddress,
    receiver_history_compression::NativeStateId, BoundaryId, EventId, ExactComplexWaveCurrent,
};
use life::native_intelligence::{ReturnedScaffoldInteraction, ScaffoldCultivationError};
use num_rational::BigRational as Rat;

/// Found one explicit genuinely later exterior interaction at the neutral return port.
pub fn returned_local_interaction(
    emitted: NativeEmissionAddress,
    occurrence: EventId,
    boundary: BoundaryId,
    current: ExactComplexWaveCurrent,
    storage: Rat,
    additional_support: BTreeSet<NativeStateId>,
) -> Result<ReturnedScaffoldInteraction, ScaffoldCultivationError> {
    ReturnedScaffoldInteraction::found(
        emitted,
        occurrence,
        boundary,
        current,
        storage,
        additional_support,
    )
}
