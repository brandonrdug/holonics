use super::*;

/// A realized exterior face with exclusive ownership of its held native successor.
pub struct SourceNeutralPendingExteriorEmission {
    pub(super) circulation: SourceNeutralExteriorCirculation,
    pub(super) emission: SourceNeutralExteriorEmission,
    pub(super) target_current_address: ResidentCurrentAddress,
}

/// A separately crossed exterior occurrence and its exact q/U-or-fibre receipt.
pub struct SourceNeutralReturnedExteriorCirculation {
    pub(super) circulation: SourceNeutralExteriorCirculation,
    pub(super) returned: SourceNeutralExteriorInferenceReturn,
}

/// A delivered boundary occurrence whose native continuation remains unchanged.
pub struct SourceNeutralAcknowledgedExteriorCirculation {
    pub(super) circulation: SourceNeutralExteriorCirculation,
    pub(super) returned: SourceNeutralExteriorDeliveryReturn,
}

/// Terminal result which returns both the measured radiation and the same resident Athena body.
pub struct SourceNeutralExteriorTerminalReturn {
    pub(super) resident: ResidentSourceNeutralAthena,
    pub(super) radiation: SourceNeutralExteriorRadiation,
}

/// One ownership-enforced exterior deed.
pub enum SourceNeutralExteriorStep {
    Emission(SourceNeutralPendingExteriorEmission),
    Terminal(SourceNeutralExteriorTerminalReturn),
}
