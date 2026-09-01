//! The one public Soulkiller dismantling boundary.
//!
//! Input charts may differ, but every admitted input returns the same three physical lanes:
//! productive source-neutral native morphology, cold reconstruction testimony, and native
//! insufficiency. The boundary consumes its input and retains no callable foreign executor.

use crate::native_ecology::holonic_intelligence::{
    DismantlingBoundaryReturn, IntoDismantlingBoundaryReturn,
};
use crate::native_spool::{NativeTransportScaffold, ReceiverInsufficiency};

#[derive(Debug, PartialEq, Eq)]
pub struct SoulkillerDismantlingReturn<ColdWitness> {
    pub native: NativeTransportScaffold,
    pub exterior: ColdWitness,
    pub insufficiency: ReceiverInsufficiency,
}

impl<ColdWitness> DismantlingBoundaryReturn for SoulkillerDismantlingReturn<ColdWitness> {
    type Productive = NativeTransportScaffold;
    type ColdWitness = ColdWitness;
    type Insufficiency = ReceiverInsufficiency;

    fn productive(&self) -> &Self::Productive {
        &self.native
    }

    fn cold_witness(&self) -> &Self::ColdWitness {
        &self.exterior
    }

    fn insufficiency(&self) -> &Self::Insufficiency {
        &self.insufficiency
    }
}

impl<ColdWitness> IntoDismantlingBoundaryReturn for SoulkillerDismantlingReturn<ColdWitness> {
    fn into_lanes(self) -> (Self::Productive, Self::ColdWitness, Self::Insufficiency) {
        (self.native, self.exterior, self.insufficiency)
    }
}

pub trait SoulkillerDismantlingInput: Sized {
    type ColdWitness;
    type Error;

    fn dismantle(self) -> Result<SoulkillerDismantlingReturn<Self::ColdWitness>, Self::Error>;
}

/// Consume one admitted exterior chart through the sole Soulkiller boundary.
pub fn dismantle<Input>(
    input: Input,
) -> Result<SoulkillerDismantlingReturn<Input::ColdWitness>, Input::Error>
where
    Input: SoulkillerDismantlingInput,
{
    input.dismantle()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native_ecology::holonic_intelligence::Bf16ExcitationDismantling;
    use crate::soulkiller::scrapyard::ReachableSectionDismantling;

    fn admitted<Input: SoulkillerDismantlingInput>() {}

    #[test]
    fn generic_reachable_and_bf16_charts_enter_one_public_boundary() {
        admitted::<Bf16ExcitationDismantling>();
        admitted::<ReachableSectionDismantling<'static>>();
    }
}
