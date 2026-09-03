//! The one public Soulkiller dismantling boundary.
//!
//! Input charts may differ, but every admitted input returns the same three physical lanes:
//! a productive source-neutral native morphology, cold reconstruction testimony, and native
//! insufficiency. The boundary consumes its input and retains no callable foreign executor.
//! The productive lane's type is the input's to declare: a spool complex from admitted exterior
//! testimony, or the cone-restricted ecology of an excited resident realization; a manifestation
//! that carries no lift declares no productive type and does not cross.

use crate::native_ecology::holonic_intelligence::{
    DismantlingBoundaryReturn, IntoDismantlingBoundaryReturn,
};

#[derive(Debug, PartialEq, Eq)]
pub struct SoulkillerDismantlingReturn<Productive, ColdWitness, Insufficiency> {
    pub native: Productive,
    pub exterior: ColdWitness,
    pub insufficiency: Insufficiency,
}

impl<Productive, ColdWitness, Insufficiency> DismantlingBoundaryReturn
    for SoulkillerDismantlingReturn<Productive, ColdWitness, Insufficiency>
{
    type Productive = Productive;
    type ColdWitness = ColdWitness;
    type Insufficiency = Insufficiency;

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

impl<Productive, ColdWitness, Insufficiency> IntoDismantlingBoundaryReturn
    for SoulkillerDismantlingReturn<Productive, ColdWitness, Insufficiency>
{
    fn into_lanes(self) -> (Self::Productive, Self::ColdWitness, Self::Insufficiency) {
        (self.native, self.exterior, self.insufficiency)
    }
}

pub trait SoulkillerDismantlingInput: Sized {
    type Productive;
    type ColdWitness;
    type Insufficiency;
    type Error;

    fn dismantle(
        self,
    ) -> Result<
        SoulkillerDismantlingReturn<Self::Productive, Self::ColdWitness, Self::Insufficiency>,
        Self::Error,
    >;
}

/// Consume one admitted exterior chart through the sole Soulkiller boundary.
pub fn dismantle<Input>(
    input: Input,
) -> Result<
    SoulkillerDismantlingReturn<Input::Productive, Input::ColdWitness, Input::Insufficiency>,
    Input::Error,
>
where
    Input: SoulkillerDismantlingInput,
{
    input.dismantle()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native_spool::fixture;
    use crate::soulkiller::scrapyard::ReachableSectionDismantling;

    fn admitted<Input: SoulkillerDismantlingInput>() {}

    #[test]
    fn the_generic_reachable_chart_enters_one_public_boundary() {
        admitted::<ReachableSectionDismantling<'static>>();
    }

    #[test]
    fn a_declared_native_body_presents_the_same_three_physical_lanes() {
        let returned = fixture::returned();
        assert_eq!(returned.productive(), &fixture::scaffold());
        assert_eq!(returned.cold_witness(), &());
        assert_eq!(returned.insufficiency(), &fixture::insufficiency());
        let (native, exterior, insufficiency) = returned.into_lanes();
        native.validate().expect("productive lane");
        assert_eq!(exterior, ());
        insufficiency.validate().expect("insufficiency lane");
    }
}
