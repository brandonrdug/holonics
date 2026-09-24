/// One typed, atomic receiving membrane.
///
/// A membrane does not erase the morphology of its application in order to become reusable.
/// `Occurrence<'a>` may borrow a complete incidence complex, a mathematical event, or any other
/// world-owned material section. `Return` remains the exact receiver testimony caused by that
/// occurrence. Implementations commit a successor only after the complete local law succeeds.
pub trait CausalMembrane {
    type Standing: ?Sized;
    type Occurrence<'a>
    where
        Self: 'a;
    type Return;
    type Error;

    fn standing(&self) -> &Self::Standing;

    fn receive_occurrence<'a>(
        &mut self,
        occurrence: Self::Occurrence<'a>,
    ) -> Result<Self::Return, Self::Error>
    where
        Self: 'a;
}
