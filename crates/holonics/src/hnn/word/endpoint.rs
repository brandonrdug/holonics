//! Bound actual producing-cut operands for an unpublished channel C/K endpoint.
//! The existing PowerForm::held and held_rate remain the only work/crossing law.
use super::*;

#[derive(Clone)]
pub(crate) struct ChannelEndpoint {
    field: Field,
    current: Current,
    commit: u64,
    identity: u128,
    before: PowerForm,
    carry: ReceptionCarry,
}

pub(crate) struct ContactEndpoint {
    pub(crate) work: Rat,
    pub(crate) rate: Vec<Rat>,
    pub(crate) forms: [ExactRatMatrix; 2],
}

impl ChannelEndpoint {
    pub(crate) fn bind(
        field: &Field,
        material: &crate::hnn::constitution::Constitution,
        current: &Current,
        change: &EndChange,
        carry: &ReceptionCarry,
    ) -> Result<Self, HnnError> {
        let before = PowerForm::read(field, material, current)?;
        if !carry.fits(field)
            || &carry.change != change
            || carry.conductances != before.conductances
        {
            return Err(HnnError::Unadmitted {
                reason: "a channel endpoint binds the actual producing change, references and canonical momentum",
            });
        }
        for (contact, ((c, state), pi)) in before
            .storage
            .iter()
            .zip(&change.states)
            .zip(&carry.momenta)
            .enumerate()
        {
            if c.apply(&state[1])? != *pi {
                return Err(HnnError::HeldMomentum { contact });
            }
        }
        Ok(Self {
            field: field.clone(),
            current: current.clone(),
            commit: material.commit(),
            identity: material.material_identity(),
            before,
            carry: carry.clone(),
        })
    }

    pub(crate) fn admits_predecessor(
        &self,
        material: &crate::hnn::constitution::Constitution,
    ) -> bool {
        material.commit() == self.commit
            && material.material_identity() == self.identity
            && PowerForm::read(&self.field, material, &self.current)
                .is_ok_and(|form| form == self.before)
    }

    pub(crate) fn momentum(&self, contact: usize) -> &[Rat] {
        &self.carry.momenta[contact]
    }
    pub(crate) fn rate(&self, contact: usize) -> &[Rat] {
        &self.carry.change.states[contact][1]
    }
    pub(crate) fn tick(&self) -> usize {
        self.carry.ticks
    }

    pub(crate) fn contact(
        &self,
        material: &crate::hnn::constitution::Constitution,
        contact: usize,
    ) -> Result<ContactEndpoint, HnnError> {
        if material.material_identity() != self.identity || contact >= self.before.storage.len() {
            return Err(HnnError::Unadmitted {
                reason: "a held channel endpoint keeps its producing declaration and contact",
            });
        }
        let after = PowerForm::read(&self.field, material, &self.current)?;
        // Keep every other form at its producing value. The existing full held
        // owner then reads exactly this contact's combined signed C/K work.
        let mut local = self.before.clone();
        local.storage[contact] = after.storage[contact].clone();
        local.stiffness[contact] = after.stiffness[contact].clone();
        let held = self.before.held(&local, &self.carry.change)?;
        if local.storage[contact].apply(&held.change.states[contact][1])?
            != self.carry.momenta[contact]
        {
            return Err(HnnError::HeldMomentum { contact });
        }
        Ok(ContactEndpoint {
            work: held.deposition,
            rate: held.change.states[contact][1].clone(),
            forms: [
                after.storage[contact].subtract(&self.before.storage[contact])?,
                after.stiffness[contact].subtract(&self.before.stiffness[contact])?,
            ],
        })
    }
}
