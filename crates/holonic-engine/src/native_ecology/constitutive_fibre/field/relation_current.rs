//! The current field relation received at an actual historical source, entirely on the device.
//! Both source branches cross their producing frame into the contemporary relation frame.

use super::*;

impl<'chart> NativeConstitutiveField<'chart> {
    /// Read the contemporary local relation at an available source anchor. The target is the
    /// field's original root receiving chart. This observer neither advances the ecology nor
    /// consumes/issues a receiving capability; its immutable return may feed a later native port.
    /// Archived source placement is ordinary cold I/O and is separately counted by its owner.
    pub fn read_constitutive_source(
        &mut self,
        source: &NativeFieldSourceAnchor,
    ) -> Result<ResidentConstitutiveReturn<'chart>, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if !Rc::ptr_eq(&source.owner, &self.owner) || source.occurrence >= self.history.len() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        self.mount_history_source(source.occurrence)?;
        let surface = self.relation.surface;
        let nodes = self.nodes();
        let transformed = surface.fresh_section(1, 4 * nodes + 1, ResidentGrain(0))?;
        let mut returned = self
            .relation
            .allocate_current_return(self.relation.occurrences)?;
        let mut passage = surface.begin_passage(&[vec![], vec![0]])?;
        {
            let lane = passage.open(0, &[])?;
            let history = &self.history[source.occurrence];
            surface.record_field_source_frame(
                &lane,
                &history.resident()?.section,
                &history.frame.native,
                &self.frame.native,
                nodes,
                &transformed,
            )?;
        }
        passage.close(0, &transformed, 64)?;
        {
            let lane = passage.open(1, &[0])?;
            surface.record_constitutive_query(
                &lane,
                &self.relation.basis,
                ResidentConstitutiveCurrent {
                    section: &transformed,
                    offset: 0,
                    width: 4 * nodes,
                    denominator: Some(4 * nodes),
                    disposition: None,
                },
                returned.report(),
            )?;
        }
        passage.close(1, returned.report(), 64)?;
        let reading = passage.finish()?.launch()?;
        if !reading.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "{:?}",
                reading.obstruction
            )));
        }
        returned.qualify_field_source(source.occurrence);
        Ok(returned)
    }
}

#[cfg(test)]
mod tests;
