use super::*;

#[cfg(test)]
mod tests;

/// An immutable resident source port joining the actual outgoing field current with every
/// operative internal `b` coordinate. The packed enclosure is an outer receiver; the report,
/// operative sections, births, and owner remain attached as finer source witnesses.
pub struct NativeFieldCurrentSource<'c> {
    surface: &'c ResidentSurface<'c>,
    owner: Rc<()>,
    cut: usize,
    grain: u32,
    width: usize,
    packed: ResidentSection<'c>,
    report: Rc<ResidentSection<'c>>,
    _producing: Rc<OperativeSections<'c>>,
    births: Vec<NativeOperativeContactBirth>,
}

impl<'c> NativeFieldCurrentSource<'c> {
    pub fn occurrence(&self) -> Option<usize> {
        self.cut.checked_sub(1)
    }
    pub fn field_cut(&self) -> usize {
        self.cut
    }
    pub fn boundary_components(&self) -> usize {
        self.width - self.internal_components()
    }
    pub fn internal_components(&self) -> usize {
        self.births.len() * 2
    }
    pub fn births(&self) -> &[NativeOperativeContactBirth] {
        &self.births
    }
    pub fn same_owner(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.owner, &other.owner)
    }
    pub fn outgoing_report(&self) -> &ResidentSection<'c> {
        &self.report
    }
    pub fn enclosure(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.surface,
            section: &self.packed,
            offset: 0,
            width: self.width,
            grain: ResidentGrain(self.grain),
        }
    }
}

impl<'c> NativeConstitutiveField<'c> {
    /// Pack the actual outgoing junction block and all operative internal coordinates into one
    /// resident outer enclosure. No numerical readout or field mutation occurs.
    pub fn read_current_source(&mut self) -> Result<NativeFieldCurrentSource<'c>, Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        let nodes = self.nodes();
        let junction = self.junction.as_ref().ok_or(Error::Shape)?;
        let report = Rc::clone(&junction.current);
        let surface = self.relation.surface;
        let owner = Rc::clone(&self.owner);
        let cut = self.history.len();
        let staging = self.stage_operative_contacts()?;
        let count = staging.births.len();
        let d = nodes.checked_mul(6).ok_or(Error::Shape)?;
        let width = d
            .checked_add(count.checked_mul(2).ok_or(Error::Shape)?)
            .ok_or(Error::Shape)?;
        let packed = surface.fresh_section(1, 2 * (width + 1), ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_field_current_source(
                &lane,
                &report,
                &staging.sections.b,
                &staging.sections.bounds,
                nodes,
                count,
                &packed,
            )?;
        }
        passage.close(0, &packed, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "field current source: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeFieldCurrentSource {
            surface,
            owner,
            cut,
            grain: staging.grain,
            width,
            packed,
            report,
            _producing: Rc::clone(&staging.sections),
            births: staging.births.clone(),
        })
    }
}
