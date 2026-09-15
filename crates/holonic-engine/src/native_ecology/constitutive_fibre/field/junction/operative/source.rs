use super::*;
mod reflection;
mod reflection_commit;
mod reflection_target;
mod rest;
pub use rest::NativeFieldCurrentSourceRest;
pub use reflection_target::NativeFieldReflectionTarget;
pub use reflection::NativeFieldReflection;

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
    packed: Rc<ResidentSection<'c>>,
    material: std::cell::OnceCell<ResidentSection<'c>>,
    reflection: std::cell::OnceCell<ResidentSection<'c>>,
    report: Rc<ResidentSection<'c>>,
    _producing: Rc<OperativeSections<'c>>,
    births: Vec<NativeOperativeContactBirth>,
}

impl<'c> NativeFieldCurrentSource<'c> {
    /// The actual operative D columns in the order of births(), with their full
    /// Frobenius bound. Column identity follows the caused contact population.
    pub fn material(&self)->Result<Option<ResidentNormalEnclosureView<'_, 'c>>,Error>{
        if self.births.is_empty(){return Ok(None);}
        let d=self.boundary_components();let count=self.births.len();
        let width=d.checked_mul(count).ok_or(Error::Shape)?;
        if self.material.get().is_none(){
            let out=self.surface.fresh_section(1,width.checked_add(1).and_then(|v|v.checked_mul(2))
                .ok_or(Error::Shape)?,ResidentGrain(0))?;
            let mut p=self.surface.begin_passage(&[vec![]])?;
            {let lane=p.open(0,&[])?;self.surface.record_field_material_source(&lane,&self._producing.map,
                &self._producing.bounds,d,count,&out)?;}
            p.close(0,&out,64)?;let r=p.finish()?.launch()?;
            if !r.obstruction.is_empty(){return Err(Error::Arithmetic(format!("operative material source: {:?}",r.obstruction)));}
            self.material.set(out).map_err(|_|Error::Uncertain)?;
        }
        Ok(Some(ResidentNormalEnclosureView{surface:self.surface,section:self.material.get().unwrap(),
            offset:0,width,grain:ResidentGrain(self.grain)}))
    }
    /// A material difference in the same field/contact chart. Matching widths
    /// alone do not identify these columns or their causal origins.
    pub fn material_difference(&self,prior:&Self)->Result<ResidentNormalEnclosure<'c>,Error>{
        if !self.same_owner(prior)||self.births!=prior.births{return Err(Error::ForeignOccurrence);}
        self.material()?.ok_or(Error::Shape)?.difference(prior.material()?.ok_or(Error::Shape)?)
    }
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
        if let Some(image) = staging.field.junction.as_ref().and_then(|j| j.valid_joint_current()) {
            if Rc::ptr_eq(&staging.sections.b, &staging.field.junction.as_ref().unwrap().operative.as_ref().unwrap().sections.b) {
                return Ok(NativeFieldCurrentSource {
                    surface, owner, cut, grain: staging.grain, width, packed: Rc::clone(image),
                    material: std::cell::OnceCell::new(), reflection: std::cell::OnceCell::new(),
                    report, _producing: Rc::clone(&staging.sections), births: staging.births.clone(),
                });
            }
        }
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
            packed: Rc::new(packed),
            material:std::cell::OnceCell::new(),
            reflection:std::cell::OnceCell::new(),
            report,
            _producing: Rc::clone(&staging.sections),
            births: staging.births.clone(),
        })
    }
}
