//! Conditional source sections used to evaluate an entire dependent return generator.
use super::*;
/// Constructive coordinates of the declared family receiver, retaining all coordinate aliases.
/// The kernel of this coordinate map decodes to zero source difference.
pub struct NormalReceiverCoordinates<'a, 'c> {
    source: &'a NormalWaveFamily<'c>,
    coordinates: ResidentSection<'c>,
    fibre: ResidentConstitutiveReturn<'c>,
}
impl<'a, 'c> NormalReceiverCoordinates<'a, 'c> {
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        self.source
    }
    pub fn coordinates(&self) -> &ResidentSection<'c> {
        &self.coordinates
    }
    pub fn coordinate_fibre(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.fibre
    }
    /// The original source decoder retains the full coordinate kernel. This packet merely
    /// encodes its declared receiver face; it does not replace the source or the generator.
    pub fn into_coordinates(self) -> ResidentSection<'c> {
        self.coordinates
    }
}
impl<'c> NormalWaveFamily<'c> {
    pub fn receiver_coordinates(
        &self,
    ) -> Result<NormalReceiverCoordinates<'_, 'c>, ConstitutiveFibreError> {
        let s = self.origin.fibre().surface;
        let t = self.relation.target_width();
        let receiver = self.read_receiver()?.into_report();
        let graph = s.fresh_section(2 * t, 2 * t, ResidentGrain(0))?;
        let coordinates = s.fresh_section(1, t + 1, ResidentGrain(0))?;
        let fibre = ResidentConstitutiveReturn::allocate(
            s,
            t,
            t,
            self.relation.occurrence(),
            ConstitutiveSourceChart::Linear,
        )?;
        let workspace = s.fresh_section(1, 8 * t, ResidentGrain(0))?;
        let mut p = s.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            s.record_coupled_receiver_coordinates(
                &lane,
                self.relation.report(),
                self.relation.source_width(),
                t,
                &receiver,
                &graph,
                &coordinates,
                fibre.report(),
                &workspace,
            )?;
        }
        p.close(0, &coordinates, 64)?;
        let result = p.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "source receiver coordinates: {:?}",
                result.obstruction
            )));
        }
        Ok(NormalReceiverCoordinates {
            source: self,
            coordinates,
            fibre,
        })
    }
    pub(in super::super) fn parameter_section(
        &self,
        parameters: &ResidentSection<'c>,
        anchor: &ResidentSection<'c>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        let s = self.origin.fibre().surface;
        let t = self.relation.target_width();
        let returned = ResidentConstitutiveReturn::allocate(
            s,
            1,
            t,
            self.relation.occurrence(),
            ConstitutiveSourceChart::Linear,
        )?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_coupled_family_section(
                &lane,
                self.relation.report(),
                self.relation.source_width(),
                t,
                parameters,
                anchor,
                returned.report(),
            )?;
        }
        passage.close(0, returned.report(), 64)?;
        let result = passage.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "dependent source section: {:?}",
                result.obstruction
            )));
        }
        Ok(returned)
    }
    /// The image and final map come from the actual retained word; source restriction has not
    /// changed its clock. The caller retains the parameter assignment and complete original domain.
    pub(in super::super) fn parameter_image(
        &self,
        relation: ResidentConstitutiveReturn<'c>,
        last: Rc<ResidentWaveRelation<'c>>,
        coverage: ResidentSection<'c>,
        passages: u64,
    ) -> Self {
        Self {
            origin: Rc::clone(&self.origin),
            relation,
            last_relation: Some(last),
            affine_coverage: Some(coverage),
            passages,
        }
    }
}
