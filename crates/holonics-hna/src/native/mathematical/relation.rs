//! Native binding for a finite calibrated bilinear relation and its condition fibre.
//!
//! Formation and refinement are delegated to `ResidentConstitutiveFibre` and
//! `ResidentConditionImage`. All source, condition and observed-return packets remain native;
//! this adapter never copies a witness into a host weight or selects a fibre representative.

use holonic_engine::{
    native_ecology::constitutive_fibre::{
        ConditionImageReading, ConditionPreimageReading, ConstitutiveFibreError,
        ResidentConditionImage, ResidentConditionPreimage, ResidentConstitutiveCurrent,
        ResidentConstitutiveFibre,
    },
    resident_section::ResidentSurface,
};

/// One continuing caller-calibrated relation. Extents are the admitted finite bilinear chart,
/// not a claim about an unrestricted total linear map.
pub(super) struct NativeConditionRelation<'c> {
    law: ResidentConstitutiveFibre<'c>,
    condition: Option<ResidentConditionPreimage<'c>>,
    pending: Option<(u64, ResidentConditionImage<'c>)>,
    next_prediction: u64,
}

impl<'c> NativeConditionRelation<'c> {
    /// Create the empty finite relation. Calibration rows are admitted by `calibrate`.
    pub fn found(
        surface: &'c ResidentSurface<'c>,
        source_complex: usize,
        condition_complex: usize,
        target_complex: usize,
    ) -> Result<Self, ConstitutiveFibreError> {
        Ok(Self {
            law: ResidentConstitutiveFibre::found_bilinear_contact(
                surface,
                source_complex,
                condition_complex,
                target_complex,
            )?,
            condition: None,
            pending: None,
            next_prediction: 0,
        })
    }

    pub fn occurrences(&self) -> u64 {
        self.law.occurrences()
    }

    /// Admit one supplied source/condition/observation calibration row on the GPU.
    pub fn calibrate(
        &mut self,
        source: ResidentConstitutiveCurrent<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        observed: Option<ResidentConstitutiveCurrent<'_, 'c>>,
    ) -> Result<(), ConstitutiveFibreError> {
        if self.condition.is_some() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        self.law
            .advance_bilinear_contact(source, condition, observed)
            .map(|_| ())
    }

    /// Form the complete native condition preimage for a supplied source and observed output.
    pub fn form_condition(
        &mut self,
        source: ResidentConstitutiveCurrent<'_, 'c>,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<(), ConstitutiveFibreError> {
        if self.condition.is_some() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        self.condition = Some(self.law.read_condition_preimage(source, observed)?);
        Ok(())
    }

    pub fn condition(&self) -> Option<&ResidentConditionPreimage<'c>> {
        self.condition.as_ref()
    }

    /// Prepare one new source image from the contemporary condition family.
    pub fn predict(
        &mut self,
        source: ResidentConstitutiveCurrent<'_, 'c>,
        retain: bool,
    ) -> Result<(Option<u64>, ConditionImageReading), ConstitutiveFibreError> {
        if retain && self.pending.is_some() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let condition = self
            .condition
            .as_ref()
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let image = self.law.read_condition_image(source, condition)?;
        self.retain_image(image, retain)
    }

    /// Transport the whole live source/condition family through a compiled prospective action.
    /// Its output may have any declared width; one shared family supplies every component.
    pub fn predict_through(
        &mut self,
        operator: &ResidentConstitutiveFibre<'c>,
        retain: bool,
    ) -> Result<(Option<u64>, ConditionImageReading), ConstitutiveFibreError> {
        if retain && self.pending.is_some() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let condition = self
            .condition
            .as_ref()
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let image = condition.read_image(operator)?;
        self.retain_image(image, retain)
    }

    fn retain_image(
        &mut self,
        image: ResidentConditionImage<'c>,
        retain: bool,
    ) -> Result<(Option<u64>, ConditionImageReading), ConstitutiveFibreError> {
        let reading = image.inspect()?;
        let id = if retain {
            let id = self.next_prediction;
            let next = id.checked_add(1).ok_or(ConstitutiveFibreError::Shape)?;
            self.pending = Some((id, image));
            self.next_prediction = next;
            Some(id)
        } else {
            None
        };
        Ok((id, reading))
    }

    pub fn pending_id(&self) -> Option<u64> {
        self.pending.as_ref().map(|(id, _)| *id)
    }

    /// Refine the live joint image with an actual observed output. Failed refinement leaves
    /// standing and pending material intact; success publishes the contemporary family.
    pub fn observe_pending(
        &mut self,
        id: u64,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ConditionPreimageReading, ConstitutiveFibreError> {
        let (pending_id, image) = self
            .pending
            .as_ref()
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        if id != *pending_id {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let next = image.receive(observed)?;
        let reading = next.inspect()?;
        self.condition = Some(next);
        self.pending = None;
        Ok(reading)
    }

    pub fn release_prediction(&mut self, id: u64) -> Result<(), ConstitutiveFibreError> {
        if self.pending_id() != Some(id) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        self.pending = None;
        Ok(())
    }
}
