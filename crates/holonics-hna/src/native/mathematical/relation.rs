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

use super::super::CurrentWire;
use super::{invalid, NativeSessionError, RationalWire};
use holonic_engine::native_ecology::constitutive_fibre::{
    ResidentNormalEnclosure, ResidentNormalMaterial,
};
use holonic_engine::resident_section::ResidentSection;
use serde_json::{json, Value};

fn normal_face(
    value: &holonic_engine::native_ecology::constitutive_fibre::NativeFieldCurrentBall,
) -> Value {
    json!({"center":value.center.iter().map(CurrentWire::from_current).collect::<Vec<_>>(),
        "radius":RationalWire::from_rational(&value.radius),"scope":"one joint Euclidean enclosure"})
}

/// One fitted source/condition relation. The two immutable operator handles are actual
/// restrictions of one preparation packet, not semantic labels or expected-answer routing.
pub(super) struct NativeConditionalPredictor<'c> {
    pub source_operator: u64,
    pub condition_operator: u64,
    pub material: ResidentNormalMaterial<'c>,
    pending: Option<(u64, ResidentSection<'c>, ResidentNormalEnclosure<'c>)>,
    next_prediction: u64,
}
impl<'c> NativeConditionalPredictor<'c> {
    pub fn new(
        source_operator: u64,
        condition_operator: u64,
        material: ResidentNormalMaterial<'c>,
    ) -> Self {
        Self {
            source_operator,
            condition_operator,
            material,
            pending: None,
            next_prediction: 0,
        }
    }
    pub fn pending_id(&self) -> Option<u64> {
        self.pending.as_ref().map(|p| p.0)
    }
    pub fn predict(
        &mut self,
        features: ResidentSection<'c>,
        retain: bool,
    ) -> Result<Value, NativeSessionError> {
        if retain && self.pending.is_some() {
            return Err(invalid(
                "observe or dispose of the pending section prediction first",
            ));
        }
        let next = self
            .next_prediction
            .checked_add(u64::from(retain))
            .ok_or_else(|| invalid("prediction addresses exhausted"))?;
        let forecast = self
            .material
            .read(ResidentConstitutiveCurrent::rational(&features)?)?
            .into_forward();
        let output = forecast.inspect()?;
        let prediction = if retain {
            let id = self.next_prediction;
            self.pending = Some((id, features, forecast));
            self.next_prediction = next;
            Some(id)
        } else {
            None
        };
        Ok(
            json!({"status":"section-predicted","prediction":prediction,"output":normal_face(&output),
            "observations":self.material.observations(),"scope":"joint normal-reference enclosure from pre-target resident source/condition features"}),
        )
    }
    pub fn observe(
        &mut self,
        id: u64,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<Value, NativeSessionError> {
        let (pending, features, forecast) = self
            .pending
            .as_ref()
            .ok_or_else(|| invalid("no pending section prediction"))?;
        if *pending != id {
            return Err(invalid("foreign section prediction"));
        }
        // Complete the original forecast read before any formation; it is not recomputed
        // using material changed by intervening observations.
        let producing = forecast.inspect()?;
        let returned = self
            .material
            .receive(ResidentConstitutiveCurrent::rational(features)?, observed)?;
        let report = returned.inspect_after();
        drop(returned);
        // The native return succeeded. A later observer failure must not permit applying
        // that observation a second time on retry.
        self.pending = None;
        let report = report.map_err(|e| {
            invalid(format!(
                "section observation consumed; receiver read failed: {e}"
            ))
        })?;
        Ok(
            json!({"status":"section-observed","prediction_consumed":id,"producing_forecast":normal_face(&producing),
            "return":report,"observations":self.material.observations()}),
        )
    }
    pub fn release(&mut self, id: u64) -> Result<(), NativeSessionError> {
        if self.pending_id() != Some(id) {
            return Err(invalid("foreign section prediction"));
        }
        self.pending = None;
        Ok(())
    }
}

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
