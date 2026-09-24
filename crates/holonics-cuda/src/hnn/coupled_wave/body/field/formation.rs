//! Standing-condition and local formation ports for the operative field.
//!
//! These methods keep the field and its generator neighborhood as one continuing owner. A
//! condition is an actual resident current, the contextual section is derived at the supplied
//! source, and a formation step retains both the pre-target standing and the returned condition
//! family. No resident carrier is read into host numeric state.

use super::*;
use crate::native_ecology::constitutive_fibre::{
    ConstitutiveSourceChart, GeneratorNeighborhoodStep, NeighborhoodEvidence,
};

/// The forecast and deposits use `producing_condition`. `step.prior_condition` is the
/// contemporary standing met by the returning target; `step.contact` retains its full preimage.
pub struct NativeFieldFormation<'input, 'c> {
    pub producing_condition: ResidentConstitutiveCurrent<'input, 'c>,
    pub step: GeneratorNeighborhoodStep<'input, 'c>,
}

impl<'c> FieldModel<'c> {
    pub(in super::super) fn receive_condition(
        &mut self,
        incoming: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<(), NativeSessionError> {
        if incoming.components() != self.condition_width {
            return Err(invalid("field standing condition shape mismatch"));
        }
        let next = self
            .epoch
            .checked_add(1)
            .ok_or_else(|| invalid("field model epoch exhausted"))?;
        self.reaction.receive_condition(incoming)?;
        self.epoch = next;
        Ok(())
    }

    pub(super) fn standing_condition(
        &self,
    ) -> Result<ResidentConstitutiveCurrent<'_, 'c>, NativeSessionError> {
        Ok(self.reaction.condition())
    }

    pub(super) fn contextual_section(
        &self,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentContextualSection<'c>, NativeSessionError> {
        Ok(self
            .reaction
            .generator(self.member)?
            .contextual_section(source)?)
    }

    pub(super) fn last_evidence(&self) -> Option<&NeighborhoodEvidence<'c>> {
        self.reaction.last_received_evidence()
    }

    /// Snapshot the current neighborhood condition before entering the mutable field passage.
    /// The optional held mask uses the same receiver path as `generate_received_field`.
    pub(super) fn generate_standing(
        &mut self,
        input: ResidentNormalInput<'_, 'c>,
        commit: bool,
        retain: bool,
        held: Option<&[bool]>,
    ) -> Result<NativeFieldGeneratedSection<'c>, NativeSessionError> {
        let standing = self.reaction.condition().to_owned(self.field.surface())?;
        let condition = ResidentConstitutiveCurrent::rational(&standing)?;
        self.generate(input, condition, commit, retain, held)
    }

    /// Form one actual local source/condition/target passage through the neighborhood. The
    /// supplied condition is the producing `c` for the normal material return, while the
    /// neighborhood's contemporary standing remains the receiver for contact formation. Its
    /// step retains the pre-target condition and returned condition family; the target is only
    /// the observed reaction target.
    pub(super) fn form_reaction<'input>(
        &mut self,
        source: ResidentConstitutiveCurrent<'input, 'c>,
        condition: ResidentConstitutiveCurrent<'input, 'c>,
        target: ResidentConstitutiveCurrent<'input, 'c>,
    ) -> Result<NativeFieldFormation<'input, 'c>, NativeSessionError>
    where
        'c: 'input,
    {
        let ConstitutiveSourceChart::BilinearContact {
            source_complex,
            condition_complex,
        } = self.reaction.generator(self.member)?.source_chart()
        else {
            return Err(invalid(
                "field formation requires bilinear source/condition chart",
            ));
        };
        let source_width = source_complex
            .checked_mul(2)
            .ok_or_else(|| invalid("field source width overflow"))?;
        let condition_width = condition_complex
            .checked_mul(2)
            .ok_or_else(|| invalid("field condition width overflow"))?;
        let target_width = self
            .reaction
            .predictive_material(self.member)?
            .ok_or_else(|| invalid("absent reaction material"))?
            .targets()
            .checked_mul(2)
            .ok_or_else(|| invalid("field target width overflow"))?;
        if source.components() != source_width
            || condition.components() != condition_width
            || target.components() != target_width
        {
            return Err(invalid(
                "field formation source/condition/target shape mismatch",
            ));
        }
        let next = self
            .epoch
            .checked_add(1)
            .ok_or_else(|| invalid("field model epoch exhausted"))?;
        self.reaction
            .epoch()
            .checked_add(1)
            .ok_or_else(|| invalid("field neighborhood epoch exhausted"))?;
        let step = self.reaction.receive_reaction_observation_at(
            self.member,
            source,
            condition,
            target,
        )?;
        self.epoch = next;
        Ok(NativeFieldFormation {
            producing_condition: condition,
            step,
        })
    }
}
