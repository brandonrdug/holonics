//! **The dependent lift of a return, read at the contemporary cut.**
//!
//! [definition] The source family of a pending comparison is indexed by `θ`, with jointly
//! produced operands `x(θ)` and `η(θ) = v − c(θ)` (`Mathematics/DependentConstitutiveReturn.lean`).
//! At the contemporary relation `R` and condition `h₀` the point constitutive law applied under
//! one assignment gives `(h_θ, R_θ)`; the family `θ ↦ (h_θ, R_θ)` is a generator of
//! alternatives, never the span or union of their material rows.
//!
//! [definition; agent-inferred] Phase 12b: every alternative is read at the *contemporary*
//! family and constitution. `evaluate(θ)` substitutes one resident `θ` packet into both operands
//! (checking the original anchor on the device), prepares the point consequence and moves the
//! contemporary family one passage through it; nothing is published. A return publishes the
//! declared section (`ResidentNormalWave::return_coupled_prediction`); the other sections are
//! readings of the pending comparison, not retained state after publication.
use super::*;
use crate::native_ecology::constitutive_fibre::resident::ResidentNeighborhoodAlternative;
use crate::native_ecology::constitutive_fibre::{
    AffineContactReading, ConstitutiveFibreReturn, PreparedConditionContact,
};

/// Exclusive access fixes the contemporary condition/material cut while this dependent law
/// is evaluated. It borrows a comparison read at that cut; it does not clone the ecology.
pub struct CoupledConstitutiveFamily<'w, 'j, 'c> {
    wave: &'w mut ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
    comparison: &'j NormalCoupledComparison<'c>,
}

/// One evaluated conditional consequence at the contemporary cut. It has deliberately no
/// publication method: a parameter substitution is not evidence that this alternative was the
/// actual source.
pub struct CoupledConstitutiveAlternative<'p, 'j, 'c> {
    comparison: &'j NormalCoupledComparison<'c>,
    parameters: &'p ResidentSection<'c>,
    source: ResidentSection<'c>,
    difference: ResidentSection<'c>,
    anchor: ResidentSection<'c>,
    consequence: ResidentNeighborhoodAlternative<'c>,
    relation: Rc<ResidentWaveRelation<'c>>,
    current: Rc<NormalWaveFamily<'c>>,
    successor: Rc<NormalWaveFamily<'c>>,
}

impl<'w, 'j, 'c> CoupledConstitutiveFamily<'w, 'j, 'c> {
    pub fn comparison(&self) -> &NormalCoupledComparison<'c> {
        self.comparison
    }
    pub fn source_parameters(&self) -> usize {
        self.comparison.parameter_rows() - 1
    }
    /// Substitute a bound source coordinate. Neither producing-condition equality nor an old
    /// relation-membership witness is required: the condition is allowed to REACT to a return
    /// that the old relation cannot represent. The original source bound remains mandatory.
    pub fn evaluate<'p>(
        &mut self,
        parameters: &'p ResidentSection<'c>,
    ) -> Result<CoupledConstitutiveAlternative<'p, 'j, 'c>, ConstitutiveFibreError> {
        let c = self.comparison;
        self.wave.is_contemporary(c)?;
        let (source, difference, anchor) = read_return_operands(c, parameters)?;
        let consequence = self.wave.continuation.neighborhood.prepare_consequence_at(
            c.member(),
            ResidentConstitutiveCurrent::rational(&source)?,
            Some(ResidentConstitutiveCurrent::rational(&difference)?),
            Some(c.relation().fixed_condition()),
        )?;
        let relation = Rc::new(self.wave.neighborhood().read_wave_relation_in_chart(
            c.member(),
            c.relation().roots(),
            c.relation().source_receiver(),
            Some(&consequence),
        )?);
        let current = self.wave.current_shared();
        let successor = Rc::new(current.read_through(Rc::clone(&relation))?);
        Ok(CoupledConstitutiveAlternative {
            comparison: c,
            parameters,
            source,
            difference,
            anchor,
            consequence: consequence.into_alternative()?,
            relation,
            current,
            successor,
        })
    }
}

impl<'p, 'j, 'c> CoupledConstitutiveAlternative<'p, 'j, 'c> {
    pub fn comparison(&self) -> &NormalCoupledComparison<'c> {
        self.comparison
    }
    pub fn parameters(&self) -> &'p ResidentSection<'c> {
        self.parameters
    }
    pub fn source(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        ResidentConstitutiveCurrent::rational(&self.source).expect("constructed source")
    }
    pub fn observed_difference(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        ResidentConstitutiveCurrent::rational(&self.difference).expect("constructed difference")
    }
    pub fn condition(&self) -> &PreparedConditionContact<'c> {
        &self.consequence.condition
    }
    pub fn prediction(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.consequence.prediction
    }
    pub fn formation(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.consequence.formation
    }
    /// This map is conditional on `θ`: the member law developed by this alternative's operands.
    pub fn conditional_relation(&self) -> &ResidentWaveRelation<'c> {
        &self.relation
    }
    /// The contemporary family the alternative acts on.
    pub fn current_section(&self) -> &NormalWaveFamily<'c> {
        &self.current
    }
    /// The proposed contemporary passage through the new conditional material and condition.
    pub fn successor_section(&self) -> &NormalWaveFamily<'c> {
        &self.successor
    }
    pub fn read_formed_source(
        &self,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        self.consequence
            .material
            .action()
            .read_bilinear(source, self.consequence.condition.successor())
    }
    pub fn inspect_condition(&self) -> Result<AffineContactReading, ConstitutiveFibreError> {
        self.condition().inspect()
    }
    pub fn inspect_formation(&self) -> Result<ConstitutiveFibreReturn, ConstitutiveFibreError> {
        self.formation().inspect()
    }
    pub fn inspect_anchor_difference(&self) -> Result<Vec<Rat>, ConstitutiveFibreError> {
        let s = self.comparison.source().origin().fibre().surface;
        let a = wides(&s.read_out(&self.anchor)?)?;
        if a[0] != 0 || a[1] <= 0 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        Ok(a[2..]
            .iter()
            .map(|v| Rat::new((*v).into(), a[1].into()))
            .collect())
    }
}

impl<'c> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    /// The dependent lift of a comparison read at the contemporary cut; a comparison read at an
    /// earlier cut refuses (re-read it).
    pub fn read_coupled_constitutive_family<'w, 'j>(
        &'w mut self,
        comparison: &'j NormalCoupledComparison<'c>,
    ) -> Result<CoupledConstitutiveFamily<'w, 'j, 'c>, ConstitutiveFibreError> {
        self.is_contemporary(comparison)?;
        self.neighborhood().require_usable()?;
        Ok(CoupledConstitutiveFamily {
            wave: self,
            comparison,
        })
    }
}

#[cfg(test)]
mod tests;

/// The `θ`-face operands of a comparison: the source `x(θ)`, the observed difference `η(θ)` and
/// the anchor check (inside the original anchor ball, with the difference to its centre).
pub(in super::super) fn read_return_operands<'c>(
    comparison: &NormalCoupledComparison<'c>,
    parameters: &ResidentSection<'c>,
) -> Result<
    (
        ResidentSection<'c>,
        ResidentSection<'c>,
        ResidentSection<'c>,
    ),
    ConstitutiveFibreError,
> {
    let c = comparison;
    let s = c.source().origin().fibre().surface;
    let n = c.relation().roots();
    let k = c.relation().condition_complex();
    let anchor = s.fresh_section(1, 2 * (4 * n + 2), ResidentGrain(0))?;
    let source = s.fresh_section(1, 6 * n + 1, ResidentGrain(0))?;
    let difference = s.fresh_section(1, 2 * n + 1, ResidentGrain(0))?;
    let mut passage = s.begin_passage(&[vec![]])?;
    {
        let lane = passage.open(0, &[])?;
        s.record_coupled_joint_anchor(
            &lane,
            c.source().affine_relation().report(),
            c.source().affine_relation().source_width(),
            c.source().anchor(),
            n,
            c.parameter_rows() - 1,
            parameters,
            &anchor,
        )?;
        s.record_coupled_family_operands(
            &lane,
            c.coefficients(),
            n,
            k,
            parameters,
            &anchor,
            &source,
            &difference,
        )?;
    }
    passage.close(0, &difference, 64)?;
    let result = passage.finish()?.launch()?;
    if !result.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "dependent source substitution: {:?}",
            result.obstruction
        )));
    }
    Ok((source, difference, anchor))
}
