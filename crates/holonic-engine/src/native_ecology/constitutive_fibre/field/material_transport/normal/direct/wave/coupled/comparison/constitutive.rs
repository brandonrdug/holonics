//! Dependent lift of the existing condition-contact and member-formation operation. Each
//! substitution retains the SAME theta in x(theta), eta(theta), condition and material return.
//! The family is a generator of alternatives, never the span/union of their material rows.
use super::*;
use crate::native_ecology::constitutive_fibre::resident::PreparedNeighborhoodConsequence;
use crate::native_ecology::constitutive_fibre::{
    ConditionContactReading, ConstitutiveFibreReturn, PreparedConditionContact,
};

/// Exclusive access fixes the contemporary condition/material cut while this dependent law
/// is evaluated. It shares the real pending comparison; it does not clone the ecology.
pub struct CoupledConstitutiveFamily<'w, 'j, 'c> {
    wave: &'w mut ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
    comparison: &'j NormalCoupledComparison<'c>,
}

/// One evaluated conditional consequence. It has deliberately no publication method: a
/// parameter substitution is not evidence that this alternative was the actual source.
pub struct CoupledConstitutiveAlternative<'p, 'j, 'c> {
    comparison: &'j NormalCoupledComparison<'c>,
    parameters: &'p ResidentSection<'c>,
    source: ResidentSection<'c>,
    difference: ResidentSection<'c>,
    anchor: ResidentSection<'c>,
    consequence: PreparedNeighborhoodConsequence<'c>,
    relation: ResidentWaveRelation<'c>,
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
                self.source_parameters(),
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
        let consequence = self.wave.continuation.neighborhood.prepare_consequence(
            c.member(),
            ResidentConstitutiveCurrent::rational(&source)?,
            Some(ResidentConstitutiveCurrent::rational(&difference)?),
        )?;
        let relation = self.wave.neighborhood().read_consequence_wave_relation(
            c.member(),
            n,
            c.relation().source_receiver(),
            Some(&consequence),
        )?;
        Ok(CoupledConstitutiveAlternative {
            comparison: c,
            parameters,
            source,
            difference,
            anchor,
            consequence,
            relation,
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
        self.consequence
            .condition()
            .expect("observed dependent return")
    }
    pub fn prediction(&self) -> &ResidentConstitutiveReturn<'c> {
        self.consequence.prediction()
    }
    pub fn formation(&self) -> &ResidentConstitutiveReturn<'c> {
        self.consequence
            .formation()
            .expect("observed dependent return")
    }
    /// This map is conditional on the retained theta. A later use must retain its joining
    /// source/current relation; treating it as the one published material would lose that joint.
    pub fn conditional_relation(&self) -> &ResidentWaveRelation<'c> {
        &self.relation
    }
    pub fn inspect_condition(&self) -> Result<ConditionContactReading, ConstitutiveFibreError> {
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
    pub fn read_coupled_constitutive_family<'w, 'j>(
        &'w mut self,
        comparison: &'j NormalCoupledComparison<'c>,
    ) -> Result<CoupledConstitutiveFamily<'w, 'j, 'c>, ConstitutiveFibreError> {
        let cut = self
            .continuation
            .pending
            .get(&comparison.id)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        if !Rc::ptr_eq(cut, &comparison.cut) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        self.neighborhood().require_usable()?;
        Ok(CoupledConstitutiveFamily {
            wave: self,
            comparison,
        })
    }
}

#[cfg(test)]
mod tests;
