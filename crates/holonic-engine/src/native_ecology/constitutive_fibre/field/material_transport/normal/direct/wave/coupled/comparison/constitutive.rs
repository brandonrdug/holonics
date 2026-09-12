//! Dependent lift of the existing condition-contact and member-formation operation. Each
//! substitution retains the SAME theta in x(theta), eta(theta), condition and material return.
//! The family is a generator of alternatives, never the span/union of their material rows.
use super::*;
use crate::native_ecology::constitutive_fibre::resident::ResidentNeighborhoodAlternative;
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
    /// The actual source-to-current word to which a complete dependent return must be joined.
    /// This keeps intervening incidence available; equal source/current marginals are not used
    /// to infer a missing coupling.
    pub fn continuation(
        &self,
    ) -> Result<NormalCoupledContinuation<'_, 'c>, ConstitutiveFibreError> {
        let handle = self
            .wave
            .pending_coupled_prediction(self.comparison.prediction_id())?;
        self.wave.pending_coupled_continuation(&handle)
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
        // Condition the actual historic word on this same source assignment. Every later
        // free output direction is still an affine fibre; no intermediate receiver is read.
        let mut image = c.source().parameter_section(parameters, &anchor)?;
        let mut final_map = None;
        let mut final_coverage = None;
        for (_, maps) in self.wave.continuation.transport.range(c.prediction_id()..) {
            for map in maps {
                let (next, coverage) = if map.is_total_current_map() {
                    map.read_source_image(&image)?
                } else {
                    map.read_image(&image)?.into_output()
                };
                image = next;
                final_coverage = Some(coverage);
                final_map = Some(Rc::clone(map));
            }
        }
        let current = Rc::new(c.source().parameter_image(
            image,
            final_map.ok_or(ConstitutiveFibreError::Shape)?,
            final_coverage.ok_or(ConstitutiveFibreError::Shape)?,
            self.wave.current().passages(),
        ));
        let consequence = self.wave.continuation.neighborhood.prepare_consequence(
            c.member(),
            ResidentConstitutiveCurrent::rational(&source)?,
            Some(ResidentConstitutiveCurrent::rational(&difference)?),
        )?;
        let relation = Rc::new(self.wave.neighborhood().read_consequence_wave_relation(
            c.member(),
            n,
            c.relation().source_receiver(),
            Some(&consequence),
        )?);
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
    /// This map is conditional on the retained theta. A later use must retain its joining
    /// source/current relation; treating it as the one published material would lose that joint.
    pub fn conditional_relation(&self) -> &ResidentWaveRelation<'c> {
        &self.relation
    }
    /// Contemporary current conditional on theta, through the unmodified historical word.
    pub fn current_section(&self) -> &NormalWaveFamily<'c> {
        &self.current
    }
    /// The proposed contemporary passage through the new conditional material and condition.
    /// This is a section of the whole successor generator, not a separately published state.
    pub fn successor_section(&self) -> &NormalWaveFamily<'c> {
        &self.successor
    }
    pub(in super::super) fn retained_successor(&self)->Rc<NormalWaveFamily<'c>>{Rc::clone(&self.successor)}
    pub(in super::super) fn retained_current(&self)->Rc<NormalWaveFamily<'c>>{Rc::clone(&self.current)}
    pub(in super::super) fn member_relation(&self,member:usize,
        other:Option<&ResidentConstitutiveFibre<'c>>,chart:WaveSourceReceiver,
    )->Result<ResidentWaveRelation<'c>,ConstitutiveFibreError>{
        let law=if member==self.comparison.member(){&self.consequence.material}else{other.ok_or(ConstitutiveFibreError::Shape)?};
        law.read_wave_relation_in_chart(self.condition().successor(),self.comparison.relation().roots(),chart)
    }
    pub(in super::super) fn apply_map(&mut self,map:Rc<ResidentWaveRelation<'c>>,passage:u64)->Result<(),ConstitutiveFibreError>{
        let next=Rc::new(self.successor.read_through_at(Rc::clone(&map),passage)?);
        self.current=Rc::clone(&self.successor);self.successor=next;self.relation=map;Ok(())
    }
    pub fn read_formed_source(
        &self,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        self.consequence
            .material
            .read_bilinear(source, self.consequence.condition.successor())
    }
    pub(in super::super) fn actuate_source(
        &mut self,
        member: usize,
        other: Option<&ResidentConstitutiveFibre<'c>>,
        chart: WaveSourceReceiver,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<(), ConstitutiveFibreError> {
        let passage=self.successor.passages().checked_add(1).ok_or(ConstitutiveFibreError::Shape)?;
        self.actuate_source_at(member,other,chart,source,passage)
    }
    pub(in super::super) fn actuate_source_at(&mut self,member:usize,
        other:Option<&ResidentConstitutiveFibre<'c>>,chart:WaveSourceReceiver,
        source:ResidentConstitutiveCurrent<'_, 'c>,passage:u64,
    )->Result<(),ConstitutiveFibreError>{
        let law = if member == self.comparison.member() {
            &self.consequence.material
        } else {
            other.ok_or(ConstitutiveFibreError::Shape)?
        };
        let relation = law.read_wave_relation_in_chart(
            self.condition().successor(),
            self.comparison.relation().roots(),
            chart,
        )?;
        let map = Rc::new(relation.read_source_contact(law, source)?);
        self.apply_map(map,passage)
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
