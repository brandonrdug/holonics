//! Device compilation of a real pending comparison, with its actual source/condition/material
//! cuts retained. Relation row witnesses are existential coefficients, not learned map weights.
use super::*;
use crate::resident_section::{ResidentBilinearMap, ResidentBilinearReturn};

pub struct CompiledCoupledJoint<'a, 'c> {
    comparison: &'a NormalCoupledComparison<'c>,
    material_owner: Rc<()>,
    material_cut: u64,
    source_parameters: usize,
    condition_components: usize,
    witnesses: usize,
    parameters: usize,
    map: ResidentBilinearMap<'c>,
}
#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct CoupledJointReading {
    pub relation_residual: Vec<Rat>,
    pub producing_condition_residual: Vec<Rat>,
    pub anchor_difference: Vec<Rat>,
    pub within_anchor: bool,
}
pub struct CoupledJointEvaluation<'a, 'j, 'c> {
    compiled: &'a CompiledCoupledJoint<'j, 'c>,
    parameters: &'a ResidentSection<'c>,
    returned: ResidentBilinearReturn<'c>,
    anchor: ResidentSection<'c>,
}
impl<'a, 'c> CompiledCoupledJoint<'a, 'c> {
    pub fn comparison(&self) -> &NormalCoupledComparison<'c> {
        self.comparison
    }
    pub fn source_parameters(&self) -> usize {
        self.source_parameters
    }
    pub fn condition_components(&self) -> usize {
        self.condition_components
    }
    pub fn relation_witnesses(&self) -> usize {
        self.witnesses
    }
    pub fn parameter_count(&self) -> usize {
        self.parameters
    }
    pub fn material_cut(&self) -> u64 {
        self.material_cut
    }
    pub fn matches_material(&self, material: &ResidentConstitutiveFibre<'c>) -> bool {
        Rc::ptr_eq(&self.material_owner, &material.basis_owner)
            && self.material_cut == material.occurrences
    }
    /// Reads an actual shared parameter occurrence. A zero equation residual is not an anchor
    /// certificate: the independent original bound is evaluated and returned alongside it.
    pub fn evaluate<'r>(
        &'r self,
        parameters: &'r ResidentSection<'c>,
    ) -> Result<CoupledJointEvaluation<'r, 'a, 'c>, ConstitutiveFibreError> {
        let c = self.comparison;
        let s = c.source().origin().fibre().surface;
        let n = c.relation().roots();
        let anchor = s.fresh_section(1, 2 * (4 * n + 2), ResidentGrain(0))?;
        let mut p = s.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            s.record_coupled_joint_anchor(
                &lane,
                c.source().affine_relation().report(),
                c.source().affine_relation().source_width(),
                c.source().anchor(),
                n,
                self.parameters,
                parameters,
                &anchor,
            )?;
        }
        p.close(0, &anchor, 64)?;
        let result = p.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "joint anchor: {:?}",
                result.obstruction
            )));
        }
        let returned = self.map.apply_affine_shared(parameters)?;
        Ok(CoupledJointEvaluation {
            compiled: self,
            parameters,
            returned,
            anchor,
        })
    }
}
impl<'a, 'j, 'c> CoupledJointEvaluation<'a, 'j, 'c> {
    pub fn parameters(&self) -> &'a ResidentSection<'c> {
        self.parameters
    }
    pub fn compiled(&self) -> &CompiledCoupledJoint<'j, 'c> {
        self.compiled
    }
    pub fn residual(&self) -> &ResidentSection<'c> {
        self.returned.output()
    }
    pub fn inspect(&self) -> Result<CoupledJointReading, ConstitutiveFibreError> {
        let s = self.compiled.comparison.source().origin().fibre().surface;
        let raw = s.read_out(self.returned.output())?;
        if raw.iter().any(|(a, b)| a != b) || raw.last().is_none_or(|v| v.0 <= 0) {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let den = raw.last().unwrap().0;
        let v = raw[..raw.len() - 1]
            .iter()
            .map(|(n, _)| Rat::new((*n).into(), den.into()))
            .collect::<Vec<_>>();
        let a = wides(&s.read_out(&self.anchor)?)?;
        if a.len() != 4 * self.compiled.comparison.relation().roots() + 2
            || a[1] <= 0
            || !(0..=1).contains(&a[0])
        {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        Ok(CoupledJointReading {
            relation_residual: v[..self.compiled.witnesses].to_vec(),
            producing_condition_residual: v[self.compiled.witnesses..].to_vec(),
            anchor_difference: a[2..]
                .iter()
                .map(|n| Rat::new((*n).into(), a[1].into()))
                .collect(),
            within_anchor: a[0] == 0,
        })
    }
}
impl<'c> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    /// Compile at the contemporary member-material cut while retaining the ORIGINAL producing
    /// condition and source. This is read-only; pending consumption still requires incorporation.
    pub fn compile_coupled_joint<'a>(
        &self,
        comparison: &'a NormalCoupledComparison<'c>,
    ) -> Result<CompiledCoupledJoint<'a, 'c>, ConstitutiveFibreError> {
        let pending = self
            .continuation
            .pending
            .get(&comparison.id)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        if !Rc::ptr_eq(pending, &comparison.cut) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let material = self.neighborhood().generator(comparison.member())?;
        if !material.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let n = comparison.relation().roots();
        let k = comparison.relation().condition_complex();
        let source = n.checked_mul(6).ok_or(ConstitutiveFibreError::Shape)?;
        let condition = k.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        let t = n
            .checked_mul(8)
            .and_then(|v| v.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let f = source
            .checked_mul(k)
            .and_then(|v| v.checked_add(source)?.checked_add(condition))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let w = f.checked_add(2 * n).ok_or(ConstitutiveFibreError::Shape)?;
        if material.source_chart
            != (ConstitutiveSourceChart::BilinearContact {
                source_complex: 3 * n,
                condition_complex: k,
            })
            || material.source_width != f
            || material.target_width != 2 * n
            || comparison.parameter_rows() != t + 1
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let parameters = t
            .checked_add(condition)
            .and_then(|v| v.checked_add(w))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let rank = source
            .checked_mul(condition)
            .and_then(|v| {
                v.checked_add(source)?
                    .checked_add(condition)?
                    .checked_add(2 * n)?
                    .checked_add(w)?
                    .checked_add(1)
            })
            .ok_or(ConstitutiveFibreError::Shape)?;
        let ac = rank
            .checked_mul(parameters + 1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let outputs = w + condition;
        let dc = outputs
            .checked_mul(rank)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let scratch = ac
            .checked_add(dc)
            .and_then(|v| v.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if [ac, dc, scratch].iter().any(|v| *v >= u32::MAX as usize) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let s = self.material.surface;
        let left = s.fresh_section(1, ac + 1, ResidentGrain(0))?;
        let right = s.fresh_section(1, ac + 1, ResidentGrain(0))?;
        let receiver = s.fresh_section(1, dc + 1, ResidentGrain(0))?;
        let workspace = s.fresh_section(1, scratch, ResidentGrain(0))?;
        let mut p = s.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            s.record_coupled_joint_compile(
                &lane,
                comparison.coefficients(),
                &material.basis,
                comparison.relation().fixed_condition(),
                n,
                k,
                &left,
                &right,
                &receiver,
                &workspace,
            )?;
        }
        p.close(0, &left, 64)?;
        let result = p.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "coupled joint compile: {:?}",
                result.obstruction
            )));
        }
        let map = ResidentBilinearMap::from_resident_packets(
            s,
            left,
            rank,
            parameters + 1,
            right,
            rank,
            parameters + 1,
            receiver,
            outputs,
            rank,
        )?;
        Ok(CompiledCoupledJoint {
            comparison,
            material_owner: Rc::clone(&material.basis_owner),
            material_cut: material.occurrences,
            source_parameters: t,
            condition_components: condition,
            witnesses: w,
            parameters,
            map,
        })
    }
}

#[cfg(test)]
pub(super) mod tests;
