//! An actual next-current receiver joins (c,v) while retaining the complete original anchor.
//! This is a total observation passage, not a conditional prediction or a material deposit.
use super::*;
impl<'c> ResidentWaveRelation<'c> {
    pub fn observed_next(&self) -> Option<ResidentConstitutiveCurrent<'_, 'c>> {
        self.observation
            .as_ref()
            .map(|v| ResidentConstitutiveCurrent::rational(v).expect("admitted observation"))
    }
    pub(crate) fn is_total_current_map(&self) -> bool {
        self.source.is_some() || self.observation.is_some()
    }
    pub fn read_observed_next(
        &self,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<Self, ConstitutiveFibreError> {
        let (basis, snapshot) = observation_basis(self.surface, self.roots, observed)?;
        Ok(Self {
            surface: self.surface,
            basis,
            fixed: Rc::clone(&self.fixed),
            roots: self.roots,
            condition_complex: self.condition_complex,
            relation_cut: self.relation_cut,
            producing_owner: Rc::clone(&self.producing_owner),
            receiver: self.receiver,
            source: None,
            observation: Some(snapshot),
            source_geometry: Rc::clone(&self.source_geometry),
        })
    }
}
pub(super) fn observation_basis<'c>(
    s: &'c ResidentSurface<'c>,
    n: usize,
    observed: ResidentConstitutiveCurrent<'_, 'c>,
) -> Result<(ResidentSection<'c>, ResidentSection<'c>), ConstitutiveFibreError> {
    let r = n.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
    if observed.width != r {
        return Err(ConstitutiveFibreError::Shape);
    }
    let q = n
        .checked_mul(8)
        .and_then(|v| v.checked_add(2))
        .ok_or(ConstitutiveFibreError::Shape)?;
    let k = q.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
    let basis = s.fresh_section(k, k, ResidentGrain(0))?;
    let snapshot = s.fresh_section(1, r + 1, ResidentGrain(0))?;
    let workspace = s.fresh_section(1, 2 * (k + r), ResidentGrain(0))?;
    let mut p = s.begin_passage(&[vec![]])?;
    {
        let lane = p.open(0, &[])?;
        s.record_wave_observed_next(&lane, observed, n, &basis, &snapshot, &workspace)?;
    }
    p.close(0, &basis, 64)?;
    let result = p.finish()?.launch()?;
    if !result.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "observed next-current map: {:?}",
            result.obstruction
        )));
    }
    Ok((basis, snapshot))
}
