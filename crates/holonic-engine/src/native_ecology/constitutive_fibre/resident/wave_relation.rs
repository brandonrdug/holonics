use super::*;
mod rest;
pub use rest::NormalWaveRelationRest;

/// Immutable fixed-condition pullback of one bilinear law into the wave family chart.
/// The basis is a derived relation; it owns no learned material and no continuing ecology.
pub struct ResidentWaveRelation<'c> {
    pub(in super::super) surface: &'c ResidentSurface<'c>,
    pub(in super::super) basis: ResidentSection<'c>,
    pub(in super::super) fixed: ResidentSection<'c>,
    pub(in super::super) roots: usize,
    pub(in super::super) condition_complex: usize,
    pub(in super::super) relation_cut: u64,
    producing_owner: Rc<()>,
}
impl<'c> ResidentWaveRelation<'c> {
    pub(in super::super) fn new(
        surface: &'c ResidentSurface<'c>,
        basis: ResidentSection<'c>,
        fixed: ResidentSection<'c>,
        roots: usize,
        condition_complex: usize,
        relation_cut: u64,
        producing_owner: Rc<()>,
    ) -> Self {
        Self {
            surface,
            basis,
            fixed,
            roots,
            condition_complex,
            relation_cut,
            producing_owner,
        }
    }
    pub fn width(&self) -> usize {
        2 + 8 * self.roots
    }
    pub fn relation_cut(&self) -> u64 {
        self.relation_cut
    }
    pub fn roots(&self) -> usize {
        self.roots
    }
    pub fn fixed_condition(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        ResidentConstitutiveCurrent::rational(&self.fixed)
            .expect("completed fixed-condition snapshot")
    }
    pub fn condition_complex(&self) -> usize {
        self.condition_complex
    }
    pub fn same_producing_cut(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.producing_owner, &other.producing_owner)
            && self.relation_cut == other.relation_cut
    }
}

impl<'chart> ResidentConstitutiveFibre<'chart> {
    /// Pull one actual fixed condition through the bilinear law into the wave family chart.
    /// This allocates only derived relation sections; the learned basis and this move owner are
    /// never changed. The fixed condition is copied to a resident snapshot by the same passage.
    pub fn read_wave_relation(
        &self,
        condition: ResidentConstitutiveCurrent<'_, 'chart>,
        roots: usize,
    ) -> Result<ResidentWaveRelation<'chart>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let ConstitutiveSourceChart::BilinearContact {
            source_complex,
            condition_complex,
        } = self.source_chart
        else {
            return Err(ConstitutiveFibreError::Shape);
        };
        if roots == 0
            || roots.checked_mul(3) != Some(source_complex)
            || roots.checked_mul(2) != Some(self.target_width)
            || condition_complex.checked_mul(2) != Some(condition.width)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let ns = roots.checked_mul(3).ok_or(ConstitutiveFibreError::Shape)?;
        let q = roots
            .checked_mul(8)
            .and_then(|v| v.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let u = roots
            .checked_mul(10)
            .and_then(|v| v.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let feature = ns
            .checked_mul(condition_complex)
            .and_then(|v| {
                v.checked_add(ns)?
                    .checked_add(condition_complex)?
                    .checked_mul(2)
            })
            .ok_or(ConstitutiveFibreError::Shape)?;
        let l = roots
            .checked_mul(2)
            .and_then(|v| v.checked_add(feature))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let relation = l.checked_add(u).ok_or(ConstitutiveFibreError::Shape)?;
        let d = q.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        relation
            .checked_mul(relation)
            .and_then(|_| d.checked_mul(d))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if relation > u32::MAX as usize || d > u32::MAX as usize {
            return Err(ConstitutiveFibreError::Shape);
        }
        let graph = self
            .surface
            .fresh_section(relation, relation, ResidentGrain(0))?;
        let derived = self.surface.fresh_section(2 * q, 2 * q, ResidentGrain(0))?;
        let fixed = self
            .surface
            .fresh_section(1, 2 * condition_complex + 1, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_constitutive_wave_relation(
                &lane,
                &self.basis,
                condition,
                roots,
                condition_complex,
                &graph,
                &derived,
                &fixed,
            )?;
        }
        passage.close(0, &derived, i64::BITS)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "wave relation: {:?}",
                receipt.obstruction
            )));
        }
        Ok(ResidentWaveRelation::new(
            self.surface,
            derived,
            fixed,
            roots,
            condition_complex,
            self.occurrences,
            Rc::clone(&self.basis_owner),
        ))
    }
}
