//! The existing unit-admittance reaction, exposed for an actual current meeting any
//! compatible affine receiver family. This creates a reaction; it does not identify a cause.
use super::*;

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct AffineContactReading {
    pub relation_cut: u64,
    pub metric: ConditionContactMetric,
    pub status: ConditionContactStatus,
    pub predecessor: Vec<Rat>,
    pub successor: Vec<Rat>,
    pub incoming_normal: Vec<Rat>,
    pub returned_normal: Vec<Rat>,
    pub difference: Vec<Rat>,
}

/// A declared contact of actual standing with the complete incoming family. Its point
/// successor is a realized reaction under this law, never a claim that the family is unique.
/// Borrowing the original family prevents this receiver from hiding that source fibre.
pub struct ResidentAffineContact<'a, 'c> {
    family: &'a ResidentConstitutiveReturn<'c>,
    section: ResidentSection<'c>,
    metric: ConditionContactMetric,
}
/// Immutable target-vertical geometry compiled from one producing local law. This is
/// derived standing, not another learner. Every use checks the complete incoming directions.
pub(crate) struct ResidentWaveSourceGeometry<'c> {
    surface: &'c ResidentSurface<'c>,
    width: usize,
    directions: ResidentSection<'c>,
    graph: ResidentSection<'c>,
}
impl<'c> ResidentWaveSourceGeometry<'c> {
    pub(crate) fn compile(law:&ResidentConstitutiveFibre<'c>) -> Result<Self,ConstitutiveFibreError> {
        law.require_usable_geometry()?;
        let s=law.surface;let c=law.target_width.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        let k=c.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        let directions=s.fresh_section(c,c,ResidentGrain(0))?;
        let graph=s.fresh_section(k,k,ResidentGrain(0))?;
        let workspace=s.fresh_section(1,2*k,ResidentGrain(0))?;
        let mut passage=s.begin_passage(&[vec![]])?;
        {let lane=passage.open(0,&[])?;s.record_wave_source_geometry(&lane,&law.basis,law.source_width,law.target_width,&directions,&graph,&workspace)?;}
        passage.close(0,&graph,64)?;let receipt=passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty(){return Err(ConstitutiveFibreError::Arithmetic(format!("wave source geometry: {:?}",receipt.obstruction)));}
        Ok(Self{surface:s,width:c,directions,graph})
    }
}
impl ResidentConstitutiveFibre<'_> {
    fn require_usable_geometry(&self)->Result<(),ConstitutiveFibreError>{
        if self.usable {Ok(())}else{Err(ConstitutiveFibreError::Uncertain)}
    }
}
impl<'c> ResidentConstitutiveReturn<'c> {
    pub(crate) fn read_contact_with_geometry<'a>(&'a self,
        actual:ResidentConstitutiveCurrent<'_, 'c>, metric:ConditionContactMetric,
        geometry:&ResidentWaveSourceGeometry<'c>) -> Result<ResidentAffineContact<'a,'c>,ConstitutiveFibreError> {
        if !std::ptr::eq(self.surface,geometry.surface) || self.target_width!=geometry.width || actual.width!=geometry.width {
            return Err(ConstitutiveFibreError::Shape);
        }
        let s=self.surface;let section=s.fresh_section(1,5*geometry.width+2,ResidentGrain(0))?;
        let mut passage=s.begin_passage(&[vec![]])?;
        {let lane=passage.open(0,&[])?;s.record_prepared_condition_contact(&lane,actual,&self.report,self.source_width,&geometry.directions,&geometry.graph,&section)?;}
        passage.close(0,&section,64)?;let receipt=passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty(){return Err(ConstitutiveFibreError::Arithmetic(format!("prepared affine contact: {:?}",receipt.obstruction)));}
        Ok(ResidentAffineContact{family:self,section,metric})
    }
    /// For F=a+V and actual h, react by h'=P_V h+(I-P_V)a. The realified metric is
    /// declared by the caller. This is a new contact operation, not a point cast of F.
    pub fn read_contact<'a>(
        &'a self,
        actual: ResidentConstitutiveCurrent<'_, 'c>,
        metric: ConditionContactMetric,
    ) -> Result<ResidentAffineContact<'a, 'c>, ConstitutiveFibreError> {
        let section = affine_contact_section(self.surface, actual, self)?;
        Ok(ResidentAffineContact {
            family: self,
            section,
            metric,
        })
    }
}
impl<'a, 'c> ResidentAffineContact<'a, 'c> {
    pub fn family(&self) -> &'a ResidentConstitutiveReturn<'c> {
        self.family
    }
    pub fn metric(&self) -> ConditionContactMetric {
        self.metric
    }
    fn view(&self, block: usize, guarded: bool) -> ResidentConstitutiveCurrent<'_, 'c> {
        let c = self.family.target_width;
        ResidentConstitutiveCurrent {
            section: &self.section,
            offset: block * c,
            width: c,
            denominator: Some(5 * c),
            disposition: guarded.then_some(5 * c + 1),
        }
    }
    pub fn predecessor(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.view(0, false)
    }
    /// Consumers check the contact disposition on device; an empty family supplies no reaction.
    /// Actual standing after this contact, including the unchanged prior when F is empty.
    /// This carries no assertion of compatibility; family() and inspect() retain that distinction.
    pub fn actual_successor(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.view(1, false)
    }
    pub fn successor(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.view(1, true)
    }
    pub fn incoming_normal(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.view(2, true)
    }
    pub fn returned_normal(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.view(3, true)
    }
    pub fn difference(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.view(4, true)
    }
    pub fn inspect(&self) -> Result<AffineContactReading, ConstitutiveFibreError> {
        read_affine_contact(self.family, &self.section, self.metric)
    }
    pub(crate) fn into_section(self) -> ResidentSection<'c> {
        self.section
    }
}

pub(in super::super) fn read_affine_contact(
    family: &ResidentConstitutiveReturn<'_>,
    section: &ResidentSection<'_>,
    metric: ConditionContactMetric,
) -> Result<AffineContactReading, ConstitutiveFibreError> {
    let words = family.surface.read_out(section)?;
    let c = family.target_width;
    if words.len() != 5 * c + 2 || words[5 * c].0 <= 0 || words.iter().any(|(lo, hi)| lo != hi) {
        return Err(ConstitutiveFibreError::Uncertain);
    }
    let row = |at: usize| {
        words[at..at + c]
            .iter()
            .map(|v| Rat::new(v.0.into(), words[5 * c].0.into()))
            .collect()
    };
    Ok(AffineContactReading {
        relation_cut: family.occurrence,
        metric: metric,
        status: match words[5 * c + 1].0 {
            0 => ConditionContactStatus::Compatible,
            1 => ConditionContactStatus::OutsideRepresentedRelation,
            _ => return Err(ConstitutiveFibreError::Uncertain),
        },
        predecessor: row(0),
        successor: row(c),
        incoming_normal: row(2 * c),
        returned_normal: row(3 * c),
        difference: row(4 * c),
    })
}

pub(super) fn affine_contact_section<'c>(
    surface: &'c ResidentSurface<'c>,
    actual: ResidentConstitutiveCurrent<'_, 'c>,
    family: &ResidentConstitutiveReturn<'c>,
) -> Result<ResidentSection<'c>, ConstitutiveFibreError> {
    let c = family.target_width;
    if actual.width != c || c == 0 || c % 2 != 0 || !std::ptr::eq(surface, family.surface) {
        return Err(ConstitutiveFibreError::Shape);
    }
    let required = c.checked_mul(9 * 16).ok_or(ConstitutiveFibreError::Shape)?;
    let available = surface.declaration().max_sectiond_bytes;
    if required > available as usize {
        return Err(ConstitutiveFibreError::ScratchAperture {
            required,
            available,
        });
    }
    let k = c.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
    let width = c
        .checked_mul(5)
        .and_then(|v| v.checked_add(2))
        .ok_or(ConstitutiveFibreError::Shape)?;
    let graph = surface.fresh_section(k, k, ResidentGrain(0))?;
    let section = surface.fresh_section(1, width, ResidentGrain(0))?;
    let mut passage = surface.begin_passage(&[vec![]])?;
    {
        let lane = passage.open(0, &[])?;
        surface.record_condition_contact(
            &lane,
            actual,
            Some((&family.report, family.source_width, &graph)),
            &section,
        )?;
    }
    passage.close(0, &section, 64)?;
    let receipt = passage.finish()?.launch()?;
    if !receipt.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "affine contact: {:?}",
            receipt.obstruction
        )));
    }
    Ok(section)
}

#[cfg(test)]
mod tests;
