//! Portable immutable return, used when a native current is pending at an exterior boundary.
use super::*;

#[derive(Clone, Debug, Serialize, serde::Deserialize)]
pub struct ConstitutiveReturnRest {
    schema: String,
    source_width: usize,
    target_width: usize,
    occurrence: u64,
    source_occurrence: Option<usize>,
    source_chart: ConstitutiveSourceChart,
    words: Vec<i64>,
}
impl ConstitutiveReturnRest {
    pub fn validate(&self) -> Result<(), ConstitutiveFibreError> {
        let w = self
            .source_width
            .checked_add(self.target_width)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let size = self
            .target_width
            .checked_mul(self.target_width)
            .and_then(|n| n.checked_add(w)?.checked_add(4))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if w > u32::MAX as usize - 4
            || self.schema != "holonics.constitutive-return.v1"
            || self.target_width == 0
            || self.words.len() != size
            || self.words[w] <= 0
            || !(0..=2).contains(&self.words[w + 1])
            || self.words[w + 2] < -1
            || self.words[w + 2] >= w as i64
            || self.words[w + 3] < 0
            || self.words[w + 3] > w as i64
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        if self.words[w + 1] == 0 && self.words[w + 4..].iter().any(|v| *v != 0) {
            return Err(ConstitutiveFibreError::Shape);
        }
        if self.words[w + 1] != 1 && self.words[..self.source_width].iter().any(|v| *v != 0) {
            return Err(ConstitutiveFibreError::Shape);
        }
        if let ConstitutiveSourceChart::BilinearContact {
            source_complex,
            condition_complex,
        } = self.source_chart
        {
            if source_complex == 0
                || condition_complex == 0
                || source_complex
                    .checked_mul(condition_complex)
                    .and_then(|v| {
                        v.checked_add(source_complex)?
                            .checked_add(condition_complex)?
                            .checked_mul(2)
                    })
                    .is_none()
            {
                return Err(ConstitutiveFibreError::Shape);
            }
        }
        Ok(())
    }
    pub(crate) fn source_width(&self)->usize{self.source_width}
    pub(crate) fn occurrence(&self)->u64{self.occurrence}
    pub(crate) fn outside_domain(&self)->bool{self.words[self.source_width+self.target_width+1]==1}
    /// Validate a fixed homogeneous prefix without treating a plural target as a point.
    pub(crate) fn validate_constant_prefix(&self,prefix:&[i64])->Result<(),ConstitutiveFibreError>{
        self.validate()?;
        if prefix.len()>self.target_width{return Err(ConstitutiveFibreError::Shape);}
        let w=self.source_width+self.target_width;
        if self.words[w+1]==1{return Ok(());}
        for (j,value) in prefix.iter().enumerate(){
            if (self.words[self.source_width+j] as i128)!=(*value as i128)*(self.words[w] as i128)
                ||(0..self.target_width).any(|i|self.words[w+4+i*self.target_width+j]!=0){return Err(ConstitutiveFibreError::Shape);}
        }
        Ok(())
    }
    pub fn is_unique_current(&self) -> bool {
        self.validate().is_ok() && self.words[self.source_width + self.target_width + 1] == 0
    }
    pub fn target_width(&self) -> usize {
        self.target_width
    }
    /// Exact cold current words for exterior codec validation at a durable boundary.
    pub fn unique_current_words(&self) -> Option<(&[i64], i64)> {
        self.is_unique_current().then(|| {
            (
                &self.words[self.source_width..self.source_width + self.target_width],
                self.words[self.source_width + self.target_width],
            )
        })
    }
    pub fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        self.validate()?;
        let report = surface.mount_section_rest(
            &ResidentSectionRest::found(
                1,
                self.words.len(),
                ResidentGrain(0),
                64,
                self.words.into_iter().map(|v| (v, v)).collect(),
            )
            .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        Ok(ResidentConstitutiveReturn {
            surface,
            report,
            source_width: self.source_width,
            target_width: self.target_width,
            occurrence: self.occurrence,
            source_occurrence: self.source_occurrence,
            source_chart: self.source_chart,
        })
    }
}
impl ResidentConstitutiveReturn<'_> {
    /// Exterior persistence only. No live ecology or learned relation is copied.
    pub fn rest(&self) -> Result<ConstitutiveReturnRest, ConstitutiveFibreError> {
        let words = self.surface.read_out(&self.report)?;
        if words.iter().any(|(a, b)| a != b) {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let rest = ConstitutiveReturnRest {
            schema: "holonics.constitutive-return.v1".into(),
            source_width: self.source_width,
            target_width: self.target_width,
            occurrence: self.occurrence,
            source_occurrence: self.source_occurrence,
            source_chart: self.source_chart,
            words: words.into_iter().map(|(v, _)| v).collect(),
        };
        rest.validate()?;
        Ok(rest)
    }
    pub fn target_width(&self) -> usize {
        self.target_width
    }
}
