//! A declared terminal differential-current receiver. No alphabet, byte or completion symbol
//! enters this native owner. Full current reports and numerical residuals remain in history.
use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldDifferentialReading {
    pub occurrence: usize,
    /// When this is a receiver of the current constitutive relation at a historical source,
    /// retain its contemporary state cut separately from that source's occurrence ordinal.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub relation_cut: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub constitutive_status: Option<NativeFieldReceiverStatus>,
    pub first_complex: usize,
    pub pairs: usize,
    pub positive: u64,
    pub negative: u64,
    pub unresolved: u64,
    /// Exact zero differences are a subset of unresolved pairs. Numerical overlap is separate.
    pub exact_zero: u64,
}

impl<'chart> NativeConstitutiveField<'chart> {
    /// Read Re(out[right]-out[left]) on disjoint adjacent complex-coordinate pairs. A sign
    /// returns only when the entire current ball lies in that open half-space. This terminal
    /// observer reads four mask words; no current center is selected or supplied to development.
    pub fn read_differential_pairs(
        &self,
        occurrence: usize,
        first_complex: usize,
        pairs: usize,
    ) -> Result<Option<NativeFieldDifferentialReading>, ConstitutiveFibreError> {
        if !(1..=63).contains(&pairs)
            || first_complex
                .checked_add(2 * pairs)
                .is_none_or(|end| end > 3 * self.nodes())
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let Some(representation) = self.junction_representation() else {
            return Ok(None);
        };
        let event = self
            .history
            .get(occurrence)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        event.with_resident(self.relation.surface, |resident| {
            let report = resident
                .junction
                .as_ref()
                .ok_or(ConstitutiveFibreError::Uncertain)?;
            self.read_differential_report(
                report,
                occurrence,
                6 * self.nodes(),
                representation.kernel().0,
                first_complex,
                pairs,
            )
            .map(Some)
        })
    }

    /// The learned transport's native material current, observed without reading its coefficient
    /// matrix or source field back to the host.
    pub fn read_material_transport_pairs(
        &self,
        occurrence: usize,
        pairs: usize,
    ) -> Result<Option<NativeFieldDifferentialReading>, ConstitutiveFibreError> {
        if !(1..=63).contains(&pairs) || 2 * pairs > self.nodes() {
            return Err(ConstitutiveFibreError::Shape);
        }
        let event = self
            .history
            .get(occurrence)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        event.with_resident(self.relation.surface, |resident| {
            let Some(report) = resident.transport.as_ref() else {
                return Ok(None);
            };
            self.read_differential_report(
                report,
                occurrence,
                2 * self.nodes(),
                if self.material_transport_source()
                    == Some(NativeMaterialTransportSource::CompleteCurrent)
                {
                    4
                } else {
                    3
                },
                0,
                pairs,
            )
            .map(Some)
        })
    }

    fn read_differential_report(
        &self,
        report: &ResidentSection<'chart>,
        occurrence: usize,
        dimension: usize,
        mode: u32,
        first_complex: usize,
        pairs: usize,
    ) -> Result<NativeFieldDifferentialReading, ConstitutiveFibreError> {
        let surface = self.relation.surface;
        let output = surface.fresh_section(1, 4, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_field_differential_receiver(
                &lane,
                report,
                dimension,
                mode,
                first_complex,
                pairs,
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let reading = passage.finish()?.launch()?;
        if !reading.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "{:?}",
                reading.obstruction
            )));
        }
        let words = surface.read_out(&output)?;
        if words.iter().any(|(lo, hi)| lo != hi || *lo < 0) {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let positive = words[0].0 as u64;
        let negative = words[1].0 as u64;
        let unresolved = words[2].0 as u64;
        let exact_zero = words[3].0 as u64;
        let mask = (1u64 << pairs) - 1;
        if positive & negative != 0
            || positive & unresolved != 0
            || negative & unresolved != 0
            || (positive | negative | unresolved) != mask
            || exact_zero & !unresolved != 0
        {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        Ok(NativeFieldDifferentialReading {
            occurrence,
            relation_cut: None,
            constitutive_status: None,
            first_complex,
            pairs,
            positive,
            negative,
            unresolved,
            exact_zero,
        })
    }
}

#[cfg(test)]
mod tests;
