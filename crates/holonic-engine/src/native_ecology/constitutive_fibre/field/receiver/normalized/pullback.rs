//! The material source derivative uses the producing M and query, never a later surrogate.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum NativeMaterialPullbackMetric {
    /// Negative derivative of KL(q || p) in the declared real-potential chart.
    RelativeEntropy,
    /// Negative derivative of one half the squared probability discrepancy.
    SquaredProbability,
}

/// Resident partial adjoint with historical operator factors held fixed. This carries both
/// query arguments, including every born internal current. It is not a finite successor or
/// the adjoint of the entire chronology by itself.
pub struct NativeMaterialSourcePullback<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    pub(in super::super::super) _owner: Rc<()>,
    _observation: Rc<ResidentSection<'chart>>,
    _normalized: Rc<ResidentSection<'chart>>,
    _history: Vec<(Rc<ResidentSection<'chart>>, Rc<ResidentSection<'chart>>)>,
    pub(in super::super::super) output: ResidentSection<'chart>,
    pub(in super::super::super) source: NativeFieldLineage,
    pub(in super::super::super) receiving: NativeFieldLineage,
    metric: NativeMaterialPullbackMetric,
    group_width: usize,
    series_terms: u32,
    nodes: usize,
    pub(in super::super::super) contacts: usize,
    pub(in super::super::super) grain: u32,
}

#[derive(Clone, Debug, Serialize)]
pub struct NativeMaterialSourcePullbackReading {
    pub source: NativeFieldLineage,
    pub receiving: NativeFieldLineage,
    pub metric: NativeMaterialPullbackMetric,
    pub group_width: usize,
    pub series_terms: u32,
    pub grain: u32,
    /// Interleaved real/imaginary coordinates of the two visible branches per node.
    pub visible_source: Vec<ExactInterval>,
    /// Interleaved real/imaginary coordinates of all three outgoing branches per node.
    pub outgoing_current: Vec<ExactInterval>,
    /// Interleaved real/imaginary coordinates in retained contact birth order.
    pub internal_current: Vec<ExactInterval>,
}

impl NativeMaterialSourcePullback<'_> {
    pub fn inspect(&self) -> Result<NativeMaterialSourcePullbackReading, ConstitutiveFibreError> {
        let rest = self.surface.detach_section(&self.output, 64)?;
        let raw = material_transport::wides(&rest.intervals)?;
        if raw.len() != 2 * (10 * self.nodes + 2 * self.contacts) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let scale = BigInt::one() << self.grain;
        let values = raw
            .chunks_exact(2)
            .map(|p| {
                ExactInterval::new(
                    Rat::new(p[0].into(), scale.clone()),
                    Rat::new(p[1].into(), scale.clone()),
                )
                .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(NativeMaterialSourcePullbackReading {
            source: self.source.clone(),
            receiving: self.receiving.clone(),
            metric: self.metric,
            group_width: self.group_width,
            series_terms: self.series_terms,
            grain: self.grain,
            visible_source: values[..4 * self.nodes].to_vec(),
            outgoing_current: values[4 * self.nodes..10 * self.nodes].to_vec(),
            internal_current: values[10 * self.nodes..].to_vec(),
        })
    }
}

impl<'chart> NativeConstitutiveField<'chart> {
    /// Return the declared metric through the material prediction that originally produced
    /// this source. Delayed reception retains that original operator cut and context. This
    /// partial derivative holds its historical factors fixed; their own producing adjoints
    /// remain separate. No morphology/current is committed by this operation.
    pub fn pull_back_material_source(
        &self,
        returned: &NativeNormalizedMaterialReturn<'chart>,
        metric: NativeMaterialPullbackMetric,
    ) -> Result<NativeMaterialSourcePullback<'chart>, ConstitutiveFibreError> {
        if !Rc::ptr_eq(&self.owner, &returned.owner) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        if self.material_transport_source()
            != Some(NativeMaterialTransportSource::OperativeContextual)
        {
            return Err(ConstitutiveFibreError::Arithmetic(
                "material source pullback requires the operative contextual carrier".into(),
            ));
        }
        let source = returned.source.occurrence;
        let surface = self.relation.surface;
        let mut held = Vec::with_capacity(source + 1);
        let mut pointers = Vec::with_capacity(3 * (source + 1));
        let mut contacts = 0;
        for at in 0..=source {
            let (report, b, count) = self
                .history
                .get(at)
                .ok_or(ConstitutiveFibreError::ForeignOccurrence)?
                .with_resident(surface, |r| {
                    let report = r
                        .transport
                        .as_ref()
                        .ok_or(ConstitutiveFibreError::Uncertain)?;
                    let op = r
                        .operative
                        .as_ref()
                        .ok_or(ConstitutiveFibreError::Uncertain)?;
                    Ok((report.clone(), op.b.clone(), op.count))
                })?;
            if report.width() != 150 * self.nodes() + 96 {
                return Err(ConstitutiveFibreError::Shape);
            }
            for word in [
                report.lo_device_ptr() as i64,
                b.lo_device_ptr() as i64,
                count as i64,
            ] {
                pointers.push((word, word));
            }
            held.push((report, b));
            contacts = count;
        }
        let table = surface.mount_section_rest(
            &ResidentSectionRest::found(source + 1, 3, ResidentGrain(0), 64, pointers)
                .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))?,
        )?;
        let factors = surface.fresh_section(2 * (source + 1), 20, ResidentGrain(0))?;
        let output =
            surface.fresh_section(1, 4 * (10 * self.nodes() + 2 * contacts), ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_field_material_pullback(
                &lane,
                &table,
                &returned.output,
                source,
                self.nodes(),
                contacts,
                returned.grain,
                match metric {
                    NativeMaterialPullbackMetric::RelativeEntropy => 0,
                    NativeMaterialPullbackMetric::SquaredProbability => 1,
                },
                &factors,
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "material source pullback: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeMaterialSourcePullback {
            surface,
            _owner: self.owner.clone(),
            _observation: returned._observation.clone(),
            _normalized: returned.output.clone(),
            _history: held,
            output,
            source: returned.source.clone(),
            receiving: returned.receiving.clone(),
            metric,
            group_width: returned.group_width,
            series_terms: returned.series_terms,
            nodes: self.nodes(),
            contacts,
            grain: returned.grain,
        })
    }
}

#[cfg(test)]
mod tests;
