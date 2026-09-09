//! The material source derivative uses the producing M and query, never a later surrogate.
use super::*;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, serde::Deserialize)]
pub enum NativeMaterialPullbackMetric {
    /// Negative derivative of KL(q || p) in the declared real-potential chart.
    #[default]
    RelativeEntropy,
    /// Negative derivative of one half the squared probability discrepancy.
    SquaredProbability,
    /// Negative derivative of half squared complex-current discrepancy, including phase.
    SquaredCurrent,
}

/// Resident partial adjoint with historical operator factors held fixed. This carries both
/// query arguments, including every born internal current. It is not a finite successor or
/// the adjoint of the entire chronology by itself.
pub struct NativeMaterialSourcePullback<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    pub(in super::super::super) _owner: Rc<()>,
    _observation: Rc<ResidentSection<'chart>>,
    _covector_input: Rc<ResidentSection<'chart>>,
    _history: Vec<Rc<ResidentSection<'chart>>>,
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
    /// Zero for the ungrouped complex-current metric.
    pub group_width: usize,
    /// Zero when the metric needs no exponential series.
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
        if metric == NativeMaterialPullbackMetric::SquaredCurrent {
            return self
                .pull_back_material_current(returned.receiving.occurrence)?
                .ok_or(ConstitutiveFibreError::ForeignOccurrence);
        }
        self.material_query_pullback(
            returned.output.clone(),
            returned._observation.clone(),
            returned.source.clone(),
            returned.receiving.clone(),
            metric,
            returned.group_width,
            returned.series_terms,
            returned.grain,
        )
    }

    /// Return the full complex-current discrepancy through its actual producing material
    /// operator. No exponential observation or nonzero packet mass is required by this metric.
    /// The same unit complex-current metric drives the ordinary material coefficient fit.
    pub fn pull_back_material_current(
        &self,
        receiving: usize,
    ) -> Result<Option<NativeMaterialSourcePullback<'chart>>, ConstitutiveFibreError> {
        if !self.material_transport_source().is_some_and(NativeMaterialTransportSource::is_operative)
        {
            return Err(ConstitutiveFibreError::Arithmetic(
                "material source pullback requires the operative contextual carrier".into(),
            ));
        }
        let event = self
            .history
            .get(receiving)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let Some(source) = event.lineage.received_from else {
            return Ok(None);
        };
        let producer = self
            .history
            .get(source)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let surface = self.relation.surface;
        let prediction = producer.with_resident(surface, |r| {
            r.transport.clone().ok_or(ConstitutiveFibreError::Uncertain)
        })?;
        let observation = event.with_resident(surface, |r| {
            r.transport.clone().ok_or(ConstitutiveFibreError::Uncertain)
        })?;
        let targets = self
            .material_target_dimension()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let output = Rc::new(surface.fresh_section(1, 8 * targets, ResidentGrain(0))?);
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_field_material_current_covector(
                &lane,
                &prediction,
                &observation,
                targets,
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "material current covector: {:?}",
                receipt.obstruction
            )));
        }
        self.material_query_pullback(
            output,
            observation,
            producer.lineage.clone(),
            event.lineage.clone(),
            NativeMaterialPullbackMetric::SquaredCurrent,
            0,
            0,
            self.transport_grain()?,
        )
        .map(Some)
    }

    #[allow(clippy::too_many_arguments)]
    fn material_query_pullback(
        &self,
        covector: Rc<ResidentSection<'chart>>,
        observation: Rc<ResidentSection<'chart>>,
        source_lineage: NativeFieldLineage,
        receiving: NativeFieldLineage,
        metric: NativeMaterialPullbackMetric,
        group_width: usize,
        series_terms: u32,
        grain: u32,
    ) -> Result<NativeMaterialSourcePullback<'chart>, ConstitutiveFibreError> {
        if !self.material_transport_source().is_some_and(NativeMaterialTransportSource::is_operative)
        {
            return Err(ConstitutiveFibreError::Arithmetic(
                "material source pullback requires the operative contextual carrier".into(),
            ));
        }
        if self.material_transport_source()==Some(NativeMaterialTransportSource::OperativeLinear){
            return self.linear_material_query_pullback(covector,observation,source_lineage,receiving,metric,group_width,series_terms,grain);
        }
        let source = source_lineage.occurrence;
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
            if report.width()
                != self
                    .material_transport_source()
                    .unwrap()
                    .report_words_for(self.nodes(), self.material_target().unwrap())
                    .ok_or(ConstitutiveFibreError::Shape)?
            {
                return Err(ConstitutiveFibreError::Shape);
            }
            for word in [
                report.lo_device_ptr() as i64,
                b.lo_device_ptr() as i64,
                count as i64,
            ] {
                pointers.push((word, word));
            }
            held.push(report);held.push(b);
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
                &covector,
                source,
                self.nodes(),
                self.material_target_dimension()
                    .ok_or(ConstitutiveFibreError::Shape)?,
                contacts,
                grain,
                match metric {
                    NativeMaterialPullbackMetric::RelativeEntropy => 0,
                    NativeMaterialPullbackMetric::SquaredProbability => 1,
                    NativeMaterialPullbackMetric::SquaredCurrent => 2,
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
            _observation: observation,
            _covector_input: covector,
            _history: held,
            output,
            source: source_lineage,
            receiving,
            metric,
            group_width,
            series_terms,
            nodes: self.nodes(),
            contacts,
            grain,
        })
    }
}

#[cfg(test)]
mod tests;

mod linear;
