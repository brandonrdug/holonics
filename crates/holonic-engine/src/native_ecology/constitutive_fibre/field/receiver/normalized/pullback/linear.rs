use super::*;
impl<'c> NativeConstitutiveField<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn linear_material_query_pullback(
        &self,
        covector: Rc<ResidentSection<'c>>,
        observation: Rc<ResidentSection<'c>>,
        source: NativeFieldLineage,
        receiving: NativeFieldLineage,
        metric: NativeMaterialPullbackMetric,
        group_width: usize,
        series_terms: u32,
        grain: u32,
    ) -> Result<NativeMaterialSourcePullback<'c>, ConstitutiveFibreError> {
        let surface = self.relation.surface;
        let n = self.nodes();
        let targets = self
            .material_target_dimension()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let (source_report, contacts) = self
            .history
            .get(source.occurrence)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?
            .with_resident(surface, |h| {
                Ok((
                    h.transport
                        .clone()
                        .ok_or(ConstitutiveFibreError::Uncertain)?,
                    h.operative
                        .as_ref()
                        .ok_or(ConstitutiveFibreError::Uncertain)?
                        .count,
                ))
            })?;
        let mut pointers = vec![];
        let mut held = vec![source_report.clone()];
        for h in &self.history[source.occurrence + 1..] {
            // Material return factors suffice for this journal. An archived row need not
            // restore its historical interior to the device just to recover a matrix entry.
            let report = if let Some(r) = h.resident.as_ref() {
                r.transport
                    .clone()
                    .ok_or(ConstitutiveFibreError::Uncertain)?
            } else {
                Rc::new(
                    surface.mount_section_rest(
                        &h.transport_rest(surface)?
                            .ok_or(ConstitutiveFibreError::Uncertain)?,
                    )?,
                )
            };
            let p = report.lo_device_ptr() as i64;
            let linked = i64::from(h.lineage.observed_source().is_some());
            pointers.extend([(p, p), (linked, linked)]);
            held.push(report);
        }
        let later = held.len() - 1;
        if pointers.is_empty() {
            pointers.resize(2, (0, 0));
        }
        let table = surface.mount_section_rest(
            &ResidentSectionRest::found(later.max(1), 2, ResidentGrain(0), 64, pointers)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        let output = surface.fresh_section(1, 4 * (10 * n + 2 * contacts), ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_linear_material_pullback(
                &lane,
                &self
                    .transport
                    .as_ref()
                    .ok_or(ConstitutiveFibreError::Shape)?
                    .state,
                &table,
                &source_report,
                &covector,
                n,
                targets,
                contacts,
                later,
                grain,
                match metric {
                    NativeMaterialPullbackMetric::RelativeEntropy => 0,
                    NativeMaterialPullbackMetric::SquaredProbability => 1,
                    NativeMaterialPullbackMetric::SquaredCurrent => 2,
                },
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "linear material pullback: {:?}",
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
            source,
            receiving,
            metric,
            group_width,
            series_terms,
            nodes: n,
            contacts,
            grain,
        })
    }
}
