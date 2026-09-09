use super::*;

/// Complete set of possible maximizing coordinates over the retained Euclidean current ball.
/// The ball may enclose a smaller causal family: this does not identify its complete source
/// Preimage Fibre, and a selected coordinate does not select a unique source current.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeMaterialPacketReading {
    pub occurrence: usize,
    pub target_chart: NativeMaterialTarget,
    pub target_dimension: usize,
    pub selected: Option<usize>,
    pub unexcluded: Vec<usize>,
}
impl NativeConstitutiveField<'_> {
    pub fn read_material_packet(
        &self,
        occurrence: usize,
    ) -> Result<Option<NativeMaterialPacketReading>, ConstitutiveFibreError> {
        let Some(chart) = self.material_target() else {
            return Ok(None);
        };
        let targets = chart
            .dimension(self.nodes())
            .ok_or(ConstitutiveFibreError::Shape)?;
        let event = self
            .history
            .get(occurrence)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let surface = self.relation.surface;
        let report = event.with_resident(surface, |r| {
            r.transport.clone().ok_or(ConstitutiveFibreError::Uncertain)
        })?;
        let output = surface.fresh_section(1, targets + 2, ResidentGrain(0))?;
        let scratch = surface.fresh_section(1, 2 * targets, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_field_material_packet_receiver(
                &lane, &report, targets, &scratch, &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "packet receiver: {:?}",
                receipt.obstruction
            )));
        }
        let words = surface.read_out(&output)?;
        if words.iter().any(|(a, b)| a != b) || words.len() != targets + 2 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let unexcluded = words[2..]
            .iter()
            .enumerate()
            .filter_map(|(i, p)| (p.0 == 1).then_some(i))
            .collect::<Vec<_>>();
        if words[2..].iter().any(|p| !matches!(p.0, 0 | 1))
            || words[0].0 != unexcluded.len() as i64
            || unexcluded.is_empty()
        {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let selected = (unexcluded.len() == 1).then_some(unexcluded[0]);
        if words[1].0 != selected.map_or(-1, |i| i as i64) {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        Ok(Some(NativeMaterialPacketReading {
            occurrence,
            target_chart: chart,
            target_dimension: targets,
            selected,
            unexcluded,
        }))
    }
}
