use super::*;
use std::rc::Rc;

/// One simultaneous unit-basis read over consecutive blocks of one joint enclosure.
pub struct NormalSectionBasisFace<'a, 'c> {
    source: ResidentNormalEnclosureView<'a, 'c>,
    surface: &'c ResidentSurface<'c>,
    coordinates: Vec<usize>,
    _permutation: Rc<ResidentSection<'c>>,
    report: ResidentSection<'c>,
    sections: usize,
}

impl<'a, 'c> NormalSectionBasisFace<'a, 'c> {
    pub fn source(&self) -> ResidentNormalEnclosureView<'a, 'c> {
        self.source
    }
    pub fn sections(&self) -> usize {
        self.sections
    }
    pub fn selections(&self) -> Result<Vec<NormalBasisSelection>, ConstitutiveFibreError> {
        let values = wides(&self.surface.read_out(&self.report)?)?;
        if values.len() != 5 * self.sections {
            return Err(ConstitutiveFibreError::Shape);
        }
        let scale = BigInt::one() << self.source.grain.0;
        (0..self.sections)
            .map(|section| {
                let v = &values[5 * section..5 * (section + 1)];
                if v[0] < 0
                    || v[2] < 1
                    || v[2] as usize > self.coordinates.len()
                    || !matches!(v[3], 0 | 1)
                    || v[4] < 0
                {
                    return Err(ConstitutiveFibreError::Shape);
                }
                let selected = usize::try_from(v[0]).map_err(|_| ConstitutiveFibreError::Shape)?;
                if selected >= self.coordinates.len() {
                    return Err(ConstitutiveFibreError::Shape);
                }
                Ok(NormalBasisSelection {
                    selected,
                    selected_coordinate: self.coordinates[selected],
                    centre_score: Rat::new(v[1].into(), scale.clone()),
                    centre_ties: usize::try_from(v[2])
                        .map_err(|_| ConstitutiveFibreError::Shape)?,
                    score_radius: Rat::new(v[4].into(), scale.clone()),
                    robust: v[3] == 1,
                })
            })
            .collect()
    }
}

impl<'a, 'c> ResidentNormalEnclosureView<'a, 'c> {
    /// Read every requested section from one shared joint centre and radius.
    pub fn read_basis_sections(
        self,
        chart: &NormalWaveBasisChart<'c>,
        sections: usize,
    ) -> Result<NormalSectionBasisFace<'a, 'c>, ConstitutiveFibreError> {
        let n = chart.coordinates().len();
        let width = n
            .checked_mul(2)
            .and_then(|v| v.checked_mul(sections))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if sections == 0
            || sections > u32::MAX as usize
            || self.width != width
            || !std::ptr::eq(self.surface, chart.receiver_surface())
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let scores = self
            .surface
            .fresh_section(1, 2 * n * sections, ResidentGrain(0))?;
        let report = self
            .surface
            .fresh_section(1, 10 * sections, ResidentGrain(0))?;
        let mut p = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            self.surface.record_normal_wave_basis_sections(
                &lane,
                self,
                chart.permutation_section(),
                n,
                sections,
                self.grain.0,
                &scores,
                &report,
            )?;
        }
        p.close(0, &report, 64)?;
        let r = p.finish()?.launch()?;
        if !r.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normal section basis receiver: {:?}",
                r.obstruction
            )));
        }
        Ok(NormalSectionBasisFace {
            source: self,
            surface: self.surface,
            coordinates: chart.coordinates().to_vec(),
            _permutation: Rc::clone(chart.permutation_section()),
            report,
            sections,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;
    fn mount<'c>(s: &'c ResidentSurface<'c>, values: &[i128]) -> ResidentSection<'c> {
        let words = values
            .iter()
            .flat_map(|v| {
                let b = v.to_le_bytes();
                [
                    i64::from_le_bytes(b[..8].try_into().unwrap()),
                    i64::from_le_bytes(b[8..].try_into().unwrap()),
                ]
            })
            .map(|v| (v, v))
            .collect();
        s.mount_section_rest(
            &ResidentSectionRest::found(1, 2 * values.len(), ResidentGrain(0), 64, words).unwrap(),
        )
        .unwrap()
    }
    /// Parity law (section basis): each section selects the exact maximal real coordinate, a chart
    /// permutation permutes the selection, and exact centre ties are reported as non-robust.
    #[test]
    #[ignore = "requires CUDA; all section selections share one complex source ball"]
    fn joint_basis_sections_preserve_source_phase_radius_and_permutation() {
        let ro = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&ro).unwrap();
        let g = ResidentGrain(8);
        let scale = 1i128 << 8;
        let current = mount(
            &s,
            &[
                scale,
                7 * scale,
                0,
                -3 * scale,
                0,
                scale,
                2 * scale,
                -4 * scale,
                scale / 4,
            ],
        );
        let view = ResidentNormalEnclosureView {
            surface: &s,
            section: &current,
            offset: 0,
            width: 8,
            grain: g,
        };
        let chart = NormalWaveBasisChart::identity(&s, 2).unwrap();
        let reads = s.census().section_read_outs;
        let face = view.read_basis_sections(&chart, 2).unwrap();
        assert_eq!(s.census().section_read_outs, reads);
        let out = face.selections().unwrap();
        assert_eq!(out.iter().map(|v| v.selected).collect::<Vec<_>>(), [0, 1]);
        assert!(out.iter().all(|v| v.robust
            && v.centre_ties == 1
            && v.score_radius == Rat::new(1.into(), 4.into())));
        assert_eq!(face.source().inspect().unwrap(), view.inspect().unwrap());
        let reverse = NormalWaveBasisChart::from_permutation(&s, &[1, 0]).unwrap();
        let changed = view
            .read_basis_sections(&reverse, 2)
            .unwrap()
            .selections()
            .unwrap();
        assert_eq!(
            changed.iter().map(|v| v.selected).collect::<Vec<_>>(),
            [1, 0]
        );
        assert_eq!(
            changed
                .iter()
                .map(|v| v.selected_coordinate)
                .collect::<Vec<_>>(),
            [0, 1]
        );
        assert!(view.read_basis_sections(&chart, 1).is_err());
        let ties = mount(&s, &[scale, 0, scale, 2 * scale, scale]);
        let view = ResidentNormalEnclosureView {
            surface: &s,
            section: &ties,
            offset: 0,
            width: 4,
            grain: g,
        };
        let selected = view
            .read_basis_sections(&chart, 1)
            .unwrap()
            .selections()
            .unwrap();
        assert_eq!(selected[0].centre_ties, 2);
        assert_eq!(selected[0].selected, 0);
        assert!(!selected[0].robust);
    }
}
