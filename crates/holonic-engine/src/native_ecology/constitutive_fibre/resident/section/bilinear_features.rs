use super::*;

/// Same-row exact source/condition packets, retaining both supplied sections.
pub struct ResidentBilinearFeatures<'a, 'c> {
    source: ResidentConstitutiveSection<'a, 'c>,
    conditions: ResidentConstitutiveSection<'a, 'c>,
    features: ResidentSection<'c>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;
    #[test]
    #[ignore = "requires CUDA; same-row bilinear sources retain complex signs and rational denominators without host readout"]
    fn joined_rows_preserve_complex_rational_sources() {
        let ro = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&ro).unwrap();
        let mount = |rows, width, v: Vec<i64>| {
            s.mount_section_rest(
                &ResidentSectionRest::found(
                    rows,
                    width,
                    ResidentGrain(0),
                    64,
                    v.into_iter().map(|v| (v, v)).collect(),
                )
                .unwrap(),
            )
            .unwrap()
        };
        let a = mount(2, 5, vec![1, 2, -1, 0, 2, 2, 0, 0, -3, 5]);
        let c = mount(2, 3, vec![-2, 1, 3, 1, -1, 2]);
        let reads = s.census().section_read_outs;
        let joined = ResidentConstitutiveSection::rationals(&a)
            .unwrap()
            .bilinear_features(&s, ResidentConstitutiveSection::rationals(&c).unwrap())
            .unwrap();
        assert_eq!(s.census().section_read_outs, reads);
        assert_eq!(joined.source().rows(), 2);
        assert_eq!(joined.conditions().rows(), 2);
        assert_eq!(joined.features().components(), 10);
        let values = s.detach_section(&joined.features, 64).unwrap();
        let expected = [
            [
                (1, 2),
                (1, 1),
                (-1, 2),
                (0, 1),
                (-2, 3),
                (1, 3),
                (-2, 3),
                (-1, 2),
                (1, 3),
                (-1, 6),
            ],
            [
                (2, 5),
                (0, 1),
                (0, 1),
                (-3, 5),
                (1, 2),
                (-1, 2),
                (1, 5),
                (-1, 5),
                (-3, 10),
                (-3, 10),
            ],
        ];
        for (row, want) in values.intervals.chunks_exact(11).zip(expected) {
            assert!(row.iter().all(|(a, b)| a == b));
            for ((v, _), (n, d)) in row[..10].iter().zip(want) {
                assert_eq!(
                    Rat::new((*v).into(), row[10].0.into()),
                    Rat::new(n.into(), d.into())
                );
            }
        }
        let one = mount(1, 3, vec![1, 0, 1]);
        assert!(ResidentConstitutiveSection::rationals(&a)
            .unwrap()
            .bilinear_features(&s, ResidentConstitutiveSection::rationals(&one).unwrap())
            .is_err());
    }
}

impl<'a, 'c> ResidentBilinearFeatures<'a, 'c> {
    pub fn source(&self) -> ResidentConstitutiveSection<'a, 'c> {
        self.source
    }
    pub fn conditions(&self) -> ResidentConstitutiveSection<'a, 'c> {
        self.conditions
    }
    pub fn features(&self) -> ResidentConstitutiveSection<'_, 'c> {
        ResidentConstitutiveSection::rationals(&self.features)
            .expect("completed resident bilinear features")
    }
    /// Transfer the joined packet for a delayed return. Its direct source and condition
    /// blocks remain present, followed by their products; the consumer retains that chart.
    pub fn into_features(self) -> ResidentSection<'c> {
        self.features
    }
}

impl<'a, 'c> ResidentConstitutiveSection<'a, 'c> {
    /// Form exact feature packets for each same-row source/condition contact in one passage.
    pub fn bilinear_features(
        self,
        surface: &'c ResidentSurface<'c>,
        conditions: ResidentConstitutiveSection<'a, 'c>,
    ) -> Result<ResidentBilinearFeatures<'a, 'c>, ConstitutiveFibreError> {
        if self.rows() == 0
            || self.rows() != conditions.rows()
            || self.components() % 2 != 0
            || conditions.components() % 2 != 0
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let source_complex = self.components() / 2;
        let condition_complex = conditions.components() / 2;
        let width = source_complex
            .checked_mul(condition_complex)
            .and_then(|n| n.checked_add(source_complex))
            .and_then(|n| n.checked_add(condition_complex))
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let features = surface.fresh_section(
            self.rows(),
            width.checked_add(1).ok_or(ConstitutiveFibreError::Shape)?,
            ResidentGrain(0),
        )?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            for row in 0..self.rows() {
                surface.record_constitutive_bilinear_source_row(
                    &lane,
                    self.row(row)?,
                    conditions.row(row)?,
                    &features,
                    row,
                )?;
            }
        }
        passage.close(0, &features, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "resident bilinear feature section: {:?}",
                receipt.obstruction
            )));
        }
        Ok(ResidentBilinearFeatures {
            source: self,
            conditions,
            features,
        })
    }
}
