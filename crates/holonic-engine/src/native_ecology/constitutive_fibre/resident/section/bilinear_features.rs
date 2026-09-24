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
    use num_traits::{One, Zero};
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

    /// The complex-product realization of `c ⊗ s` in the interleaved real chart, as the
    /// exact host bilinear owner reads it. Columns are `(left, right)` at `i·2k + j`.
    fn mixed_product_operator(
        source_complex: usize,
        condition_complex: usize,
    ) -> holonics::exact_linear::BilinearOperator {
        let right = 2 * condition_complex;
        let mut coefficients =
            vec![vec![Rat::zero(); 2 * source_complex * right]; 2 * source_complex * condition_complex];
        for i in 0..source_complex {
            for j in 0..condition_complex {
                let out = 2 * (j * source_complex + i);
                coefficients[out][(2 * i) * right + 2 * j] = Rat::one();
                coefficients[out][(2 * i + 1) * right + 2 * j + 1] = -Rat::one();
                coefficients[out + 1][(2 * i) * right + 2 * j + 1] = Rat::one();
                coefficients[out + 1][(2 * i + 1) * right + 2 * j] = Rat::one();
            }
        }
        holonics::exact_linear::BilinearOperator::new(
            2 * source_complex,
            right,
            holonics::exact_linear::ExactRatMatrix::new(coefficients).unwrap(),
        )
        .unwrap()
    }

    #[test]
    #[ignore = "requires CUDA; one feature covector returns to both bilinear operands and pairs with the exact differential"]
    fn feature_covector_returns_to_source_and_condition() {
        let ro = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&ro).unwrap();
        let grain = ResidentGrain(16);
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
        // Two rows, two complex source coordinates, one complex condition; unit denominators
        // keep the whole return exact, so every rounding slot below must stay empty.
        let source_words = [1i64, 2, -1, 0, 1, 2, 0, 0, -3, 1];
        let condition_words = [3i64, -1, 1, 0, 2, 1];
        let covector_words = [
            1i64, 0, 0, 1, 2, -1, -1, -2, 1, 1, 1, 0, 2, 1, 1, -1, 0, 3, 0, 0, -1, 1,
        ];
        let source = mount(2, 5, source_words.to_vec());
        let condition = mount(2, 3, condition_words.to_vec());
        let covector = mount(2, 11, covector_words.to_vec());
        let joined = ResidentConstitutiveSection::rationals(&source)
            .unwrap()
            .bilinear_features(
                &s,
                ResidentConstitutiveSection::rationals(&condition).unwrap(),
            )
            .unwrap();
        let covector = ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::rationals(&covector).unwrap(),
            grain,
        )
        .unwrap();
        let reads = s.census().section_read_outs;
        let (returned_source, returned_condition) = joined.pull_back(&covector).unwrap();
        assert_eq!(s.census().section_read_outs, reads);
        assert_eq!(returned_source.rows(), 2);
        assert_eq!(returned_source.components(), 4);
        assert_eq!(returned_condition.components(), 2);
        let product = mixed_product_operator(2, 1);
        let rat = |v: i64| Rat::from_integer(v.into());
        let mut source_covector = Vec::new();
        let mut condition_covector = Vec::new();
        for row in 0..2 {
            let x = &source_words[row * 5..row * 5 + 5];
            let h = &condition_words[row * 3..row * 3 + 3];
            let g = &covector_words[row * 11..row * 11 + 11];
            let (left, right) = product
                .pullback(
                    &(0..4).map(|i| rat(x[i])).collect::<Vec<_>>(),
                    &(0..2).map(|j| rat(h[j])).collect::<Vec<_>>(),
                    &(0..4).map(|j| rat(g[6 + j])).collect::<Vec<_>>(),
                )
                .unwrap();
            let ball = returned_source.row(row).unwrap().inspect().unwrap();
            assert!(ball.radius.is_zero());
            for i in 0..2 {
                assert_eq!(ball.center[i].real, rat(g[2 * i]) + &left[2 * i]);
                assert_eq!(ball.center[i].imaginary, rat(g[2 * i + 1]) + &left[2 * i + 1]);
                source_covector.push(ball.center[i].real.clone());
                source_covector.push(ball.center[i].imaginary.clone());
            }
            let ball = returned_condition.row(row).unwrap().inspect().unwrap();
            assert!(ball.radius.is_zero());
            assert_eq!(ball.center[0].real, rat(g[4]) + &right[0]);
            assert_eq!(ball.center[0].imaginary, rat(g[5]) + &right[1]);
            condition_covector.push(ball.center[0].real.clone());
            condition_covector.push(ball.center[0].imaginary.clone());
        }
        // The exact differential, taken as a finite difference of the same forward owner with
        // its own second-order term removed, pairs with the covector through both returns.
        let delta_source = [1i64, -1, 0, 2];
        let delta_condition = [1i64, 1];
        let mut bumped_source = Vec::new();
        let mut bumped_condition = Vec::new();
        for row in 0..2 {
            for i in 0..4 {
                bumped_source.push(source_words[row * 5 + i] + delta_source[i]);
            }
            bumped_source.push(1);
            for j in 0..2 {
                bumped_condition.push(condition_words[row * 3 + j] + delta_condition[j]);
            }
            bumped_condition.push(1);
        }
        let bumped_source = mount(2, 5, bumped_source);
        let bumped_condition = mount(2, 3, bumped_condition);
        let bumped = ResidentConstitutiveSection::rationals(&bumped_source)
            .unwrap()
            .bilinear_features(
                &s,
                ResidentConstitutiveSection::rationals(&bumped_condition).unwrap(),
            )
            .unwrap();
        let before = s.detach_section(&joined.features, 64).unwrap();
        let after = s.detach_section(&bumped.features, 64).unwrap();
        let read = |rest: &ResidentSectionRest, row: usize| -> Vec<Rat> {
            let words = &rest.intervals[row * 11..row * 11 + 11];
            (0..10)
                .map(|j| Rat::new(words[j].0.into(), words[10].0.into()))
                .collect()
        };
        let second_order = product
            .apply(
                &delta_source.iter().map(|v| rat(*v)).collect::<Vec<_>>(),
                &delta_condition.iter().map(|v| rat(*v)).collect::<Vec<_>>(),
            )
            .unwrap();
        for row in 0..2 {
            let g = &covector_words[row * 11..row * 11 + 11];
            let (before_row, after_row) = (read(&before, row), read(&after, row));
            let mut pairing = Rat::zero();
            for j in 0..10 {
                let mut differential = &after_row[j] - &before_row[j];
                if j >= 6 {
                    differential -= &second_order[j - 6];
                }
                pairing += differential * rat(g[j]);
            }
            let mut returned = Rat::zero();
            for i in 0..4 {
                returned += rat(delta_source[i]) * &source_covector[row * 4 + i];
            }
            for j in 0..2 {
                returned += rat(delta_condition[j]) * &condition_covector[row * 2 + j];
            }
            assert_eq!(pairing, returned);
        }
        // Shape and parity refusals: a covector of the wrong feature width or row population
        // is not silently restricted onto the retained operands.
        let narrow = mount(2, 7, vec![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]);
        let narrow = ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::rationals(&narrow).unwrap(),
            grain,
        )
        .unwrap();
        assert!(joined.pull_back(&narrow).is_err());
        let single = mount(1, 11, vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]);
        let single = ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::rationals(&single).unwrap(),
            grain,
        )
        .unwrap();
        assert!(joined.pull_back(&single).is_err());
        // The conjugated operand still forms an exact feature packet, but its product with the
        // covector leaves the wide carrier: the return refuses instead of truncating a
        // coordinate. The scale is declared here, not chosen to make an assertion pass.
        let coarse = ResidentGrain(60);
        let condition_octave = 1i64 << 40;
        let covector_octave = 1i64 << 30;
        let huge_condition = mount(
            2,
            3,
            vec![condition_octave, 0, 1, condition_octave, 0, 1],
        );
        let huge = ResidentConstitutiveSection::rationals(&source)
            .unwrap()
            .bilinear_features(
                &s,
                ResidentConstitutiveSection::rationals(&huge_condition).unwrap(),
            )
            .unwrap();
        let heavy = mount(
            2,
            11,
            vec![
                0,
                0,
                0,
                0,
                0,
                0,
                covector_octave,
                0,
                covector_octave,
                0,
                1,
                0,
                0,
                0,
                0,
                0,
                0,
                covector_octave,
                0,
                covector_octave,
                0,
                1,
            ],
        );
        let heavy = ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::rationals(&heavy).unwrap(),
            coarse,
        )
        .unwrap();
        assert!(huge.pull_back(&heavy).is_err());
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

    /// Return one feature covector to BOTH operands of the same row.
    ///
    /// `φ = [s, c, c⊗s]` is holomorphic in each operand, so the real transpose of its
    /// differential multiplies by the conjugate of the other operand:
    /// `g_s = g[s] + Σ_c conj(c) g[c⊗s]` and `g_c = g[c] + Σ_s conj(s) g[c⊗s]`. Hence
    /// `⟨Dφ[δs,δc], g⟩ = ⟨δs, g_s⟩ + ⟨δc, g_c⟩` in the interleaved real chart. The
    /// retained forward operands are the linearization point and stay exact point rows;
    /// each returned enclosure carries the radius this law transported to it. The pair is
    /// `(source covector, condition covector)`; neither is a state displacement.
    pub fn pull_back(
        &self,
        covector: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<
        (
            ResidentNormalEnclosureSection<'c>,
            ResidentNormalEnclosureSection<'c>,
        ),
        ConstitutiveFibreError,
    > {
        let surface = self.features.surface();
        let rows = self.source.rows();
        let source_complex = self.source.components() / 2;
        let condition_complex = self.conditions.components() / 2;
        let width = source_complex
            .checked_mul(condition_complex)
            .and_then(|n| n.checked_add(source_complex))
            .and_then(|n| n.checked_add(condition_complex))
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if covector.rows() != rows
            || covector.components() != width
            || !std::ptr::eq(covector.resident_section().surface(), surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let words = |components: usize| {
            components
                .checked_mul(2)
                .and_then(|n| n.checked_add(1)?.checked_mul(2))
                .ok_or(ConstitutiveFibreError::Shape)
        };
        let source_out =
            surface.fresh_section(rows, words(source_complex)?, ResidentGrain(0))?;
        let condition_out =
            surface.fresh_section(rows, words(condition_complex)?, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_bilinear_source_adjoint(
                &lane,
                self.source,
                self.conditions,
                covector.resident_section(),
                &source_out,
                &condition_out,
            )?;
        }
        passage.close(0, &source_out, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "bilinear source adjoint: {:?}",
                receipt.obstruction
            )));
        }
        Ok((
            ResidentNormalEnclosureSection::from_resident(
                surface,
                source_out,
                rows,
                2 * source_complex,
                covector.grain(),
            )?,
            ResidentNormalEnclosureSection::from_resident(
                surface,
                condition_out,
                rows,
                2 * condition_complex,
                covector.grain(),
            )?,
        ))
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
