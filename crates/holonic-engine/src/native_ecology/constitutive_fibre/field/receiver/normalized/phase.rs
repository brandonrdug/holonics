use super::*;
use crate::resident_section::Dyadic;
use crate::resident_section::SLOT_WORDS;

/// A phase participation whose normalization is the existing resident normalized receiver.
pub struct NativePhaseParticipation<'c> {
    surface: &'c ResidentSurface<'c>,
    query: Rc<ResidentNormalEnclosureSection<'c>>,
    neighbors: Rc<ResidentNormalEnclosureSection<'c>>,
    logits: ResidentNormalEnclosureSection<'c>,
    normalized: NativeNormalizedSection<'c>,
    output: Rc<ResidentNormalEnclosureSection<'c>>,
    rows: usize,
    neighbors_per_row: usize,
    components: usize,
    beta: Dyadic,
    series_terms: u32,
    grain: ResidentGrain,
}

pub struct NativePhaseParticipationAdjoint<'c> {
    source: ResidentNormalEnclosureSection<'c>,
    neighbors: ResidentNormalEnclosureSection<'c>,
    rows: usize,
    neighbors_per_row: usize,
    components: usize,
    beta: Dyadic,
    grain: ResidentGrain,
}

impl<'c> ResidentNormalEnclosureSection<'c> {
    /// Form bounded phase logits, then delegate normalization to `normalized_participation`.
    pub fn phase_participation(
        self: Rc<Self>,
        neighbors: Rc<Self>,
        neighbors_per_row: usize,
        beta: Dyadic,
        terms: SeriesAperture,
    ) -> Result<NativePhaseParticipation<'c>, ConstitutiveFibreError> {
        let rows = self.rows();
        let components = self.components();
        let grain = self.grain();
        let fail = || ConstitutiveFibreError::Shape;
        if rows == 0
            || components == 0
            || components % 2 != 0
            || rows > u32::MAX as usize
            || components > u32::MAX as usize / 4
            || neighbors_per_row > u32::MAX as usize / 4
            || neighbors_per_row == 0
            || neighbors.rows() != rows.checked_mul(neighbors_per_row).ok_or_else(fail)?
            || neighbors.components() != components
            || grain != neighbors.grain()
            || !(1..=120).contains(&grain.0)
            || terms.0 == 0
            || terms.0 == u32::MAX
            || !std::ptr::eq(
                self.resident_section().surface(),
                neighbors.resident_section().surface(),
            )
        {
            return Err(fail());
        }
        let surface = self.resident_section().surface();
        let logits =
            surface.fresh_section(rows, (2 * neighbors_per_row + 1) * 2, ResidentGrain(0))?;
        let flags = surface.fresh_section(rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut pass = surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            surface.record_phase_participation(
                &lane,
                self.resident_section(),
                neighbors.resident_section(),
                rows,
                neighbors_per_row,
                components,
                grain.0,
                beta,
                &logits,
                &flags,
            )?;
            surface.collect_phase_status(&lane, &flags, rows)?;
        }
        pass.close(0, &logits, 64)?;
        let receipt = pass.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "phase logits: {:?}",
                receipt.obstruction
            )));
        }
        let logits = ResidentNormalEnclosureSection::from_resident(
            surface,
            logits,
            rows,
            2 * neighbors_per_row,
            grain,
        )?;
        let normalized = logits.normalized_participation(
            neighbors_per_row,
            terms,
            NativeNormalizedFaceMeasure::ExponentialPotential,
        )?;
        let output = surface.fresh_section(rows, (components + 1) * 2, ResidentGrain(0))?;
        let flags = surface.fresh_section(rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut pass = surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            surface.record_phase_weighted(
                &lane,
                neighbors.resident_section(),
                normalized.participation().resident_section(),
                rows,
                neighbors_per_row,
                components,
                grain.0,
                &output,
                &flags,
            )?;
            surface.collect_phase_status(&lane, &flags, rows)?;
        }
        pass.close(0, &output, 64)?;
        let receipt = pass.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "phase weighted: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativePhaseParticipation {
            surface,
            query: self,
            neighbors,
            logits,
            normalized,
            output: Rc::new(ResidentNormalEnclosureSection::from_resident(
                surface, output, rows, components, grain,
            )?),
            rows,
            neighbors_per_row,
            components,
            beta,
            series_terms: terms.0,
            grain,
        })
    }
}

impl<'c> NativePhaseParticipation<'c> {
    pub fn rows(&self) -> usize {
        self.rows
    }
    pub fn neighbors_per_row(&self) -> usize {
        self.neighbors_per_row
    }
    pub fn components(&self) -> usize {
        self.components
    }
    pub fn beta(&self) -> Dyadic {
        self.beta
    }
    pub fn series_terms(&self) -> u32 {
        self.series_terms
    }
    pub fn grain(&self) -> ResidentGrain {
        self.grain
    }
    pub fn output(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.output
    }
    pub fn shared_output(&self) -> Rc<ResidentNormalEnclosureSection<'c>> {
        Rc::clone(&self.output)
    }
    pub fn participation(&self) -> &ResidentNormalEnclosureSection<'c> {
        self.normalized.participation()
    }
    pub fn logits(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.logits
    }
    pub fn normalized(&self) -> &NativeNormalizedSection<'c> {
        &self.normalized
    }
    pub fn transported_neighbors(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.neighbors
    }
    pub fn pull_back(
        &self,
        gy: &ResidentNormalEnclosureSection<'c>,
        gp: Option<&ResidentNormalEnclosureSection<'c>>,
    ) -> Result<NativePhaseParticipationAdjoint<'c>, ConstitutiveFibreError> {
        if gy.rows() != self.rows
            || gy.components() != self.components
            || gy.grain() != self.grain
            || !std::ptr::eq(gy.resident_section().surface(), self.surface)
            || gp.is_some_and(|v| {
                v.rows() != self.rows
                    || v.components() != 2 * self.neighbors_per_row
                    || v.grain() != self.grain
                    || !std::ptr::eq(v.resident_section().surface(), self.surface)
            })
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let terms = self.surface.fresh_section(
            self.rows,
            (2 * self.neighbors_per_row + 1) * 2,
            ResidentGrain(0),
        )?;
        let flags = self
            .surface
            .fresh_section(self.rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut pass = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            self.surface.record_phase_terms(
                &lane,
                self.neighbors.resident_section(),
                gy.resident_section(),
                gp.map(|v| v.resident_section()),
                self.rows,
                self.neighbors_per_row,
                self.components,
                self.grain.0,
                &terms,
                &flags,
            )?;
            self.surface
                .collect_phase_status(&lane, &flags, self.rows)?;
        }
        pass.close(0, &terms, 64)?;
        let receipt = pass.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "phase terms: {:?}",
                receipt.obstruction
            )));
        }
        let terms = ResidentNormalEnclosureSection::from_resident(
            self.surface,
            terms,
            self.rows,
            2 * self.neighbors_per_row,
            self.grain,
        )?;
        let normalized_return = self.normalized.pull_back(&terms)?;
        let h = normalized_return.potentials();
        let source =
            self.surface
                .fresh_section(self.rows, (self.components + 1) * 2, ResidentGrain(0))?;
        let returned = self.surface.fresh_section(
            self.rows * self.neighbors_per_row,
            (self.components + 1) * 2,
            ResidentGrain(0),
        )?;
        let flags = self
            .surface
            .fresh_section(self.rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut pass = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            self.surface.record_phase_adjoint(
                &lane,
                self.query.resident_section(),
                self.neighbors.resident_section(),
                self.normalized.participation().resident_section(),
                h.resident_section(),
                gy.resident_section(),
                self.rows,
                self.neighbors_per_row,
                self.components,
                self.grain.0,
                self.beta,
                &source,
                &returned,
                &flags,
            )?;
            self.surface
                .collect_phase_status(&lane, &flags, self.rows)?;
        }
        pass.close(0, &source, 64)?;
        let receipt = pass.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "phase adjoint: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativePhaseParticipationAdjoint {
            source: ResidentNormalEnclosureSection::from_resident(
                self.surface,
                source,
                self.rows,
                self.components,
                self.grain,
            )?,
            neighbors: ResidentNormalEnclosureSection::from_resident(
                self.surface,
                returned,
                self.rows * self.neighbors_per_row,
                self.components,
                self.grain,
            )?,
            rows: self.rows,
            neighbors_per_row: self.neighbors_per_row,
            components: self.components,
            beta: self.beta,
            grain: self.grain,
        })
    }
}
impl<'c> NativePhaseParticipationAdjoint<'c> {
    pub fn query(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.source
    }
    pub fn transported_neighbors(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.neighbors
    }
    pub fn rows(&self) -> usize {
        self.rows
    }
    pub fn neighbors_per_row(&self) -> usize {
        self.neighbors_per_row
    }
    pub fn components(&self) -> usize {
        self.components
    }
    pub fn beta(&self) -> Dyadic {
        self.beta
    }
    pub fn grain(&self) -> ResidentGrain {
        self.grain
    }
}

#[cfg(test)]
mod gpu_tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;
    use crate::resident_section::ResidentSectionRest;

    fn words(values: &[i128]) -> Vec<(i64, i64)> {
        values
            .iter()
            .flat_map(|v| [*v as i64, (*v >> 64) as i64])
            .map(|v| (v, v))
            .collect()
    }
    fn balls<'c>(
        surface: &'c ResidentSurface<'c>,
        rows: &[(Vec<i128>, i128)],
        components: usize,
    ) -> ResidentNormalEnclosureSection<'c> {
        let flat: Vec<i128> = rows
            .iter()
            .flat_map(|(v, r)| v.iter().copied().chain([*r]))
            .collect();
        let section = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    rows.len(),
                    2 * (components + 1),
                    ResidentGrain(0),
                    64,
                    words(&flat),
                )
                .unwrap(),
            )
            .unwrap();
        ResidentNormalEnclosureSection::from_resident(
            surface,
            section,
            rows.len(),
            components,
            ResidentGrain(12),
        )
        .unwrap()
    }

    #[test]
    #[ignore = "requires CUDA; native logits -> normalized receiver -> weighted return"]
    fn native_phase_equal_logits_and_nonzero_radius() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let unit = 1i128 << 12;
        let query = Rc::new(balls(&surface, &[(vec![unit, 0, 0, 0], unit / 16)], 4));
        let neighbors = Rc::new(balls(
            &surface,
            &[
                (vec![unit, 0, 0, 0], unit / 16),
                (vec![unit, 0, 0, 0], unit / 16),
            ],
            4,
        ));
        let result = query
            .phase_participation(neighbors, 2, Dyadic::ONE, SeriesAperture(32))
            .unwrap();
        assert_eq!(result.rows(), 1);
        assert_eq!(result.neighbors_per_row(), 2);
        assert_eq!(result.participation().rows(), 1);
        assert!(result.output().row(0).unwrap().inspect().unwrap().radius > Rat::zero());
    }

    #[test]
    #[ignore = "requires CUDA; distinguishes the optional participation-covector branch"]
    fn native_phase_gp_only_pullback_returns_resident_neighbor_covector() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let unit = 1i128 << 12;
        let q = Rc::new(balls(&surface, &[(vec![unit, 0, 0, 0], 0)], 4));
        let u = Rc::new(balls(
            &surface,
            &[(vec![0, unit, 0, 0], 0), (vec![0, -unit, 0, 0], 0)],
            4,
        ));
        let phase = q
            .phase_participation(u, 2, Dyadic::ONE, SeriesAperture(32))
            .unwrap();
        let gy = balls(&surface, &[(vec![0, 0, 0, 0], 0)], 4);
        let gp = balls(&surface, &[(vec![unit, 0, 0, 0], 0)], 4);
        let returned = phase.pull_back(&gy, Some(&gp)).unwrap();
        let query = returned.query().row(0).unwrap().inspect().unwrap();
        assert_eq!(query.center[0].imaginary, Rat::new(1.into(), 2.into()));
        assert_eq!(query.center[0].real, Rat::zero());
        assert_eq!(query.radius, Rat::zero());
        for (row, sign) in [(0, 1), (1, -1)] {
            let u = returned
                .transported_neighbors()
                .row(row)
                .unwrap()
                .inspect()
                .unwrap();
            assert_eq!(u.center[0].real, Rat::new(sign.into(), 4.into()));
            assert_eq!(u.center[0].imaginary, Rat::zero());
            assert_eq!(u.radius, Rat::zero());
        }
        // Both variation terms and both uncertain covector branches on the same producer.
        let gy = balls(&surface, &[(vec![0, unit, 0, 0], unit / 128)], 4);
        let gp = balls(&surface, &[(vec![unit, 0, 0, 0], unit / 128)], 4);
        let returned = phase.pull_back(&gy, Some(&gp)).unwrap();
        let q = returned.query().row(0).unwrap().inspect().unwrap();
        assert!(q.contains(&[
            ExactComplexWaveCurrent::new(Rat::zero(), Rat::new(3.into(), 2.into())),
            ExactComplexWaveCurrent::zero()
        ]));
        for (row, sign) in [(0, 3), (1, -3)] {
            let u = returned
                .transported_neighbors()
                .row(row)
                .unwrap()
                .inspect()
                .unwrap();
            assert!(u.contains(&[
                ExactComplexWaveCurrent::new(
                    Rat::new(sign.into(), 4.into()),
                    Rat::new(1.into(), 2.into())
                ),
                ExactComplexWaveCurrent::zero()
            ]));
            assert!(u.radius > Rat::zero());
        }
    }

    #[test]
    #[ignore = "requires CUDA; checks unequal-logit normalized intervals on the native path"]
    fn native_phase_unequal_logits_return_distinct_participation_faces() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let unit = 1i128 << 12;
        let query = Rc::new(balls(&surface, &[(vec![unit, 0, 0, 0], 0)], 4));
        let neighbors = Rc::new(balls(
            &surface,
            &[(vec![unit, 0, 0, 0], 0), (vec![-unit, 0, 0, 0], 0)],
            4,
        ));
        let result = query
            .phase_participation(neighbors, 2, Dyadic::ONE, SeriesAperture(32))
            .unwrap();
        let rows = result.normalized().read_participation().unwrap();
        assert!(rows[0][0].upper > rows[0][1].lower);
    }
}
