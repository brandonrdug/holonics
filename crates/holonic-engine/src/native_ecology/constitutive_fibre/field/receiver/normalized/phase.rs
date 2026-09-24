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
                false,
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
                false,
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
impl<'c> NativePhaseParticipation<'c> {
    /// The phase face of the complex pair potential `s_j = beta <q|u_j>`:
    /// `phi_j = Im s_j / 2 = (beta/2) sum (q_re u_im - q_im u_re)`. The magnitude face
    /// `p = softmax(Re s)` and the weighted output are unchanged and do not read it; this is
    /// read from the producing operands on request, so the participation passage itself carries
    /// no second softmax and no extra work. Returned as a ball of the logits chart: `phi` in each
    /// real slot, exactly zero in each imaginary one.
    ///
    /// No consumer yet: owed to campaign 2 (rings), where the participation's phase face joins
    /// each ring's storage/flow mode.
    pub fn phase(&self) -> Result<ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        let phase = self.surface.fresh_section(
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
            self.surface.record_phase_participation_phase(
                &lane,
                self.query.resident_section(),
                self.neighbors.resident_section(),
                self.rows,
                self.neighbors_per_row,
                self.components,
                self.grain.0,
                self.beta,
                &phase,
                &flags,
            )?;
            self.surface
                .collect_phase_status(&lane, &flags, self.rows)?;
        }
        pass.close(0, &phase, 64)?;
        let receipt = pass.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "phase face: {:?}",
                receipt.obstruction
            )));
        }
        ResidentNormalEnclosureSection::from_resident(
            self.surface,
            phase,
            self.rows,
            2 * self.neighbors_per_row,
            self.grain,
        )
    }

    /// The adjoint of the phase face for a covector `g_phi` on it (real slot per neighbour):
    /// `dq_re += (beta/2) sum_j g_j u_j,im`, `dq_im -= (beta/2) sum_j g_j u_j,re`,
    /// `du_j,re -= (beta/2) g_j q_im`, `du_j,im += (beta/2) g_j q_re`. The two faces read
    /// disjoint slots of `s`, so these terms add to `pull_back`'s magnitude adjoint.
    ///
    /// No consumer yet: owed to campaign 2 (rings), with `phase`.
    pub fn pull_back_phase(
        &self,
        gphi: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<NativePhaseParticipationAdjoint<'c>, ConstitutiveFibreError> {
        if gphi.rows() != self.rows
            || gphi.components() != 2 * self.neighbors_per_row
            || gphi.grain() != self.grain
            || !std::ptr::eq(gphi.resident_section().surface(), self.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
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
            self.surface.record_phase_participation_phase_adjoint(
                &lane,
                self.query.resident_section(),
                self.neighbors.resident_section(),
                gphi.resident_section(),
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
                "phase face adjoint: {:?}",
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
    /// Move the two source covectors without allocating or copying resident packets.
    pub fn into_parts(
        self,
    ) -> (
        ResidentNormalEnclosureSection<'c>,
        ResidentNormalEnclosureSection<'c>,
    ) {
        (self.source, self.neighbors)
    }
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

impl NativePhaseParticipation<'_> {
    /// **This participation as a receiver element** (plan phase 7): it reads the query and the
    /// transported neighbours at zero flow and injects the drive `y = Σ a U Ψ` into the field. It is
    /// an exterior drive whose delivered power `⟨e_D, y⟩` enters the field's balance
    /// (`Holon/Law.lean::exterior_drive_balance`); its sign is the consumer's, never assumed.
    pub fn receiver_element(&self) -> ActiveReceiver {
        let query = self.rows * self.components;
        ActiveReceiver::declared(
            "phase participation",
            query + query * self.neighbors_per_row,
            ReceiverPower::ExteriorDrive {
                drive_ports: real_coordinates(&self.output),
            },
        )
    }

    /// `⟨e_D, y⟩` enclosed over the returned drive balls at a declared real-coded drive effort:
    /// the host-side active term this receiver contributes to the field's `EnergyBalance`.
    pub fn delivered_power(
        &self,
        drive_effort: &[Rat],
    ) -> Result<ExactInterval, ConstitutiveFibreError> {
        delivered_power_enclosure(&self.output, drive_effort)
    }
}

impl NativePhaseParticipationAdjoint<'_> {
    /// **This adjoint as a receiver element** (plan phase 7): the covector return onto the
    /// producing query and transported neighbours, a power-preserving pullback
    /// (`Holon/Law.lean::pullback_law`).
    pub fn receiver_element(&self) -> ActiveReceiver {
        ActiveReceiver::declared(
            "phase participation adjoint",
            real_coordinates(&self.source) + real_coordinates(&self.neighbors),
            ReceiverPower::Pullback,
        )
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

    /// Phase-participation parity: the device phase face is exactly `Im⟨q|u⟩/2` and its adjoint
    /// returns the exact halves derived by hand below.
    #[test]
    #[ignore = "requires CUDA; the complex pair potential's phase face and its adjoint"]
    fn native_phase_face_is_half_the_imaginary_potential_and_returns_its_adjoint() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let unit = 1i128 << 12;
        // q = (1 + 0i, 0 + 1i); u_0 = (0 + 1i, 0 + 0i), u_1 = (1 + 0i, 1 + 0i).
        // Im<q|u_0> = 1*1 - 0*0 + 0*0 - 1*0 = 1; Im<q|u_1> = 1*0 - 0*1 + 0*0 - 1*1 = -1.
        let q = Rc::new(balls(&surface, &[(vec![unit, 0, 0, unit], 0)], 4));
        let u = Rc::new(balls(
            &surface,
            &[(vec![0, unit, 0, 0], 0), (vec![unit, 0, unit, 0], 0)],
            4,
        ));
        let phase = q
            .phase_participation(u, 2, Dyadic::ONE, SeriesAperture(32))
            .unwrap();
        let face = phase.phase().unwrap().row(0).unwrap().inspect().unwrap();
        assert_eq!(face.center[0].real, Rat::new(1.into(), 2.into()));
        assert_eq!(face.center[1].real, Rat::new((-1).into(), 2.into()));
        assert!(face.center.iter().all(|c| c.imaginary == Rat::zero()));
        assert_eq!(face.radius, Rat::zero());
        // The participation itself still reads Re s only (equal real scores 0 and 1).
        let p = phase.normalized().read_participation().unwrap();
        assert!(p[0][1].lower > p[0][0].upper);
        // Adjoint of phi_0 alone: dq = (1/2)(u_0,im ; -u_0,re) per pair, du_0 = (1/2)(-q_im ; q_re).
        let g = balls(&surface, &[(vec![unit, 0, 0, 0], 0)], 4);
        let returned = phase.pull_back_phase(&g).unwrap();
        let dq = returned.query().row(0).unwrap().inspect().unwrap();
        assert_eq!(
            dq.center,
            vec![
                ExactComplexWaveCurrent::new(Rat::new(1.into(), 2.into()), Rat::zero()),
                ExactComplexWaveCurrent::zero(),
            ]
        );
        let du0 = returned
            .transported_neighbors()
            .row(0)
            .unwrap()
            .inspect()
            .unwrap();
        assert_eq!(
            du0.center,
            vec![
                ExactComplexWaveCurrent::new(Rat::zero(), Rat::new(1.into(), 2.into())),
                ExactComplexWaveCurrent::new(Rat::new((-1).into(), 2.into()), Rat::zero()),
            ]
        );
        let du1 = returned
            .transported_neighbors()
            .row(1)
            .unwrap()
            .inspect()
            .unwrap();
        assert!(du1.center.iter().all(|c| c.is_zero()));
    }

}
