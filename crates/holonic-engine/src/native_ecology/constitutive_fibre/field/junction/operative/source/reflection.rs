use super::*;
use crate::resident_section::SLOT_WORDS;

/// One producing source reflection applied to a row section. Every row shares the same source
/// cut, factor and internal `b` branch; only its boundary current and enclosing radius differ.
pub struct NativeFieldReflectionSection<'a, 'c> {
    source: &'a NativeFieldCurrentSource<'c>,
    input: &'a ResidentNormalEnclosureSection<'c>,
    joint_input: ResidentNormalEnclosureSection<'c>,
    output: ResidentNormalEnclosureSection<'c>,
    trace: ResidentSection<'c>,
}

impl<'a, 'c> NativeFieldReflectionSection<'a, 'c> {
    pub fn source(&self) -> &NativeFieldCurrentSource<'c> {
        self.source
    }
    pub fn input(&self) -> &ResidentNormalEnclosureSection<'c> {
        self.input
    }
    pub fn joint_input(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.joint_input
    }
    pub fn output(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.output
    }
    pub fn into_output(self) -> ResidentNormalEnclosureSection<'c> {
        self.output
    }
    pub fn inspect_residuals(&self) -> Result<Vec<Vec<ExactComplexWaveCurrent>>, Error> {
        let words = self.source.surface.read_out(&self.trace)?;
        words
            .chunks_exact(self.trace.width())
            .map(|row| {
                super::super::decode_reflection_residual(
                    row,
                    self.source.boundary_components(),
                    self.source.grain,
                )
            })
            .collect()
    }

    /// Form and pull back a fixed-D output residual for every target row in one resident passage.
    /// The reflection is self-adjoint under the declared unit pairing, so this keeps D fixed while
    /// preserving the complete joint current and the shared internal branch.
    pub fn input_covectors(
        &self,
        targets: &ResidentNormalEnclosureSection<'c>,
        mask: Option<&ResidentSection<'c>>,
        step_bits: u32,
    ) -> Result<ResidentNormalEnclosureSection<'c>, Error> {
        let source = self.source;
        let surface = source.surface;
        let d = source.boundary_components();
        let count = source.births.len();
        let width = d.checked_add(2 * count).ok_or(Error::Shape)?;
        if self.output.rows() == 0
            || targets.rows() != self.output.rows()
            || targets.components() != d
            || targets.grain() != self.output.grain()
            || step_bits > 120
        {
            return Err(Error::Shape);
        }
        if let Some(mask) = mask {
            if mask.rows() != 1 || mask.width() != d / 2 || mask.grain().0 != 0 {
                return Err(Error::Shape);
            }
        }
        let target_residual =
            surface.fresh_section(targets.rows(), 2 * (width + 1), ResidentGrain(0))?;
        let mut p = surface
            .begin_passage(&[vec![]])
            .map_err(|e| Error::Arithmetic(e.to_string()))?;
        {
            let lane = p
                .open(0, &[])
                .map_err(|e| Error::Arithmetic(e.to_string()))?;
            surface
                .record_field_target_residual_section(
                    &lane,
                    self.output.resident_section(),
                    targets.resident_section(),
                    mask,
                    d,
                    count,
                    targets.rows(),
                    step_bits,
                    &target_residual,
                )
                .map_err(|e| Error::Arithmetic(e.to_string()))?;
        }
        p.close(0, &target_residual, 64)
            .map_err(|e| Error::Arithmetic(e.to_string()))?;
        let receipt = p
            .finish()
            .map_err(|e| Error::Arithmetic(e.to_string()))?
            .launch()
            .map_err(|e| Error::Arithmetic(e.to_string()))?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "field target residual: {:?}",
                receipt.obstruction
            )));
        }
        let residual = ResidentNormalEnclosureSection::from_resident(
            surface,
            target_residual,
            targets.rows(),
            width,
            self.output.grain(),
        )
        .map_err(|_| Error::Shape)?;
        self.reflect_joint_section(&residual)
    }

    /// Apply the fixed-D paired reflection to already formed full joint rows. This is the
    /// self-adjoint Swing path used when D is held fixed during a collective target pullback.
    pub fn reflect_joint_section(
        &self,
        inputs: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<ResidentNormalEnclosureSection<'c>, Error> {
        let source = self.source;
        let surface = source.surface;
        let d = source.boundary_components();
        let count = source.births.len();
        let width = d.checked_add(2 * count).ok_or(Error::Shape)?;
        if inputs.rows() == 0
            || inputs.components() != width
            || inputs.grain() != self.output.grain()
            || !std::ptr::eq(inputs.resident_section().surface(), surface)
        {
            return Err(Error::Shape);
        }
        let factor = self.source.reflection.get().ok_or(Error::Uncertain)?;
        let output = surface.fresh_section(inputs.rows(), 2 * (width + 1), ResidentGrain(0))?;
        let flags = surface.fresh_section(inputs.rows(), SLOT_WORDS / 2, ResidentGrain(0))?;
        let work = surface.fresh_section(
            inputs.rows(),
            d.checked_mul(3)
                .and_then(|v| v.checked_add(count)?.checked_add(d / 2)?.checked_mul(2))
                .ok_or(Error::Shape)?,
            ResidentGrain(0),
        )?;
        let dots = surface.fresh_section(
            inputs
                .rows()
                .checked_mul(count.max(1))
                .ok_or(Error::Shape)?,
            10,
            ResidentGrain(0),
        )?;
        let mut p = surface
            .begin_passage(&[vec![]])
            .map_err(|e| Error::Arithmetic(e.to_string()))?;
        {
            let lane = p
                .open(0, &[])
                .map_err(|e| Error::Arithmetic(e.to_string()))?;
            surface
                .record_field_source_reflection_joint_section(
                    &lane,
                    &source._producing.map,
                    &source._producing.bounds,
                    factor,
                    inputs.resident_section(),
                    d,
                    count,
                    source.grain,
                    &work,
                    &dots,
                    &output,
                    &flags,
                )
                .map_err(|e| Error::Arithmetic(e.to_string()))?;
        }
        p.close(0, &output, 64)
            .map_err(|e| Error::Arithmetic(e.to_string()))?;
        let receipt = p
            .finish()
            .map_err(|e| Error::Arithmetic(e.to_string()))?
            .launch()
            .map_err(|e| Error::Arithmetic(e.to_string()))?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "fixed-D joint reflection: {:?}",
                receipt.obstruction
            )));
        }
        ResidentNormalEnclosureSection::from_resident(
            surface,
            output,
            inputs.rows(),
            width,
            inputs.grain(),
        )
        .map_err(|_| Error::Shape)
    }
}

/// Application of an immutable operative material to a declared joint (u,b)
/// input. The whole source and signed residual remain behind the output ball.
pub struct NativeFieldReflection<'a, 'c> {
    source: &'a NativeFieldCurrentSource<'c>,
    input: ResidentNormalEnclosureView<'a, 'c>,
    pub(super) output: Rc<ResidentSection<'c>>,
    residual: ResidentSection<'c>,
}
impl<'a, 'c> NativeFieldReflection<'a, 'c> {
    pub fn source(&self) -> &NativeFieldCurrentSource<'c> {
        self.source
    }
    pub(crate) fn residual_section(&self) -> &ResidentSection<'c> {
        &self.residual
    }
    pub fn input(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.input
    }
    pub fn output(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.source.surface,
            section: &self.output,
            offset: 0,
            width: self.source.width,
            grain: ResidentGrain(self.source.grain),
        }
    }
    pub fn inspect_residual(&self) -> Result<Vec<ExactComplexWaveCurrent>, Error> {
        let words = self.source.surface.read_out(&self.residual)?;
        super::super::decode_reflection_residual(
            &words,
            self.source.boundary_components(),
            self.source.grain,
        )
    }
}
impl<'c> NativeFieldCurrentSource<'c> {
    /// Compile the actual material once and apply its complete reflection to
    /// each supplied bounded current. No field occurrence or material is changed.
    pub fn reflect<'a>(
        &'a self,
        input: ResidentNormalEnclosureView<'a, 'c>,
    ) -> Result<NativeFieldReflection<'a, 'c>, Error> {
        if input.components() != self.width || input.grain() != ResidentGrain(self.grain) {
            return Err(Error::Shape);
        }
        let s = self.surface;
        let d = self.boundary_components();
        let k = self.births.len();
        let covariance = self
            ._producing
            .ensure_covariance(s, d, k, self.grain)?;
        if self.reflection.get().is_none() {
            let words = d
                .checked_mul(d)
                .and_then(|v| v.checked_add(d)?.checked_mul(2))
                .ok_or(Error::Shape)?;
            let factor = s.fresh_section(1, words, ResidentGrain(0))?;
            let mut p = s.begin_passage(&[vec![]])?;
            {
                let lane = p.open(0, &[])?;
                s.record_field_source_factor(
                    &lane,
                    covariance,
                    d,
                    self.grain,
                    &factor,
                )?;
            }
            p.close(0, &factor, 64)?;
            let r = p.finish()?.launch()?;
            if !r.obstruction.is_empty() {
                return Err(Error::Arithmetic(format!(
                    "operative source factor: {:?}",
                    r.obstruction
                )));
            }
            self.reflection.set(factor).map_err(|_| Error::Uncertain)?;
        }
        let output = s.fresh_section(1, 2 * (self.width + 1), ResidentGrain(0))?;
        let residual =
            s.fresh_section(1, d.checked_mul(18).ok_or(Error::Shape)?, ResidentGrain(0))?;
        let ww = d
            .checked_mul(3)
            .and_then(|v| v.checked_add(k)?.checked_add(d / 2)?.checked_mul(2))
            .ok_or(Error::Shape)?;
        let work = s.fresh_section(1, ww, ResidentGrain(0))?;
        let dots = s.fresh_section(k.max(1), 10, ResidentGrain(0))?;
        let mut p = s.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            s.record_field_source_reflection(
                &lane,
                &self._producing.map,
                &self._producing.bounds,
                self.reflection.get().unwrap(),
                input,
                d,
                k,
                &work,
                &dots,
                &residual,
                &output,
            )?;
        }
        p.close(0, &output, 64)?;
        let r = p.finish()?.launch()?;
        if !r.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "operative source reflection: {:?}",
                r.obstruction
            )));
        }
        Ok(NativeFieldReflection {
            source: self,
            input,
            output: Rc::new(output),
            residual,
        })
    }

    /// Apply the same producing material/factor to every row of a resident boundary section.
    /// The shared internal branch is appended by the device kernel; no row-wise host launch or
    /// separate field owner is created. The returned rows retain the complete joint radius.
    pub fn reflect_section<'a>(
        &'a self,
        boundary_rows: &'a ResidentNormalEnclosureSection<'c>,
    ) -> Result<NativeFieldReflectionSection<'a, 'c>, Error> {
        let source_view = self.enclosure();
        let d = self.boundary_components();
        let count = self.births.len();
        if d == 0
            || boundary_rows.components() != d
            || boundary_rows.grain() != source_view.grain()
            || !std::ptr::eq(
                source_view.surface(),
                boundary_rows.resident_section().surface(),
            )
        {
            return Err(Error::Shape);
        }
        let factor = if let Some(factor) = self.reflection.get() {
            factor
        } else {
            let covariance = self
                ._producing
                .ensure_covariance(self.surface, d, count, self.grain)?;
            let words = d
                .checked_mul(d)
                .and_then(|v| v.checked_add(d)?.checked_mul(2))
                .ok_or(Error::Shape)?;
            let factor = self.surface.fresh_section(1, words, ResidentGrain(0))?;
            let mut p = self.surface.begin_passage(&[vec![]])?;
            {
                let lane = p.open(0, &[])?;
                self.surface.record_field_source_factor(
                    &lane,
                    covariance,
                    d,
                    self.grain,
                    &factor,
                )?;
            }
            p.close(0, &factor, 64)?;
            let r = p.finish()?.launch()?;
            if !r.obstruction.is_empty() {
                return Err(Error::Arithmetic(format!(
                    "operative source factor: {:?}",
                    r.obstruction
                )));
            }
            self.reflection.set(factor).map_err(|_| Error::Uncertain)?;
            self.reflection.get().ok_or(Error::Uncertain)?
        };
        let out_width = d.checked_add(2 * count).ok_or(Error::Shape)?;
        let output = self.surface.fresh_section(
            boundary_rows.rows(),
            2 * (out_width + 1),
            ResidentGrain(0),
        )?;
        let flags =
            self.surface
                .fresh_section(boundary_rows.rows(), SLOT_WORDS / 2, ResidentGrain(0))?;
        let joint_input = self.surface.fresh_section(
            boundary_rows.rows(),
            2 * (out_width + 1),
            ResidentGrain(0),
        )?;
        let trace = self
            .surface
            .fresh_section(boundary_rows.rows(), 18 * d, ResidentGrain(0))?;
        let work = self.surface.fresh_section(
            boundary_rows.rows(),
            d.checked_mul(3)
                .and_then(|v| v.checked_add(count)?.checked_add(d / 2)?.checked_mul(2))
                .ok_or(Error::Shape)?,
            ResidentGrain(0),
        )?;
        let dots = self.surface.fresh_section(
            boundary_rows
                .rows()
                .checked_mul(count.max(1))
                .ok_or(Error::Shape)?,
            10,
            ResidentGrain(0),
        )?;
        let mut p = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            self.surface.record_field_source_reflection_section(
                &lane,
                &self._producing.map,
                &self._producing.bounds,
                factor,
                boundary_rows,
                source_view,
                d,
                count,
                &work,
                &dots,
                &trace,
                &joint_input,
                &output,
                &flags,
            )?;
        }
        p.close(0, &output, 64)?;
        let r = p.finish()?.launch()?;
        if !r.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "operative source reflection section: {:?}",
                r.obstruction
            )));
        }
        Ok(NativeFieldReflectionSection {
            source: self,
            input: boundary_rows,
            joint_input: ResidentNormalEnclosureSection::from_resident(
                self.surface,
                joint_input,
                boundary_rows.rows(),
                out_width,
                source_view.grain(),
            )
            .map_err(|_| Error::Shape)?,
            output: ResidentNormalEnclosureSection::from_resident(
                self.surface,
                output,
                boundary_rows.rows(),
                out_width,
                source_view.grain(),
            )
            .map_err(|_| Error::Shape)?,
            trace,
        })
    }
}
