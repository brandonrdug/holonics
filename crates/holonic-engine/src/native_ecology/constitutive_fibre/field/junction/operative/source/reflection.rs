use super::*;

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
                    &self._producing.covariance,
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
}
