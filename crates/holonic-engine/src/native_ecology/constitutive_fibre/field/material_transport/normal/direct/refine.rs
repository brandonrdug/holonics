use super::*;

impl<'c> ResidentNormalMaterial<'c> {
    /// Refine the numerical realization to a finer grain. The exact moments (the constitution's
    /// storage and source) are unchanged; only the applied coefficients' realization error
    /// shrinks. Returns the predecessor constitution: a shared cut of the section it replaced
    /// (its `inspect()` is the before-reading; `self.inspect()` the after-reading).
    pub fn refine_realization(
        &mut self,
        grain: ResidentGrain,
    ) -> Result<ResidentNormalMaterial<'c>, ConstitutiveFibreError> {
        if grain.0 <= self.grain.0 || grain.0 > 120 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let layout = self.source_chart.layout(self.targets)?;
        let next = self
            .surface
            .fresh_section(1, layout.state_words, ResidentGrain(0))?;
        let work = self
            .surface
            .fresh_section(1, layout.workspace_words, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_normal_refine(
                &lane,
                &self.state,
                self.source_complex(),
                self.targets,
                self.grain.0,
                grain.0,
                &next,
                &work,
            )?;
        }
        passage.close(0, &next, 64)?;
        let returned = passage.finish()?.launch()?;
        if !returned.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normal realization refinement: {:?}",
                returned.obstruction
            )));
        }
        let predecessor = self.clone();
        self.state = Rc::new(next);
        self.grain = grain;
        Ok(predecessor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;
    #[test]
    #[ignore = "requires CUDA; a finer realization preserves every exact moment and source-family bound, without replaying observations"]
    fn finer_realization_retains_source_geometry_and_reduces_only_numerical_error() {
        let readout = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&readout).unwrap();
        let point = |v: &[i64]| {
            s.mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    v.len(),
                    ResidentGrain(0),
                    64,
                    v.iter().map(|v| (*v, *v)).collect(),
                )
                .unwrap(),
            )
            .unwrap()
        };
        let x = point(&[1, 0, 0, 0, 0, 0, 3]);
        let y = point(&[1, 0]);
        let mut material = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(16)).unwrap();
        material
            .receive(
                ResidentConstitutiveCurrent::rational(&x).unwrap(),
                ResidentConstitutiveCurrent::integers(&y).unwrap(),
            )
            .unwrap();
        let before = material.inspect().unwrap();
        let reads = s.census().section_read_outs;
        let returned = material.refine_realization(ResidentGrain(32)).unwrap();
        assert_eq!(s.census().section_read_outs, reads);
        let after = material.inspect().unwrap();
        assert_eq!(returned.inspect().unwrap().source_normal, before.source_normal);
        assert_eq!((returned.grain(), material.grain()), (ResidentGrain(16), ResidentGrain(32)));
        assert_eq!(before.source_normal, after.source_normal);
        assert_eq!(before.cross_source, after.cross_source);
        assert_eq!(before.source_normal_error, after.source_normal_error);
        assert_eq!(before.cross_source_error, after.cross_source_error);
        assert_eq!(before.target_energy, after.target_energy);
        assert_eq!(before.target_energy_error, after.target_energy_error);
        assert!(after.normal_residual_upper < before.normal_residual_upper);
        assert_eq!(material.observations(), 1);
        material.rest().unwrap().validate().unwrap();
    }
}
