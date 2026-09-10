use super::*;

pub struct NormalRealizationRefinement<'c> {
    surface: &'c ResidentSurface<'c>,
    before: Rc<ResidentSection<'c>>,
    after: Rc<ResidentSection<'c>>,
    roots: usize,
    targets: usize,
    pub before_grain: ResidentGrain,
    pub after_grain: ResidentGrain,
    pub observations: u64,
}
impl NormalRealizationRefinement<'_> {
    pub fn inspect_before(&self) -> Result<NativeNormalMaterialState, ConstitutiveFibreError> {
        decode_state(
            &self.surface.detach_section(&self.before, 64)?,
            self.roots,
            self.targets,
            self.before_grain.0,
        )
    }
    pub fn inspect_after(&self) -> Result<NativeNormalMaterialState, ConstitutiveFibreError> {
        decode_state(
            &self.surface.detach_section(&self.after, 64)?,
            self.roots,
            self.targets,
            self.after_grain.0,
        )
    }
}
impl<'c> ResidentNormalMaterial<'c> {
    pub fn refine_realization(
        &mut self,
        grain: ResidentGrain,
    ) -> Result<NormalRealizationRefinement<'c>, ConstitutiveFibreError> {
        if grain.0 <= self.grain.0 || grain.0 > 120 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let layout =
            NormalLayout::new(self.roots, self.targets).ok_or(ConstitutiveFibreError::Shape)?;
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
                self.roots,
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
        let next = Rc::new(next);
        let before = std::mem::replace(&mut self.state, Rc::clone(&next));
        let before_grain = std::mem::replace(&mut self.grain, grain);
        Ok(NormalRealizationRefinement {
            surface: self.surface,
            before,
            after: next,
            roots: self.roots,
            targets: self.targets,
            before_grain,
            after_grain: grain,
            observations: self.observations,
        })
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
        let after = returned.inspect_after().unwrap();
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
