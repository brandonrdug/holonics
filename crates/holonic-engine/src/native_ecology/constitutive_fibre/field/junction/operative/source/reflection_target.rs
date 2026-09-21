//! A real output target reaches the same paired source and its material through the existing adjoint.
use super::*;
use crate::native_ecology::constitutive_fibre::ResidentHeldSection;

#[cfg(test)]
mod tests;

pub struct NativeFieldReflectionTarget<'a, 'b, 'c> {
    reflection: &'a NativeFieldReflection<'b, 'c>,
    target: ResidentNormalEnclosureView<'a, 'c>,
    ports: Rc<ResidentSection<'c>>,
    currents: Rc<ResidentSection<'c>>,
    delta_bounds: Rc<ResidentSection<'c>>,
    _diagnostics: ResidentSection<'c>,
    incoming: ResidentSection<'c>,
    receiver: Option<&'a crate::native_ecology::constitutive_fibre::ResidentHeldSection<'c>>,
}
impl<'a, 'b, 'c> NativeFieldReflectionTarget<'a, 'b, 'c> {
    pub fn input_covector(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        let source = self.reflection.source();
        ResidentNormalEnclosureView {
            surface: source.surface,
            section: &self.incoming,
            offset: 0,
            width: source.width,
            grain: ResidentGrain(source.grain),
        }
    }
    pub fn target(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.target
    }
    pub fn receiver(&self) -> Option<&ResidentHeldSection<'c>> {
        self.receiver
    }
    pub fn material_covector(
        &self,
    ) -> Result<(PairedContactCotangent, relational_geometry::Rat), Error> {
        let source = self.reflection.source();
        let surface = source.surface;
        let ports = wides(&surface.read_out(&self.ports)?)?;
        let currents = wides(&surface.read_out(&self.currents)?)?;
        let bounds = wides(&surface.read_out(&self.delta_bounds)?)?;
        let scale = num_bigint::BigInt::from(1u8) << source.grain;
        let values = |v: &[i128]| {
            v.chunks_exact(2)
                .map(|p| {
                    ExactComplexWaveCurrent::new(
                        relational_geometry::Rat::new(p[0].into(), scale.clone()),
                        relational_geometry::Rat::new(p[1].into(), scale.clone()),
                    )
                })
                .collect()
        };
        let d = source.boundary_components();
        let k = source.births.len();
        Ok((
            PairedContactCotangent {
                port_factors: [values(&ports[..d]), values(&ports[d..2 * d])],
                contact_factors: [values(&currents[..2 * k]), values(&currents[2 * k..4 * k])],
            },
            relational_geometry::Rat::new(bounds[0].into(), scale),
        ))
    }
}
impl<'b, 'c> NativeFieldReflection<'b, 'c> {
    /// Descending cotangent of 2^-step_bits * ||output-target||²/2. A boundary-only target
    /// supplies zero interior covector. No point is selected from an enclosed source.
    pub fn compare_target<'a>(
        &'a self,
        target: ResidentNormalEnclosureView<'a, 'c>,
        step_bits: u32,
    ) -> Result<NativeFieldReflectionTarget<'a, 'b, 'c>, Error> {
        self.compare_target_with_receiver(target, step_bits, None)
    }

    pub fn compare_received_target<'a>(
        &'a self,
        target: ResidentNormalEnclosureView<'a, 'c>,
        step_bits: u32,
        receiver: &'a ResidentHeldSection<'c>,
    ) -> Result<NativeFieldReflectionTarget<'a, 'b, 'c>, Error> {
        let source = self.source();
        let d = source.boundary_components();
        let given = receiver.given();
        if !std::ptr::eq(given.surface, source.surface)
            || given.components() != d
            || target.components() == 0
            || given.grain() != ResidentGrain(source.grain)
            || (target.components() > d && target.components() != source.width)
            || target.components() % 2 != 0
        {
            return Err(Error::Shape);
        }
        self.compare_target_with_receiver(target, step_bits, Some(receiver))
    }

    fn compare_target_with_receiver<'a>(
        &'a self,
        target: ResidentNormalEnclosureView<'a, 'c>,
        step_bits: u32,
        receiver: Option<&'a ResidentHeldSection<'c>>,
    ) -> Result<NativeFieldReflectionTarget<'a, 'b, 'c>, Error> {
        let source = self.source();
        let surface = source.surface;
        let d = source.boundary_components();
        let k = source.births.len();
        let covariance = source
            ._producing
            .ensure_covariance(surface, d, k, source.grain)?;
        let n = d / 6;
        if d % 6 != 0 || target.grain() != ResidentGrain(source.grain) {
            return Err(Error::Shape);
        }
        let forward = surface.fresh_section(1, 12 * (d + 1), ResidentGrain(0))?;
        let after_b = surface.fresh_section(k.max(1), 4, ResidentGrain(0))?;
        let bounds = surface.fresh_section(1, 4, ResidentGrain(0))?;
        let query = surface.fresh_section(1, 4 * (10 * n + 2 * k), ResidentGrain(0))?;
        let ports = Rc::new(surface.fresh_section(2, 2 * d, ResidentGrain(0))?);
        let currents = Rc::new(surface.fresh_section(2, 4 * k.max(1), ResidentGrain(0))?);
        let delta_bounds = Rc::new(surface.fresh_section(1, 4, ResidentGrain(0))?);
        let diagnostics = surface.fresh_section(1, 2 * (2 * d + 4 * k + 8), ResidentGrain(0))?;
        let workspace =
            surface.fresh_section(1, 2 * (d * d + 3 * d + 4 * k + 2), ResidentGrain(0))?;
        let dots = surface.fresh_section(k.max(1), 10, ResidentGrain(0))?;
        let incoming = surface.fresh_section(1, 2 * (source.width + 1), ResidentGrain(0))?;
        let mut pass = surface.begin_passage(&[vec![], vec![0], vec![1]])?;
        {
            let lane = pass.open(0, &[])?;
            surface.record_field_reflection_target(
                &lane,
                self.input(),
                self.output(),
                target,
                &source._producing.bounds,
                receiver.map(|r| r.mask()),
                n,
                k,
                step_bits,
                [&forward, &after_b, &bounds, &query],
            )?;
        }
        pass.close(0, &query, 64)?;
        {
            let lane = pass.open(1, &[0])?;
            surface.record_operative_material_adjoint(
                &lane,
                [
                    &source._producing.map,
                    &after_b,
                    &bounds,
                    covariance,
                    &source._producing.covariance.get().ok_or(Error::Uncertain)?.bound,
                    &forward,
                    &query,
                ],
                n,
                k,
                source.grain,
                [&ports, &currents, &delta_bounds, &diagnostics],
                &workspace,
                &dots,
            )?;
        }
        pass.close(1, &diagnostics, 64)?;
        {
            let lane = pass.open(2, &[1])?;
            surface.record_field_reflection_input_cotangent(
                &lane,
                &diagnostics,
                d,
                k,
                &incoming,
            )?;
        }
        pass.close(2, &incoming, 64)?;
        let completion = pass.finish()?.launch()?;
        if !completion.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "reflection target: {:?}",
                completion.obstruction
            )));
        }
        Ok(NativeFieldReflectionTarget {
            reflection: self,
            target,
            ports,
            currents,
            delta_bounds,
            _diagnostics: diagnostics,
            incoming,
            receiver,
        })
    }
}

impl<'c> NativeConstitutiveField<'c> {
    /// Apply the source-derived contact response to the contemporary material. The public model
    /// consumes the originating target handle once; delayed gradients retain their producing D.
    pub fn apply_reflection_target(
        &mut self,
        returned: &NativeFieldReflectionTarget<'_, '_, 'c>,
        realization: NativeContactRealization,
    ) -> Result<(), Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        let source = returned.reflection.source();
        let op = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?;
        if !Rc::ptr_eq(&source.owner, &self.owner)
            || source.births != op.births
            || source.grain != op.grain
        {
            return Err(Error::ForeignOccurrence);
        }
        let update = Rc::new(OperativeReturn {
            at_cut: self.history.len(),
            contact_count: op.births.len(),
            factor_count: source.births.len(),
            realization,
            origin: Rc::clone(&op.origin),
            ports: Rc::clone(&returned.ports),
            currents: Rc::clone(&returned.currents),
            current_difference_source: None,
            source_overlap: None,
            b: None,
            bounds: Rc::clone(&returned.delta_bounds),
        });
        let (sections, origin, returns, program) = {
            let view = self.stage_operative_contacts()?;
            let staged = view.stage_return_using(update, &returned.currents)?;
            (
                staged.sections,
                staged.origin,
                staged.returns,
                staged.program,
            )
        };
        let op = self.junction.as_mut().unwrap().operative.as_mut().unwrap();
        op.sections = sections;
        op.origin = origin;
        op.returns = returns;
        op.program = program;
        Ok(())
    }
}
