//! Publish the already evaluated operative current through the same field owner.
use super::*;

impl<'c> NativeConstitutiveField<'c> {
    /// Install one source-qualified reflection. The material is unchanged; the internal-current
    /// delta enters the existing operative journal so historical source decoding and rest retain
    /// the actual transition. This does not fabricate an external observed occurrence.
    pub fn commit_reflection(
        &mut self,
        reflected: &NativeFieldReflection<'_, 'c>,
    ) -> Result<(), Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        let source = reflected.source();
        let junction = self.junction.as_ref().ok_or(Error::Shape)?;
        let op = junction.operative.as_ref().ok_or(Error::Shape)?;
        if !Rc::ptr_eq(&source.owner, &self.owner)
            || source.cut != self.history.len()
            || source.births != op.births
            || !Rc::ptr_eq(&source._producing, &op.sections)
            || !Rc::ptr_eq(&source.report, &junction.current)
        {
            return Err(Error::ForeignOccurrence);
        }
        let surface = self.relation.surface;
        let d = source.boundary_components();
        let k = source.births.len();
        let ports = Rc::new(surface.fresh_section(2, 2 * d, ResidentGrain(0))?);
        // An exact zero material increment has no contact factors. The current delta remains.
        let currents = Rc::new(surface.fresh_section(2, 4, ResidentGrain(0))?);
        let delta_b = Rc::new(surface.fresh_section(k.max(1), 4, ResidentGrain(0))?);
        let delta_bounds = Rc::new(surface.fresh_section(1, 4, ResidentGrain(0))?);
        let mut pass = surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            surface.record_field_reflection_current_delta(
                &lane,
                &op.sections.b,
                &op.sections.bounds,
                reflected.output(),
                d,
                k,
                [&ports, &currents, &delta_b, &delta_bounds],
            )?;
        }
        pass.close(0, &delta_bounds, 64)?;
        let completion = pass.finish()?.launch()?;
        if !completion.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "reflection current delta: {:?}",
                completion.obstruction
            )));
        }
        let returned = Rc::new(OperativeReturn {
            at_cut: self.history.len(),
            contact_count: k,
            factor_count: 0,
            realization: NativeContactRealization::EnclosedFlow,
            origin: Rc::clone(&op.origin),
            ports,
            currents: Rc::clone(&currents),
            current_difference_source: None,
            source_overlap: None,
            b: Some(delta_b),
            bounds: delta_bounds,
        });
        let report = Rc::new(surface.fresh_section(1, 12 * (d + 1), ResidentGrain(0))?);
        let (sections, origin, returns, program) = {
            let view = self.stage_operative_contacts()?;
            let staged =
                view.stage_return_using_image(returned, &currents, Some(reflected.output()))?;
            let mut pass = surface.begin_passage(&[vec![]])?;
            {
                let lane = pass.open(0, &[])?;
                surface.record_field_reflection_report(
                    &lane,
                    reflected.input(),
                    reflected.output(),
                    source.outgoing_report(),
                    &staged.sections.aggregate,
                    &staged.sections.moment_bounds,
                    reflected.residual_section(),
                    d,
                    k,
                    source.grain,
                    &report,
                )?;
            }
            pass.close(0, &report, 64)?;
            let completion = pass.finish()?.launch()?;
            if !completion.obstruction.is_empty() {
                return Err(Error::Arithmetic(format!(
                    "reflection report: {:?}",
                    completion.obstruction
                )));
            }
            (
                staged.sections,
                staged.origin,
                staged.returns,
                staged.program,
            )
        };
        // Every fallible operation precedes this publication. Old source handles retain their
        // original immutable report/material, and fail the freshness test on a second commit.
        let junction = self.junction.as_mut().unwrap();
        let op = junction.operative.as_mut().unwrap();
        op.sections = sections;
        op.origin = origin;
        op.returns = returns;
        op.program = program;
        junction.joint_current = Some((
            Rc::clone(&report),
            Rc::clone(&op.sections.b),
            Rc::clone(&reflected.output),
        ));
        junction.current = report;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;

    fn field<'c>(surface: &'c ResidentSurface<'c>) -> NativeConstitutiveField<'c> {
        let seed = NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        let mut f = NativeConstitutiveField::found_with_enclosed_junction(
            surface,
            vec![seed],
            ResidentGrain(48),
        )
        .unwrap();
        let first = f
            .advance_resident(&mut NativeFieldOccurrence::entering(vec![
                NativePhaseCurrent::new(1, 0, 1).unwrap(),
            ]))
            .unwrap();
        f.advance_resident(&mut NativeFieldOccurrence::through(
            first.source,
            vec![NativePhaseCurrent::new(0, 1, 1).unwrap()],
        ))
        .unwrap();
        f.enable_operative_contacts().unwrap();
        f
    }

    #[test]
    #[ignore = "requires CUDA; actual reflected current, single publication and native field rest"]
    fn committed_reflection_is_the_next_field_and_reopens() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let mut field = field(&surface);
        let source = field.read_current_source().unwrap();
        let input = source.enclosure().to_owned().unwrap();
        let reflection = source.reflect(input.view()).unwrap();
        let expected = reflection.output().inspect().unwrap();
        let before = field.census().section_read_outs;
        field.commit_reflection(&reflection).unwrap();
        assert_eq!(field.census().section_read_outs, before);
        let current = field.read_current_source().unwrap();
        let actual = current.enclosure().inspect().unwrap();
        assert_eq!(actual.center, expected.center);
        assert_eq!(actual, expected);
        assert!(matches!(
            field.commit_reflection(&reflection),
            Err(Error::ForeignOccurrence)
        ));
        // Changing D through the producing adjoint leaves q untouched, including its
        // common radius. This must not silently fall back to adding marginal radii.
        let target = source
            .enclosure()
            .restrict(0..source.boundary_components())
            .unwrap();
        let update = reflection.compare_target(target.view(), 3).unwrap();
        field
            .apply_reflection_target(&update, NativeContactRealization::DyadicDeposit)
            .unwrap();
        assert_eq!(
            field
                .read_current_source()
                .unwrap()
                .enclosure()
                .inspect()
                .unwrap(),
            actual
        );
        let rest = field.rest(&[], &[]).unwrap();
        let mut bytes = Vec::new();
        rest.write(&mut bytes).unwrap();
        drop(field);
        let rest = NativeFieldRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
        let (mut resumed, _, _) = NativeConstitutiveField::remount(&surface, rest).unwrap();
        assert_eq!(
            resumed
                .read_current_source()
                .unwrap()
                .enclosure()
                .inspect()
                .unwrap(),
            actual
        );
        resumed
            .advance_resident(&mut NativeFieldOccurrence::entering(vec![
                NativePhaseCurrent::new(2, 1, 1).unwrap(),
            ]))
            .unwrap();
        assert!(resumed
            .junction
            .as_ref()
            .unwrap()
            .valid_joint_current()
            .is_none());
        assert_ne!(
            resumed
                .read_current_source()
                .unwrap()
                .enclosure()
                .inspect()
                .unwrap()
                .center,
            actual.center
        );
    }
}
