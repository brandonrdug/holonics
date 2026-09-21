//! Publish the already evaluated operative current through the same field owner.
use super::*;

/// A completely staged publication of one full joint endpoint.  All resident allocations,
/// current-delta arithmetic and the report are finished before this value can be committed.
/// Consuming it is infallible and therefore cannot leave a half-published `(q,b)` state.
pub struct NativeFieldJointCurrentCommit<'c> {
    owner: Rc<()>,
    cut: usize,
    births: Vec<NativeOperativeContactBirth>,
    producing: Rc<OperativeSections<'c>>,
    sections: Rc<OperativeSections<'c>>,
    origin: Rc<()>,
    returns: Vec<Rc<OperativeReturn<'c>>>,
    program: Option<OperativeMapProgram<'c>>,
    report: Rc<ResidentSection<'c>>,
    output: Rc<ResidentSection<'c>>,
    width: usize,
    grain: u32,
}

impl<'c> NativeFieldJointCurrentCommit<'c> {
    pub fn cut(&self) -> usize {
        self.cut
    }
    pub fn width(&self) -> usize {
        self.width
    }
    pub fn grain(&self) -> ResidentGrain {
        ResidentGrain(self.grain)
    }
}

impl<'c> NativeConstitutiveField<'c> {
    /// Matrix-free endpoint publication with its actual resident Richardson residual trace.
    pub fn prepare_joint_current_commit_from_action<'a>(
        &mut self,
        action: &NativeFieldMatrixFreeAction<'a, 'c>,
        final_full_output: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<NativeFieldJointCurrentCommit<'c>, Error> {
        let trace = action.residual_trace()?;
        self.prepare_joint_current_commit_from_source(
            action.source(),
            action.input(),
            final_full_output,
            Some(trace),
        )
    }

    /// Stage a full endpoint from any source-owned action, including the matrix-free action. The
    /// residual trace must certify this action; the matrix-free adapter converts its resident
    /// residual packet. Publication performs all current/report work before commit.
    pub fn prepare_joint_current_commit_from_source(
        &mut self,
        source: &NativeFieldCurrentSource<'c>,
        input: ResidentNormalEnclosureView<'_, 'c>,
        final_full_output: ResidentNormalEnclosureView<'_, 'c>,
        residual_trace: Option<&ResidentSection<'c>>,
    ) -> Result<NativeFieldJointCurrentCommit<'c>, Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        let junction = self.junction.as_ref().ok_or(Error::Shape)?;
        let op = junction.operative.as_ref().ok_or(Error::Shape)?;
        if !Rc::ptr_eq(&source.owner, &self.owner)
            || source.cut != self.history.len()
            || source.births != op.births
            || !Rc::ptr_eq(&source._producing, &op.sections)
            || !Rc::ptr_eq(&source.report, &junction.current)
            || input.components() != source.width
            || final_full_output.components() != source.width
            || input.grain() != ResidentGrain(source.grain)
            || final_full_output.grain() != ResidentGrain(source.grain)
            || !std::ptr::eq(input.surface(), self.relation.surface)
            || !std::ptr::eq(final_full_output.surface(), self.relation.surface)
        {
            return Err(Error::ForeignOccurrence);
        }
        let surface = self.relation.surface;
        let output = Rc::new(surface.fresh_section(1, 2 * (source.width + 1), ResidentGrain(0))?);
        let mut copy_pass = surface.begin_passage(&[vec![]])?;
        {
            let lane = copy_pass.open(0, &[])?;
            surface.record_field_enclosure_copy(&lane, final_full_output, &output)?;
        }
        copy_pass.close(0, &output, 64)?;
        let copy_completion = copy_pass.finish()?.launch()?;
        if !copy_completion.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "joint endpoint copy: {:?}",
                copy_completion.obstruction
            )));
        }
        let final_view = ResidentNormalEnclosureView {
            surface,
            section: &output,
            offset: 0,
            width: source.width,
            grain: ResidentGrain(source.grain),
        };
        let d = source.boundary_components();
        let k = source.births.len();
        let ports = Rc::new(surface.fresh_section(2, 2 * d, ResidentGrain(0))?);
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
                final_view,
                d,
                k,
                [&ports, &currents, &delta_b, &delta_bounds],
            )?;
        }
        pass.close(0, &delta_bounds, 64)?;
        let completion = pass.finish()?.launch()?;
        if !completion.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "joint reflection current delta: {:?}",
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
        let trace = residual_trace.ok_or(Error::Uncertain)?;
        if trace.rows() != 1 || trace.width() != 18 * d {
            return Err(Error::Shape);
        }
        let (sections, origin, returns, program) = {
            let view = self.stage_operative_contacts()?;
            let staged = view.stage_return_using_image(returned, &currents, Some(final_view))?;
            let mut pass = surface.begin_passage(&[vec![]])?;
            {
                let lane = pass.open(0, &[])?;
                surface.record_field_reflection_report(
                    &lane,
                    input,
                    final_view,
                    source.outgoing_report(),
                    &staged.sections.aggregate,
                    &staged.sections.moment_bounds,
                    trace,
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
                    "joint reflection report: {:?}",
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
        Ok(NativeFieldJointCurrentCommit {
            owner: Rc::clone(&self.owner),
            cut: self.history.len(),
            births: source.births.clone(),
            producing: Rc::clone(&source._producing),
            sections,
            origin,
            returns,
            program,
            report,
            output,
            width: source.width,
            grain: source.grain,
        })
    }

    /// Stage a full relaxed endpoint for the source cut.  `final_full_output` is the complete
    /// resident `(q,b)` result of the caller's held relaxation, rather than a raw local reflection.
    /// It is copied into a source-owned resident packet during preparation so commit has no
    /// fallible device work left to perform.
    pub fn prepare_joint_current_commit(
        &mut self,
        reflected: &NativeFieldReflection<'_, 'c>,
        final_full_output: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<NativeFieldJointCurrentCommit<'c>, Error> {
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
            || final_full_output.components() != source.width
            || final_full_output.grain() != ResidentGrain(source.grain)
            || !std::ptr::eq(final_full_output.surface(), self.relation.surface)
        {
            return Err(Error::ForeignOccurrence);
        }

        let surface = self.relation.surface;
        // Reuse the producing output when the endpoint is that exact resident section.  A
        // relaxed caller may supply another section; that endpoint is copied into the source
        // owner before any staged arithmetic so publication remains infallible.
        let output = if std::ptr::eq(final_full_output.section(), reflected.output().section()) {
            Rc::clone(&reflected.output)
        } else {
            let copied = surface.fresh_section(1, 2 * (source.width + 1), ResidentGrain(0))?;
            let mut pass = surface.begin_passage(&[vec![]])?;
            {
                let lane = pass.open(0, &[])?;
                surface.record_field_enclosure_copy(&lane, final_full_output, &copied)?;
            }
            pass.close(0, &copied, 64)?;
            let completion = pass.finish()?.launch()?;
            if !completion.obstruction.is_empty() {
                return Err(Error::Arithmetic(format!(
                    "joint endpoint copy: {:?}",
                    completion.obstruction
                )));
            }
            Rc::new(copied)
        };
        let final_view = ResidentNormalEnclosureView {
            surface,
            section: &output,
            offset: 0,
            width: source.width,
            grain: ResidentGrain(source.grain),
        };
        let d = source.boundary_components();
        let k = source.births.len();
        let ports = Rc::new(surface.fresh_section(2, 2 * d, ResidentGrain(0))?);
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
                final_view,
                d,
                k,
                [&ports, &currents, &delta_b, &delta_bounds],
            )?;
        }
        pass.close(0, &delta_bounds, 64)?;
        let completion = pass.finish()?.launch()?;
        if !completion.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "joint reflection current delta: {:?}",
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
            let staged = view.stage_return_using_image(returned, &currents, Some(final_view))?;
            let mut pass = surface.begin_passage(&[vec![]])?;
            {
                let lane = pass.open(0, &[])?;
                surface.record_field_reflection_report(
                    &lane,
                    reflected.input(),
                    final_view,
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
                    "joint reflection report: {:?}",
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
        Ok(NativeFieldJointCurrentCommit {
            owner: Rc::clone(&self.owner),
            cut: self.history.len(),
            births: source.births.clone(),
            producing: Rc::clone(&source._producing),
            sections,
            origin,
            returns,
            program,
            report,
            output,
            width: source.width,
            grain: source.grain,
        })
    }

    /// Validate freshness and ownership without allocating or mutating the field.
    pub fn can_commit_joint_current(
        &self,
        prepared: &NativeFieldJointCurrentCommit<'c>,
    ) -> Result<(), Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        let junction = self.junction.as_ref().ok_or(Error::Shape)?;
        let op = junction.operative.as_ref().ok_or(Error::Shape)?;
        if !Rc::ptr_eq(&prepared.owner, &self.owner)
            || prepared.cut != self.history.len()
            || prepared.births != op.births
            || !Rc::ptr_eq(&prepared.producing, &op.sections)
            || prepared.width != 6 * self.nodes() + 2 * op.births.len()
            || prepared.grain != op.grain
        {
            return Err(Error::ForeignOccurrence);
        }
        Ok(())
    }

    /// Publish a previously checked endpoint.  This function has no fallible operations.
    pub fn commit_joint_current(
        &mut self,
        prepared: NativeFieldJointCurrentCommit<'c>,
    ) -> Result<(), Error> {
        self.can_commit_joint_current(&prepared)?;
        let junction = self.junction.as_mut().expect("validated junction");
        let op = junction
            .operative
            .as_mut()
            .expect("validated operative state");
        op.sections = prepared.sections;
        op.origin = prepared.origin;
        op.returns = prepared.returns;
        op.program = prepared.program;
        junction.joint_current = Some((
            Rc::clone(&prepared.report),
            Rc::clone(&op.sections.b),
            prepared.output,
        ));
        junction.current = prepared.report;
        Ok(())
    }

    /// Install one source-qualified reflection. The material is unchanged; the internal-current
    /// delta enters the existing operative journal so historical source decoding and rest retain
    /// the actual transition. This does not fabricate an external observed occurrence.
    pub fn commit_reflection(
        &mut self,
        reflected: &NativeFieldReflection<'_, 'c>,
    ) -> Result<(), Error> {
        let prepared = self.prepare_joint_current_commit(reflected, reflected.output())?;
        self.commit_joint_current(prepared)
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
        assert!(
            resumed
                .junction
                .as_ref()
                .unwrap()
                .valid_joint_current()
                .is_none()
        );
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
