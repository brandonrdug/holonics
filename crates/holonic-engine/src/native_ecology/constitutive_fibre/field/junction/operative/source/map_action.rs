//! Sparse declared-incidence and resident low-rank D action ownership.
use super::*;

/// Resident CSR incidence plus low-rank correction for one declared global D operator.
///
/// `D0` is contact-major CSR: `row_offsets` has `k+1` exact integer entries, `columns` has
/// `nnz` exact integer boundary addresses, and `values` has one complex coefficient per entry.
/// `left[p]` and `right[p]` are the two complex factors of the retained low-rank correction.
pub struct NativeFieldDeclaredIncidence<'c> {
    pub row_offsets: ResidentSection<'c>,
    pub columns: ResidentSection<'c>,
    pub values: ResidentSection<'c>,
    pub transpose_offsets: ResidentSection<'c>,
    pub transpose_rows: ResidentSection<'c>,
    pub transpose_values: ResidentSection<'c>,
    pub left: ResidentSection<'c>,
    pub right: ResidentSection<'c>,
    pub defects: ResidentSection<'c>,
    pub rows: usize,
    pub boundary_components: usize,
    pub rank: usize,
    pub nonzeros: usize,
}

pub struct NativeFieldFactorAction<'a, 'c> {
    source: &'a NativeFieldCurrentSource<'c>,
    input: ResidentNormalEnclosureView<'a, 'c>,
    output: Rc<ResidentSection<'c>>,
    residual: Rc<ResidentSection<'c>>,
    layout: NativeFieldJointLayout,
    steps: usize,
    omega_bits: u32,
    solve_method: u32,
}

fn valid(
    surface: &ResidentSurface<'_>,
    section: &ResidentSection<'_>,
    rows: usize,
    width: usize,
) -> bool {
    section.rows() == rows
        && section.width() == width
        && section.grain() == ResidentGrain(0)
        && std::ptr::eq(section.surface(), surface)
}

impl<'c> NativeConstitutiveField<'c> {
    /// Admit CSR D0 and resident low-rank factors without allocating a k*d contact matrix.
    pub fn register_declared_incidence(
        &mut self,
        incidence: NativeFieldDeclaredIncidence<'c>,
        b: ResidentSection<'c>,
        bounds: ResidentSection<'c>,
        origins: Vec<NativeFieldContactOrigin>,
    ) -> Result<(), Error> {
        if !self.relation.usable || self.pending.is_some() || incidence.rows == 0 {
            return Err(Error::Uncertain);
        }
        let junction = self.junction.as_ref().ok_or(Error::Shape)?;
        if junction.operative.is_some() {
            return Err(Error::ForeignOccurrence);
        }
        let d = self.nodes().checked_mul(6).ok_or(Error::Shape)?;
        let surface = self.relation.surface;
        if incidence.boundary_components != d
            || origins.len() != incidence.rows
            || origins
                .iter()
                .enumerate()
                .any(|(column, origin)| !origin.is_declared() || origin.column() != column)
            || !valid(surface, &incidence.row_offsets, 1, 2 * (incidence.rows + 1))
            || !valid(
                surface,
                &incidence.columns,
                1,
                2 * incidence.nonzeros.max(1),
            )
            || !valid(surface, &incidence.values, 1, 4 * incidence.nonzeros.max(1))
            || !valid(surface, &incidence.transpose_offsets, 1, 2 * (d / 2 + 1))
            || !valid(
                surface,
                &incidence.transpose_rows,
                1,
                2 * incidence.nonzeros.max(1),
            )
            || !valid(
                surface,
                &incidence.transpose_values,
                1,
                4 * incidence.nonzeros.max(1),
            )
            || !valid(surface, &incidence.left, incidence.rank.max(1), 2 * d)
            || !valid(
                surface,
                &incidence.right,
                incidence.rank.max(1),
                4 * incidence.rows,
            )
            || !valid(surface, &incidence.defects, incidence.rank.max(1), 2)
            || !valid(surface, &b, incidence.rows, 4)
            || !valid(surface, &bounds, 1, 4)
        {
            return Err(Error::Shape);
        }
        let grain = match self.junction_representation() {
            Some(NativeFieldJunctionRepresentation::EnclosedDyadic { fractional_bits }) => {
                fractional_bits
            }
            _ => return Err(Error::Shape),
        };
        // The legacy map slot is a one-row placeholder. Factor action owns the actual CSR/low-rank
        // operator; no k*d dense map is allocated or populated.
        let mut sections = factored_sections(surface, d, incidence.rows)?;
        let staged = Rc::get_mut(&mut sections).ok_or(Error::Uncertain)?;
        staged.b = Rc::new(b);
        staged.bounds = Rc::new(bounds);
        staged.factor_program = Some(Rc::new(OperativeFactorProgram {
            row_offsets: Rc::new(incidence.row_offsets),
            columns: Rc::new(incidence.columns),
            values: Rc::new(incidence.values),
            transpose_offsets: Rc::new(incidence.transpose_offsets),
            transpose_rows: Rc::new(incidence.transpose_rows),
            transpose_values: Rc::new(incidence.transpose_values),
            left: Rc::new(incidence.left),
            right: Rc::new(incidence.right),
            defects: Rc::new(incidence.defects),
            rows: incidence.rows,
            boundary_components: d,
            rank: incidence.rank,
            nonzeros: incidence.nonzeros,
        }));
        // Admission is transactional: compute D b, the operator norm and the complete
        // aggregate radius before making this source visible to any action consumer.
        sections.refresh_factor_aggregate(surface, grain)?;
        let births = origins
            .iter()
            .map(|origin| NativeOperativeContactBirth {
                source: origin.source(),
                receiving: origin.receiving(),
            })
            .collect();
        self.junction.as_mut().ok_or(Error::Shape)?.operative = Some(OperativeState {
            recent_producers: Default::default(),
            recent_propagations: Default::default(),
            propagate_from: None,
            sections: Rc::clone(&sections),
            initial: sections,
            activated_at: self.history.len(),
            grain,
            births,
            declared_origins: origins,
            origin: Rc::new(()),
            returns: Vec::new(),
            program: None,
        });
        self.junction.as_mut().unwrap().solver = NativeFieldJunctionSolver::Full;
        Ok(())
    }
}

impl<'c> NativeFieldCurrentSource<'c> {
    pub fn factor_action_matrix_free_auto<'a>(
        &'a self,
        input: ResidentNormalEnclosureView<'a, 'c>,
        steps: usize,
        omega_bits: u32,
    ) -> Result<NativeFieldFactorAction<'a, 'c>, Error> {
        self._producing
            .factor_program
            .as_ref()
            .ok_or(Error::Shape)?;
        if input.components() != self.width
            || input.grain() != ResidentGrain(self.grain)
            || steps == 0
            || (omega_bits > 120 && omega_bits != u32::MAX)
        {
            return Err(Error::Shape);
        }
        let d = self.boundary_components();
        let count = self.births.len();
        let (output, residual) = Self::prepare_factor_sections(self, input, steps, omega_bits, 0)?;
        Ok(NativeFieldFactorAction {
            source: self,
            input,
            output,
            residual,
            layout: NativeFieldJointLayout {
                boundary_components: d,
                internal_components: 2 * count,
                joint_components: self.width,
                contact_count: count,
                field_cut: self.cut,
                grain: self.grain,
            },
            steps,
            omega_bits,
            solve_method: 0,
        })
    }

    pub(super) fn prepare_factor_sections<'a, 'v>(
        source: &'a NativeFieldCurrentSource<'c>,
        input: ResidentNormalEnclosureView<'v, 'c>,
        steps: usize,
        omega_bits: u32,
        solve_method: u32,
    ) -> Result<(Rc<ResidentSection<'c>>, Rc<ResidentSection<'c>>), Error> {
        let program = source
            ._producing
            .factor_program
            .as_ref()
            .ok_or(Error::Shape)?;
        let d = source.boundary_components();
        let count = source.births.len();
        let output = Rc::new(source.surface.fresh_section(
            1,
            2 * (source.width + 1),
            ResidentGrain(0),
        )?);
        let residual = Rc::new(
            source
                .surface
                .fresh_section(1, 2 * (d + 1), ResidentGrain(0))?,
        );
        let work = source.surface.fresh_section(
            1,
            2 * (5 * d + 4 * count + 3 * program.rank + 1),
            ResidentGrain(0),
        )?;
        let mut passage = source.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            source.surface.record_field_factor_action(
                &lane,
                &program.row_offsets,
                &program.columns,
                &program.values,
                &program.transpose_offsets,
                &program.transpose_rows,
                &program.transpose_values,
                &program.left,
                &program.right,
                &program.defects,
                &source._producing.moment_bounds,
                &source._producing.bounds,
                input,
                d,
                count,
                program.nonzeros,
                program.rank,
                source.grain,
                steps,
                omega_bits,
                solve_method,
                &work,
                &output,
                &residual,
            )?;
        }
        passage.close(0, &output, 64)?;
        let completion = passage.finish()?.launch()?;
        if !completion.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "factor action: {:?}",
                completion.obstruction
            )));
        }
        Ok((output, residual))
    }
}

impl<'a, 'c> NativeFieldFactorAction<'a, 'c> {
    pub(super) fn from_sections(
        source: &'a NativeFieldCurrentSource<'c>,
        input: ResidentNormalEnclosureView<'a, 'c>,
        output: Rc<ResidentSection<'c>>,
        residual: Rc<ResidentSection<'c>>,
        steps: usize,
        omega_bits: u32,
        solve_method: u32,
    ) -> Self {
        let d = source.boundary_components();
        Self {
            source,
            input,
            output,
            residual,
            layout: NativeFieldJointLayout {
                boundary_components: d,
                internal_components: source.internal_components(),
                joint_components: source.width,
                contact_count: source.births.len(),
                field_cut: source.cut,
                grain: source.grain,
            },
            steps,
            omega_bits,
            solve_method,
        }
    }
    pub fn pullback_full_auto(
        &self,
        covector: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<NativeFieldActionPullback<'a, 'c>, Error> {
        if covector.components() != self.layout.joint_components
            || covector.grain() != ResidentGrain(self.layout.grain)
        {
            return Err(Error::Shape);
        }
        let program = self
            .source
            ._producing
            .factor_program
            .as_ref()
            .ok_or(Error::Shape)?;
        let (incoming, incoming_residual) = NativeFieldCurrentSource::prepare_factor_sections(
            self.source,
            covector,
            self.steps,
            self.omega_bits,
            self.solve_method,
        )?;
        let d = self.layout.boundary_components;
        let count = self.layout.contact_count;
        let ports = Rc::new(
            self.source
                .surface
                .fresh_section(2, 2 * d, ResidentGrain(0))?,
        );
        let currents = Rc::new(self.source.surface.fresh_section(
            2,
            4 * count.max(1),
            ResidentGrain(0),
        )?);
        let bounds = Rc::new(self.source.surface.fresh_section(1, 4, ResidentGrain(0))?);
        let work = self.source.surface.fresh_section(
            1,
            2 * (2 * d + 4 * count + 2 * program.rank),
            ResidentGrain(0),
        )?;
        let mut passage = self.source.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.source.surface.record_field_factor_pullback(
                &lane,
                &program.row_offsets,
                &program.columns,
                &program.values,
                &program.transpose_offsets,
                &program.transpose_rows,
                &program.transpose_values,
                &program.left,
                &program.right,
                self.input,
                self.output(),
                covector,
                &incoming,
                d,
                count,
                program.nonzeros,
                program.rank,
                self.layout.grain,
                &work,
                &ports,
                &currents,
                &bounds,
            )?;
        }
        passage.close(0, &bounds, 64)?;
        let completion = passage.finish()?.launch()?;
        if !completion.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "factor pullback: {:?}",
                completion.obstruction
            )));
        }
        Ok(NativeFieldActionPullback::from_factor(
            self.source,
            incoming,
            ports,
            currents,
            bounds,
            incoming_residual,
            self.layout,
        ))
    }
    pub fn output(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.source.surface,
            section: &self.output,
            offset: 0,
            width: self.layout.joint_components,
            grain: ResidentGrain(self.layout.grain),
        }
    }
    pub fn input(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.input
    }
    pub fn source(&self) -> &NativeFieldCurrentSource<'c> {
        self.source
    }
    pub fn residual(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.source.surface,
            section: &self.residual,
            offset: 0,
            width: self.layout.boundary_components,
            grain: ResidentGrain(self.layout.grain),
        }
    }
    pub fn steps(&self) -> usize {
        self.steps
    }
    pub fn omega_bits(&self) -> u32 {
        self.omega_bits
    }
}
