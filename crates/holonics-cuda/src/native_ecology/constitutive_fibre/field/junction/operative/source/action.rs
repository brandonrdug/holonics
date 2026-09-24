//! The source-owned action for one complete operative field state.
//!
//! `NativeFieldCurrentSource` is the owner of the producing cut.  This wrapper gives callers a
//! small, explicit packet for the global action
//!
//! ```text
//! A = I + D D*,  A v = 2(a + D b),  w = v - a,  b_ref = D* v - b
//! ```
//!
//! The arithmetic remains in the resident reflection path.  The wrapper deliberately carries
//! the layout and causal column origins alongside the output so a consumer cannot mistake a
//! batch of local rows for the one continuing `(q,b)` state.
use super::*;
mod contact_amplitude;
mod contact_scale;
pub use contact_amplitude::NativeDeclaredAmplitudeCommit;
pub use contact_scale::NativeDeclaredFactorScaleGradient;

/// Causal identity of one column of the producing D map. Observation-derived births and
/// caller-declared contacts remain different tagged origins even when their addresses match.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum NativeFieldContactOrigin {
    Observed {
        column: usize,
        source: usize,
        receiving: usize,
    },
    Declared {
        column: usize,
        source: usize,
        receiving: usize,
    },
}

impl NativeFieldContactOrigin {
    pub fn observed(column: usize, source: usize, receiving: usize) -> Self {
        Self::Observed {
            column,
            source,
            receiving,
        }
    }

    pub fn declared(column: usize, source: usize, receiving: usize) -> Self {
        Self::Declared {
            column,
            source,
            receiving,
        }
    }

    pub fn column(self) -> usize {
        match self {
            Self::Observed { column, .. } | Self::Declared { column, .. } => column,
        }
    }

    pub fn source(self) -> usize {
        match self {
            Self::Observed { source, .. } | Self::Declared { source, .. } => source,
        }
    }

    pub fn receiving(self) -> usize {
        match self {
            Self::Observed { receiving, .. } | Self::Declared { receiving, .. } => receiving,
        }
    }

    pub fn is_declared(self) -> bool {
        matches!(self, Self::Declared { .. })
    }
}

/// Dimensions of the resident joint chart.  Components count interleaved real/imaginary words.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
pub struct NativeFieldJointLayout {
    pub boundary_components: usize,
    pub internal_components: usize,
    pub joint_components: usize,
    pub contact_count: usize,
    pub field_cut: usize,
    pub grain: u32,
}

/// Which factor representation the action uses at this source cut.
///
/// The dense reference caches its device solve factor. Matrix-free variants execute D/D*
/// directly, either over explicit columns or a sparse incidence anchor with retained
/// outer-product factors. No host numerical matrix is formed by these actions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
pub enum NativeFieldActionFactorization {
    ResidentDenseReference { boundary_squared_components: usize },
    ResidentRichardsonMatrixFree { steps: usize, omega_bits: u32 },
    ResidentFactorProgramMatrixFree { steps: usize, omega_bits: u32 },
    ResidentFactorProgramChebyshevMatrixFree { steps: usize, omega_bits: u32 },
}

/// One source-qualified, residual-certified application of the global S_D action.
pub struct NativeFieldAction<'a, 'c> {
    source: &'a NativeFieldCurrentSource<'c>,
    reflection: NativeFieldReflection<'a, 'c>,
    layout: NativeFieldJointLayout,
    factorization: NativeFieldActionFactorization,
    origins: Vec<NativeFieldContactOrigin>,
}

/// Matrix-free resident action over the declared contact columns. Its workspace contains only
/// D/D* products and Richardson state; no boundary-square covariance is allocated.
pub struct NativeFieldMatrixFreeAction<'a, 'c> {
    source: &'a NativeFieldCurrentSource<'c>,
    input: ResidentNormalEnclosureView<'a, 'c>,
    output: Rc<ResidentSection<'c>>,
    residual: Rc<ResidentSection<'c>>,
    trace: std::cell::OnceCell<ResidentSection<'c>>,
    layout: NativeFieldJointLayout,
    factorization: NativeFieldActionFactorization,
    origins: Vec<NativeFieldContactOrigin>,
}

/// Full joint source pullback. `incoming` is the `(g_q,g_b)` covector at the source; `ports`
/// and `currents` retain the two outer-product terms of the D cotangent in resident sections.
pub struct NativeFieldActionPullback<'a, 'c> {
    source: &'a NativeFieldCurrentSource<'c>,
    incoming: Rc<ResidentSection<'c>>,
    ports: Rc<ResidentSection<'c>>,
    currents: Rc<ResidentSection<'c>>,
    delta_bounds: Rc<ResidentSection<'c>>,
    residual: Rc<ResidentSection<'c>>,
    layout: NativeFieldJointLayout,
}

/// One atomically staged contemporary D/material successor formed by summing several complete
/// joint pullbacks. The continuing q/b current is carried by the staged operative sections and is
/// not recommitted from an observation.
pub struct NativeFieldGlobalMaterialCommit<'c> {
    owner: Rc<()>,
    cut: usize,
    births: Vec<NativeOperativeContactBirth>,
    producing: Rc<OperativeSections<'c>>,
    sections: Rc<OperativeSections<'c>>,
    origin: Rc<()>,
    returns: Vec<Rc<OperativeReturn<'c>>>,
    program: Option<OperativeMapProgram<'c>>,
    grain: u32,
}

impl<'a, 'c> NativeFieldAction<'a, 'c> {
    pub(super) fn prepare(
        source: &'a NativeFieldCurrentSource<'c>,
        input: ResidentNormalEnclosureView<'a, 'c>,
    ) -> Result<Self, Error> {
        if input.components() != source.width || input.grain() != ResidentGrain(source.grain) {
            return Err(Error::Shape);
        }
        let reflection = source.reflect(input)?;
        let boundary_components = source.boundary_components();
        let internal_components = source.internal_components();
        let layout = NativeFieldJointLayout {
            boundary_components,
            internal_components,
            joint_components: boundary_components
                .checked_add(internal_components)
                .ok_or(Error::Shape)?,
            contact_count: source.births.len(),
            field_cut: source.field_cut(),
            grain: source.grain,
        };
        let factorization = NativeFieldActionFactorization::ResidentDenseReference {
            boundary_squared_components: boundary_components
                .checked_mul(boundary_components)
                .ok_or(Error::Shape)?,
        };
        Ok(Self {
            source,
            reflection,
            layout,
            factorization,
            origins: source.contact_origins(),
        })
    }

    pub fn source(&self) -> &NativeFieldCurrentSource<'c> {
        self.source
    }

    pub fn input(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.reflection.input()
    }

    /// The full resident endpoint `(w,b_ref)` and its outward carrier radius.
    pub fn output(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.reflection.output()
    }

    pub fn layout(&self) -> NativeFieldJointLayout {
        self.layout
    }

    pub fn factorization(&self) -> NativeFieldActionFactorization {
        self.factorization
    }

    pub fn contact_origins(&self) -> &[NativeFieldContactOrigin] {
        &self.origins
    }

    /// The signed exact-solve residual, decoded only when a caller explicitly requests it.
    pub fn inspect_residual(&self) -> Result<Vec<ExactComplexWaveCurrent>, Error> {
        self.reflection.inspect_residual()
    }

    /// The source D columns as an outer resident enclosure.  This is the declared sparse/contact
    /// incidence anchor; the action does not expand it into a host-side D D* covariance.
    pub fn material(&self) -> Result<Option<ResidentNormalEnclosureView<'_, 'c>>, Error> {
        self.source.material()
    }

    /// Expose the existing full-word producing adjoint.  Its returned paired factors are later
    /// summed by the native contact response owner as
    /// `G_D = lambda (b-b_ref)* + v (g_b-D*lambda)*`, with both rank-two terms retained.
    pub fn compare_target<'t>(
        &'t self,
        target: ResidentNormalEnclosureView<'t, 'c>,
        step_bits: u32,
    ) -> Result<NativeFieldReflectionTarget<'t, 'a, 'c>, Error> {
        self.reflection.compare_target(target, step_bits)
    }

    pub fn into_reflection(self) -> NativeFieldReflection<'a, 'c> {
        self.reflection
    }
}

impl<'a, 'c> NativeFieldMatrixFreeAction<'a, 'c> {
    pub(super) fn prepare(
        source: &'a NativeFieldCurrentSource<'c>,
        input: ResidentNormalEnclosureView<'a, 'c>,
        steps: usize,
        omega_bits: u32,
    ) -> Result<Self, Error> {
        Self::prepare_with_method(source, input, steps, omega_bits, 0)
    }

    pub(super) fn prepare_with_method(
        source: &'a NativeFieldCurrentSource<'c>,
        input: ResidentNormalEnclosureView<'a, 'c>,
        steps: usize,
        omega_bits: u32,
        solve_method: u32,
    ) -> Result<Self, Error> {
        if input.components() != source.width
            || input.grain() != ResidentGrain(source.grain)
            || steps == 0
            || (omega_bits > 120 && omega_bits != u32::MAX)
            || solve_method > 1
        {
            return Err(Error::Shape);
        }
        let d = source.boundary_components();
        let count = source.births.len();
        let width = d.checked_add(2 * count).ok_or(Error::Shape)?;
        if source._producing.factor_program.is_some() {
            let (output, residual) = NativeFieldCurrentSource::prepare_factor_sections(
                source,
                input,
                steps,
                omega_bits,
                solve_method,
            )?;
            let factorization = if solve_method == 1 {
                NativeFieldActionFactorization::ResidentFactorProgramChebyshevMatrixFree {
                    steps,
                    omega_bits,
                }
            } else {
                NativeFieldActionFactorization::ResidentFactorProgramMatrixFree {
                    steps,
                    omega_bits,
                }
            };
            return Ok(Self {
                source,
                input,
                output,
                residual,
                trace: std::cell::OnceCell::new(),
                layout: NativeFieldJointLayout {
                    boundary_components: d,
                    internal_components: source.internal_components(),
                    joint_components: width,
                    contact_count: count,
                    field_cut: source.field_cut(),
                    grain: source.grain,
                },
                factorization,
                origins: source.contact_origins(),
            });
        }
        if solve_method != 0 {
            return Err(Error::Shape);
        }
        let output = Rc::new(
            source
                .surface
                .fresh_section(1, 2 * (width + 1), ResidentGrain(0))?,
        );
        let residual = Rc::new(
            source
                .surface
                .fresh_section(1, 2 * (d + 1), ResidentGrain(0))?,
        );
        let work_wide = d
            .checked_mul(5)
            .and_then(|v| v.checked_add(4 * count)?.checked_add(1))
            .ok_or(Error::Shape)?;
        let work = source
            .surface
            .fresh_section(1, 2 * work_wide, ResidentGrain(0))?;
        let mut passage = source.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            source.surface.record_field_global_action(
                &lane,
                &source._producing.map,
                &source._producing.bounds,
                input,
                d,
                count,
                source.grain,
                steps,
                omega_bits,
                &work,
                &output,
                &residual,
            )?;
        }
        passage.close(0, &output, 64)?;
        let completion = passage.finish()?.launch()?;
        if !completion.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "global resident action: {:?}",
                completion.obstruction
            )));
        }
        Ok(Self {
            source,
            input,
            output,
            residual,
            trace: std::cell::OnceCell::new(),
            layout: NativeFieldJointLayout {
                boundary_components: d,
                internal_components: source.internal_components(),
                joint_components: width,
                contact_count: count,
                field_cut: source.field_cut(),
                grain: source.grain,
            },
            factorization: NativeFieldActionFactorization::ResidentRichardsonMatrixFree {
                steps,
                omega_bits,
            },
            origins: source.contact_origins(),
        })
    }

    pub fn source(&self) -> &NativeFieldCurrentSource<'c> {
        self.source
    }

    pub fn input(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.input
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

    pub fn residual(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.source.surface,
            section: &self.residual,
            offset: 0,
            width: self.layout.boundary_components,
            grain: ResidentGrain(self.layout.grain),
        }
    }

    pub fn layout(&self) -> NativeFieldJointLayout {
        self.layout
    }

    pub fn factorization(&self) -> NativeFieldActionFactorization {
        self.factorization
    }

    pub fn contact_origins(&self) -> &[NativeFieldContactOrigin] {
        &self.origins
    }

    pub fn residual_bound(&self) -> Result<holonics::geometry::Rat, Error> {
        Ok(self.residual().inspect()?.radius)
    }

    /// Convert the resident Richardson residual center to the report trace layout for atomic
    /// endpoint publication. This is a device resident conversion; it does not read or rewrite
    /// the residual on the host.
    pub fn residual_trace(&self) -> Result<&ResidentSection<'c>, Error> {
        if self.trace.get().is_none() {
            let trace = self.source.surface.fresh_section(
                1,
                18 * self.layout.boundary_components,
                ResidentGrain(0),
            )?;
            let mut passage = self.source.surface.begin_passage(&[vec![]])?;
            {
                let lane = passage.open(0, &[])?;
                self.source.surface.record_field_global_residual_trace(
                    &lane,
                    &self.residual,
                    self.layout.boundary_components,
                    &trace,
                )?;
            }
            passage.close(0, &trace, 64)?;
            let completion = passage.finish()?.launch()?;
            if !completion.obstruction.is_empty() {
                return Err(Error::Arithmetic(format!(
                    "global residual trace: {:?}",
                    completion.obstruction
                )));
            }
            self.trace.set(trace).map_err(|_| Error::Uncertain)?;
        }
        Ok(self.trace.get().expect("residual trace initialized"))
    }

    /// Pull back any full joint output covector. The internal b covector is retained and enters
    /// the second rank-two D factor; a boundary-only target is not substituted.
    pub fn pullback_full<'g>(
        &'a self,
        covector: ResidentNormalEnclosureView<'g, 'c>,
        steps: usize,
        omega_bits: u32,
    ) -> Result<NativeFieldActionPullback<'a, 'c>, Error> {
        if covector.components() != self.layout.joint_components
            || covector.grain() != ResidentGrain(self.layout.grain)
            || steps == 0
            || (omega_bits > 120 && omega_bits != u32::MAX)
            || !std::ptr::eq(covector.surface(), self.source.surface)
        {
            return Err(Error::Shape);
        }
        if self.source._producing.factor_program.is_some() {
            let solve_method = matches!(
                self.factorization,
                NativeFieldActionFactorization::ResidentFactorProgramChebyshevMatrixFree { .. }
            ) as u32;
            let factor = NativeFieldFactorAction::from_sections(
                self.source,
                self.input,
                Rc::clone(&self.output),
                Rc::clone(&self.residual),
                steps,
                omega_bits,
                solve_method,
            );
            return factor.pullback_full_auto(covector);
        }
        let d = self.layout.boundary_components;
        let count = self.layout.contact_count;
        let width = self.layout.joint_components;
        let surface = self.source.surface;
        let incoming = Rc::new(surface.fresh_section(1, 2 * (width + 1), ResidentGrain(0))?);
        let ports = Rc::new(surface.fresh_section(2, 2 * d, ResidentGrain(0))?);
        let currents = Rc::new(surface.fresh_section(2, 4 * count.max(1), ResidentGrain(0))?);
        let delta_bounds = Rc::new(surface.fresh_section(1, 4, ResidentGrain(0))?);
        let residual = Rc::new(surface.fresh_section(1, 2 * (d + 1), ResidentGrain(0))?);
        let work_wide = d
            .checked_mul(5)
            .and_then(|v| v.checked_add(4 * count)?.checked_add(1))
            .ok_or(Error::Shape)?;
        let work = surface.fresh_section(1, 2 * work_wide, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_field_global_pullback(
                &lane,
                &self.source._producing.map,
                &self.source._producing.bounds,
                self.input,
                self.output(),
                covector,
                d,
                count,
                self.layout.grain,
                steps,
                omega_bits,
                &work,
                &incoming,
                &ports,
                &currents,
                &delta_bounds,
                &residual,
            )?;
        }
        passage.close(0, &incoming, 64)?;
        let completion = passage.finish()?.launch()?;
        if !completion.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "global resident pullback: {:?}",
                completion.obstruction
            )));
        }
        Ok(NativeFieldActionPullback {
            source: self.source,
            incoming,
            ports,
            currents,
            delta_bounds,
            residual,
            layout: self.layout,
        })
    }

    pub fn pullback_full_auto<'g>(
        &'a self,
        covector: ResidentNormalEnclosureView<'g, 'c>,
        steps: usize,
    ) -> Result<NativeFieldActionPullback<'a, 'c>, Error> {
        self.pullback_full(covector, steps, u32::MAX)
    }
}

impl<'a, 'c> NativeFieldActionPullback<'a, 'c> {
    pub(super) fn from_factor(
        source: &'a NativeFieldCurrentSource<'c>,
        incoming: Rc<ResidentSection<'c>>,
        ports: Rc<ResidentSection<'c>>,
        currents: Rc<ResidentSection<'c>>,
        delta_bounds: Rc<ResidentSection<'c>>,
        residual: Rc<ResidentSection<'c>>,
        layout: NativeFieldJointLayout,
    ) -> Self {
        Self {
            source,
            incoming,
            ports,
            currents,
            delta_bounds,
            residual,
            layout,
        }
    }
    pub fn source(&self) -> &NativeFieldCurrentSource<'c> {
        self.source
    }

    pub fn input_covector(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.source.surface,
            section: &self.incoming,
            offset: 0,
            width: self.layout.joint_components,
            grain: ResidentGrain(self.layout.grain),
        }
    }

    pub fn residual_bound(&self) -> Result<holonics::geometry::Rat, Error> {
        let view = ResidentNormalEnclosureView {
            surface: self.source.surface,
            section: &self.residual,
            offset: 0,
            width: self.layout.boundary_components,
            grain: ResidentGrain(self.layout.grain),
        };
        Ok(view.inspect()?.radius)
    }

    pub(super) fn resident_ports(&self) -> Rc<ResidentSection<'c>> {
        Rc::clone(&self.ports)
    }

    pub(super) fn resident_currents(&self) -> Rc<ResidentSection<'c>> {
        Rc::clone(&self.currents)
    }

    pub(super) fn resident_bounds(&self) -> Rc<ResidentSection<'c>> {
        Rc::clone(&self.delta_bounds)
    }
}

impl<'c> NativeConstitutiveField<'c> {
    /// Sum complete source-qualified rank-two D factors and stage one contemporary material
    /// return. Every resident factor and the resulting operative sections are ready before the
    /// caller publishes the successor with `commit_global_action_material_return`.
    pub fn prepare_global_action_material_return<'a>(
        &mut self,
        pullbacks: &[&NativeFieldActionPullback<'a, 'c>],
        step_bits: u32,
        realization: NativeContactRealization,
    ) -> Result<NativeFieldGlobalMaterialCommit<'c>, Error> {
        if !self.relation.usable
            || self.pending.is_some()
            || pullbacks.is_empty()
            || step_bits > 120
        {
            return Err(Error::Uncertain);
        }
        let source = pullbacks[0].source;
        let junction = self.junction.as_ref().ok_or(Error::Shape)?;
        let op = junction.operative.as_ref().ok_or(Error::Shape)?;
        let d = source.boundary_components();
        let count = source.births.len();
        if !Rc::ptr_eq(&source.owner, &self.owner) || source.births != op.births {
            return Err(Error::ForeignOccurrence);
        }
        for pullback in pullbacks {
            if !Rc::ptr_eq(&pullback.source.owner, &self.owner)
                || pullback.source.births != op.births
                || pullback.source.grain != op.grain
                || pullback.layout.boundary_components != d
                || pullback.layout.contact_count != count
            {
                return Err(Error::ForeignOccurrence);
            }
        }
        let owner = Rc::clone(&self.owner);
        let cut = self.history.len();
        let births = op.births.clone();
        let producing = Rc::clone(&op.sections);
        let source_grain = op.grain;
        let surface = self.relation.surface;
        let factored_reference = realization == NativeContactRealization::DyadicDeposit
            && source._producing.factor_program.is_some();
        let mut staged = self.stage_operative_contacts()?;
        for (factor_stage, pullback) in pullbacks.iter().enumerate() {
            let (ports, currents, bounds) = if step_bits == 0 {
                (
                    pullback.resident_ports(),
                    pullback.resident_currents(),
                    pullback.resident_bounds(),
                )
            } else {
                let ports = Rc::new(surface.fresh_section(2, 2 * d, ResidentGrain(0))?);
                let currents = pullback.resident_currents();
                let bounds = Rc::new(surface.fresh_section(1, 4, ResidentGrain(0))?);
                let mut pass = surface.begin_passage(&[vec![]])?;
                {
                    let lane = pass.open(0, &[])?;
                    surface.record_field_global_scale_ports(
                        &lane,
                        &pullback.ports,
                        &pullback.delta_bounds,
                        d,
                        step_bits,
                        &ports,
                        &bounds,
                    )?;
                }
                pass.close(0, &bounds, 64)?;
                let completion = pass.finish()?.launch()?;
                if !completion.obstruction.is_empty() {
                    return Err(Error::Arithmetic(format!(
                        "global material scale: {:?}",
                        completion.obstruction
                    )));
                }
                (ports, currents, bounds)
            };
            let bounds = if factored_reference {
                // Exact deposits retain the factor-ball reference bound in the journal. The
                // active D successor has zero coefficient uncertainty by this realization law.
                bounds
            } else {
                let matrix_bound = Rc::new(surface.fresh_section(1, 4, ResidentGrain(0))?);
                let mut pass = surface.begin_passage(&[vec![]])?;
                {
                    let lane = pass.open(0, &[])?;
                    surface.record_field_factor_delta_bound(
                        &lane,
                        &ports,
                        &currents,
                        &bounds,
                        d,
                        count,
                        source_grain,
                        &matrix_bound,
                    )?;
                }
                pass.close(0, &matrix_bound, 64)?;
                let receipt = pass.finish()?.launch()?;
                if !receipt.obstruction.is_empty() {
                    let reference = surface
                        .detach_section(&bounds, 64)
                        .map_err(Error::from)
                        .and_then(|rest| wides(&rest.intervals).map_err(Error::from))
                        .map(|values| {
                            values
                                .into_iter()
                                .map(|value| {
                                    holonics::geometry::Rat::new(
                                        value.into(),
                                        num_bigint::BigInt::from(1) << source_grain,
                                    )
                                    .to_string()
                                })
                                .collect::<Vec<_>>()
                        });
                    return Err(Error::Arithmetic(format!(
                        "global material bound at factor stage {factor_stage}, grain {source_grain}, factor radii {reference:?}: {:?}",
                        receipt.obstruction,
                    )));
                }
                matrix_bound
            };
            let returned = Rc::new(OperativeReturn {
                at_cut: cut,
                contact_count: count,
                factor_count: count,
                realization,
                bound_kind: if factored_reference {
                    NativeOperativeBoundKind::FactorBalls
                } else {
                    NativeOperativeBoundKind::MatrixAndInternal
                },
                origin: Rc::clone(&staged.origin),
                ports,
                currents: Rc::clone(&currents),
                current_difference_source: None,
                source_overlap: None,
                b: None,
                bounds,
            });
            staged = staged.stage_return_using(Rc::clone(&returned), &returned.currents)?;
        }
        Ok(NativeFieldGlobalMaterialCommit {
            owner,
            cut,
            births,
            producing,
            sections: staged.sections,
            origin: staged.origin,
            returns: staged.returns,
            program: staged.program,
            grain: source_grain,
        })
    }

    pub fn commit_global_action_material_return(
        &mut self,
        prepared: NativeFieldGlobalMaterialCommit<'c>,
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
            || prepared.grain != op.grain
        {
            return Err(Error::ForeignOccurrence);
        }
        let junction = self.junction.as_mut().expect("validated junction");
        let joint_image = junction.joint_current.take();
        let op = junction
            .operative
            .as_mut()
            .expect("validated operative state");
        op.sections = prepared.sections;
        op.origin = prepared.origin;
        op.returns = prepared.returns;
        op.program = prepared.program;
        if let Some((report, _, image)) = joint_image {
            junction.joint_current = Some((report, Rc::clone(&op.sections.b), image));
        }
        Ok(())
    }
}
