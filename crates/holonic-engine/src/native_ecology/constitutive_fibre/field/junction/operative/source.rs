use super::super::super::material_transport::wides;
use super::*;
mod action;
mod map_action;
mod reflection;
mod reflection_commit;
mod reflection_target;
mod rest;
pub use action::{
    NativeFieldAction, NativeFieldActionFactorization, NativeFieldActionPullback,
    NativeFieldContactOrigin, NativeFieldGlobalMaterialCommit, NativeFieldJointLayout,
    NativeFieldMatrixFreeAction,
};
pub use map_action::{NativeFieldDeclaredIncidence, NativeFieldFactorAction};
pub use reflection::{NativeFieldReflection, NativeFieldReflectionSection};
pub use reflection_commit::NativeFieldJointCurrentCommit;
pub use reflection_target::NativeFieldReflectionTarget;
pub use rest::NativeFieldCurrentSourceRest;

#[cfg(test)]
mod tests;

/// An immutable resident source port joining the actual outgoing field current with every
/// operative internal `b` coordinate. The packed enclosure is an outer receiver; the report,
/// operative sections, births, and owner remain attached as finer source witnesses.
pub struct NativeFieldCurrentSource<'c> {
    surface: &'c ResidentSurface<'c>,
    owner: Rc<()>,
    cut: usize,
    grain: u32,
    width: usize,
    packed: Rc<ResidentSection<'c>>,
    material: std::cell::OnceCell<ResidentSection<'c>>,
    reflection: std::cell::OnceCell<ResidentSection<'c>>,
    report: Rc<ResidentSection<'c>>,
    _producing: Rc<OperativeSections<'c>>,
    births: Vec<NativeOperativeContactBirth>,
    declared_origins: Vec<NativeFieldContactOrigin>,
}

impl<'c> NativeFieldCurrentSource<'c> {
    /// Cold source-qualified inspection of the certified resident D/factor bounds.
    /// This reads only the existing small aggregate packets and never realizes D or D D*.
    pub fn inspect_operator_bounds(&self) -> Result<serde_json::Value, Error> {
        let read = |section: &ResidentSection<'c>| -> Result<Vec<i128>, Error> {
            let rest = self
                .surface
                .detach_section(section, 64)
                .map_err(Error::from)?;
            wides(&rest.intervals).map_err(Error::from)
        };
        let moments = read(&self._producing.moment_bounds)?;
        let bounds = read(&self._producing.bounds)?;
        if moments.len() != 4 || bounds.len() != 2 || moments.iter().chain(&bounds).any(|v| *v < 0)
        {
            return Err(Error::Shape);
        }
        let grain = self.grain;
        let rat = |value: i128| -> String {
            relational_geometry::Rat::new(value.into(), num_bigint::BigInt::from(1u8) << grain)
                .to_string()
        };
        let mut map_error = bounds[0];
        let mut rank = 0usize;
        let mut nonzeros = 0usize;
        let mut rows = self.births.len();
        let mut factor = false;
        if let Some(program) = &self._producing.factor_program {
            factor = true;
            rank = program.rank;
            nonzeros = program.nonzeros;
            rows = program.rows;
            let defects = read(&program.defects)?;
            if defects.len() != rank.max(1) || defects.iter().any(|v| *v < 0) {
                return Err(Error::Shape);
            }
            map_error = defects
                .into_iter()
                .take(rank)
                .try_fold(map_error, |sum, value| {
                    sum.checked_add(value).ok_or(Error::Shape)
                })?;
        }
        Ok(serde_json::json!({
            "representation": if factor { "csr-low-rank" } else { "dense-reference" },
            "operator_center_norm_upper": rat(moments[2]),
            "internal_norm_upper": rat(moments[3]),
            "map_error_upper": rat(map_error),
            "internal_radius": rat(bounds[1]),
            "grain": grain,
            "boundary_components": self.boundary_components(),
            "internal_components": self.internal_components(),
            "rows": rows,
            "rank": rank,
            "nonzeros": nonzeros,
            "field_cut": self.cut,
            "contact_count": self.births.len(),
        }))
    }
    /// The actual operative D columns in the order of births(), with their full
    /// Frobenius bound. Column identity follows the caused contact population.
    pub fn material(&self) -> Result<Option<ResidentNormalEnclosureView<'_, 'c>>, Error> {
        if self.births.is_empty() {
            return Ok(None);
        }
        if self._producing.factor_program.is_some() {
            return Err(invalid(
                "dense material receiver requires explicit factor-program realization",
            ));
        }
        let d = self.boundary_components();
        let count = self.births.len();
        let width = d.checked_mul(count).ok_or(Error::Shape)?;
        if self.material.get().is_none() {
            let out = self.surface.fresh_section(
                1,
                width
                    .checked_add(1)
                    .and_then(|v| v.checked_mul(2))
                    .ok_or(Error::Shape)?,
                ResidentGrain(0),
            )?;
            let mut p = self.surface.begin_passage(&[vec![]])?;
            {
                let lane = p.open(0, &[])?;
                self.surface.record_field_material_source(
                    &lane,
                    &self._producing.map,
                    &self._producing.bounds,
                    d,
                    count,
                    &out,
                )?;
            }
            p.close(0, &out, 64)?;
            let r = p.finish()?.launch()?;
            if !r.obstruction.is_empty() {
                return Err(Error::Arithmetic(format!(
                    "operative material source: {:?}",
                    r.obstruction
                )));
            }
            self.material.set(out).map_err(|_| Error::Uncertain)?;
        }
        Ok(Some(ResidentNormalEnclosureView {
            surface: self.surface,
            section: self.material.get().unwrap(),
            offset: 0,
            width,
            grain: ResidentGrain(self.grain),
        }))
    }
    /// A material difference in the same field/contact chart. Matching widths
    /// alone do not identify these columns or their causal origins.
    pub fn material_difference(&self, prior: &Self) -> Result<ResidentNormalEnclosure<'c>, Error> {
        if !self.same_owner(prior) || self.births != prior.births {
            return Err(Error::ForeignOccurrence);
        }
        self.material()?
            .ok_or(Error::Shape)?
            .difference(prior.material()?.ok_or(Error::Shape)?)
    }
    pub fn occurrence(&self) -> Option<usize> {
        self.cut.checked_sub(1)
    }
    pub fn field_cut(&self) -> usize {
        self.cut
    }
    pub fn boundary_components(&self) -> usize {
        self.width - self.internal_components()
    }
    pub fn internal_components(&self) -> usize {
        self.births.len() * 2
    }
    pub fn births(&self) -> &[NativeOperativeContactBirth] {
        &self.births
    }

    /// The causal address of every resident internal column.  These addresses are taken from
    /// admitted operative births; they are not reconstructed from the current values and an
    /// authored observation cannot create one.  The column order is the order used by D and D*.
    pub fn contact_origins(&self) -> Vec<NativeFieldContactOrigin> {
        if !self.declared_origins.is_empty() {
            return self.declared_origins.clone();
        }
        self.births
            .iter()
            .enumerate()
            .map(|(column, birth)| {
                NativeFieldContactOrigin::observed(column, birth.source, birth.receiving)
            })
            .collect()
    }

    /// Compile the source-owned global action at the supplied full joint input.  The action
    /// keeps the source cut and its resident D/D* factor; it never publishes a field transition.
    pub fn action<'a>(
        &'a self,
        input: ResidentNormalEnclosureView<'a, 'c>,
    ) -> Result<NativeFieldAction<'a, 'c>, Error> {
        NativeFieldAction::prepare(self, input)
    }

    /// Apply the declared-contact global action without forming a boundary-square covariance.
    /// `omega_bits` is the caller-certified Richardson aperture, normally
    /// `ceil(log2(1 + L))` for its declared Lipschitz bound L.
    pub fn action_matrix_free<'a>(
        &'a self,
        input: ResidentNormalEnclosureView<'a, 'c>,
        steps: usize,
        omega_bits: u32,
    ) -> Result<NativeFieldMatrixFreeAction<'a, 'c>, Error> {
        NativeFieldMatrixFreeAction::prepare(self, input, steps, omega_bits)
    }

    /// Resident auto-aperture variant. The device derives the smallest dyadic omega aperture
    /// dominating its certified operator-norm bound before the first Richardson step.
    pub fn action_matrix_free_auto<'a>(
        &'a self,
        input: ResidentNormalEnclosureView<'a, 'c>,
        steps: usize,
    ) -> Result<NativeFieldMatrixFreeAction<'a, 'c>, Error> {
        NativeFieldMatrixFreeAction::prepare(self, input, steps, u32::MAX)
    }
    pub fn same_owner(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.owner, &other.owner)
    }

    /// Retain the immutable producing source for a pending word or receiving cut.  The resident
    /// source sections and owner witness are shared; lazily compiled material caches are local to
    /// the clone and therefore cannot make two actions publish the same factor accidentally.
    pub fn retained_clone(&self) -> Self {
        Self {
            surface: self.surface,
            owner: Rc::clone(&self.owner),
            cut: self.cut,
            grain: self.grain,
            width: self.width,
            packed: Rc::clone(&self.packed),
            material: std::cell::OnceCell::new(),
            reflection: std::cell::OnceCell::new(),
            report: Rc::clone(&self.report),
            _producing: Rc::clone(&self._producing),
            births: self.births.clone(),
            declared_origins: self.declared_origins.clone(),
        }
    }

    /// Alias used by consumers that store the producing source in a durable word handle.
    pub fn snapshot(&self) -> Self {
        self.retained_clone()
    }
    pub fn outgoing_report(&self) -> &ResidentSection<'c> {
        &self.report
    }
    pub fn enclosure(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.surface,
            section: &self.packed,
            offset: 0,
            width: self.width,
            grain: ResidentGrain(self.grain),
        }
    }
}

impl<'c> NativeConstitutiveField<'c> {
    /// Register an actual declared contact map on this continuing field.  The map, internal
    /// branch and bounds are supplied as resident sections from the caller's admitted geometry;
    /// no occurrence, observation or synthetic priming event is created here.  Origins are tagged
    /// `Declared` and remain separate from observation-derived births.
    pub fn register_declared_contact_map(
        &mut self,
        map: ResidentSection<'c>,
        b: ResidentSection<'c>,
        bounds: ResidentSection<'c>,
        origins: Vec<NativeFieldContactOrigin>,
    ) -> Result<(), Error> {
        if !self.relation.usable || self.pending.is_some() || origins.is_empty() {
            return Err(Error::Uncertain);
        }
        if origins
            .iter()
            .enumerate()
            .any(|(column, origin)| !origin.is_declared() || origin.column() != column)
        {
            return Err(Error::ForeignOccurrence);
        }
        let junction = self.junction.as_ref().ok_or(Error::Shape)?;
        if junction.operative.is_some() {
            return Err(Error::ForeignOccurrence);
        }
        let d = self.nodes().checked_mul(6).ok_or(Error::Shape)?;
        let count = origins.len();
        let surface = self.relation.surface;
        let valid = |section: &ResidentSection<'c>, rows: usize, width: usize| {
            section.rows() == rows
                && section.width() == width
                && section.grain() == ResidentGrain(0)
                && std::ptr::eq(section.surface(), surface)
        };
        if !valid(&map, count, 2 * d) || !valid(&b, count, 4) || !valid(&bounds, 1, 4) {
            return Err(Error::Shape);
        }
        let grain = match self.junction_representation() {
            Some(NativeFieldJunctionRepresentation::EnclosedDyadic { fractional_bits }) => {
                fractional_bits
            }
            _ => return Err(Error::Shape),
        };
        let mut staged = sections(surface, d, count)?;
        {
            let sections = Rc::get_mut(&mut staged).ok_or(Error::Uncertain)?;
            sections.map = Rc::new(map);
            sections.b = Rc::new(b);
            sections.bounds = Rc::new(bounds);
        }
        let rounds = surface.fresh_section(1, d, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_operative_aggregate(
                &lane,
                d,
                count,
                grain,
                staged.current(),
                &staged.aggregate,
                &staged.moment_bounds,
                &rounds,
            )?;
        }
        passage.close(0, &staged.moment_bounds, 64)?;
        let completion = passage.finish()?.launch()?;
        if !completion.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "declared contact moments: {:?}",
                completion.obstruction
            )));
        }
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
            initial: Rc::clone(&staged),
            sections: staged,
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

    /// Admit the caller's declared contact chart against the field's actual causal births.
    /// Declarations are addresses only: they cannot manufacture a D column or prime an
    /// observation.  The resident map and internal branch continue to come from the same
    /// operative staging owner, and a mismatch is refused before publication.
    pub fn admit_declared_contact_origins(
        &mut self,
        origins: &[NativeFieldContactOrigin],
    ) -> Result<(), Error> {
        let should_install = self
            .junction
            .as_ref()
            .is_some_and(|junction| junction.operative.is_none());
        let staged = self.stage_operative_contacts()?;
        if origins.iter().enumerate().any(|(column, origin)| {
            !origin.is_declared()
                || origin.column() != column
                || origin.column() >= staged.births().len()
        }) {
            return Err(Error::ForeignOccurrence);
        }
        let declared = origins.to_vec();
        if should_install {
            let owned = staged.into_owned();
            let mut owned = owned;
            owned.declared_origins = declared;
            self.junction.as_mut().ok_or(Error::Shape)?.operative = Some(owned);
            self.junction.as_mut().unwrap().solver = NativeFieldJunctionSolver::Full;
        } else if let Some(operative) = self.junction.as_mut().and_then(|j| j.operative.as_mut()) {
            operative.declared_origins = declared;
        }
        Ok(())
    }

    /// Pack the actual outgoing junction block and all operative internal coordinates into one
    /// resident outer enclosure. No numerical readout or field mutation occurs.
    pub fn read_current_source(&mut self) -> Result<NativeFieldCurrentSource<'c>, Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        let nodes = self.nodes();
        let junction = self.junction.as_ref().ok_or(Error::Shape)?;
        let report = Rc::clone(&junction.current);
        let surface = self.relation.surface;
        let owner = Rc::clone(&self.owner);
        let cut = self.history.len();
        let staging = self.stage_operative_contacts()?;
        let count = staging.births.len();
        let d = nodes.checked_mul(6).ok_or(Error::Shape)?;
        let width = d
            .checked_add(count.checked_mul(2).ok_or(Error::Shape)?)
            .ok_or(Error::Shape)?;
        if let Some(image) = staging
            .field
            .junction
            .as_ref()
            .and_then(|j| j.valid_joint_current())
        {
            if Rc::ptr_eq(
                &staging.sections.b,
                &staging
                    .field
                    .junction
                    .as_ref()
                    .unwrap()
                    .operative
                    .as_ref()
                    .unwrap()
                    .sections
                    .b,
            ) {
                return Ok(NativeFieldCurrentSource {
                    surface,
                    owner,
                    cut,
                    grain: staging.grain,
                    width,
                    packed: Rc::clone(image),
                    material: std::cell::OnceCell::new(),
                    reflection: std::cell::OnceCell::new(),
                    report,
                    _producing: Rc::clone(&staging.sections),
                    births: staging.births.clone(),
                    declared_origins: staging.declared_origins.clone(),
                });
            }
        }
        let packed = surface.fresh_section(1, 2 * (width + 1), ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_field_current_source(
                &lane,
                &report,
                &staging.sections.b,
                &staging.sections.bounds,
                nodes,
                count,
                &packed,
            )?;
        }
        passage.close(0, &packed, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "field current source: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeFieldCurrentSource {
            surface,
            owner,
            cut,
            grain: staging.grain,
            width,
            packed: Rc::new(packed),
            material: std::cell::OnceCell::new(),
            reflection: std::cell::OnceCell::new(),
            report,
            _producing: Rc::clone(&staging.sections),
            births: staging.births.clone(),
            declared_origins: staging.declared_origins.clone(),
        })
    }
}
