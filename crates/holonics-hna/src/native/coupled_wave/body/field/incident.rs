//! Incident-conditioned finite word on one global constitutive field.
mod rest;
#[cfg(test)]
#[path = "incident_tests.rs"]
mod tests;
use super::*;
use crate::native::field_geometry::GeometricFieldSpec;
use holonic_engine::{
    native_ecology::constitutive_fibre::{
        NativePhaseParticipation, ResidentNormalEnclosureSection, ResidentNormalMaterial,
        ResidentNormalMaterialView,
    },
    resident_section::{Dyadic, SeriesAperture},
    ExactWavePhaseTransport,
};
pub use rest::NativeIncidentModelRest;

/// Numerical proposal for the same residual-certified global reflection. Persisting this
/// choice keeps an older pending word's rounded producing operation unchanged.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum IncidentFieldSolver {
    #[default]
    Richardson,
    Chebyshev,
}
impl IncidentFieldSolver {
    pub(crate) fn is_richardson(&self) -> bool {
        *self == Self::Richardson
    }
    fn action<'a, 'c>(
        self,
        source: &'a NativeFieldCurrentSource<'c>,
        input: ResidentNormalEnclosureView<'a, 'c>,
        steps: usize,
    ) -> Result<
        holonic_engine::native_ecology::constitutive_fibre::NativeFieldMatrixFreeAction<'a, 'c>,
        NativeSessionError,
    > {
        match self {
            Self::Richardson => source.action_matrix_free_auto(input, steps),
            Self::Chebyshev => source.action_matrix_free_chebyshev(input, steps),
        }
        .map_err(invalid)
    }
}

/// A declared local chart and material ownership on the existing geometric field.
/// Equal degree does not imply shared material: sharing is supplied explicitly by this chart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IncidentFieldSpec {
    pub geometry: GeometricFieldSpec,
    pub local_roots: usize,
    /// One owner per geometric site, numbered contiguously. An empty list declares one per site.
    #[serde(default)]
    pub material_owners: Vec<usize>,
    #[serde(default = "solve_steps")]
    pub solve_steps: usize,
    #[serde(default, skip_serializing_if = "IncidentFieldSolver::is_richardson")]
    pub solver: IncidentFieldSolver,
}
fn solve_steps() -> usize {
    256
}
#[derive(Clone)]
struct IncidentSite {
    sources: Vec<usize>,
    phases: Vec<ExactWavePhaseTransport>,
    differences: Vec<usize>,
    material: usize,
}
#[derive(Clone)]
struct IncidentLayout {
    sites: Vec<IncidentSite>,
    slot_rows: Vec<usize>,
    width: usize,
    material_features: Vec<usize>,
    beta: Dyadic,
    series: u32,
    steps: usize,
    relaxation_bits: u32,
}
struct IncidentGroup {
    material: usize,
    receivers: Vec<usize>,
    neighbors: usize,
    differences: usize,
    sources: Vec<usize>,
    phases: Vec<ExactWavePhaseTransport>,
    difference_sources: Vec<usize>,
    difference_phases: Vec<ExactWavePhaseTransport>,
    query_repeats: Vec<usize>,
    condition_held: Vec<bool>,
}
impl IncidentLayout {
    fn groups(&self, admitted: &[Vec<bool>]) -> Vec<Rc<IncidentGroup>> {
        let mut grouped: BTreeMap<(usize, usize, usize), Vec<usize>> = BTreeMap::new();
        for (r, site) in self.sites.iter().enumerate() {
            grouped
                .entry((
                    site.material,
                    admitted[r].iter().filter(|v| **v).count(),
                    site.differences.len(),
                ))
                .or_default()
                .push(r);
        }
        grouped
            .into_iter()
            .map(|((material, neighbors, differences), receivers)| {
                let mut group = IncidentGroup {
                    material,
                    receivers,
                    neighbors,
                    differences,
                    sources: vec![],
                    phases: vec![],
                    difference_sources: vec![],
                    difference_phases: vec![],
                    query_repeats: vec![],
                    condition_held: vec![],
                };
                for (row, &r) in group.receivers.iter().enumerate() {
                    let site = &self.sites[r];
                    for (port, &source) in site.sources.iter().enumerate() {
                        if admitted[r][port] {
                            group.sources.push(source);
                            group.phases.push(site.phases[port].clone());
                        }
                    }
                    for &port in &site.differences {
                        group.difference_sources.push(site.sources[port]);
                        group.difference_phases.push(site.phases[port].clone());
                        group.query_repeats.push(row);
                        group
                            .condition_held
                            .extend(std::iter::repeat_n(!admitted[r][port], self.width / 2));
                    }
                }
                Rc::new(group)
            })
            .collect()
    }
}
impl IncidentFieldSpec {
    fn compile(&self) -> Result<IncidentLayout, NativeSessionError> {
        if self.solve_steps == 0 || self.solve_steps > u32::MAX as usize {
            return Err(invalid("incident solve resource aperture"));
        }
        let geometry = self.geometry.compile()?;
        let width = self
            .local_roots
            .checked_mul(6)
            .filter(|n| *n > 0)
            .ok_or_else(|| invalid("incident local root extent"))?;
        let owners = if self.material_owners.is_empty() {
            (0..geometry.rows).collect()
        } else {
            self.material_owners.clone()
        };
        if owners.len() != geometry.rows {
            return Err(invalid("incident material owner extent"));
        }
        let mut sites = vec![None; geometry.rows];
        for group in &geometry.groups {
            for (at, &row) in group.receivers.iter().enumerate() {
                let range = at * group.neighbors..(at + 1) * group.neighbors;
                let sources = group.sources[range.clone()].to_vec();
                let phases = group.phases[range].to_vec();
                let differences = sources
                    .iter()
                    .zip(&phases)
                    .enumerate()
                    .filter_map(|(i, (s, p))| {
                        (*s != row || *p != ExactWavePhaseTransport::identity()).then_some(i)
                    })
                    .collect();
                sites[row] = Some(IncidentSite {
                    sources,
                    phases,
                    differences,
                    material: owners[row],
                });
            }
        }
        let sites = sites
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| invalid("uncovered incident site"))?;
        let count = owners
            .iter()
            .copied()
            .max()
            .and_then(|n| n.checked_add(1))
            .ok_or_else(|| invalid("incident material extent"))?;
        if count > sites.len() {
            return Err(invalid("incident material owners must be contiguous"));
        }
        let mut features = vec![0; count];
        for site in &sites {
            let d = width / 2;
            let c = site
                .differences
                .len()
                .checked_mul(d)
                .ok_or_else(|| invalid("incident condition extent"))?;
            let f = if c == 0 {
                d
            } else {
                d.checked_mul(c)
                    .and_then(|n| n.checked_add(d)?.checked_add(c))
                    .ok_or_else(|| invalid("incident feature extent"))?
            };
            if features[site.material] != 0 && features[site.material] != f {
                return Err(invalid(
                    "shared incident material has incompatible ordered port charts",
                ));
            }
            features[site.material] = f;
        }
        if features.contains(&0) {
            return Err(invalid("incident material owners must be contiguous"));
        }
        Ok(IncidentLayout {
            sites,
            slot_rows: geometry.slot_rows,
            width,
            material_features: features,
            beta: Dyadic {
                significand: geometry.beta_significand,
                exponent: geometry.beta_exponent,
            },
            series: geometry.series_terms,
            steps: geometry.steps,
            relaxation_bits: geometry.relaxation_bits,
        })
    }
}

struct IncidentSiteStep<'c> {
    group: Rc<IncidentGroup>,
    query: Rc<ResidentNormalEnclosureSection<'c>>,
    phase: NativePhaseParticipation<'c>,
    condition: Option<ResidentNormalEnclosureSection<'c>>,
    features: ResidentNormalEnclosureSection<'c>,
}
struct IncidentStep<'c> {
    sites: Vec<IncidentSiteStep<'c>>,
    input: ResidentNormalEnclosure<'c>,
}
pub(crate) struct IncidentWord<'c> {
    source: NativeFieldCurrentSource<'c>,
    material: Vec<ResidentNormalMaterialView<'c>>,
    anchor: Rc<ResidentNormalEnclosure<'c>>,
    held: Vec<bool>,
    admitted: Vec<Vec<bool>>,
    steps: Vec<IncidentStep<'c>>,
    output: ResidentNormalEnclosure<'c>,
    epoch: u64,
    solver: IncidentFieldSolver,
    solve_steps: usize,
}
/// A prepared complete joint section. Receiving faces and pending storage are prepared before
/// this immutable word is committed to the continuing body.
pub struct NativeIncidentGenerated<'c> {
    word: Rc<IncidentWord<'c>>,
    comparison: Option<u64>,
}
pub struct NativeIncidentMaterialReturn<'c> {
    comparison: u64,
    epoch: u64,
    next_epoch: u64,
    observations: u64,
    anchor: ResidentNormalEnclosure<'c>,
    material: Vec<ResidentNormalMaterial<'c>>,
    contact: Option<
        holonic_engine::native_ecology::constitutive_fibre::NativeFieldGlobalMaterialCommit<'c>,
    >,
}
impl<'c> NativeIncidentMaterialReturn<'c> {
    pub fn anchor_covector(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.anchor.view()
    }
}
impl<'c> NativeIncidentGenerated<'c> {
    pub fn source_anchor(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.word.anchor.view()
    }
    pub fn boundary_components(&self) -> usize {
        self.word.source.boundary_components()
    }
    pub fn joint_output(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.word.output.view()
    }
    pub fn boundary(&self) -> Result<ResidentNormalEnclosure<'c>, NativeSessionError> {
        Ok(self
            .word
            .output
            .view()
            .restrict(0..self.word.source.boundary_components())?)
    }
    pub fn comparison_id(&self) -> Option<u64> {
        self.comparison
    }
    pub fn producing_epoch(&self) -> u64 {
        self.word.epoch
    }
    /// Source journal position of the immutable operative map/current used by this word.
    pub fn producing_field_cut(&self) -> usize {
        self.word.source.field_cut()
    }
    pub fn producing_material_observations(&self) -> Vec<u64> {
        self.word
            .material
            .iter()
            .map(ResidentNormalMaterialView::observations)
            .collect()
    }
    pub fn operator_bounds(&self) -> Result<Value, NativeSessionError> {
        self.word.source.inspect_operator_bounds().map_err(invalid)
    }
}
pub(crate) struct IncidentFieldModel<'c> {
    field: NativeConstitutiveField<'c>,
    spec: IncidentFieldSpec,
    layout: IncidentLayout,
    materials: Vec<ResidentNormalMaterial<'c>>,
    epoch: u64,
    generations: u64,
    observations: u64,
    next_comparison: u64,
    pending: BTreeMap<u64, Rc<IncidentWord<'c>>>,
}
/// Producing covectors, before the normal law stages contemporary material successors.
/// Contact operands retain every stage, including its internal-output covector.
pub(super) struct IncidentPullback<'c> {
    anchor: ResidentNormalEnclosure<'c>,
    material: Vec<
        Vec<(
            ResidentNormalEnclosureSection<'c>,
            ResidentNormalEnclosureSection<'c>,
        )>,
    >,
    contacts: Vec<(ResidentNormalEnclosure<'c>, ResidentNormalEnclosure<'c>)>,
}
fn phases(count: usize) -> Vec<ExactWavePhaseTransport> {
    vec![ExactWavePhaseTransport::identity(); count]
}
fn opposite() -> ExactWavePhaseTransport {
    ExactWavePhaseTransport::new(
        num_rational::BigRational::from_integer((-1).into()),
        num_rational::BigRational::from_integer(0.into()),
    )
    .expect("unit polarity")
}
fn zero<'c>(
    surface: &'c ResidentSurface<'c>,
    rows: usize,
    width: usize,
    grain: ResidentGrain,
) -> Result<ResidentNormalEnclosureSection<'c>, NativeSessionError> {
    Ok(ResidentNormalEnclosureSection::zeros(
        surface, rows, width, grain,
    )?)
}
impl<'c> IncidentFieldModel<'c> {
    pub(crate) fn new(
        field: NativeConstitutiveField<'c>,
        spec: IncidentFieldSpec,
    ) -> Result<Self, NativeSessionError> {
        let layout = spec.compile()?;
        Self::with_layout(field, spec, layout)
    }
    fn with_layout(
        mut field: NativeConstitutiveField<'c>,
        spec: IncidentFieldSpec,
        layout: IncidentLayout,
    ) -> Result<Self, NativeSessionError> {
        field.enable_operative_contacts()?;
        let source = field.read_current_source()?;
        if layout.sites.len().checked_mul(layout.width) != Some(source.boundary_components()) {
            return Err(invalid(
                "incident sites do not cover the global field boundary",
            ));
        }
        let materials = layout
            .material_features
            .iter()
            .map(|&f| {
                ResidentNormalMaterial::found_features(
                    field.surface(),
                    f,
                    layout.width / 2,
                    source.enclosure().grain(),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            field,
            spec,
            layout,
            materials,
            epoch: 0,
            generations: 0,
            observations: 0,
            next_comparison: 0,
            pending: BTreeMap::new(),
        })
    }
    fn word(
        &mut self,
        prepared_boundary: ResidentNormalEnclosureView<'_, 'c>,
        held: &[bool],
        admitted: Vec<Vec<bool>>,
    ) -> Result<IncidentWord<'c>, NativeSessionError> {
        let source = self.field.read_current_source()?;
        let boundary = source.boundary_components();
        if prepared_boundary.components() != boundary
            || held.len() != boundary / 2
            || prepared_boundary.grain() != source.enclosure().grain()
        {
            return Err(invalid("incident source anchor chart"));
        }
        let anchor = Rc::new(if source.internal_components() == 0 {
            prepared_boundary.to_owned()?
        } else {
            prepared_boundary.join(
                source
                    .enclosure()
                    .restrict(boundary..boundary + source.internal_components())?
                    .view(),
            )?
        });
        let mut joint_held = held.to_vec();
        joint_held.resize((boundary + source.internal_components()) / 2, false);
        let material = self
            .materials
            .iter()
            .map(ResidentNormalMaterial::retained_view)
            .collect::<Vec<_>>();
        let (steps, output) = self.evaluate(&source, &material, &anchor, &joint_held, &admitted)?;
        Ok(IncidentWord {
            source,
            material,
            anchor,
            held: joint_held,
            admitted,
            steps,
            output,
            epoch: self.epoch,
            solver: self.spec.solver,
            solve_steps: self.spec.solve_steps,
        })
    }

    pub(crate) fn epoch(&self) -> u64 {
        self.epoch
    }
    pub(crate) fn roots(&self) -> usize {
        self.field.nodes()
    }
    pub(crate) fn members(&self) -> usize {
        self.materials.len()
    }
    pub(crate) fn passages(&self) -> u64 {
        self.generations
    }
    pub(crate) fn observations(&self) -> Option<u64> {
        Some(self.observations)
    }
    pub(crate) fn pending(&self) -> usize {
        self.pending.len()
    }
    pub(crate) fn pending_ids(&self) -> Vec<u64> {
        self.pending.keys().copied().collect()
    }
    pub(crate) fn release(&mut self, id: u64) -> Result<(), NativeSessionError> {
        self.pending
            .remove(&id)
            .ok_or_else(|| invalid("unknown incident producing comparison"))?;
        Ok(())
    }
    pub(crate) fn inspect(&mut self) -> Result<Value, NativeSessionError> {
        let source = self.field.read_current_source()?;
        Ok(
            json!({"scope":"incident-field-joint","epoch":self.epoch,"generations":self.generations,
            "joint":source.enclosure().inspect()?,"boundary_components":source.boundary_components(),
            "internal_components":source.internal_components(),"sites":self.layout.sites.len()}),
        )
    }
    pub(crate) fn inspect_material(&self, member: usize) -> Result<Value, NativeSessionError> {
        let material = self
            .materials
            .get(member)
            .ok_or_else(|| invalid("incident material owner"))?;
        Ok(json!({"scope":"incident-field-joint","owner":member,"material":material.inspect()?}))
    }
    pub(crate) fn prepare(
        &mut self,
        boundary: ResidentNormalEnclosureView<'_, 'c>,
        held: &[bool],
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        let admitted = self
            .layout
            .sites
            .iter()
            .map(|s| vec![true; s.sources.len()])
            .collect();
        Ok(NativeIncidentGenerated {
            word: Rc::new(self.word(boundary, held, admitted)?),
            comparison: None,
        })
    }
    pub(crate) fn publish(
        &mut self,
        mut generated: NativeIncidentGenerated<'c>,
        commit: bool,
        retain: bool,
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        if generated.comparison.is_some()
            || generated.word.epoch != self.epoch
            || generated.word.solver != self.spec.solver
            || generated.word.solve_steps != self.spec.solve_steps
        {
            return Err(invalid("stale or already retained incident generation"));
        }
        let next_id = if retain {
            self.next_comparison
                .checked_add(1)
                .ok_or_else(|| invalid("incident comparison exhausted"))?
        } else {
            self.next_comparison
        };
        let generations = if commit {
            self.generations
                .checked_add(1)
                .ok_or_else(|| invalid("incident generation exhausted"))?
        } else {
            self.generations
        };
        let staged = if commit {
            let last = generated
                .word
                .steps
                .last()
                .ok_or_else(|| invalid("empty incident word"))?;
            let reflection = generated.word.solver.action(
                &generated.word.source,
                last.input.view(),
                generated.word.solve_steps,
            )?;
            Some(self.field.prepare_joint_current_commit_from_action(
                &reflection,
                generated.word.output.view(),
            )?)
        } else {
            None
        };
        if let Some(staged) = staged {
            self.field.commit_joint_current(staged)?;
        }
        if retain {
            generated.comparison = Some(self.next_comparison);
            self.pending
                .insert(self.next_comparison, Rc::clone(&generated.word));
        }
        self.next_comparison = next_id;
        self.generations = generations;
        Ok(generated)
    }
    fn evaluate(
        &self,
        source: &NativeFieldCurrentSource<'c>,
        material: &[ResidentNormalMaterialView<'c>],
        anchor: &ResidentNormalEnclosure<'c>,
        held: &[bool],
        admitted: &[Vec<bool>],
    ) -> Result<(Vec<IncidentStep<'c>>, ResidentNormalEnclosure<'c>), NativeSessionError> {
        let layout = &self.layout;
        if admitted.len() != layout.sites.len()
            || admitted
                .iter()
                .zip(&layout.sites)
                .any(|(a, s)| a.len() != s.sources.len() || !a.iter().any(|v| *v))
        {
            return Err(invalid("incident admitted contact restrictions"));
        }
        let boundary = source.boundary_components();
        let mut current = anchor.view().to_owned()?;
        let anchor_section = anchor.view().as_section()?;
        let groups = layout.groups(admitted);
        let mut steps = Vec::with_capacity(layout.steps);
        for _ in 0..layout.steps {
            let q = current
                .view()
                .restrict(0..boundary)?
                .view()
                .split_rows(layout.sites.len(), layout.width)?;
            let mut sites = Vec::with_capacity(groups.len());
            let mut incoming: Option<ResidentNormalEnclosureSection<'c>> = None;
            for group in &groups {
                let rows = group.receivers.len();
                let query =
                    Rc::new(q.gather_phase_rows(&group.receivers, &phases(rows), layout.width)?);
                let neighbors =
                    Rc::new(q.gather_phase_rows(&group.sources, &group.phases, layout.width)?);
                let phase = query.clone().phase_participation(
                    neighbors,
                    group.neighbors,
                    layout.beta,
                    SeriesAperture(layout.series),
                )?;
                let condition = if group.differences == 0 {
                    None
                } else {
                    let u = q.gather_phase_rows(
                        &group.difference_sources,
                        &group.difference_phases,
                        layout.width,
                    )?;
                    let neg_q = query.gather_phase_rows(
                        &group.query_repeats,
                        &vec![opposite(); group.query_repeats.len()],
                        layout.width,
                    )?;
                    let delta = u
                        .sum_same_shape(&neg_q)?
                        .pack_components(group.differences)?;
                    let zero_condition = zero(
                        self.field.surface(),
                        rows,
                        delta.components(),
                        delta.grain(),
                    )?;
                    Some(delta.held_refinement(&zero_condition, &group.condition_held, 0)?)
                };
                let features = match &condition {
                    Some(c) => query.bilinear_enclosed_features(c)?,
                    None => ResidentNormalEnclosureSection::concatenate_rows(&[&query])?,
                };
                let reaction = material[group.material].read_applied_enclosed_section(&features)?;
                let scattered = phase
                    .output()
                    .sum_same_shape(&reaction)?
                    .scatter_phase_adjoint(&group.receivers, &phases(rows), layout.sites.len())?;
                incoming = Some(match incoming {
                    Some(previous) => previous.sum_same_shape(&scattered)?,
                    None => scattered,
                });
                sites.push(IncidentSiteStep {
                    group: Rc::clone(group),
                    query,
                    phase,
                    condition,
                    features,
                });
            }
            let a = incoming
                .ok_or_else(|| invalid("incident field has no material group"))?
                .pack_components(layout.sites.len())?
                .row(0)?
                .to_owned()?;
            let input = if source.internal_components() == 0 {
                a
            } else {
                a.view().join(
                    current
                        .view()
                        .restrict(boundary..boundary + source.internal_components())?
                        .view(),
                )?
            };
            let reflection =
                self.spec
                    .solver
                    .action(source, input.view(), self.spec.solve_steps)?;
            current = reflection
                .output()
                .as_section()?
                .held_refinement(&anchor_section, held, layout.relaxation_bits)?
                .row(0)?
                .to_owned()?;
            steps.push(IncidentStep { sites, input });
        }
        Ok((steps, current))
    }

    fn pull_back(
        &self,
        word: &IncidentWord<'c>,
        output_covector: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<IncidentPullback<'c>, NativeSessionError> {
        let layout = &self.layout;
        let boundary = word.source.boundary_components();
        let joint = boundary + word.source.internal_components();
        let grain = word.anchor.view().grain();
        if output_covector.components() != joint || output_covector.grain() != grain {
            return Err(invalid("incident full joint covector chart"));
        }
        let zero_joint = zero(self.field.surface(), 1, joint, grain)?;
        let mut gradient = output_covector.as_section()?;
        let mut anchor_gradient = zero(self.field.surface(), 1, joint, grain)?;
        let mut material = (0..self.materials.len())
            .map(|_| Vec::new())
            .collect::<Vec<_>>();
        let mut contacts = Vec::with_capacity(word.steps.len());
        for step in word.steps.iter().rev() {
            // The anchor includes b_pre. Its contribution is present at every stage.
            let anchor_part =
                zero_joint.held_refinement(&gradient, &word.held, layout.relaxation_bits)?;
            anchor_gradient = anchor_gradient.sum_same_shape(&anchor_part)?;
            let returned =
                gradient.held_refinement(&zero_joint, &word.held, layout.relaxation_bits)?;
            let full = returned.row(0)?;
            // S_D is self-adjoint under the declared unit pairing. This includes g_b_ref.
            let reflection = word.solver.action(&word.source, full, word.solve_steps)?;
            let incoming_covector = reflection.output();
            let ga = incoming_covector
                .restrict(0..boundary)?
                .view()
                .split_rows(layout.sites.len(), layout.width)?;
            let mut previous = zero(
                self.field.surface(),
                layout.sites.len(),
                layout.width,
                grain,
            )?;
            for stage in &step.sites {
                let group = &stage.group;
                let rows = group.receivers.len();
                let g = ga.gather_phase_rows(&group.receivers, &phases(rows), layout.width)?;
                let gf = word.material[group.material].pull_back_enclosed_section(&g)?;
                let (gq, gdelta) = match &stage.condition {
                    Some(c) => {
                        let (q, c) = stage.query.bilinear_enclosed_pullback(c, &gf)?;
                        (q, Some(c))
                    }
                    None => (gf, None),
                };
                let phase = stage.phase.pull_back(&g, None)?;
                let mut query = gq.sum_same_shape(phase.query())?;
                previous = previous.sum_same_shape(
                    &phase.transported_neighbors().scatter_phase_adjoint(
                        &group.sources,
                        &group.phases,
                        layout.sites.len(),
                    )?,
                )?;
                if let Some(delta) = gdelta {
                    let zero_condition = zero(
                        self.field.surface(),
                        rows,
                        delta.components(),
                        delta.grain(),
                    )?;
                    let parts = delta
                        .held_refinement(&zero_condition, &group.condition_held, 0)?
                        .split_components(group.differences)?;
                    query = query.sum_same_shape(&parts.scatter_phase_adjoint(
                        &group.query_repeats,
                        &vec![opposite(); parts.rows()],
                        rows,
                    )?)?;
                    previous = previous.sum_same_shape(&parts.scatter_phase_adjoint(
                        &group.difference_sources,
                        &group.difference_phases,
                        layout.sites.len(),
                    )?)?;
                }
                previous = previous.sum_same_shape(&query.scatter_phase_adjoint(
                    &group.receivers,
                    &phases(rows),
                    layout.sites.len(),
                )?)?;
                material[group.material].push((
                    ResidentNormalEnclosureSection::concatenate_rows(&[&stage.features])?,
                    g,
                ));
            }
            let q = previous
                .pack_components(layout.sites.len())?
                .row(0)?
                .to_owned()?;
            gradient = if word.source.internal_components() == 0 {
                q.view().as_section()?
            } else {
                q.view()
                    .join(incoming_covector.restrict(boundary..joint)?.view())?
                    .view()
                    .as_section()?
            };
            // These are unscaled producing derivatives. The material transaction applies sigma once.
            contacts.push((step.input.view().to_owned()?, full.to_owned()?));
        }
        Ok(IncidentPullback {
            anchor: anchor_gradient
                .sum_same_shape(&gradient)?
                .row(0)?
                .to_owned()?,
            material,
            contacts,
        })
    }
}

impl<'c> NativeCoupledBody<'c> {
    pub fn prepare_incident_material_return(
        &mut self,
        id: u64,
        output_covector: ResidentNormalEnclosureView<'_, 'c>,
        step_bits: u32,
    ) -> Result<NativeIncidentMaterialReturn<'c>, NativeSessionError> {
        use holonic_engine::native_ecology::constitutive_fibre::NativeContactRealization;
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid("incident return requires its model chart"));
        };
        if step_bits > 120 {
            return Err(invalid("incident material return scale"));
        }
        let word = Rc::clone(
            model
                .pending
                .get(&id)
                .ok_or_else(|| invalid("unknown incident comparison"))?,
        );
        let next_epoch = model
            .epoch
            .checked_add(1)
            .ok_or_else(|| invalid("incident material epoch exhausted"))?;
        let observations = model
            .observations
            .checked_add(1)
            .ok_or_else(|| invalid("incident observation count exhausted"))?;
        let returned = model.pull_back(&word, output_covector)?;
        let mut material = Vec::with_capacity(model.materials.len());
        for (current, rows) in model.materials.iter().zip(&returned.material) {
            let features = ResidentNormalEnclosureSection::concatenate_rows(
                &rows.iter().map(|r| &r.0).collect::<Vec<_>>(),
            )?;
            let covectors = ResidentNormalEnclosureSection::concatenate_rows(
                &rows.iter().map(|r| &r.1).collect::<Vec<_>>(),
            )?;
            material.push(current.stage_covector_return(&features, &covectors, step_bits)?);
        }
        let contact = if word.source.internal_components() == 0 {
            None
        } else {
            let actions = returned
                .contacts
                .iter()
                .map(|(input, _)| {
                    word.solver
                        .action(&word.source, input.view(), word.solve_steps)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let pullbacks = actions
                .iter()
                .zip(&returned.contacts)
                .map(|(action, (_, g))| action.pullback_full_auto(g.view(), word.solve_steps))
                .collect::<Result<Vec<_>, _>>()?;
            Some(model.field.prepare_global_action_material_return(
                &pullbacks.iter().collect::<Vec<_>>(),
                step_bits,
                NativeContactRealization::DyadicDeposit,
            )?)
        };
        Ok(NativeIncidentMaterialReturn {
            comparison: id,
            epoch: model.epoch,
            next_epoch,
            observations,
            anchor: returned.anchor,
            material,
            contact,
        })
    }
    /// Publish prepared material only. The continuing q/b endpoint remains the latest generation.
    pub fn publish_incident_material_return(
        &mut self,
        prepared: NativeIncidentMaterialReturn<'c>,
    ) -> Result<(), NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid("incident return requires its model chart"));
        };
        if prepared.epoch != model.epoch || !model.pending.contains_key(&prepared.comparison) {
            return Err(invalid("stale incident material publication"));
        }
        if let Some(contact) = prepared.contact {
            model.field.commit_global_action_material_return(contact)?;
        }
        model.materials = prepared.material;
        model.epoch = prepared.next_epoch;
        model.observations = prepared.observations;
        model.pending.remove(&prepared.comparison);
        Ok(())
    }
    /// Found the declared incidence action D=B_U* with unit contact amplitudes. This creates
    /// physical contact columns, without creating a source observation or a priming event.
    pub fn found_incident_field(
        surface: &'c ResidentSurface<'c>,
        spec: IncidentFieldSpec,
        grain: ResidentGrain,
    ) -> Result<Self, NativeSessionError> {
        use holonic_engine::native_ecology::constitutive_fibre::{
            NativeFieldContactOrigin, NativeFieldDeclaredIncidence, NativeJunctionSeed,
            NativePhaseCurrent,
        };
        use num_traits::{ToPrimitive, Zero};
        let layout = spec.compile()?;
        let nodes = layout
            .sites
            .len()
            .checked_mul(spec.local_roots)
            .ok_or_else(|| invalid("incident root extent"))?;
        let boundary = layout
            .width
            .checked_mul(layout.sites.len())
            .ok_or_else(|| invalid("incident boundary extent"))?;
        let contacts = layout
            .sites
            .iter()
            .map(|s| s.differences.len())
            .sum::<usize>()
            .checked_mul(layout.width / 2)
            .ok_or_else(|| invalid("incident contact extent"))?;
        // The declared columns each have at most two complex entries. Their CSR source
        // retains the oriented incidence; no dense boundary-by-contact chart is formed.
        let max_nonzeros = contacts
            .checked_mul(2)
            .ok_or_else(|| invalid("incident sparse map extent"))?;
        // These packets live in device global memory. Their allocation is charged by
        // ResidentSurface; the per-block shared-memory aperture does not bound this map.
        max_nonzeros
            .checked_mul(4)
            .and_then(|n| n.checked_mul(16))
            .ok_or_else(|| invalid("incident sparse map byte extent"))?;
        let seed = NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        let mut field =
            NativeConstitutiveField::found_incident_source_only(surface, vec![seed; nodes], grain)?;
        if contacts > 0 {
            if !(1..=120).contains(&grain.0) {
                return Err(invalid("incident declared map grain"));
            }
            let scale = num_bigint::BigInt::from(1u8) << grain.0;
            let mut offsets = Vec::with_capacity(contacts + 1);
            offsets.push(0i128);
            let mut columns = Vec::with_capacity(max_nonzeros);
            let mut values = Vec::with_capacity(max_nonzeros * 2);
            let mut origins = Vec::with_capacity(contacts);
            let mut round = 0i128;
            for (r, site) in layout.sites.iter().enumerate() {
                for &port in &site.differences {
                    let from = site.sources[port];
                    let phase = &site.phases[port];
                    let mut coordinate =
                        |x: &num_rational::BigRational| -> Result<i128, NativeSessionError> {
                            let numerator = x.numer() * &scale;
                            if !(&numerator % x.denom()).is_zero() {
                                round = round
                                    .checked_add(1)
                                    .ok_or_else(|| invalid("declared map enclosure radius"))?;
                            }
                            (numerator / x.denom())
                                .to_i128()
                                .ok_or_else(|| invalid("declared phase exceeds native map carrier"))
                        };
                    let re = coordinate(&phase.cosine)?;
                    let im = coordinate(&(-&phase.sine))?;
                    for channel in 0..layout.width / 2 {
                        let column = origins.len();
                        let source_address = from * layout.width + 2 * channel;
                        let receiver_address = r * layout.width + 2 * channel;
                        columns.push(source_address as i128);
                        if source_address == receiver_address {
                            values.extend([
                                re.checked_sub(1i128 << grain.0)
                                    .ok_or_else(|| invalid("declared incidence carrier"))?,
                                im,
                            ]);
                        } else {
                            values.extend([re, im]);
                            columns.push(receiver_address as i128);
                            values.extend([-(1i128 << grain.0), 0]);
                        }
                        offsets.push(columns.len() as i128);
                        origins.push(NativeFieldContactOrigin::declared(column, from, r));
                    }
                }
            }
            // Each rounded phase entry appears once per local channel.
            round = round
                .checked_mul((layout.width / 2) as i128)
                .ok_or_else(|| invalid("declared incidence radius"))?;
            let mount = |rows,
                         width,
                         values: Vec<i128>|
             -> Result<ResidentSection<'c>, NativeSessionError> {
                let intervals = values
                    .into_iter()
                    .flat_map(|v| [v as i64, (v >> 64) as i64])
                    .map(|v| (v, v))
                    .collect();
                Ok(surface
                    .mount_section_rest(
                        &ResidentSectionRest::found(rows, width, ResidentGrain(0), 64, intervals)
                            .map_err(invalid)?,
                    )
                    .map_err(invalid)?)
            };
            let nonzeros = columns.len();
            let mut transpose = vec![Vec::new(); boundary / 2];
            for contact in 0..contacts {
                for entry in offsets[contact] as usize..offsets[contact + 1] as usize {
                    transpose[columns[entry] as usize / 2].push((
                        contact,
                        values[2 * entry],
                        values[2 * entry + 1],
                    ));
                }
            }
            let mut transpose_offsets = Vec::with_capacity(boundary / 2 + 1);
            let mut transpose_rows = Vec::with_capacity(nonzeros);
            let mut transpose_values = Vec::with_capacity(2 * nonzeros);
            transpose_offsets.push(0i128);
            for row in transpose {
                for (contact, re, im) in row {
                    transpose_rows.push(contact as i128);
                    transpose_values.extend([re, im]);
                }
                transpose_offsets.push(transpose_rows.len() as i128);
            }
            field.register_declared_incidence(
                NativeFieldDeclaredIncidence {
                    row_offsets: mount(1, 2 * offsets.len(), offsets)?,
                    columns: mount(1, 2 * nonzeros, columns)?,
                    values: mount(1, 4 * nonzeros, values)?,
                    transpose_offsets: mount(1, 2 * transpose_offsets.len(), transpose_offsets)?,
                    transpose_rows: mount(1, 2 * nonzeros, transpose_rows)?,
                    transpose_values: mount(1, 4 * nonzeros, transpose_values)?,
                    // Rank zero has no factor entries. These slots are never interpreted.
                    left: mount(1, 2 * boundary, vec![0; boundary])?,
                    right: mount(1, 4 * contacts, vec![0; 2 * contacts])?,
                    defects: mount(1, 2, vec![0])?,
                    rows: contacts,
                    boundary_components: boundary,
                    rank: 0,
                    nonzeros,
                },
                mount(contacts, 4, vec![0; 2 * contacts])?,
                mount(1, 4, vec![round, 0])?,
                origins,
            )?;
        }
        Ok(Self {
            state: Some(BodyState::Incident(IncidentFieldModel::with_layout(
                field, spec, layout,
            )?)),
        })
    }
    pub fn incident_dimensions(
        &self,
    ) -> Result<(usize, usize, ResidentGrain, Vec<usize>), NativeSessionError> {
        match self.state()? {
            BodyState::Incident(model) => Ok((
                model.layout.sites.len(),
                model.layout.width,
                model.materials[0].grain(),
                model.layout.slot_rows.clone(),
            )),
            _ => Err(invalid("incident dimensions require their model chart")),
        }
    }
    pub fn incident_solver(&self) -> Result<(IncidentFieldSolver, usize), NativeSessionError> {
        match self.state()? {
            BodyState::Incident(model) => Ok((model.spec.solver, model.spec.solve_steps)),
            _ => Err(invalid("incident solver requires its model chart")),
        }
    }
    /// Read the small, typed comparison-bound packets without expanding the retained
    /// material factors into a boundary-by-contact matrix.
    pub fn inspect_incident_material_return_bounds(&self) -> Result<Value, NativeSessionError> {
        match self.state()? {
            BodyState::Incident(model) => {
                let count = model
                    .field
                    .operative_return_storage()
                    .map_or(0, |s| s.returns);
                let bounds = (0..count)
                    .map(|at| model.field.inspect_contact_deposit_bound(at))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(json!(bounds))
            }
            _ => Err(invalid(
                "incident material returns require their model chart",
            )),
        }
    }
    /// Change only the numerical solve on a model with no outstanding producing comparisons.
    /// Material and continuing q/b are retained. New checkpoints record the selected proposal.
    pub fn configure_incident_solver(
        &mut self,
        solver: IncidentFieldSolver,
        steps: usize,
    ) -> Result<(), NativeSessionError> {
        if steps == 0 || steps > u32::MAX as usize {
            return Err(invalid("incident solve resource aperture"));
        }
        match self.state_mut()? {
            BodyState::Incident(model) if model.pending.is_empty() => {
                model.spec.solver = solver;
                model.spec.solve_steps = steps;
                Ok(())
            }
            BodyState::Incident(_) => Err(invalid(
                "retain the producing solver until pending comparisons return",
            )),
            _ => Err(invalid("incident solver requires its model chart")),
        }
    }
    pub fn incident_current_boundary(
        &mut self,
    ) -> Result<ResidentNormalEnclosure<'c>, NativeSessionError> {
        match self.state_mut()? {
            BodyState::Incident(model) => {
                let source = model.field.read_current_source()?;
                Ok(source
                    .enclosure()
                    .restrict(0..source.boundary_components())?)
            }
            _ => Err(invalid("incident current requires its model chart")),
        }
    }
    pub fn incident_comparison(
        &self,
        id: u64,
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        match self.state()? {
            BodyState::Incident(model) => Ok(NativeIncidentGenerated {
                word: Rc::clone(
                    model
                        .pending
                        .get(&id)
                        .ok_or_else(|| invalid("unknown incident comparison"))?,
                ),
                comparison: Some(id),
            }),
            _ => Err(invalid("incident comparison requires its model chart")),
        }
    }
    /// Restrict source-to-source participation and difference ports by the actual ordered
    /// source cells and recorded joins. Other declared physical contacts retain their scope.
    pub fn prepare_incident_field_restricted(
        &mut self,
        boundary: ResidentNormalEnclosureView<'_, 'c>,
        held: &[bool],
        source_sites: &[usize],
        contacts: &[(usize, usize)],
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid(
                "incident source restriction requires its model chart",
            ));
        };
        let sources = source_sites
            .iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
        if sources.len() != source_sites.len()
            || sources.iter().any(|r| *r >= model.layout.sites.len())
        {
            return Err(invalid("incident source-cell site restriction"));
        }
        let contacts = contacts
            .iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
        for &(from, to) in &contacts {
            if !sources.contains(&from)
                || !sources.contains(&to)
                || !model.layout.sites[to].sources.contains(&from)
            {
                return Err(invalid(
                    "recorded source contact is outside the declared field incidence",
                ));
            }
        }
        let admitted = model
            .layout
            .sites
            .iter()
            .enumerate()
            .map(|(r, site)| {
                site.sources
                    .iter()
                    .zip(&site.phases)
                    .map(|(&s, p)| {
                        (s == r && *p == ExactWavePhaseTransport::identity())
                            || !sources.contains(&r)
                            || !sources.contains(&s)
                            || contacts.contains(&(s, r))
                    })
                    .collect()
            })
            .collect();
        Ok(NativeIncidentGenerated {
            word: Rc::new(model.word(boundary, held, admitted)?),
            comparison: None,
        })
    }
    pub fn from_incident_field(
        field: NativeConstitutiveField<'c>,
        spec: IncidentFieldSpec,
    ) -> Result<Self, NativeSessionError> {
        Ok(Self {
            state: Some(BodyState::Incident(IncidentFieldModel::new(field, spec)?)),
        })
    }
    pub fn prepare_incident_field(
        &mut self,
        boundary: ResidentNormalEnclosureView<'_, 'c>,
        held: &[bool],
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        match self.state_mut()? {
            BodyState::Incident(model) => model.prepare(boundary, held),
            _ => Err(invalid(
                "incident operation requires its declared model chart",
            )),
        }
    }
    pub fn publish_incident_field(
        &mut self,
        generated: NativeIncidentGenerated<'c>,
        commit: bool,
        retain_comparison: bool,
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        match self.state_mut()? {
            BodyState::Incident(model) => model.publish(generated, commit, retain_comparison),
            _ => Err(invalid(
                "incident operation requires its declared model chart",
            )),
        }
    }
}
