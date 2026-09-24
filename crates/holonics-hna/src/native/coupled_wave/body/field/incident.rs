//! Incident-conditioned finite word on one global constitutive field.
mod machine;
mod machine_episode;
mod machine_receiving;
mod machine_source;
mod machine_source_contacts;
use machine_episode::{GeneratorSourceMoment, RetainedComparison};
#[allow(unused_imports)] // named by session consumers through the body's methods
pub use machine_episode::{GeneratorMomentHolon, GeneratorSourceMomentMeta};
pub use machine_source::GeneratorSourceBinding;
pub use machine_source_contacts::{GeneratorSourceContact, GeneratorSourceContactKind};
mod machine_transport;
pub use machine_receiving::{
    GeneratorPhasePort, GeneratorPhaseReceiverBinding, NativeGeneratorPhaseReception,
};
mod energy;
mod rest;
pub use energy::IncidentEnergyBalance;
mod holon_chart;
#[allow(unused_imports)] // the phase-8 chart; named by its conformance tests and future consumers
pub use holon_chart::{ResidentHolonChart, RingReaction};
pub use machine::GeneratorIncidentFieldSpec;
use machine::{IncidentModelSpec, MachineGroupMaps};
use machine_transport::{MachineParticipation, MachineValueTransport};
#[cfg(test)]
mod machine_tests;
#[cfg(test)]
#[path = "incident_tests.rs"]
mod tests;
use super::*;
use crate::native::field_geometry::GeometricFieldSpec;
use holonic_engine::{
    ExactWavePhaseTransport,
    native_ecology::constitutive_fibre::{
        NativePairParticipation, NativePhaseParticipation, ResidentNormalEnclosureSection,
        ResidentNormalMaterial, ResidentNormalMaterialView,
    },
    resident_section::{Dyadic, SeriesAperture},
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

/// The receiving chart used to compare current rows. The quadrance arm keeps varying
/// self-energies and both geometric/value covectors. A full screw/configuration chart must
/// additionally provide its maps; this arm does not label arbitrary currents as screw phases.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum IncidentParticipationChart {
    #[default]
    Bilinear,
    /// Explicit same-source chart: score=-beta*|q-Uq_i|²/2, value=Uq_i.
    /// Its neighbor receives the sum of geometric and value covectors. This is a current
    /// specialization; a spatial generator chart additionally supplies its configuration maps.
    QuadranceCurrent,
}
impl IncidentParticipationChart {
    pub(crate) fn is_bilinear(&self) -> bool {
        *self == Self::Bilinear
    }
}

/// [definition; agent-inferred] The declared law of the learned reaction `M Φ(s,c)`.
/// `Legacy` reads the complex-bilinear `Φ = s ⊕ c ⊕ (c ⊗ s)` and deposits the normal-law solve
/// as is. `PowerNeutral` reads `Φ = s ⊕ c ⊕ (c_r s)_r` over the real coordinates of `c` and, after
/// every deposit, holds each modulated slice exactly skew-Hermitian (`Re⟨s, J(c)s⟩ = 0` for every
/// admitted `c`) and the linear self-relation passive (its Hermitian part is the resistive
/// element); the contrast coupling is kept under the declared skew return of the joint port
/// relation (`ResidentNormalMaterial::project_power_neutral_reaction`). A complex-bilinear block
/// cannot be power-neutral for all complex `c` (`Holon/Reaction.lean::
/// bilinear_reaction_workless_iff_zero`). An absent field is `Legacy`, so saved wires keep their
/// law; new generator declarations state `PowerNeutral`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ReactionLaw {
    #[default]
    Legacy,
    PowerNeutral,
}
impl ReactionLaw {
    pub(crate) fn is_legacy(&self) -> bool {
        *self == Self::Legacy
    }
    /// Complex feature count for `n` complex current coordinates and `c` complex contrast
    /// coordinates.
    pub(crate) fn features(self, n: usize, c: usize) -> Option<usize> {
        let products = match self {
            Self::Legacy => n.checked_mul(c)?,
            Self::PowerNeutral => n.checked_mul(c)?.checked_mul(2)?,
        };
        n.checked_add(c)?.checked_add(products)
    }
}

/// The fixed-size receipt of the power-neutral deposits: count, the latest projection and running
/// sums/maxima of what the projections removed. A reading, never a gate. The deposit ledger of the
/// Holon balance (`holonic_core::deposition::DepositLedger`) is recorded against the current's
/// declared unit storage pairing, which a reaction deposit does not change: each such deposit has
/// `ε = 0` exactly, so its product stays `1`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReactionDepositRecord {
    pub deposits: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last:
        Option<Vec<holonic_engine::native_ecology::constitutive_fibre::NormalReactionProjection>>,
    /// `Σ` over deposits and owners of the removed slice Hermitian parts `‖·‖_F²`.
    pub bilinear_removed_square_sum: relational_geometry::Rat,
    /// `max` over deposits and owners of the linear removed rank.
    pub linear_removed_rank_max: usize,
    /// `Σ` of the linear removed traces.
    pub linear_removed_trace_sum: relational_geometry::Rat,
    /// `Σ ‖removed‖₁` over deposits and owners.
    pub removed_l1_sum: relational_geometry::Rat,
    /// Storage `ε` of each reaction deposit against the unit pairing (exactly zero) and the
    /// ledger product `∏(1 + ε_k)`.
    pub storage_epsilon: relational_geometry::Rat,
    pub ledger_product: relational_geometry::Rat,
}
impl ReactionDepositRecord {
    pub(crate) fn is_empty(&self) -> bool {
        self.deposits == 0
    }
    fn record(
        &mut self,
        projections: Vec<
            holonic_engine::native_ecology::constitutive_fibre::NormalReactionProjection,
        >,
    ) -> Result<(), NativeSessionError> {
        use num_traits::One;
        if self.deposits == 0 {
            self.ledger_product = relational_geometry::Rat::one();
        }
        self.deposits = self
            .deposits
            .checked_add(1)
            .ok_or_else(|| invalid("reaction deposit count"))?;
        for p in &projections {
            self.bilinear_removed_square_sum += &p.bilinear_removed_square;
            self.linear_removed_rank_max = self.linear_removed_rank_max.max(p.linear_removed_rank);
            self.linear_removed_trace_sum += &p.linear_removed_trace;
            self.removed_l1_sum += &p.removed_l1;
        }
        // Unit storage pairing: Q_(k+1) = Q_k, certified with ε = 0.
        let unit = holonic_core::inertia::SymmetricForm::from_diagonal(vec![
            relational_geometry::Rat::one();
            1
        ]);
        holonic_core::deposition::DepositLedger::certify_deposit(
            &unit,
            &unit,
            &self.storage_epsilon,
        )
        .map_err(invalid)?;
        self.ledger_product =
            &self.ledger_product * (relational_geometry::Rat::one() + &self.storage_epsilon);
        self.last = Some(projections);
        Ok(())
    }
}

/// A declared local chart and material ownership on the existing geometric field.
/// Equal degree does not imply shared material: sharing is supplied explicitly by this chart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IncidentFieldSpec {
    pub geometry: GeometricFieldSpec,
    #[serde(
        default,
        skip_serializing_if = "IncidentParticipationChart::is_bilinear"
    )]
    pub participation: IncidentParticipationChart,
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
    /// Machine admitted-arc index per port; None is a self comparison.
    machine_arcs: Vec<Option<usize>>,
}
#[derive(Clone)]
struct IncidentLayout {
    machine: Option<Rc<crate::native::field_geometry::machine::CompiledGeneratorMachine>>,
    sites: Vec<IncidentSite>,
    slot_rows: Vec<usize>,
    width: usize,
    source_condition_ports: usize,
    material_features: Vec<usize>,
    beta: Dyadic,
    participation: IncidentParticipationChart,
    series: u32,
    steps: usize,
    relaxation_bits: u32,
    reaction: ReactionLaw,
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
    machine_arcs: Vec<Option<usize>>,
    difference_arcs: Vec<Option<usize>>,
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
                    machine_arcs: vec![],
                    difference_arcs: vec![],
                };
                for (row, &r) in group.receivers.iter().enumerate() {
                    let site = &self.sites[r];
                    for (port, &source) in site.sources.iter().enumerate() {
                        if admitted[r][port] {
                            group.sources.push(source);
                            group.phases.push(site.phases[port].clone());
                            if !site.machine_arcs.is_empty() {
                                group.machine_arcs.push(site.machine_arcs[port]);
                            }
                        }
                    }
                    for &port in &site.differences {
                        group.difference_sources.push(site.sources[port]);
                        group.difference_phases.push(site.phases[port].clone());
                        if !site.machine_arcs.is_empty() {
                            group.difference_arcs.push(site.machine_arcs[port]);
                        }
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
        if self.participation == IncidentParticipationChart::QuadranceCurrent
            && (self.geometry.beta_significand < 0 || self.geometry.beta_exponent == i32::MIN)
        {
            return Err(invalid(
                "quadrance participation requires a nonnegative admitted scale",
            ));
        }
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
                    machine_arcs: vec![],
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
            machine: None,
            sites,
            slot_rows: geometry.slot_rows,
            width,
            source_condition_ports: 0,
            material_features: features,
            reaction: ReactionLaw::Legacy,
            participation: self.participation,
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
    phase: IncidentParticipationForward<'c>,
    condition: Option<ResidentNormalEnclosureSection<'c>>,
    external_condition: Option<ResidentNormalEnclosureSection<'c>>,
    machine_difference: Option<MachineValueTransport<'c>>,
    features: ResidentNormalEnclosureSection<'c>,
    /// The power-neutral law's implicit reaction stage; `None` under the legacy law.
    cayley: Option<CayleyStage<'c>>,
}
/// [definition; agent-inferred] The Cayley (implicit-midpoint) reaction stage of one group.
/// The reaction acts on the participation drive `p` as the modulated skew interconnection
/// `J(c)` with the resistive part of `W_s` and the contrast port `W_c c`:
/// `(I − K(c)/2) y = (I + K(c)/2) p + W_c c`, `K(c) = W_s + Σ_r c_r A_r`, and `y` (not
/// `p + W Φ(q, c)`) is the site's incoming current. [agent-inferred] The drive, not the standing
/// query, is what the step carries: then `|y|² − |p|² = −2⟨x̄, R x̄⟩ + 2 Re⟨x̄, W_c c⟩` exactly
/// (`Holon/Cayley.lean::midpoint_reaction_balance`), gain exactly `1` on the drive whatever
/// `|Δ|` (`Holon/Cayley.lean::cayley_isometry`), whereas carrying the query would leave
/// `p − q` outside the isometry. The standing current still enters through the contrast `Δ`
/// (which modulates `J`) and through participation. The explicit law's gain `1 + h²|J x|²/|x|²`
/// (`Holon/Cayley.lean::explicit_step_growth`) is what this replaces.
struct CayleyStage<'c> {
    certificate: holonic_engine::native_ecology::constitutive_fibre::PowerNeutralCertificate<'c>,
    step: ResidentNormalEnclosureSection<'c>,
    midpoint: ResidentNormalEnclosureSection<'c>,
}
enum IncidentParticipationForward<'c> {
    Bilinear(NativePhaseParticipation<'c>),
    Quadrance(NativePairParticipation<'c>),
    Machine(MachineParticipation<'c>),
}
impl<'c> IncidentParticipationForward<'c> {
    fn output(&self) -> &ResidentNormalEnclosureSection<'c> {
        match self {
            Self::Bilinear(p) => p.output(),
            Self::Quadrance(p) => p.output(),
            Self::Machine(p) => p.output(),
        }
    }
    #[cfg(test)]
    fn transported_neighbors(&self) -> &ResidentNormalEnclosureSection<'c> {
        match self {
            Self::Bilinear(p) => p.transported_neighbors(),
            Self::Quadrance(p) => p.values(),
            Self::Machine(p) => p.values(),
        }
    }
    fn pull_back(
        &self,
        gy: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<
        (
            ResidentNormalEnclosureSection<'c>,
            ResidentNormalEnclosureSection<'c>,
        ),
        NativeSessionError,
    > {
        match self {
            Self::Machine(_) => Err(invalid(
                "machine participation returns through its distinct charts",
            )),
            Self::Bilinear(p) => Ok(p.pull_back(gy, None)?.into_parts()),
            Self::Quadrance(p) => {
                let (query, neighbors, values) = p.pull_back(gy, None)?.into_parts();
                // The serialized QuadranceCurrent chart declares one source in both roles.
                Ok((query, neighbors.sum_same_shape(&values)?))
            }
        }
    }
}

struct IncidentStep<'c> {
    sites: Vec<IncidentSiteStep<'c>>,
    input: ResidentNormalEnclosure<'c>,
    /// The step's current before (`q`), the projected reflection `S_D(input)` and the relaxed
    /// current after it: exterior readings of the energy balance, never operands of the return.
    before: Rc<ResidentNormalEnclosure<'c>>,
    reflected: ResidentNormalEnclosure<'c>,
}
pub(crate) struct IncidentWord<'c> {
    /// Ordered-source Holon of a generator word (declaration and moment `m`); the anchor is
    /// `P((L^N q₀ + m) ⊕ b₀)` at the cut this word was evaluated at.
    source_moment: Option<GeneratorSourceMoment<'c>>,
    /// The boundary a prepared word was supplied (`prepare_incident_field*`): the operand a
    /// retained comparison of this word keeps. `None` for a passage or a received moment.
    boundary: Option<Rc<ResidentNormalEnclosure<'c>>>,
    external_condition: Option<Rc<ResidentNormalEnclosureSection<'c>>>,
    machine: Option<Rc<crate::native::field_geometry::machine::CompiledGeneratorMachine>>,
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
    enclosure_propagation:
        holonic_engine::native_ecology::constitutive_fibre::NativeEnclosurePropagation,
}
/// A prepared complete joint section. Receiving faces and pending storage are prepared before
/// this immutable word is committed to the continuing body.
pub struct NativeIncidentGenerated<'c> {
    word: Rc<IncidentWord<'c>>,
    comparison: Option<u64>,
}
pub struct NativeIncidentMaterialReturn<'c> {
    /// The reaction deposit receipt this return publishes (unchanged under the legacy law).
    reaction: ReactionDepositRecord,
    /// The certificates of the projected cuts (power-neutral law), installed with them.
    reaction_certificates: Vec<
        Option<holonic_engine::native_ecology::constitutive_fibre::PowerNeutralCertificate<'c>>,
    >,
    contact_amplitude: Option<
        holonic_engine::native_ecology::constitutive_fibre::NativeDeclaredAmplitudeCommit<'c>,
    >,
    source_covector: Option<ResidentNormalEnclosureSection<'c>>,
    symbol_covector: Option<ResidentNormalEnclosureSection<'c>>,
    moment_covector: Option<ResidentNormalEnclosure<'c>>,
    condition_covector: Option<ResidentNormalEnclosureSection<'c>>,
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
    /// The reaction deposit receipt, including this return's projections.
    pub fn reaction_deposits(&self) -> &ReactionDepositRecord {
        &self.reaction
    }
    /// One relative-amplitude cotangent per pair arc, using the old producing field
    /// variation and the contemporary pair basis. Publication installs its positive proposal.
    pub fn contact_scale_covector(&self) -> Option<&ResidentNormalEnclosureSection<'c>> {
        self.contact_amplitude.as_ref().map(|p| p.gradient())
    }
    pub fn contact_amplitude_proposal(
        &self,
    ) -> Option<
        &holonic_engine::native_ecology::constitutive_fibre::NativeDeclaredAmplitudeCommit<'c>,
    > {
        self.contact_amplitude.as_ref()
    }
    /// Ordered original complex source rows returned through every ingestion/refinement stage.
    pub fn source_covector(&self) -> Option<&ResidentNormalEnclosureSection<'c>> {
        self.source_covector.as_ref()
    }
    pub fn anchor_covector(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.anchor.view()
    }
    /// Symbol passage: the encoder-table covector `|A| × 6S`,
    /// `g_E(a)|_i = C_(a,i)ᵀ g_m(s_i) + Σ_p D_(p,a,i)ᵀ g_(c,p)(s_i)`.
    pub fn symbol_covector(&self) -> Option<&ResidentNormalEnclosureSection<'c>> {
        self.symbol_covector.as_ref()
    }
    /// Generator word: `g_m`, the covector at the accumulated anchor `L^N q₀ + m` (joint
    /// chart), before the standing adjoint `(L^N)*`. It is the covector of the moment `m`.
    pub fn moment_covector(&self) -> Option<ResidentNormalEnclosureView<'_, 'c>> {
        self.moment_covector.as_ref().map(|m| m.view())
    }
    /// Generator word with condition ports: `g_c`, `G × 12P` (site rows, port blocks).
    pub fn condition_covector(&self) -> Option<&ResidentNormalEnclosureSection<'c>> {
        self.condition_covector.as_ref()
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
    spec: IncidentModelSpec,
    layout: IncidentLayout,
    materials: Vec<ResidentNormalMaterial<'c>>,
    epoch: u64,
    generations: u64,
    observations: u64,
    next_comparison: u64,
    /// Outstanding comparisons: each keeps its producing operands only (a prepared boundary or a
    /// passage's moment/condition with its declaration) and is read at the contemporary
    /// constitution when observed. Fixed in the passage length; no producing cut is retained.
    comparisons: BTreeMap<u64, Rc<RetainedComparison<'c>>>,
    /// Declared residual of the commits' rebases to their dyadic centres.
    rebase: IncidentRebaseResidual,
    /// Receipt of the power-neutral reaction deposits (empty under the legacy law).
    reaction_record: ReactionDepositRecord,
    /// Certificates of the power-neutral material cuts in force, bound to their resident states;
    /// filled lazily (one detachment per cut) and installed by each deposit's projection.
    reaction_certificates: std::cell::RefCell<
        Vec<
            Option<holonic_engine::native_ecology::constitutive_fibre::PowerNeutralCertificate<'c>>,
        >,
    >,
    /// The exterior energy balance of the latest committed power-neutral word.
    energy_balance: Option<IncidentEnergyBalance>,
    /// Test control only: publish the whole solve enclosure, as before the rebase law.
    #[cfg(test)]
    rebase_off: bool,
}

/// The residual family of committed-current rebases, fixed size. Commit `j` publishes the
/// dyadic centre `c_j` of its solve enclosure `B(c_j, r_j)` (which contains the exact solve
/// `x_j` of that commit's word, read at the published previous centre) and drops `r_j`, so
/// `‖c_j − x_j‖ ≤ r_j` in the enclosure's norm. Recorded: the count, the last, the running
/// maximum and the running sum of the dropped radii `r_j`, each exact as `n / 2^grain`.
/// Nothing claims `c_j = x_j`, and the sum is only the sum of dropped radii: it is not a
/// trajectory bound. The distance of the published centre from the exact unrebased
/// trajectory is `R_(i+1) ≤ K_i R_i + r_i` (`Objects/CommitRebase`: `Σ_i K^(n−1−i) r_i`), with
/// `K_i` a Lipschitz bound of commit `i`'s full incident word in `q₀`. No such bound is exposed
/// (`inspect_operator_bounds` bounds only the contact operator `D`, not the word with its
/// participation, reaction, projection and held relaxation), so that trajectory bound is owed.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IncidentRebaseResidual {
    pub commits: u64,
    pub grain: u32,
    /// Scaled integers, decimal: the radius value is `n / 2^grain`.
    pub last: String,
    pub max: String,
    pub sum: String,
}

impl IncidentRebaseResidual {
    fn is_empty(&self) -> bool {
        self.commits == 0
    }
    /// The propagated trajectory bound `R_(i+1) = K_i R_i + r_i` needs a Lipschitz bound `K_i`
    /// of the full incident word, which the field does not expose. Always `None` for now.
    pub fn trajectory_bound(&self) -> Option<relational_geometry::Rat> {
        None
    }
    fn scaled(value: &str) -> Result<num_bigint::BigInt, NativeSessionError> {
        if value.is_empty() {
            return Ok(num_bigint::BigInt::from(0u8));
        }
        value
            .parse::<num_bigint::BigInt>()
            .map_err(|_| invalid("rebase residual word"))
    }
    fn record(&mut self, radius: u128, grain: ResidentGrain) -> Result<(), NativeSessionError> {
        let grain = u32::from(grain.0);
        if self.commits != 0 && self.grain != grain {
            return Err(invalid("rebase residual grain changed"));
        }
        let radius = num_bigint::BigInt::from(radius);
        let max = Self::scaled(&self.max)?.max(radius.clone());
        let sum = Self::scaled(&self.sum)? + &radius;
        self.commits = self
            .commits
            .checked_add(1)
            .ok_or_else(|| invalid("rebase residual count"))?;
        self.grain = grain;
        self.last = radius.to_string();
        self.max = max.to_string();
        self.sum = sum.to_string();
        Ok(())
    }
    fn value(&self, word: &str) -> Result<relational_geometry::Rat, NativeSessionError> {
        Ok(relational_geometry::Rat::new(
            Self::scaled(word)?,
            num_bigint::BigInt::from(1u8) << self.grain,
        ))
    }
    /// `r` of the last commit.
    pub fn last_radius(&self) -> Result<relational_geometry::Rat, NativeSessionError> {
        self.value(&self.last)
    }
    /// `max_j r_j`.
    pub fn max_radius(&self) -> Result<relational_geometry::Rat, NativeSessionError> {
        self.value(&self.max)
    }
    /// `Σ_j r_j`: the sum of the dropped radii. Not a trajectory bound (see the type docs).
    pub fn sum_radius(&self) -> Result<relational_geometry::Rat, NativeSessionError> {
        self.value(&self.sum)
    }
}

/// Rebase a committed joint current to its dyadic centre at its grain: the same centre words
/// with a zero radius, and the dropped radius as the scaled integer `r·2^grain`. The rewrite is
/// on the sealed rest words (one row, host staged at the commit boundary).
fn rebase_to_centre<'c>(
    surface: &'c ResidentSurface<'c>,
    output: &ResidentNormalEnclosure<'c>,
) -> Result<(ResidentNormalEnclosure<'c>, u128), NativeSessionError> {
    let grain = output.view().grain();
    let mut rest = output.rest()?;
    let n = rest.intervals.len();
    if rest.rows != 1 || n < 2 || n != rest.width {
        return Err(invalid("rebase joint current chart"));
    }
    let (low, high) = (rest.intervals[n - 2], rest.intervals[n - 1]);
    if low.0 != low.1 || high.0 != high.1 {
        return Err(invalid("rebase requires a sealed radius word"));
    }
    let radius = (((high.0 as u64 as u128) << 64) | low.0 as u64 as u128) as i128;
    if radius < 0 {
        return Err(invalid("rebase radius sign"));
    }
    rest.intervals[n - 2] = (0, 0);
    rest.intervals[n - 1] = (0, 0);
    Ok((
        ResidentNormalEnclosure::remount(surface, rest, grain)?,
        radius as u128,
    ))
}
/// Producing covectors, before the normal law stages contemporary material successors.
/// Contact operands retain every stage, including its internal-output covector.
pub(super) struct IncidentPullback<'c> {
    source_covector: Option<ResidentNormalEnclosureSection<'c>>,
    symbol_covector: Option<ResidentNormalEnclosureSection<'c>>,
    moment_covector: Option<ResidentNormalEnclosure<'c>>,
    condition_covector: Option<ResidentNormalEnclosureSection<'c>>,
    external_covector: Option<ResidentNormalEnclosureSection<'c>>,
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

fn join_condition_columns<'c>(
    left: Option<&ResidentNormalEnclosureSection<'c>>,
    right: Option<&ResidentNormalEnclosureSection<'c>>,
) -> Result<Option<ResidentNormalEnclosureSection<'c>>, NativeSessionError> {
    match (left, right) {
        (None, None) => Ok(None),
        (Some(value), None) => Ok(Some(ResidentNormalEnclosureSection::concatenate_rows(&[
            value,
        ])?)),
        (None, Some(value)) => Ok(Some(ResidentNormalEnclosureSection::concatenate_rows(&[
            value,
        ])?)),
        (Some(left), Some(right)) => {
            if left.rows() != right.rows() || left.grain() != right.grain() {
                return Err(invalid("condition column join chart"));
            }
            let mut rows = Vec::with_capacity(left.rows());
            for row in 0..left.rows() {
                let joined = left.row(row)?.join(right.row(row)?)?;
                rows.push(joined.view().as_section()?);
            }
            let refs = rows.iter().collect::<Vec<_>>();
            Ok(Some(ResidentNormalEnclosureSection::concatenate_rows(
                &refs,
            )?))
        }
    }
}

impl<'c> IncidentFieldModel<'c> {
    pub(crate) fn new(
        field: NativeConstitutiveField<'c>,
        spec: IncidentFieldSpec,
    ) -> Result<Self, NativeSessionError> {
        Self::new_model(field, IncidentModelSpec::Legacy(spec))
    }
    fn new_model(
        field: NativeConstitutiveField<'c>,
        spec: IncidentModelSpec,
    ) -> Result<Self, NativeSessionError> {
        let layout = spec.compile()?;
        Self::with_layout(field, spec, layout)
    }
    fn with_layout(
        mut field: NativeConstitutiveField<'c>,
        spec: IncidentModelSpec,
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
            comparisons: BTreeMap::new(),
            rebase: IncidentRebaseResidual::default(),
            reaction_record: ReactionDepositRecord::default(),
            reaction_certificates: std::cell::RefCell::new(Vec::new()),
            energy_balance: None,
            #[cfg(test)]
            rebase_off: false,
        })
    }
    /// `(n, k)` of reaction material `member`: `n` complex current coordinates, `k` real contrast
    /// coordinates (features `n + c + 2nc` complex, `k = 2c`).
    fn reaction_extent(&self, member: usize) -> Result<(usize, usize), NativeSessionError> {
        let n = self.layout.width / 2;
        let features = *self
            .layout
            .material_features
            .get(member)
            .ok_or_else(|| invalid("reaction material owner"))?;
        if n == 0 || features < n || (features - n) % (2 * n + 1) != 0 {
            return Err(invalid("power-neutral reaction feature chart"));
        }
        Ok((n, 2 * ((features - n) / (2 * n + 1))))
    }
    /// The certificates of the supplied material cuts under the power-neutral law (`None` under
    /// the legacy law). A cached certificate is reused only for the exact resident state it
    /// certified; any other cut is certified by one explicit detachment.
    fn reaction_certificates(
        &self,
        material: &[ResidentNormalMaterialView<'c>],
    ) -> Result<
        Vec<
            Option<holonic_engine::native_ecology::constitutive_fibre::PowerNeutralCertificate<'c>>,
        >,
        NativeSessionError,
    > {
        if self.layout.reaction != ReactionLaw::PowerNeutral {
            return Ok(vec![None; material.len()]);
        }
        let mut cache = self.reaction_certificates.borrow_mut();
        if cache.len() != material.len() {
            cache.resize(material.len(), None);
        }
        material
            .iter()
            .enumerate()
            .map(|(member, view)| {
                if let Some(certificate) = cache[member].as_ref().filter(|c| c.certifies(view)) {
                    return Ok(Some(certificate.clone()));
                }
                let (n, k) = self.reaction_extent(member)?;
                let certificate = view.certify_power_neutral_reaction(n, k)?;
                cache[member] = Some(certificate.clone());
                Ok(Some(certificate))
            })
            .collect()
    }
    /// The incident word of a prepared boundary at the contemporary field and material: the
    /// anchor is `P(boundary ⊕ b₀(now))`. A fresh preparation and the contemporary read of a
    /// retained boundary comparison are this one computation.
    fn word_at(
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
        let anchor = if source.internal_components() == 0 {
            prepared_boundary.to_owned()?
        } else {
            prepared_boundary.join(
                source
                    .enclosure()
                    .restrict(boundary..boundary + source.internal_components())?
                    .view(),
            )?
        };
        let anchor = Rc::new(
            self.project_machine(anchor.view().as_section()?)?
                .row(0)?
                .to_owned()?,
        );
        let mut joint_held = held.to_vec();
        joint_held.resize((boundary + source.internal_components()) / 2, false);
        let material = self
            .materials
            .iter()
            .map(ResidentNormalMaterial::retained_view)
            .collect::<Vec<_>>();
        let (steps, output) =
            self.evaluate(&source, &material, &anchor, &joint_held, &admitted, None)?;
        Ok(IncidentWord {
            source_moment: None,
            boundary: Some(Rc::new(prepared_boundary.to_owned()?)),
            external_condition: None,
            machine: self.layout.machine.clone(),
            source,
            material,
            anchor,
            held: joint_held,
            admitted,
            steps,
            output,
            epoch: self.epoch,
            solver: self.spec.solver(),
            solve_steps: self.spec.solve_steps(),
            enclosure_propagation: self.spec.enclosure_propagation(),
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
        self.comparisons.len()
    }
    pub(crate) fn pending_ids(&self) -> Vec<u64> {
        self.comparisons.keys().copied().collect()
    }
    fn is_pending(&self, id: u64) -> bool {
        self.comparisons.contains_key(&id)
    }
    pub(crate) fn release(&mut self, id: u64) -> Result<(), NativeSessionError> {
        self.comparisons
            .remove(&id)
            .map(|_| ())
            .ok_or_else(|| invalid("unknown incident producing comparison"))
    }
    pub(crate) fn inspect(&mut self) -> Result<Value, NativeSessionError> {
        let source = self.field.read_current_source()?;
        Ok(
            json!({"scope":"incident-field-joint","epoch":self.epoch,"generations":self.generations,
            "joint":source.enclosure().inspect()?,"boundary_components":source.boundary_components(),
            "internal_components":source.internal_components(),"sites":self.layout.sites.len(),
            "operator":source.inspect_operator_bounds()?,
            "operative_storage":self.field.operative_return_storage(),
            "rebase_residual":&self.rebase,
            "reaction_law":self.layout.reaction,"reaction_deposits":&self.reaction_record,
            "energy_balance":&self.energy_balance,
            "chart": if self.layout.machine.is_some() {"fixed-generator-machine"} else {"legacy-slot-field"},
            "contact_material": if self.layout.machine.is_some() {"positive-pair-amplitude-family"} else {"unconstrained-global-return"}}),
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
            word: Rc::new(self.word_at(boundary, held, admitted)?),
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
            || generated.word.solver != self.spec.solver()
            || generated.word.solve_steps != self.spec.solve_steps()
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
        let retained = if retain {
            Some(self.retained_comparison(&generated.word)?)
        } else {
            None
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
            // Rebase: the published joint current is the solve enclosure's dyadic centre;
            // its dropped radius is the declared residual of this commit.
            let (centre, radius) = rebase_to_centre(self.field.surface(), &generated.word.output)?;
            #[cfg(test)]
            let centre = if self.rebase_off {
                generated.word.output.view().to_owned()?
            } else {
                centre
            };
            let mut rebase = self.rebase.clone();
            rebase.record(radius, generated.word.output.view().grain())?;
            Some((
                self.field
                    .prepare_joint_current_commit_from_action(&reflection, centre.view())?,
                rebase,
            ))
        } else {
            None
        };
        if let Some((staged, rebase)) = staged {
            // The exterior balance is read from the committed word's balls before publication.
            let balance = (self.layout.reaction == ReactionLaw::PowerNeutral)
                .then(|| self.read_energy_balance(&generated.word))
                .transpose()?;
            self.field.commit_joint_current(staged)?;
            self.rebase = rebase;
            if balance.is_some() {
                self.energy_balance = balance;
            }
        }
        if let Some(retained) = retained {
            generated.comparison = Some(self.next_comparison);
            self.comparisons
                .insert(self.next_comparison, Rc::new(retained));
        }
        self.next_comparison = next_id;
        self.generations = generations;
        Ok(generated)
    }
    /// Projection onto the declared real-coded source image. Its transpose is itself.
    fn project_machine(
        &self,
        section: ResidentNormalEnclosureSection<'c>,
    ) -> Result<ResidentNormalEnclosureSection<'c>, NativeSessionError> {
        if self.layout.machine.is_none() {
            return Ok(section);
        }
        let projected = Rc::new(section).project_real()?;
        Ok(ResidentNormalEnclosureSection::concatenate_rows(&[
            projected.output(),
        ])?)
    }

    fn evaluate(
        &self,
        source: &NativeFieldCurrentSource<'c>,
        material: &[ResidentNormalMaterialView<'c>],
        anchor: &ResidentNormalEnclosure<'c>,
        held: &[bool],
        admitted: &[Vec<bool>],
        external: Option<&ResidentNormalEnclosureSection<'c>>,
    ) -> Result<(Vec<IncidentStep<'c>>, ResidentNormalEnclosure<'c>), NativeSessionError> {
        let layout = &self.layout;
        let certificates = self.reaction_certificates(material)?;
        let external_width = layout
            .width
            .checked_mul(layout.source_condition_ports)
            .ok_or_else(|| invalid("incident external condition extent"))?;
        let zero_external = if layout.source_condition_ports > 0 && external.is_none() {
            Some(zero(
                self.field.surface(),
                layout.sites.len(),
                external_width,
                anchor.view().grain(),
            )?)
        } else {
            None
        };
        let external = external.or(zero_external.as_ref());
        if layout.source_condition_ports == 0 {
            if external.is_some() {
                return Err(invalid("external condition supplied to a zero-port field"));
            }
        } else {
            let external = external.ok_or_else(|| invalid("missing external condition field"))?;
            if external.rows() != layout.sites.len()
                || external.components() != external_width
                || external.grain() != anchor.view().grain()
            {
                return Err(invalid("external condition chart"));
            }
        }
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
        let maps = groups
            .iter()
            .map(|group| {
                layout
                    .machine
                    .as_ref()
                    .map(|machine| {
                        MachineGroupMaps::new(
                            self.field.surface(),
                            machine,
                            group,
                            anchor.view().grain(),
                            self.spec.enclosure_propagation(),
                        )
                    })
                    .transpose()
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut steps = Vec::with_capacity(layout.steps);
        for _ in 0..layout.steps {
            let q = Rc::new(
                current
                    .view()
                    .restrict(0..boundary)?
                    .view()
                    .split_rows(layout.sites.len(), layout.width)?,
            );
            let mut sites = Vec::with_capacity(groups.len());
            let mut incoming: Option<ResidentNormalEnclosureSection<'c>> = None;
            for (group, maps) in groups.iter().zip(&maps) {
                let rows = group.receivers.len();
                let query =
                    Rc::new(q.gather_phase_rows(&group.receivers, &phases(rows), layout.width)?);
                let phase = if let Some(maps) = maps {
                    IncidentParticipationForward::Machine(MachineParticipation::new_with_enclosure(
                        q.clone(),
                        &group.receivers,
                        &group.sources,
                        maps.query.clone(),
                        maps.neighbors.clone(),
                        maps.values.clone(),
                        layout.beta,
                        SeriesAperture(layout.series),
                        maps.enclosure.clone(),
                    )?)
                } else {
                    let neighbors = Rc::new(q.gather_phase_rows(
                        &group.sources,
                        &group.phases,
                        layout.width,
                    )?);
                    match layout.participation {
                        IncidentParticipationChart::Bilinear => {
                            IncidentParticipationForward::Bilinear(
                                query.clone().phase_participation(
                                    neighbors,
                                    group.neighbors,
                                    layout.beta,
                                    SeriesAperture(layout.series),
                                )?,
                            )
                        }
                        IncidentParticipationChart::QuadranceCurrent => {
                            IncidentParticipationForward::Quadrance(
                                query.clone().pair_quadrance_participation(
                                    Rc::clone(&neighbors),
                                    neighbors,
                                    group.neighbors,
                                    layout.beta,
                                    SeriesAperture(layout.series),
                                )?,
                            )
                        }
                    }
                };
                let machine_difference = maps
                    .as_ref()
                    .and_then(|m| m.differences.as_ref())
                    .map(|coefficients| {
                        MachineValueTransport::new_with_enclosure(
                            q.clone(),
                            &group.difference_sources,
                            coefficients.clone(),
                            self.spec.enclosure_propagation(),
                        )
                    })
                    .transpose()?;
                let current_condition = if group.differences == 0 {
                    None
                } else {
                    let u = match &machine_difference {
                        Some(m) => ResidentNormalEnclosureSection::concatenate_rows(&[m.output()])?,
                        None => q.gather_phase_rows(
                            &group.difference_sources,
                            &group.difference_phases,
                            layout.width,
                        )?,
                    };
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
                let external_condition = if layout.source_condition_ports == 0 {
                    None
                } else {
                    Some(
                        external
                            .ok_or_else(|| invalid("missing external condition field"))?
                            .gather_phase_rows(&group.receivers, &phases(rows), external_width)?,
                    )
                };
                let condition = join_condition_columns(
                    current_condition.as_ref(),
                    external_condition.as_ref(),
                )?;
                let (site_incoming, features, cayley) = match layout.reaction {
                    ReactionLaw::Legacy => {
                        let features = match &condition {
                            Some(c) => query.bilinear_enclosed_features(c)?,
                            None => ResidentNormalEnclosureSection::concatenate_rows(&[&query])?,
                        };
                        let reaction = material[group.material]
                            .read_applied_enclosed_section_with_enclosure(
                                &features,
                                self.spec.enclosure_propagation(),
                            )?;
                        (phase.output().sum_same_shape(&reaction)?, features, None)
                    }
                    ReactionLaw::PowerNeutral => {
                        let certificate = certificates[group.material]
                            .clone()
                            .ok_or_else(|| invalid("power-neutral material certificate"))?;
                        let (step, midpoint) = material[group.material].cayley_reaction_step(
                            &certificate,
                            phase.output(),
                            condition.as_ref(),
                        )?;
                        // The material and contrast returns are read at the midpoint.
                        let features = match &condition {
                            Some(c) => midpoint.realified_bilinear_enclosed_features(c)?,
                            None => ResidentNormalEnclosureSection::concatenate_rows(&[&midpoint])?,
                        };
                        let incoming = ResidentNormalEnclosureSection::concatenate_rows(&[&step])?;
                        (
                            incoming,
                            features,
                            Some(CayleyStage {
                                certificate,
                                step,
                                midpoint,
                            }),
                        )
                    }
                };
                let scattered = site_incoming.scatter_phase_adjoint(
                    &group.receivers,
                    &phases(rows),
                    layout.sites.len(),
                )?;
                incoming = Some(match incoming {
                    Some(previous) => previous.sum_same_shape(&scattered)?,
                    None => scattered,
                });
                sites.push(IncidentSiteStep {
                    group: Rc::clone(group),
                    query,
                    phase,
                    condition,
                    external_condition,
                    machine_difference,
                    features,
                    cayley,
                });
            }
            let a = self
                .project_machine(
                    incoming.ok_or_else(|| invalid("incident field has no material group"))?,
                )?
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
                    .solver()
                    .action(source, input.view(), self.spec.solve_steps())?;
            let reflected = self
                .project_machine(reflection.output().as_section()?)?
                .row(0)?
                .to_owned()?;
            let before = Rc::new(current);
            current = reflected
                .view()
                .as_section()?
                .held_refinement(&anchor_section, held, layout.relaxation_bits)?
                .row(0)?
                .to_owned()?;
            steps.push(IncidentStep {
                sites,
                input,
                before,
                reflected,
            });
        }
        Ok((steps, current))
    }

    fn pull_back_word(
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
        let external_width = layout
            .width
            .checked_mul(layout.source_condition_ports)
            .ok_or_else(|| invalid("incident external covector extent"))?;
        let mut external_total = if layout.source_condition_ports == 0 {
            None
        } else {
            Some(zero(
                self.field.surface(),
                layout.sites.len(),
                external_width,
                grain,
            )?)
        };
        let mut contacts = Vec::with_capacity(word.steps.len());
        for step in word.steps.iter().rev() {
            // The anchor includes b_pre. Its contribution is present at every stage.
            let anchor_part =
                zero_joint.held_refinement(&gradient, &word.held, layout.relaxation_bits)?;
            anchor_gradient = anchor_gradient.sum_same_shape(&anchor_part)?;
            let returned = self.project_machine(gradient.held_refinement(
                &zero_joint,
                &word.held,
                layout.relaxation_bits,
            )?)?;
            let full = returned.row(0)?;
            // S_D is self-adjoint under the declared unit pairing. This includes g_b_ref.
            let reflection = word.solver.action(&word.source, full, word.solve_steps)?;
            let incoming_projected = self.project_machine(reflection.output().as_section()?)?;
            let incoming_covector = incoming_projected.row(0)?;
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
                // The Cayley stage returns through `u = A⁻ᴴ g`: the material reads `(Φ(x̄,c), u)`,
                // the contrast the feature pullback of `Wᴴu` at the midpoint, and the drive
                // `(I + K/2)ᴴ u = 2u − g`; the standing query receives nothing from the reaction.
                let cayley_return = match &stage.cayley {
                    Some(cy) => Some(word.material[group.material].cayley_reaction_adjoint(
                        &cy.certificate,
                        stage.condition.as_ref(),
                        &g,
                    )?),
                    None => None,
                };
                let gdrive = cayley_return.as_ref().map_or(&g, |(_, drive)| drive);
                let gf = word.material[group.material].pull_back_enclosed_section_with_enclosure(
                    cayley_return.as_ref().map_or(&g, |(u, _)| u),
                    word.enclosure_propagation.clone(),
                )?;
                let (gq, gcondition) = match (&stage.condition, &stage.cayley) {
                    (Some(c), Some(cy)) => (
                        zero(self.field.surface(), rows, layout.width, grain)?,
                        Some(cy.midpoint.realified_bilinear_enclosed_pullback(c, &gf)?.1),
                    ),
                    (None, Some(_)) => {
                        (zero(self.field.surface(), rows, layout.width, grain)?, None)
                    }
                    (Some(c), None) => {
                        let (q, c) = match layout.reaction {
                            ReactionLaw::Legacy => {
                                stage.query.bilinear_enclosed_pullback(c, &gf)?
                            }
                            ReactionLaw::PowerNeutral => {
                                stage.query.realified_bilinear_enclosed_pullback(c, &gf)?
                            }
                        };
                        (q, Some(c))
                    }
                    (None, None) => (gf, None),
                };
                let current_width = group
                    .differences
                    .checked_mul(layout.width)
                    .ok_or_else(|| invalid("incident current condition extent"))?;
                let gdelta = if current_width == 0 {
                    None
                } else {
                    Some(
                        gcondition
                            .as_ref()
                            .ok_or_else(|| invalid("missing current condition covector"))?
                            .restrict_components(0..current_width)?,
                    )
                };
                if layout.source_condition_ports > 0 {
                    let external = gcondition
                        .as_ref()
                        .ok_or_else(|| invalid("missing complete condition covector"))?
                        .restrict_components(current_width..current_width + external_width)?;
                    let scattered = external.scatter_phase_adjoint(
                        &group.receivers,
                        &phases(rows),
                        layout.sites.len(),
                    )?;
                    external_total = Some(
                        external_total
                            .take()
                            .ok_or_else(|| invalid("external covector accumulator"))?
                            .sum_same_shape(&scattered)?,
                    );
                }
                let mut query = match &stage.phase {
                    IncidentParticipationForward::Machine(p) => {
                        previous = previous.sum_same_shape(&p.pull_back(gdrive)?)?;
                        gq
                    }
                    _ => {
                        let (phase_query, phase_neighbors) = stage.phase.pull_back(gdrive)?;
                        previous =
                            previous.sum_same_shape(&phase_neighbors.scatter_phase_adjoint(
                                &group.sources,
                                &group.phases,
                                layout.sites.len(),
                            )?)?;
                        gq.sum_same_shape(&phase_query)?
                    }
                };
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
                    let difference_return = match &stage.machine_difference {
                        Some(m) => m.pull_back(&parts)?,
                        None => parts.scatter_phase_adjoint(
                            &group.difference_sources,
                            &group.difference_phases,
                            layout.sites.len(),
                        )?,
                    };
                    previous = previous.sum_same_shape(&difference_return)?;
                }
                previous = previous.sum_same_shape(&query.scatter_phase_adjoint(
                    &group.receivers,
                    &phases(rows),
                    layout.sites.len(),
                )?)?;
                material[group.material].push((
                    ResidentNormalEnclosureSection::concatenate_rows(&[&stage.features])?,
                    match cayley_return {
                        Some((u, _)) => u,
                        None => g,
                    },
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
            source_covector: None,
            symbol_covector: None,
            moment_covector: None,
            condition_covector: None,
            external_covector: external_total,
            anchor: self
                .project_machine(anchor_gradient.sum_same_shape(&gradient)?)?
                .row(0)?
                .to_owned()?,
            material,
            contacts,
        })
    }
}

#[cfg(test)]
impl NativeCoupledBody<'_> {
    /// Test diagnostic: zero the selected power-neutral reaction blocks (linear `W_s`, contrast
    /// coupling `W_c`, modulated slices) of every reaction material.
    pub(crate) fn zero_reaction_blocks(
        &mut self,
        linear: bool,
        coupling: bool,
        slices: bool,
    ) -> Result<(), NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid("reaction columns require the incident model chart"));
        };
        if model.layout.reaction != ReactionLaw::PowerNeutral {
            return Err(invalid(
                "block attribution declared for the power-neutral chart",
            ));
        }
        let n = model.layout.width / 2;
        for (material, &features) in model
            .materials
            .iter_mut()
            .zip(&model.layout.material_features)
        {
            let c = (features - n) / (2 * n + 1);
            let mut columns = Vec::new();
            if linear {
                columns.push(0..n);
            }
            if coupling {
                columns.push(n..n + c);
            }
            if slices {
                columns.push(n + c..features);
            }
            *material = material.with_coefficient_columns_zeroed(&columns)?;
        }
        Ok(())
    }
}

impl<'c> NativeCoupledBody<'c> {
    /// Prepare the material return of a retained comparison, read at the contemporary
    /// constitution (its retained operands through the current field and material). A passage
    /// that pooled directed contacts supplies them through `prepare_generator_material_return`.
    pub fn prepare_incident_material_return(
        &mut self,
        id: u64,
        output_covector: ResidentNormalEnclosureView<'_, 'c>,
        step_bits: u32,
    ) -> Result<NativeIncidentMaterialReturn<'c>, NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid("incident return requires its model chart"));
        };
        let word = Rc::new(model.contemporary_comparison_word(id, None)?);
        self.prepare_incident_material_return_at(id, &word, output_covector, step_bits, &[])
    }

    /// The material return of comparison `id` pulled back through `word`, its word at the
    /// contemporary constitution.
    fn prepare_incident_material_return_at(
        &mut self,
        id: u64,
        word: &IncidentWord<'c>,
        output_covector: ResidentNormalEnclosureView<'_, 'c>,
        step_bits: u32,
        contacts: &[GeneratorSourceContact],
    ) -> Result<NativeIncidentMaterialReturn<'c>, NativeSessionError> {
        use holonic_engine::native_ecology::constitutive_fibre::NativeContactRealization;
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid("incident return requires its model chart"));
        };
        if step_bits > 120 {
            return Err(invalid("incident material return scale"));
        }
        if !model.is_pending(id) {
            return Err(invalid("unknown incident comparison"));
        }
        let next_epoch = model
            .epoch
            .checked_add(1)
            .ok_or_else(|| invalid("incident material epoch exhausted"))?;
        let observations = model
            .observations
            .checked_add(1)
            .ok_or_else(|| invalid("incident observation count exhausted"))?;
        let returned = model.pull_back_with_contacts(word, output_covector, contacts)?;
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
        // The power-neutral law: each normal-law solve is followed by its projections.
        let mut reaction = model.reaction_record.clone();
        let mut reaction_certificates = vec![None; material.len()];
        if model.layout.reaction == ReactionLaw::PowerNeutral {
            let mut projections = Vec::with_capacity(material.len());
            for (member, staged) in material.iter_mut().enumerate() {
                // features = n + c + 2nc complex, so the real contrast count is k = 2c.
                // With no contrast (c = 0) only the linear self-relation is projected.
                let (n, k) = model.reaction_extent(member)?;
                let (projected, receipt, certificate) =
                    staged.project_power_neutral_reaction_certified(n, k)?;
                *staged = projected;
                projections.push(receipt);
                reaction_certificates[member] = Some(certificate);
            }
            reaction.record(projections)?;
        }
        let (contact, contact_amplitude) = if word.source.internal_components() == 0 {
            (None, None)
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
            if model.layout.machine.is_some() {
                let proposal = model.field.prepare_declared_contact_amplitude_return(
                    &pullbacks.iter().collect::<Vec<_>>(),
                    3,
                    step_bits,
                )?;
                (None, Some(proposal))
            } else {
                (
                    Some(model.field.prepare_global_action_material_return(
                        &pullbacks.iter().collect::<Vec<_>>(),
                        step_bits,
                        NativeContactRealization::DyadicDeposit,
                    )?),
                    None,
                )
            }
        };
        Ok(NativeIncidentMaterialReturn {
            reaction,
            reaction_certificates,
            contact_amplitude,
            source_covector: returned.source_covector,
            symbol_covector: returned.symbol_covector,
            moment_covector: returned.moment_covector,
            condition_covector: returned.condition_covector,
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
    /// The declared residual family of committed-current rebases.
    pub fn incident_rebase_residual(&self) -> Result<IncidentRebaseResidual, NativeSessionError> {
        match self.state()? {
            BodyState::Incident(model) => Ok(model.rebase.clone()),
            _ => Err(invalid("incident rebase residual requires its model chart")),
        }
    }
    pub fn publish_incident_material_return(
        &mut self,
        prepared: NativeIncidentMaterialReturn<'c>,
    ) -> Result<(), NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid("incident return requires its model chart"));
        };
        if prepared.epoch != model.epoch || !model.is_pending(prepared.comparison) {
            return Err(invalid("stale incident material publication"));
        }
        if let Some(contact) = prepared.contact {
            model.field.commit_global_action_material_return(contact)?;
        }
        if let Some(contact) = prepared.contact_amplitude {
            model
                .field
                .commit_declared_contact_amplitude_return(contact)?;
        }
        model.materials = prepared.material;
        model.reaction_record = prepared.reaction;
        *model.reaction_certificates.borrow_mut() = prepared.reaction_certificates;
        model.epoch = prepared.next_epoch;
        model.observations = prepared.observations;
        model.comparisons.remove(&prepared.comparison);
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
                field,
                IncidentModelSpec::Legacy(spec),
                layout,
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
            BodyState::Incident(model) => Ok((model.spec.solver(), model.spec.solve_steps())),
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
    /// Change only the numerical solve. Material and continuing q/b are retained, and new
    /// checkpoints record the selected proposal. Outstanding comparisons keep no producing word,
    /// so they are read with the solver in force when they return (the contemporary cut); only a
    /// prepared but unpublished word is refused as stale by `publish_incident_field`.
    pub fn configure_incident_solver(
        &mut self,
        solver: IncidentFieldSolver,
        steps: usize,
    ) -> Result<(), NativeSessionError> {
        if steps == 0 || steps > u32::MAX as usize {
            return Err(invalid("incident solve resource aperture"));
        }
        match self.state_mut()? {
            BodyState::Incident(model) => {
                model.spec.set_solver(solver, steps);
                Ok(())
            }
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
        if model.layout.machine.is_some() {
            return Err(invalid(
                "source-cell contact restrictions do not identify generator arcs; use the machine source/phase boundary",
            ));
        }
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
            word: Rc::new(model.word_at(boundary, held, admitted)?),
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
