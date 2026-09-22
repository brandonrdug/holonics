//! Fixed generator configuration consumed by the existing incident field word.
use super::*;
use crate::native::field_geometry::{
    machine::{CompiledGeneratorMachine, GeneratorMachineSpec},
    machine_factor::MachineFactor,
};
use relational_geometry::{AffineMap3, RatMat3};

/// A fixed machine and its finite resident refinement. Each original complex-3 current is
/// encoded as six real-coded native complex channels. Geometry and rate/contact material are
/// declared here; reaction material is learned through the existing normal return.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorIncidentFieldSpec {
    pub machine: GeneratorMachineSpec,
    pub self_comparison: bool,
    pub beta_significand: i64,
    pub beta_exponent: i32,
    pub series_terms: u32,
    pub refinement_steps: usize,
    pub relaxation_bits: u32,
    #[serde(default)]
    pub material_owners: Vec<usize>,
    #[serde(default = "solve_steps")]
    pub solve_steps: usize,
    #[serde(default, skip_serializing_if = "IncidentFieldSolver::is_richardson")]
    pub solver: IncidentFieldSolver,
}

/// Untagged only to preserve the existing legacy rest spelling. The two source objects have
/// distinct required fields and deny unknown fields; neither can silently decode as the other.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub(super) enum IncidentModelSpec {
    Legacy(IncidentFieldSpec),
    Generator(GeneratorIncidentFieldSpec),
}
impl IncidentModelSpec {
    pub(super) fn compile(&self) -> Result<IncidentLayout, NativeSessionError> {
        match self {
            Self::Legacy(s) => s.compile(),
            Self::Generator(s) => s.compile(),
        }
    }
    pub(super) fn solver(&self) -> IncidentFieldSolver {
        match self {
            Self::Legacy(s) => s.solver,
            Self::Generator(s) => s.solver,
        }
    }
    pub(super) fn solve_steps(&self) -> usize {
        match self {
            Self::Legacy(s) => s.solve_steps,
            Self::Generator(s) => s.solve_steps,
        }
    }
    pub(super) fn set_solver(&mut self, solver: IncidentFieldSolver, steps: usize) {
        match self {
            Self::Legacy(s) => {
                s.solver = solver;
                s.solve_steps = steps;
            }
            Self::Generator(s) => {
                s.solver = solver;
                s.solve_steps = steps;
            }
        }
    }
}

impl GeneratorIncidentFieldSpec {
    fn compile(&self) -> Result<IncidentLayout, NativeSessionError> {
        if self.refinement_steps == 0
            || self.relaxation_bits > 120
            || self.series_terms == 0
            || self.series_terms == u32::MAX
            || self.solve_steps == 0
            || self.solve_steps > u32::MAX as usize
            || self.beta_significand < 0
            || self.beta_exponent == i32::MIN
        {
            return Err(invalid("generator machine refinement/score aperture"));
        }
        let machine = Rc::new(self.machine.compile().map_err(invalid)?);
        let rows = machine.sites().len();
        rows.checked_mul(12)
            .filter(|n| *n <= u32::MAX as usize)
            .ok_or_else(|| invalid("generator native boundary extent"))?;
        let owners = if self.material_owners.is_empty() {
            (0..rows).collect()
        } else {
            self.material_owners.clone()
        };
        if owners.len() != rows || owners.iter().any(|v| *v >= rows) {
            return Err(invalid("generator material owner extent"));
        }
        let mut sites = (0..rows)
            .map(|r| IncidentSite {
                sources: if self.self_comparison {
                    vec![r]
                } else {
                    vec![]
                },
                phases: if self.self_comparison {
                    phases(1)
                } else {
                    vec![]
                },
                differences: vec![],
                material: owners[r],
                machine_arcs: if self.self_comparison {
                    vec![None]
                } else {
                    vec![]
                },
            })
            .collect::<Vec<_>>();
        for (index, arc) in machine.arcs().iter().enumerate() {
            let site = &mut sites[arc.receiver_index()];
            site.differences.push(site.sources.len());
            site.sources.push(arc.source_index());
            site.phases.push(ExactWavePhaseTransport::identity());
            site.machine_arcs.push(Some(index));
        }
        if sites.iter().any(|s| s.sources.is_empty()) {
            return Err(invalid("generator site has no admitted current"));
        }
        let mut features = vec![0; owners.iter().max().copied().unwrap() + 1];
        for site in &sites {
            let c = site
                .differences
                .len()
                .checked_mul(6)
                .ok_or_else(|| invalid("generator condition extent"))?;
            let f = c
                .checked_mul(7)
                .and_then(|n| n.checked_add(6))
                .filter(|n| *n <= u32::MAX as usize)
                .ok_or_else(|| invalid("generator feature extent"))?;
            if features[site.material] != 0 && features[site.material] != f {
                return Err(invalid(
                    "shared generator reaction material has incompatible ordered ports",
                ));
            }
            features[site.material] = f;
        }
        if features.contains(&0) {
            return Err(invalid("generator material owners must be contiguous"));
        }
        // These are declared receiving GENERATORS. They are not positions in an exterior source.
        let slot_rows = machine
            .sites()
            .iter()
            .enumerate()
            .filter_map(|(i, site)| site.is_receiver().then_some(i))
            .collect();
        Ok(IncidentLayout {
            machine: Some(machine),
            sites,
            slot_rows,
            width: 12,
            material_features: features,
            beta: Dyadic {
                significand: self.beta_significand,
                exponent: self.beta_exponent,
            },
            participation: IncidentParticipationChart::QuadranceCurrent,
            series: self.series_terms,
            steps: self.refinement_steps,
            relaxation_bits: self.relaxation_bits,
        })
    }
}

/// Mounted once per group before the refinement loop. The declaration remains the exact
/// source, and every reused coefficient packet retains its outward rounding radius.
pub(super) struct MachineGroupMaps<'c> {
    pub query: Rc<ResidentNormalEnclosureSection<'c>>,
    pub neighbors: Rc<ResidentNormalEnclosureSection<'c>>,
    pub values: Rc<ResidentNormalEnclosureSection<'c>>,
    pub differences: Option<Rc<ResidentNormalEnclosureSection<'c>>>,
}
impl<'c> MachineGroupMaps<'c> {
    pub(super) fn new(
        surface: &'c ResidentSurface<'c>,
        machine: &CompiledGeneratorMachine,
        group: &IncidentGroup,
        grain: ResidentGrain,
    ) -> Result<Self, NativeSessionError> {
        let spatial = |site: usize| AffineMap3 {
            linear: RatMat3::identity(),
            translation: machine.sites()[site].screw().initial().clone(),
        };
        let value_map = |arc: Option<usize>| -> AffineMap3 {
            arc.map(|i| {
                let u = machine.arcs()[i].current_action();
                AffineMap3 {
                    linear: u.linear.clone(),
                    translation: u.bias.clone(),
                }
            })
            .unwrap_or_else(AffineMap3::identity)
        };
        let queries = group
            .receivers
            .iter()
            .map(|&r| spatial(r))
            .collect::<Vec<_>>();
        let neighbors = group
            .sources
            .iter()
            .zip(&group.machine_arcs)
            .map(|(&s, &a)| {
                a.map(|i| {
                    let t = machine.arcs()[i].source_to_receiver();
                    AffineMap3 {
                        linear: t.linear.clone(),
                        translation: t.apply(machine.sites()[s].screw().initial()),
                    }
                })
                .unwrap_or_else(|| spatial(s))
            })
            .collect::<Vec<_>>();
        let values = group
            .machine_arcs
            .iter()
            .map(|&a| value_map(a))
            .collect::<Vec<_>>();
        let differences = group
            .difference_arcs
            .iter()
            .map(|&a| value_map(a))
            .collect::<Vec<_>>();
        let mount = |maps: &[AffineMap3]| {
            ResidentNormalEnclosureSection::affine_coefficients(surface, maps, grain)
                .map_err(invalid)
        };
        Ok(Self {
            query: mount(&queries)?,
            neighbors: mount(&neighbors)?,
            values: mount(&values)?,
            differences: if differences.is_empty() {
                None
            } else {
                Some(mount(&differences)?)
            },
        })
    }
}

impl<'c> NativeCoupledBody<'c> {
    /// Found the same incident HNN on fixed generators and actual pair-derived contacts.
    /// This call consumes machine currents; exterior ordered-source and phase-receiver codecs
    /// are separate boundaries. It never allocates one site for each source symbol.
    pub fn found_generator_field(
        surface: &'c ResidentSurface<'c>,
        spec: GeneratorIncidentFieldSpec,
        grain: ResidentGrain,
    ) -> Result<Self, NativeSessionError> {
        use holonic_engine::native_ecology::constitutive_fibre::{
            NativeFieldContactOrigin, NativeFieldDeclaredIncidence, NativeJunctionSeed,
            NativePhaseCurrent,
        };
        let layout = spec.compile()?;
        let machine = layout.machine.as_ref().unwrap();
        let boundary = layout
            .sites
            .len()
            .checked_mul(12)
            .ok_or_else(|| invalid("machine boundary extent"))?;
        let contacts = machine
            .arcs()
            .len()
            .checked_mul(3)
            .ok_or_else(|| invalid("machine contact extent"))?;
        contacts
            .checked_mul(12)
            .and_then(|n| n.checked_mul(32))
            .ok_or_else(|| invalid("machine incidence carrier extent"))?;
        let seed = NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        let mut field = NativeConstitutiveField::found_incident_source_only(
            surface,
            vec![seed; boundary / 6],
            grain,
        )?;
        if contacts > 0 {
            let mut offsets = vec![0i128];
            let mut columns = Vec::new();
            let mut values = Vec::new();
            let mut origins = Vec::new();
            let mut radius = 0i128;
            for arc in machine.arcs() {
                let factor = MachineFactor::from_arc(arc, grain.0).map_err(invalid)?;
                radius = radius
                    .checked_add(factor.factor_error().words)
                    .ok_or_else(|| invalid("machine factor radius"))?;
                for row in factor.native_rows() {
                    for (local, coefficient) in row.iter().enumerate() {
                        if coefficient.center != 0 {
                            let site = if local < 6 {
                                arc.receiver_index()
                            } else {
                                arc.source_index()
                            };
                            columns.push((site * 12 + 2 * (local % 6)) as i128);
                            values.extend([coefficient.center, 0]);
                        }
                    }
                    offsets.push(columns.len() as i128);
                    origins.push(NativeFieldContactOrigin::declared(
                        origins.len(),
                        arc.source_index() * 2,
                        arc.receiver_index() * 2,
                    ));
                }
            }
            let nonzeros = columns.len();
            let mut transpose = vec![Vec::new(); boundary / 2];
            for row in 0..contacts {
                for at in offsets[row] as usize..offsets[row + 1] as usize {
                    transpose[columns[at] as usize / 2].push((row, values[2 * at]));
                }
            }
            let mut t_offsets = vec![0i128];
            let mut t_rows = Vec::new();
            let mut t_values = Vec::new();
            for entries in transpose {
                for (row, value) in entries {
                    t_rows.push(row as i128);
                    t_values.extend([value, 0]);
                }
                t_offsets.push(t_rows.len() as i128);
            }
            // A zero-rank contact still has a structural row and a mountable empty-data packet.
            if nonzeros == 0 {
                columns.push(0);
                values.extend([0, 0]);
                t_rows.push(0);
                t_values.extend([0, 0]);
            }
            let mount = |rows,
                         width,
                         values: Vec<i128>|
             -> Result<ResidentSection<'c>, NativeSessionError> {
                let words = values
                    .into_iter()
                    .flat_map(|v| [v as i64, (v >> 64) as i64])
                    .map(|v| (v, v))
                    .collect();
                Ok(surface
                    .mount_section_rest(
                        &ResidentSectionRest::found(rows, width, ResidentGrain(0), 64, words)
                            .map_err(invalid)?,
                    )
                    .map_err(invalid)?)
            };
            field.register_declared_incidence(
                NativeFieldDeclaredIncidence {
                    row_offsets: mount(1, 2 * offsets.len(), offsets)?,
                    columns: mount(1, 2 * nonzeros.max(1), columns)?,
                    values: mount(1, 4 * nonzeros.max(1), values)?,
                    transpose_offsets: mount(1, 2 * t_offsets.len(), t_offsets)?,
                    transpose_rows: mount(1, 2 * nonzeros.max(1), t_rows)?,
                    transpose_values: mount(1, 4 * nonzeros.max(1), t_values)?,
                    left: mount(1, 2 * boundary, vec![0; boundary])?,
                    right: mount(1, 4 * contacts, vec![0; 2 * contacts])?,
                    defects: mount(1, 2, vec![0])?,
                    rows: contacts,
                    boundary_components: boundary,
                    rank: 0,
                    nonzeros,
                },
                mount(contacts, 4, vec![0; 2 * contacts])?,
                mount(1, 4, vec![radius, 0])?,
                origins,
            )?;
        }
        Ok(Self {
            state: Some(BodyState::Incident(IncidentFieldModel::with_layout(
                field,
                IncidentModelSpec::Generator(spec),
                layout,
            )?)),
        })
    }
}
