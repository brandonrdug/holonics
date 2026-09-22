//! Ordered source injection for a fixed generator machine.
//!
//! This is the source-side companion of the tagged phase receiver.  It advances each site's
//! current by its supplied finite action and adds the encoded source row as a tangent/current
//! increment.  The affine translation is therefore applied to the standing current; an encoded
//! source value is never mistaken for a replacement spatial position.  The original joint `b`
//! chart is carried unchanged.

use super::machine_receiving::GeneratorPhasePort;
use super::machine_transport::MachineValueTransport;
use super::*;
use crate::native::field_geometry::machine::{
    CompiledGeneratorMachine, CompiledGeneratorSite, CurrentAffineMap,
};
use holonic_engine::native_ecology::constitutive_fibre::NativeEnclosurePropagation;
use holonic_engine::native_ecology::constitutive_fibre::ResidentNormalEnclosureSection;
use num_traits::Signed;
use relational_geometry::{AffineMap3, RatMat3};
use serde::{Deserialize, Serialize};
use std::cell::Cell;
use std::rc::Rc;

type Result<T> = std::result::Result<T, NativeSessionError>;

/// The fixed source identity and common clock for one ordered episode.  `clocks` covers every
/// machine site exactly once so every event has a declared exponent witness, including sites
/// that are not injection sites.  `injection_sites` names the source-participating sites whose
/// tangent rows are packed in each encoded occurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorSourceBinding {
    pub source_id: String,
    pub clock: crate::native::field_geometry::machine::ClockSpec,
    pub clocks: Vec<GeneratorPhasePort>,
    pub injection_sites: Vec<String>,
    /// Fixed ordered condition ports for directed common-frame source contrasts.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub contact_kinds: Vec<super::machine_source_contacts::GeneratorSourceContactKind>,
    /// Declared ordered offsets δ, each one further condition port after the contact kinds.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub offsets: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratorSourceClockWitness {
    pub site_id: String,
    pub first_exponent: i64,
    pub last_exponent: i64,
    pub unit: String,
}

impl GeneratorSourceBinding {
    pub fn validate_scope(
        &self,
        machine: &CompiledGeneratorMachine,
        start: u64,
        count: usize,
    ) -> Result<Vec<GeneratorSourceClockWitness>> {
        if self.source_id.is_empty() || self.clocks.is_empty() || self.injection_sites.is_empty() {
            return Err(invalid("generator source binding identity/ports"));
        }
        if self.clock.lineage.is_empty()
            || self.clock.unit.is_empty()
            || !self.clock.duration.is_positive()
            || count == 0
        {
            return Err(invalid("generator source clock/count"));
        }
        if self.clocks.len() != machine.sites().len() {
            return Err(invalid("generator source clock coverage"));
        }
        let start = i64::try_from(start).map_err(invalid)?;
        let last = start
            .checked_add(i64::try_from(count - 1).map_err(invalid)?)
            .ok_or_else(|| invalid("generator source event exponent"))?;
        let mut clock_sites = std::collections::BTreeSet::new();
        let mut witnesses = Vec::with_capacity(self.clocks.len());
        for port in &self.clocks {
            let site = machine
                .sites()
                .iter()
                .find(|site| site.id() == port.site_id)
                .ok_or_else(|| invalid("generator source clock site identity"))?;
            if !clock_sites.insert(port.site_id.clone())
                || site.clock().unit() != self.clock.unit
                || !site.clock().duration().is_positive()
            {
                return Err(invalid("generator source clock coverage/unit"));
            }
            let first = witness_exponent(site, port, start)?;
            let last_exponent = witness_exponent(site, port, last)?;
            witnesses.push(GeneratorSourceClockWitness {
                site_id: port.site_id.clone(),
                first_exponent: first,
                last_exponent,
                unit: self.clock.unit.clone(),
            });
        }
        if clock_sites.len() != machine.sites().len()
            || machine
                .sites()
                .iter()
                .any(|site| !clock_sites.contains(site.id()))
        {
            return Err(invalid(
                "generator source clocks do not cover machine sites",
            ));
        }
        let mut injections = std::collections::BTreeSet::new();
        for id in &self.injection_sites {
            let site = machine
                .sites()
                .iter()
                .find(|site| site.id() == id)
                .ok_or_else(|| invalid("generator source injection site identity"))?;
            if !site.is_source() || !injections.insert(id.clone()) {
                return Err(invalid("generator source injection roles/uniqueness"));
            }
        }
        Ok(witnesses)
    }

    pub fn source_id(&self) -> &str {
        &self.source_id
    }
    pub fn injection_sites(&self) -> &[String] {
        &self.injection_sites
    }
}

/// One resident stepper over a bounded source episode.  The coefficient section contains one
/// fixed action row per site; `apply` reuses that same finite step for every ordered event.
pub struct MachineSourceMaps<'c> {
    coefficients: Rc<ResidentNormalEnclosureSection<'c>>,
    machine_sites: usize,
    source_id: String,
    injection_indices: Vec<usize>,
    injection_count: usize,
    start: u64,
    count: usize,
    cursor: Cell<usize>,
    witnesses: Vec<GeneratorSourceClockWitness>,
    enclosure: NativeEnclosurePropagation,
    /// The exact per-site configuration step `U_g = (L_g, τ_g)`, retained for its closed-form
    /// powers. Currents use `L_g` only.
    step_maps: Vec<AffineMap3>,
    powers: std::cell::OnceCell<MomentPowers>,
}

/// The forward source step and its producing map. This is the per-step form of the moment;
/// `MachineSourceMaps::{moment, anchor}` is its closed form and is what the incident word consumes.
#[cfg_attr(not(test), allow(dead_code))]
pub struct GeneratorInjection<'c> {
    output: ResidentNormalEnclosure<'c>,
    advance: MachineValueTransport<'c>,
    injection_indices: Vec<usize>,
    injection_count: usize,
    event_index: usize,
    boundary_components: usize,
}

impl<'c> MachineSourceMaps<'c> {
    pub fn new(
        surface: &'c ResidentSurface<'c>,
        machine: &CompiledGeneratorMachine,
        binding: &GeneratorSourceBinding,
        start: u64,
        count: usize,
        grain: ResidentGrain,
    ) -> Result<Self> {
        Self::new_with_enclosure(
            surface,
            machine,
            binding,
            start,
            count,
            grain,
            NativeEnclosurePropagation::ComponentIntervals,
        )
    }
    pub fn new_with_enclosure(
        surface: &'c ResidentSurface<'c>,
        machine: &CompiledGeneratorMachine,
        binding: &GeneratorSourceBinding,
        start: u64,
        count: usize,
        grain: ResidentGrain,
        enclosure: NativeEnclosurePropagation,
    ) -> Result<Self> {
        let witnesses = binding.validate_scope(machine, start, count)?;
        if machine.sites().is_empty() || count == 0 || !(1..=120).contains(&grain.0) {
            return Err(invalid("generator source map extent/grain"));
        }
        let machine_sites = machine.sites().len();
        machine_sites
            .checked_mul(count)
            .ok_or_else(|| invalid("generator source coefficient extent"))?;
        let mut injection_indices = Vec::with_capacity(binding.injection_sites.len());
        for id in &binding.injection_sites {
            let index = machine
                .sites()
                .iter()
                .position(|site| site.id() == id)
                .ok_or_else(|| invalid("generator source injection index"))?;
            injection_indices.push(index);
        }
        let mut maps = Vec::new();
        maps.try_reserve_exact(machine_sites)
            .map_err(|_| invalid("generator source coefficient allocation"))?;
        for site in machine.sites() {
            let port = binding
                .clocks
                .iter()
                .find(|port| port.site_id == site.id())
                .ok_or_else(|| invalid("generator source action port"))?;
            // The site's origin labels its initial configuration and is retained in the
            // witness. Each occurrence applies the same declared finite step action.
            let action = super::machine_receiving::receiving_current_map(site, port.step_exponent)?;
            maps.push(CurrentAffineMap::between(
                site.screw().initial(),
                site.screw().initial(),
                &action,
            ));
        }
        let affine_maps = maps
            .into_iter()
            .map(|map| AffineMap3 {
                linear: map.linear,
                translation: map.bias,
            })
            .collect::<Vec<_>>();
        // Chart separation: the affine step acts on the site's configuration; the resident
        // current q is a tangent and advances by the linear part `L` only. The per-step current
        // coefficients therefore carry no translation.
        let current_steps = affine_maps
            .iter()
            .map(|map| AffineMap3 {
                linear: map.linear.clone(),
                translation: relational_geometry::RatVec3::zero(),
            })
            .collect::<Vec<_>>();
        let coefficients =
            ResidentNormalEnclosureSection::affine_coefficients(surface, &current_steps, grain)
                .map_err(invalid)?;
        let step_maps = affine_maps;
        Ok(Self {
            coefficients,
            machine_sites,
            source_id: binding.source_id.clone(),
            injection_indices,
            injection_count: binding.injection_sites.len(),
            start,
            count,
            cursor: Cell::new(0),
            witnesses,
            enclosure,
            step_maps,
            powers: std::cell::OnceCell::new(),
        })
    }

    pub fn source_count(&self) -> usize {
        self.count
    }
    pub fn source_id(&self) -> &str {
        &self.source_id
    }
    pub fn site_count(&self) -> usize {
        self.machine_sites
    }
    pub fn injection_count(&self) -> usize {
        self.injection_count
    }
    pub fn start(&self) -> u64 {
        self.start
    }
    pub fn next_event(&self) -> usize {
        self.cursor.get()
    }
    pub fn clock_witnesses(&self) -> &[GeneratorSourceClockWitness] {
        &self.witnesses
    }

    pub fn apply(
        &self,
        previous_joint: ResidentNormalEnclosureView<'_, 'c>,
        encoded_step: Rc<ResidentNormalEnclosureSection<'c>>,
    ) -> Result<GeneratorInjection<'c>> {
        let event = self.cursor.get();
        if event >= self.count {
            return Err(invalid("generator source episode exhausted"));
        }
        let boundary_components = self
            .machine_sites
            .checked_mul(12)
            .ok_or_else(|| invalid("generator source boundary extent"))?;
        if previous_joint.components() < boundary_components
            || encoded_step.rows() != 1
            || encoded_step.components()
                != self
                    .injection_count
                    .checked_mul(6)
                    .ok_or_else(|| invalid("generator source injection width"))?
            || encoded_step.grain() != previous_joint.grain()
        {
            return Err(invalid("generator source step chart"));
        }
        let previous = previous_joint.to_owned().map_err(invalid)?;
        let q = previous
            .view()
            .restrict(0..boundary_components)
            .map_err(invalid)?;
        let q_section = Rc::new(
            q.view()
                .split_rows(self.machine_sites, 12)
                .map_err(invalid)?,
        );
        let advance = MachineValueTransport::new_with_enclosure(
            q_section,
            &(0..self.machine_sites).collect::<Vec<_>>(),
            self.coefficients.clone(),
            self.enclosure.clone(),
        )?;
        let source_rows = encoded_step
            .split_components(self.injection_count)
            .map_err(invalid)?;
        let source_realified = Rc::new(source_rows).realify().map_err(invalid)?;
        let injection = source_realified
            .output()
            .scatter_phase_adjoint(
                &self.injection_indices,
                &vec![ExactWavePhaseTransport::identity(); self.injection_count],
                self.machine_sites,
            )
            .map_err(invalid)?;
        let qsum = advance
            .output()
            .sum_same_shape(&injection)
            .map_err(invalid)?;
        let qsum = qsum.pack_components(self.machine_sites).map_err(invalid)?;
        let qsum = qsum.row(0).map_err(invalid)?.to_owned().map_err(invalid)?;
        let output = if previous_joint.components() == boundary_components {
            qsum
        } else {
            let b = previous
                .view()
                .restrict(boundary_components..previous_joint.components())
                .map_err(invalid)?;
            qsum.view().join(b.view()).map_err(invalid)?
        };
        self.cursor.set(event + 1);
        Ok(GeneratorInjection {
            output,
            advance,
            injection_indices: self.injection_indices.clone(),
            injection_count: self.injection_count,
            event_index: event,
            boundary_components,
        })
    }
}

/// Exact composite phases of one passage of `N` cells.
/// - `standing[g] = (L_g^N, 0)`: the current chart. The resident standing current is a tangent
///   and is carried by the linear part only; this is what the anchor `L^N q₀ + m` reads.
/// - `configuration[g] = U_g^N = (L_g, τ_g)^N`: the configuration chart, where the affine
///   translation acts (the site's configuration after `N` steps; pair geometry
///   `Δ = x_a − x_b` reads configurations, never the current).
/// - `injection[i][j] = L_s^j`, `j < N`, only for injection sites.
/// Powers are formed by repeated squaring (`O(log N)`) or once per injection site, and reused.
pub(super) struct MomentPowers {
    standing: Vec<AffineMap3>,
    #[cfg_attr(not(test), allow(dead_code))]
    configuration: Vec<AffineMap3>,
    injection: Vec<Vec<RatMat3>>,
}

impl MomentPowers {
    pub(super) fn standing(&self) -> &[AffineMap3] {
        &self.standing
    }
    #[cfg_attr(not(test), allow(dead_code))]
    pub(super) fn configuration(&self) -> &[AffineMap3] {
        &self.configuration
    }
    /// `L_s^exponent` for injection position `i`.
    pub(super) fn injection(&self, i: usize, exponent: usize) -> Option<&RatMat3> {
        self.injection.get(i)?.get(exponent)
    }
}

/// The distinct symbols of a passage, sorted.
pub(super) fn present_symbols(symbols: &[usize]) -> Vec<usize> {
    let mut present = symbols.to_vec();
    present.sort_unstable();
    present.dedup();
    present
}

pub(super) fn zero_matrix() -> RatMat3 {
    RatMat3::from_i64([[0; 3]; 3])
}

/// `left ± right`, entrywise.
pub(super) fn add_matrix(left: &RatMat3, right: &RatMat3, subtract: bool) -> RatMat3 {
    RatMat3::new(std::array::from_fn(|r| {
        std::array::from_fn(|c| {
            if subtract {
                &left.rows[r][c] - &right.rows[r][c]
            } else {
                &left.rows[r][c] + &right.rows[r][c]
            }
        })
    }))
}

pub(super) fn moment_powers(
    step_maps: &[AffineMap3],
    injection_indices: &[usize],
    count: usize,
) -> Result<MomentPowers> {
    let exponent = i64::try_from(count).map_err(invalid)?;
    let configuration = step_maps
        .iter()
        .map(|step| super::machine_receiving::signed_affine_power(step, exponent))
        .collect::<Result<Vec<_>>>()?;
    let standing = configuration
        .iter()
        .map(|power| AffineMap3 {
            linear: power.linear.clone(),
            translation: relational_geometry::RatVec3::zero(),
        })
        .collect::<Vec<_>>();
    let mut injection = Vec::new();
    injection
        .try_reserve_exact(injection_indices.len())
        .map_err(|_| invalid("generator moment power allocation"))?;
    for &site in injection_indices {
        let step = step_maps
            .get(site)
            .ok_or_else(|| invalid("generator moment injection site"))?;
        let mut powers = Vec::new();
        powers
            .try_reserve_exact(count)
            .map_err(|_| invalid("generator moment power allocation"))?;
        let mut power = RatMat3::identity();
        for _ in 0..count {
            let next = step.linear.multiply(&power);
            powers.push(std::mem::replace(&mut power, next));
        }
        injection.push(powers);
    }
    Ok(MomentPowers {
        standing,
        configuration,
        injection,
    })
}

impl<'c> MachineSourceMaps<'c> {
    pub(super) fn powers(&self) -> Result<&MomentPowers> {
        if let Some(powers) = self.powers.get() {
            return Ok(powers);
        }
        let powers = moment_powers(&self.step_maps, &self.injection_indices, self.count)?;
        Ok(self.powers.get_or_init(|| powers))
    }
    pub(super) fn injection_indices(&self) -> &[usize] {
        &self.injection_indices
    }
    pub(super) fn enclosure(&self) -> &NativeEnclosurePropagation {
        &self.enclosure
    }
    pub(super) fn surface(&self) -> &'c ResidentSurface<'c> {
        self.coefficients.surface()
    }
    fn boundary_components(&self) -> Result<usize> {
        self.machine_sites
            .checked_mul(12)
            .ok_or_else(|| invalid("generator source boundary extent"))
    }

    /// Linear coefficient rows `L_(s_i)^e` for the supplied `(injection position i, e)` pairs.
    pub(super) fn phase_coefficients(
        &self,
        rows: &[(usize, usize)],
        grain: ResidentGrain,
    ) -> Result<Rc<ResidentNormalEnclosureSection<'c>>> {
        let powers = self.powers()?;
        let mut maps = Vec::new();
        maps.try_reserve_exact(rows.len())
            .map_err(|_| invalid("generator moment coefficient allocation"))?;
        for &(i, exponent) in rows {
            maps.push(AffineMap3 {
                linear: powers
                    .injection(i, exponent)
                    .ok_or_else(|| invalid("generator moment phase exponent"))?
                    .clone(),
                translation: relational_geometry::RatVec3::zero(),
            });
        }
        ResidentNormalEnclosureSection::affine_coefficients(self.surface(), &maps, grain)
            .map_err(invalid)
    }

    fn standing_coefficients(
        &self,
        grain: ResidentGrain,
    ) -> Result<Rc<ResidentNormalEnclosureSection<'c>>> {
        ResidentNormalEnclosureSection::affine_coefficients(
            self.surface(),
            self.powers()?.standing(),
            grain,
        )
        .map_err(invalid)
    }

    /// `(i, N−1−k)` for cell `k` at injection position `i`, cell-major.
    fn cell_rows(&self) -> Vec<(usize, usize)> {
        let n = self.count;
        (0..n)
            .flat_map(|k| (0..self.injection_count).map(move |i| (i, n - 1 - k)))
            .collect()
    }
    fn cell_addresses(&self) -> Vec<usize> {
        (0..self.count)
            .flat_map(|_| self.injection_indices.iter().copied())
            .collect()
    }

    /// The source moment `m = Σ_k L^(N−1−k) I E(u_k)` on the machine boundary (`12G`
    /// components). It reads each cell once and is independent of the standing it meets.
    pub fn moment(
        &self,
        encoded: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<ResidentNormalEnclosure<'c>> {
        let width = self
            .injection_count
            .checked_mul(6)
            .ok_or_else(|| invalid("generator source injection width"))?;
        if encoded.rows() != self.count || encoded.components() != width {
            return Err(invalid("generator source moment chart"));
        }
        let coefficients = self.phase_coefficients(&self.cell_rows(), encoded.grain())?;
        let cells = Rc::new(
            encoded
                .split_components(self.injection_count)
                .map_err(invalid)?,
        )
        .realify()
        .map_err(invalid)?;
        let rows = cells.output().rows();
        let increments = MachineValueTransport::new_with_enclosure(
            cells.output_handle(),
            &(0..rows).collect::<Vec<_>>(),
            coefficients,
            self.enclosure.clone(),
        )?;
        Ok(increments
            .output()
            .scatter_phase_adjoint(
                &self.cell_addresses(),
                &vec![ExactWavePhaseTransport::identity(); rows],
                self.machine_sites,
            )
            .map_err(invalid)?
            .pack_components(self.machine_sites)
            .map_err(invalid)?
            .row(0)
            .map_err(invalid)?
            .to_owned()
            .map_err(invalid)?)
    }

    /// Per-symbol phase-weighted sums `C_(a,i) = Σ_(k: u_k = a) L_(s_i)^(N−1−k)`, kept only for
    /// the symbols present in the passage: returns the sorted present symbols `a_j` and the sums
    /// indexed `j·S + i`. With them `m = Σ_j C_(a_j,·) I E(a_j)` for any encoder table `E`:
    /// storage is `O(distinct symbols × S)`, fixed in `N`, and a later table reads through them.
    pub fn symbol_moment_sums(
        &self,
        symbols: &[usize],
        alphabet: usize,
    ) -> Result<(Vec<usize>, Vec<RatMat3>)> {
        if symbols.len() != self.count || alphabet == 0 || symbols.iter().any(|a| *a >= alphabet) {
            return Err(invalid("generator symbol passage"));
        }
        let present = present_symbols(symbols);
        let s = self.injection_count;
        let rows = present
            .len()
            .checked_mul(s)
            .ok_or_else(|| invalid("generator symbol sum extent"))?;
        let mut sums = Vec::new();
        sums.try_reserve_exact(rows)
            .map_err(|_| invalid("generator symbol sum allocation"))?;
        sums.resize(rows, zero_matrix());
        let powers = self.powers()?;
        let n = self.count;
        for (k, &a) in symbols.iter().enumerate() {
            let j = present
                .binary_search(&a)
                .map_err(|_| invalid("generator symbol presence"))?;
            for i in 0..s {
                let power = powers
                    .injection(i, n - 1 - k)
                    .ok_or_else(|| invalid("generator moment phase exponent"))?;
                sums[j * s + i] = add_matrix(&sums[j * s + i], power, false);
            }
        }
        Ok((present, sums))
    }

    /// Mount phase-weighted sums as linear coefficient rows at `grain`.
    pub(super) fn mount_symbol_sums(
        &self,
        sums: &[RatMat3],
        grain: ResidentGrain,
    ) -> Result<Rc<ResidentNormalEnclosureSection<'c>>> {
        let maps = sums
            .iter()
            .map(|linear| AffineMap3 {
                linear: linear.clone(),
                translation: relational_geometry::RatVec3::zero(),
            })
            .collect::<Vec<_>>();
        ResidentNormalEnclosureSection::affine_coefficients(self.surface(), &maps, grain)
            .map_err(invalid)
    }

    /// Rows `(p, a_j, i)` in sum order `(p·J + j)·S + i` over the present symbols `a_j`.
    fn symbol_rows(&self, present: &[usize], ports: usize) -> Vec<(usize, usize, usize)> {
        let s = self.injection_count;
        (0..ports)
            .flat_map(|p| {
                present
                    .iter()
                    .flat_map(move |&a| (0..s).map(move |i| (p, a, i)))
            })
            .collect()
    }

    /// `Σ_(a,i) K_(p,a,i) I E(a)|_i` at site `s_i`, port `p`: the `G × 12P` field of `ports`
    /// blocks of mounted sums (`p`-major rows `(p, a, i)`) read through the table `E`
    /// (`|A| × 6S`).
    pub(super) fn carry_symbol_table(
        &self,
        table: &ResidentNormalEnclosureSection<'c>,
        sums: &Rc<ResidentNormalEnclosureSection<'c>>,
        ports: usize,
        present: &[usize],
    ) -> Result<ResidentNormalEnclosureSection<'c>> {
        let s = self.injection_count;
        let rows = self.symbol_rows(present, ports);
        if ports == 0
            || present.iter().any(|a| *a >= table.rows())
            || table.components() != s * 6
            || sums.rows() != rows.len()
            || !std::ptr::eq(table.surface(), self.surface())
        {
            return Err(invalid("generator symbol table chart"));
        }
        let cells = Rc::new(table.split_components(s).map_err(invalid)?)
            .realify()
            .map_err(invalid)?;
        let carried = MachineValueTransport::new_with_enclosure(
            cells.output_handle(),
            &rows.iter().map(|&(_, a, i)| a * s + i).collect::<Vec<_>>(),
            Rc::clone(sums),
            self.enclosure.clone(),
        )?;
        let addresses = rows
            .iter()
            .map(|&(p, _, i)| self.injection_indices[i] * ports + p)
            .collect::<Vec<_>>();
        carried
            .output()
            .scatter_phase_adjoint(
                &addresses,
                &vec![ExactWavePhaseTransport::identity(); addresses.len()],
                self.machine_sites * ports,
            )
            .map_err(invalid)?
            .pack_components(ports)
            .map_err(invalid)
    }

    /// Transpose of `carry_symbol_table`: a `G × 12P` covector returns to the table chart
    /// `|A| × 6S` as `Σ_p K_(p,a,i)ᵀ g_(p, s_i)`. Coefficients only; no table value is read.
    pub(super) fn pull_back_symbol_table(
        &self,
        covector: &ResidentNormalEnclosureSection<'c>,
        sums: &Rc<ResidentNormalEnclosureSection<'c>>,
        ports: usize,
        present: &[usize],
        alphabet: usize,
    ) -> Result<ResidentNormalEnclosureSection<'c>> {
        let s = self.injection_count;
        let rows = self.symbol_rows(present, ports);
        if ports == 0
            || present.iter().any(|a| *a >= alphabet)
            || covector.rows() != self.machine_sites
            || covector.components() != 12 * ports
            || sums.rows() != rows.len()
        {
            return Err(invalid("generator symbol table adjoint chart"));
        }
        let grain = covector.grain();
        let site_port = covector.split_components(ports).map_err(invalid)?;
        let addresses = rows
            .iter()
            .map(|&(p, _, i)| self.injection_indices[i] * ports + p)
            .collect::<Vec<_>>();
        let gathered = site_port
            .gather_phase_rows(
                &addresses,
                &vec![ExactWavePhaseTransport::identity(); addresses.len()],
                12,
            )
            .map_err(invalid)?;
        let zero = Rc::new(
            ResidentNormalEnclosureSection::zeros(self.surface(), alphabet * s, 12, grain)
                .map_err(invalid)?,
        );
        let carried = MachineValueTransport::new_with_enclosure(
            zero,
            &rows.iter().map(|&(_, a, i)| a * s + i).collect::<Vec<_>>(),
            Rc::clone(sums),
            self.enclosure.clone(),
        )?;
        Ok(Rc::new(carried.pull_back(&gathered)?)
            .decode_realification()
            .map_err(invalid)?
            .output()
            .pack_components(s)
            .map_err(invalid)?)
    }

    /// `m = Σ_a C_(a,·) I E(a)` on the machine boundary, from mounted symbol sums.
    pub fn symbol_moment(
        &self,
        table: &ResidentNormalEnclosureSection<'c>,
        sums: &Rc<ResidentNormalEnclosureSection<'c>>,
        present: &[usize],
    ) -> Result<ResidentNormalEnclosure<'c>> {
        Ok(self
            .carry_symbol_table(table, sums, 1, present)?
            .pack_components(self.machine_sites)
            .map_err(invalid)?
            .row(0)
            .map_err(invalid)?
            .to_owned()
            .map_err(invalid)?)
    }

    /// `g_E(a)|_i = C_(a,i)ᵀ g_q(s_i)`: the moment's encoder covector, `|A| × 6S`.
    pub fn pull_back_symbol_moment(
        &self,
        full_anchor_gradient: ResidentNormalEnclosureView<'_, 'c>,
        sums: &Rc<ResidentNormalEnclosureSection<'c>>,
        present: &[usize],
        alphabet: usize,
    ) -> Result<ResidentNormalEnclosureSection<'c>> {
        let boundary = self.boundary_components()?;
        if full_anchor_gradient.components() < boundary {
            return Err(invalid("generator source moment adjoint chart"));
        }
        let q_gradient = full_anchor_gradient
            .restrict(0..boundary)
            .map_err(invalid)?
            .view()
            .split_rows(self.machine_sites, 12)
            .map_err(invalid)?;
        self.pull_back_symbol_table(&q_gradient, sums, 1, present, alphabet)
    }

    /// The accumulated field `(L^N q + m) ⊕ b` at the supplied joint cut. A delayed reading
    /// passes the contemporary `(q, b)` and the retained `m`; nothing of an earlier standing enters.
    pub fn anchor(
        &self,
        joint: ResidentNormalEnclosureView<'_, 'c>,
        moment: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<ResidentNormalEnclosure<'c>> {
        let boundary = self.boundary_components()?;
        if joint.components() < boundary
            || moment.components() != boundary
            || moment.grain() != joint.grain()
        {
            return Err(invalid("generator source anchor chart"));
        }
        let q = joint.restrict(0..boundary).map_err(invalid)?;
        let q_section = Rc::new(
            q.view()
                .split_rows(self.machine_sites, 12)
                .map_err(invalid)?,
        );
        let standing = MachineValueTransport::new_with_enclosure(
            q_section,
            &(0..self.machine_sites).collect::<Vec<_>>(),
            self.standing_coefficients(joint.grain())?,
            self.enclosure.clone(),
        )?;
        let standing = standing
            .output()
            .pack_components(self.machine_sites)
            .map_err(invalid)?
            .row(0)
            .map_err(invalid)?
            .to_owned()
            .map_err(invalid)?;
        let q = standing.view().sum_same_shape(moment).map_err(invalid)?;
        if joint.components() == boundary {
            return Ok(q);
        }
        let b = joint
            .restrict(boundary..joint.components())
            .map_err(invalid)?;
        q.view().join(b.view()).map_err(invalid)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    /// Closed form of `N` source steps: `q_N = L^N q₀ + Σ_k L^(N−1−k) I E(u_k)`, `b` unchanged.
    pub fn accumulate(
        &self,
        previous_joint: ResidentNormalEnclosureView<'_, 'c>,
        encoded: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<ResidentNormalEnclosure<'c>> {
        if encoded.grain() != previous_joint.grain() {
            return Err(invalid("generator source moment chart"));
        }
        let moment = self.moment(encoded)?;
        self.anchor(previous_joint, moment.view())
    }

    /// `(L^N)* g_q ⊕ g_b`: the standing term's adjoint, delivered to the `q₀` it was read at.
    pub fn pull_back_standing(
        &self,
        full_anchor_gradient: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<ResidentNormalEnclosure<'c>> {
        let boundary = self.boundary_components()?;
        if full_anchor_gradient.components() < boundary {
            return Err(invalid("generator source moment adjoint chart"));
        }
        let grain = full_anchor_gradient.grain();
        let q_gradient = full_anchor_gradient
            .restrict(0..boundary)
            .map_err(invalid)?
            .view()
            .split_rows(self.machine_sites, 12)
            .map_err(invalid)?;
        // The affine and realification adjoints read only coefficients, so the transport is
        // taken at zero operands.
        let zero = Rc::new(
            ResidentNormalEnclosureSection::zeros(self.surface(), self.machine_sites, 12, grain)
                .map_err(invalid)?,
        );
        let standing = MachineValueTransport::new_with_enclosure(
            zero,
            &(0..self.machine_sites).collect::<Vec<_>>(),
            self.standing_coefficients(grain)?,
            self.enclosure.clone(),
        )?;
        let previous = standing
            .pull_back(&q_gradient)?
            .pack_components(self.machine_sites)
            .map_err(invalid)?
            .row(0)
            .map_err(invalid)?
            .to_owned()
            .map_err(invalid)?;
        if full_anchor_gradient.components() == boundary {
            return Ok(previous);
        }
        let b = full_anchor_gradient
            .restrict(boundary..full_anchor_gradient.components())
            .map_err(invalid)?;
        previous.view().join(b.view()).map_err(invalid)
    }

    /// `g_k = I* (L^(N−1−k))* g_q` for every cell: one covector per occurrence, returned as the
    /// `N × 6S` encoded chart from the coefficients alone. No source row or state is read.
    pub fn pull_back_moment(
        &self,
        full_anchor_gradient: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<ResidentNormalEnclosureSection<'c>> {
        let boundary = self.boundary_components()?;
        if full_anchor_gradient.components() < boundary {
            return Err(invalid("generator source moment adjoint chart"));
        }
        let grain = full_anchor_gradient.grain();
        let q_gradient = full_anchor_gradient
            .restrict(0..boundary)
            .map_err(invalid)?
            .view()
            .split_rows(self.machine_sites, 12)
            .map_err(invalid)?;
        let addresses = self.cell_addresses();
        let rows = addresses.len();
        let cells = q_gradient
            .gather_phase_rows(
                &addresses,
                &vec![ExactWavePhaseTransport::identity(); rows],
                12,
            )
            .map_err(invalid)?;
        let zero = Rc::new(
            ResidentNormalEnclosureSection::zeros(self.surface(), rows, 12, grain)
                .map_err(invalid)?,
        );
        let increments = MachineValueTransport::new_with_enclosure(
            zero,
            &(0..rows).collect::<Vec<_>>(),
            self.phase_coefficients(&self.cell_rows(), grain)?,
            self.enclosure.clone(),
        )?;
        let cells = increments.pull_back(&cells)?;
        Ok(Rc::new(cells)
            .decode_realification()
            .map_err(invalid)?
            .output()
            .pack_components(self.injection_count)
            .map_err(invalid)?)
    }
}

#[cfg_attr(not(test), allow(dead_code))]
impl<'c> GeneratorInjection<'c> {
    pub fn event_index(&self) -> usize {
        self.event_index
    }
    pub fn output(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.output.view()
    }

    pub fn pull_back(
        &self,
        full_anchor_gradient: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<(
        ResidentNormalEnclosure<'c>,
        ResidentNormalEnclosureSection<'c>,
    )> {
        if full_anchor_gradient.components() != self.output.view().components() {
            return Err(invalid("generator source adjoint chart"));
        }
        let q_gradient = full_anchor_gradient
            .restrict(0..self.boundary_components)
            .map_err(invalid)?;
        let q_gradient = Rc::new(
            q_gradient
                .view()
                .split_rows(self.boundary_components / 12, 12)
                .map_err(invalid)?,
        );
        let previous_q = self.advance.pull_back(&q_gradient)?;
        let previous_q = previous_q
            .pack_components(self.boundary_components / 12)
            .map_err(invalid)?
            .row(0)
            .map_err(invalid)?
            .to_owned()
            .map_err(invalid)?;
        let injected = q_gradient
            .gather_phase_rows(
                &self.injection_indices,
                &vec![ExactWavePhaseTransport::identity(); self.injection_count],
                12,
            )
            .map_err(invalid)?;
        let injected = Rc::new(injected).decode_realification().map_err(invalid)?;
        let encoded = injected
            .output()
            .pack_components(self.injection_count)
            .map_err(invalid)?;
        let previous = if full_anchor_gradient.components() == self.boundary_components {
            previous_q
        } else {
            let b = full_anchor_gradient
                .restrict(self.boundary_components..full_anchor_gradient.components())
                .map_err(invalid)?;
            previous_q.view().join(b.view()).map_err(invalid)?
        };
        Ok((previous, encoded))
    }
}

fn witness_exponent(
    site: &CompiledGeneratorSite,
    port: &GeneratorPhasePort,
    event: i64,
) -> Result<i64> {
    site.phase_origin_exponent()
        .checked_add(port.origin_exponent)
        .and_then(|value| port.step_exponent.checked_mul(event)?.checked_add(value))
        .ok_or_else(|| invalid("generator source clock exponent"))
}

#[cfg(test)]
#[path = "machine_source/tests.rs"]
mod tests;
