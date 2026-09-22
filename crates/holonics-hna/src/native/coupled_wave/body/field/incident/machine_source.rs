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
use relational_geometry::AffineMap3;
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
}

/// The forward source step and its producing map, retained for the reverse source covector.
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
        let coefficients =
            ResidentNormalEnclosureSection::affine_coefficients(surface, &affine_maps, grain)
                .map_err(invalid)?;
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
