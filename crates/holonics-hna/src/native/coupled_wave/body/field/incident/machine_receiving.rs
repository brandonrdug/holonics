//! Tagged receiving phases for a frozen generator-machine word.
//!
//! A receiving binding names an ordered machine-site port, its explicit origin/step exponent
//! offsets, a receiving clock, an aperture, and a termination receiver identity.  Exponents are
//! finite signed action counts.  The receiver retains the supplied phase/action and clock scope;
//! it does not infer a turn rate or require finite closure.

use super::machine_transport::MachineValueTransport;
use super::*;
use crate::native::field_geometry::machine::{ClockSpec, CompiledGeneratorSite};
use holonic_engine::native_ecology::constitutive_fibre::ResidentNormalEnclosureSection;
use num_traits::Zero;
use relational_geometry::{AffineMap3, Rat};
use serde::{Deserialize, Serialize};
use std::rc::Rc;

/// One ordered machine receiving port. `j` selects the action exponent
/// `site.phase_origin_exponent + origin_exponent + j * step_exponent`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorPhasePort {
    pub site_id: String,
    pub origin_exponent: i64,
    pub step_exponent: i64,
}

/// A tagged receiving boundary over the frozen generator machine.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename = "generator-phases", deny_unknown_fields)]
pub struct GeneratorPhaseReceiverBinding {
    pub receiver_id: String,
    pub ports: Vec<GeneratorPhasePort>,
    pub clock: ClockSpec,
    pub aperture: usize,
    pub termination_receiver_id: String,
}

impl<'de> Deserialize<'de> for GeneratorPhaseReceiverBinding {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
        enum Wire {
            GeneratorPhases {
                receiver_id: String,
                ports: Vec<GeneratorPhasePort>,
                clock: ClockSpec,
                aperture: usize,
                termination_receiver_id: String,
            },
        }
        let Wire::GeneratorPhases {
            receiver_id,
            ports,
            clock,
            aperture,
            termination_receiver_id,
        } = Wire::deserialize(deserializer)?;
        let binding = Self {
            receiver_id,
            ports,
            clock,
            aperture,
            termination_receiver_id,
        };
        binding.validate().map_err(serde::de::Error::custom)?;
        Ok(binding)
    }
}

impl GeneratorPhaseReceiverBinding {
    fn validate(&self) -> Result<(), NativeSessionError> {
        if self.receiver_id.is_empty() || self.termination_receiver_id.is_empty() {
            return Err(invalid("generator phase receiver identity"));
        }
        if self.ports.is_empty() || self.aperture == 0 {
            return Err(invalid("generator phase receiver aperture/ports"));
        }
        if self.clock.lineage.is_empty() || self.clock.unit.is_empty() {
            return Err(invalid("generator phase receiver clock lineage/unit"));
        }
        if self.clock.duration <= Rat::zero() {
            return Err(invalid("generator phase receiver clock duration"));
        }
        Ok(())
    }
}

/// Resident receiving output for one frozen generated word.
pub struct NativeGeneratorPhaseReception<'c> {
    word: Rc<IncidentWord<'c>>,
    comparison: Option<u64>,
    binding: GeneratorPhaseReceiverBinding,
    transport: MachineValueTransport<'c>,
    output: ResidentNormalEnclosureSection<'c>,
}

impl<'c> NativeGeneratorPhaseReception<'c> {
    pub fn binding(&self) -> &GeneratorPhaseReceiverBinding {
        &self.binding
    }

    pub fn output(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.output
    }

    pub fn producing_epoch(&self) -> u64 {
        self.word.epoch
    }

    pub fn comparison_id(&self) -> Option<u64> {
        self.comparison
    }

    /// Return directly to the public field's complete q/b covector chart. This receiver
    /// reads only the boundary, so the internal-current covector is explicitly zero.
    pub fn pull_back_joint(
        &self,
        gy: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<ResidentNormalEnclosure<'c>, NativeSessionError> {
        let rows = self.pull_back(gy)?;
        let boundary = rows.pack_components(rows.rows())?.row(0)?.to_owned()?;
        let internal = self.word.source.internal_components();
        if internal == 0 {
            return Ok(boundary);
        }
        let zero =
            ResidentNormalEnclosureSection::zeros(rows.surface(), 1, internal, rows.grain())?;
        Ok(boundary.view().join(zero.row(0)?)?)
    }

    /// Pull a packed aperture covector back through the ordered phase ports to full machine
    /// boundary rows. The returned rows retain the machine's width-12 realified chart.
    pub fn pull_back(
        &self,
        gy: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<ResidentNormalEnclosureSection<'c>, NativeSessionError> {
        if gy.rows() != self.binding.aperture
            || gy.components()
                != self
                    .binding
                    .ports
                    .len()
                    .checked_mul(12)
                    .ok_or_else(|| invalid("generator phase receiving width"))?
        {
            return Err(invalid("generator phase receiving covector shape"));
        }
        let unpacked = gy
            .split_components(self.binding.ports.len())
            .map_err(invalid)?;
        self.transport.pull_back(&unpacked)
    }
}

pub(super) fn signed_affine_power(
    action: &AffineMap3,
    exponent: i64,
) -> Result<AffineMap3, NativeSessionError> {
    let (mut base, mut remaining) = if exponent < 0 {
        (
            action
                .inverse()
                .ok_or_else(|| invalid("generator phase action inverse"))?,
            exponent.unsigned_abs(),
        )
    } else {
        (action.clone(), exponent as u64)
    };
    let mut result = AffineMap3::identity();
    while remaining != 0 {
        if remaining & 1 == 1 {
            result = result.followed_by(&base);
        }
        remaining >>= 1;
        if remaining != 0 {
            base = base.followed_by(&base);
        }
    }
    Ok(result)
}

/// The receiving phase's action on the resident current. Chart law: a current is a tangent, so
/// it advances by the linear part `L^j` of the site's affine action; the affine translation acts
/// on the site's configuration only and is not applied to the current.
pub(super) fn receiving_current_map(
    site: &CompiledGeneratorSite,
    exponent: i64,
) -> Result<AffineMap3, NativeSessionError> {
    let action = signed_affine_power(site.phase_action(), exponent)?;
    Ok(AffineMap3 {
        linear: action.linear,
        translation: relational_geometry::RatVec3::zero(),
    })
}

/// The same receiving phase acting on the site's configuration `x₀`, expressed as the
/// displacement map `x ↦ L^j x + (L^j x₀ + τ_j − x₀)` about the initial configuration. This is a
/// configuration chart, never applied to a current.
#[allow(dead_code)]
pub(super) fn receiving_configuration_map(
    site: &CompiledGeneratorSite,
    exponent: i64,
) -> Result<AffineMap3, NativeSessionError> {
    let action = signed_affine_power(site.phase_action(), exponent)?;
    let initial = site.screw().initial();
    let linear = action.linear.clone();
    let bias = linear
        .apply(initial)
        .add(&action.translation)
        .subtract(initial);
    Ok(AffineMap3 {
        linear,
        translation: bias,
    })
}

impl<'c> NativeIncidentGenerated<'c> {
    /// Receive the frozen generated boundary through ordered machine phase ports.
    ///
    /// The machine identity is carried by the producing word. This associated operation therefore
    /// cannot accidentally apply a binding from another body; no contemporary model lookup is
    /// needed. The source/receiver rows stay resident, and the returned aperture packs each
    /// phase's selected ports into one width-`12 * ports` row.
    pub fn receive_generator_phases(
        &self,
        binding: GeneratorPhaseReceiverBinding,
    ) -> Result<NativeGeneratorPhaseReception<'c>, NativeSessionError> {
        binding.validate()?;
        let machine = self
            .word
            .machine
            .as_ref()
            .ok_or_else(|| invalid("generator phase receiving requires a fixed machine"))?;
        let boundary = self.word.source.boundary_components();
        let site_count = machine.sites().len();
        let width = 12usize;
        if boundary != site_count.checked_mul(width).unwrap_or(usize::MAX) {
            return Err(invalid("generator phase machine boundary width"));
        }
        let source = self
            .word
            .output
            .view()
            .restrict(0..boundary)
            .map_err(invalid)?
            .view()
            .split_rows(site_count, width)
            .map_err(invalid)?;
        let source = Rc::new(source);
        let row_count = binding
            .aperture
            .checked_mul(binding.ports.len())
            .ok_or_else(|| invalid("generator phase receiving row extent"))?;
        if row_count > u32::MAX as usize
            || binding.ports.len().checked_mul(12).is_none()
            || binding.ports.len().checked_mul(12).unwrap_or(usize::MAX) > u32::MAX as usize
        {
            return Err(invalid("generator phase receiving extent"));
        }
        let last_j = i64::try_from(binding.aperture - 1).map_err(invalid)?;
        for port in &binding.ports {
            let site = machine
                .sites()
                .iter()
                .find(|site| site.id() == port.site_id)
                .ok_or_else(|| invalid("generator phase port site identity"))?;
            if !site.is_receiver() {
                return Err(invalid("generator phase port is not a receiver site"));
            }
            site.phase_origin_exponent()
                .checked_add(port.origin_exponent)
                .and_then(|value| port.step_exponent.checked_mul(last_j)?.checked_add(value))
                .ok_or_else(|| invalid("generator phase exponent overflow"))?;
        }
        let mut source_indices = Vec::with_capacity(row_count);
        let mut maps = Vec::with_capacity(row_count);
        for j in 0..binding.aperture {
            let j = i64::try_from(j).map_err(invalid)?;
            for port in &binding.ports {
                let site = machine
                    .sites()
                    .iter()
                    .find(|site| site.id() == port.site_id)
                    .ok_or_else(|| invalid("generator phase port site identity"))?;
                let exponent = site
                    .phase_origin_exponent()
                    .checked_add(port.origin_exponent)
                    .and_then(|value| port.step_exponent.checked_mul(j)?.checked_add(value))
                    .ok_or_else(|| invalid("generator phase exponent overflow"))?;
                let map = receiving_current_map(site, exponent)?;
                let index = machine
                    .sites()
                    .iter()
                    .position(|candidate| candidate.id() == site.id())
                    .ok_or_else(|| invalid("generator phase source site index"))?;
                source_indices.push(index);
                maps.push(map);
            }
        }
        let coefficients = ResidentNormalEnclosureSection::affine_coefficients(
            source.surface(),
            &maps,
            source.grain(),
        )
        .map_err(invalid)?;
        let transport = MachineValueTransport::new_with_enclosure(
            source.clone(),
            &source_indices,
            coefficients,
            self.word.enclosure_propagation.clone(),
        )?;
        let output = transport
            .output()
            .pack_components(binding.ports.len())
            .map_err(invalid)?;
        Ok(NativeGeneratorPhaseReception {
            word: Rc::clone(&self.word),
            comparison: self.comparison,
            binding,
            transport,
            output,
        })
    }
}

#[cfg(test)]
#[path = "machine_receiving/tests.rs"]
mod tests;
