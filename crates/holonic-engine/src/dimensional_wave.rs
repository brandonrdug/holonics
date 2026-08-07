//! Exact lossless wave current on a caused dimensional carrier ecology.
//!
//! A retained chronology is not motion.  This module therefore gives an
//! [`ExactDimensionalSource`] a separate physical realization in which exact
//! complex currents occupy oriented carrier ends, travel for declared local
//! delays, and scatter only at incident source germs.  The hot transition
//! follows the sparse arriving front and each reached germ's contiguous local
//! port population; it does not scan the receiver matrix or infer contact from
//! projected proximity.
//!
//! The scattering law is the lossless transmission-line junction law.  If
//! `a_i` is the wave arriving through a port of admittance `Y_i`, the passive
//! junction potential and departing waves are
//!
//! ```text
//! v = 2 Σ(Y_i a_i) / ΣY_i
//! b_i = v - a_i .
//! ```
//!
//! Hence `Σ Y_i |a_i|² = Σ Y_i |b_i|²` exactly.  A caused junction impulse
//! adds to `v`; its exact work is retained instead of being hidden as loss.
//! Every traversal also carries the exact unit-conic change of basis between
//! the source germ and target germ.  The reverse traversal carries its
//! inverse.  Multiple finite-place modes may therefore propagate
//! simultaneously without being flattened into one scalar cell.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;
use num_traits::{One, Signed, Zero};
use relational_geometry::{Rat, ReceiverId};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    CoordinateCarrierId, CoordinateGermId, DimensionalAxisId, DimensionalCarrierDisposition,
    DimensionalGermDisposition, DimensionalSliceReceipt, EventId, EventSuccessor,
    ExactDimensionalSource, ExactEventLaw, LogicalResourceReceipt,
};

const STANDING_SCHEMA: &str = "holonic-engine.exact-dimensional-wave-standing.v1";
const RECEIPT_SCHEMA: &str = "holonic-engine.exact-dimensional-wave-receipt.v1";
const SLICE_SCHEMA: &str = "holonic-engine.dimensional-wave-slice-receipt.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DimensionalWaveModeId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DimensionalWavePortId(pub u64);

/// One exact complex traveling population.
///
/// The two components are a local phase pair.  They are not screen
/// coordinates and are never converted to floating point by this law.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ExactComplexWaveCurrent {
    pub real: Rat,
    pub imaginary: Rat,
}

impl ExactComplexWaveCurrent {
    pub fn new(real: Rat, imaginary: Rat) -> Self {
        Self { real, imaginary }
    }

    pub fn zero() -> Self {
        Self::default()
    }

    pub fn is_zero(&self) -> bool {
        self.real.is_zero() && self.imaginary.is_zero()
    }

    pub fn norm_square(&self) -> Rat {
        &self.real * &self.real + &self.imaginary * &self.imaginary
    }

    fn add_assign(&mut self, other: &Self) {
        self.real += &other.real;
        self.imaginary += &other.imaginary;
    }

    fn scaled(&self, coefficient: &Rat) -> Self {
        Self {
            real: coefficient * &self.real,
            imaginary: coefficient * &self.imaginary,
        }
    }

    fn subtract(&self, other: &Self) -> Self {
        Self {
            real: &self.real - &other.real,
            imaginary: &self.imaginary - &other.imaginary,
        }
    }

    fn rotate(&self, cosine: &Rat, sine: &Rat) -> Self {
        Self {
            real: cosine * &self.real - sine * &self.imaginary,
            imaginary: sine * &self.real + cosine * &self.imaginary,
        }
    }
}

/// The exact co-present modal population at one receiver contact.
///
/// Currents with the same mode add before any quadratic response is formed:
/// their relative phase can therefore reinforce or cancel. Distinct modes
/// remain separate until the receiver doctrine acts, so unrelated spectral
/// bands cannot cancel merely because a terminal membrane gives them the same
/// address. `support_multiplicity` is neutral analytical support presented
/// beside the current; it is not an RGB label or an additional wave mode.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ExactReceiverPhasePopulation {
    pub coherent_modes: BTreeMap<DimensionalWaveModeId, ExactComplexWaveCurrent>,
    pub support_multiplicity: BigUint,
}

impl ExactReceiverPhasePopulation {
    pub fn receive(&mut self, mode: DimensionalWaveModeId, current: &ExactComplexWaveCurrent) {
        if current.is_zero() {
            return;
        }
        let entry = self.coherent_modes.entry(mode).or_default();
        entry.add_assign(current);
        if entry.is_zero() {
            self.coherent_modes.remove(&mode);
        }
    }

    pub fn add_support(&mut self, multiplicity: BigUint) {
        self.support_multiplicity += multiplicity;
    }

    pub fn is_empty(&self) -> bool {
        self.coherent_modes.is_empty() && self.support_multiplicity.is_zero()
    }
}

/// One exact four-coordinate response of a declared outer receiver.
///
/// The first three values are premultiplied monitor-primary coordinates.
/// `alpha` is the caused interaction/coverage response of this membrane, not a
/// fourth source wavelength. Consequently the three primary coordinates sum
/// exactly to alpha, and alpha plus transmittance is exactly one.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactPremultipliedReceiverResponse {
    pub primaries: [Rat; 3],
    pub alpha: Rat,
    pub transmittance: Rat,
}

/// A declared receiver transduction from an exact modal population to four
/// coupled terminal coordinates.
///
/// The substrate retains complex amplitudes by mode. The doctrine first
/// forms three exact quadratic phase responses
///
/// `(|Re A|², |Im A|², |Re A + Im A|²)`
///
/// after same-mode superposition, adds neutral analytical-support response,
/// and only then applies the exact saturating aperture
///
/// `primary_j = P_j / (aperture + ΣP)`.
///
/// This is an inspectable display gauge. It is not a universal color law and
/// does not identify phase, wavelength, or a source constituent with red,
/// green, blue, or opacity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactReceiverPrimaryDoctrine {
    pub aperture: Rat,
    pub support_response: Rat,
}

impl ExactReceiverPrimaryDoctrine {
    pub fn new(aperture: Rat, support_response: Rat) -> Result<Self, DimensionalWaveError> {
        if !aperture.is_positive() || support_response.is_negative() {
            return Err(DimensionalWaveError::MalformedReceiverPrimaryDoctrine);
        }
        Ok(Self {
            aperture,
            support_response,
        })
    }

    pub fn transduce(
        &self,
        population: &ExactReceiverPhasePopulation,
    ) -> ExactPremultipliedReceiverResponse {
        let support = &self.support_response
            * Rat::from_integer(population.support_multiplicity.clone().into());
        let mut responses = [support.clone(), support.clone(), support];
        for current in population.coherent_modes.values() {
            responses[0] += &current.real * &current.real;
            responses[1] += &current.imaginary * &current.imaginary;
            let diagonal = &current.real + &current.imaginary;
            responses[2] += &diagonal * &diagonal;
        }
        let total = responses
            .iter()
            .fold(Rat::zero(), |sum, response| sum + response);
        let denominator = &self.aperture + &total;
        let primaries = responses.map(|response| response / &denominator);
        let alpha = &total / &denominator;
        let transmittance = &self.aperture / denominator;
        debug_assert_eq!(
            primaries
                .iter()
                .fold(Rat::zero(), |sum, response| sum + response),
            alpha
        );
        debug_assert_eq!(&alpha + &transmittance, Rat::one());
        ExactPremultipliedReceiverResponse {
            primaries,
            alpha,
            transmittance,
        }
    }
}

/// One source finite-place or other exact phase species.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalWaveMode {
    pub id: DimensionalWaveModeId,
    pub name: String,
    pub real_axis: DimensionalAxisId,
    pub imaginary_axis: DimensionalAxisId,
}

/// One exact unitary phase transport carried by a physical section.
///
/// Endpoint coordinates can derive this relation when they determine the
/// path.  An analytical section with interior winding may instead declare the
/// caused transport explicitly.  The relation remains mode-local and must lie
/// on the exact unit conic; it is never inferred from a rendered angle.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactWavePhaseTransport {
    pub cosine: Rat,
    pub sine: Rat,
}

impl ExactWavePhaseTransport {
    pub fn new(cosine: Rat, sine: Rat) -> Result<Self, DimensionalWaveError> {
        let transport = Self { cosine, sine };
        if !transport.is_unit() {
            return Err(DimensionalWaveError::NonunitDeclaredPhaseTransport);
        }
        Ok(transport)
    }

    pub fn identity() -> Self {
        Self {
            cosine: Rat::one(),
            sine: Rat::zero(),
        }
    }

    pub fn is_unit(&self) -> bool {
        &self.cosine * &self.cosine + &self.sine * &self.sine == Rat::one()
    }

    pub fn inverse(&self) -> Self {
        Self {
            cosine: self.cosine.clone(),
            sine: -self.sine.clone(),
        }
    }

    pub fn compose(&self, next: &Self) -> Self {
        Self {
            cosine: &next.cosine * &self.cosine - &next.sine * &self.sine,
            sine: &next.sine * &self.cosine + &next.cosine * &self.sine,
        }
    }

    pub fn pow(&self, mut exponent: u32) -> Self {
        let mut factor = self.clone();
        let mut product = Self::identity();
        while exponent > 0 {
            if exponent & 1 == 1 {
                product = product.compose(&factor);
            }
            exponent >>= 1;
            if exponent > 0 {
                factor = factor.compose(&factor);
            }
        }
        product
    }

    pub fn transport(&self, current: &ExactComplexWaveCurrent) -> ExactComplexWaveCurrent {
        current.rotate(&self.cosine, &self.sine)
    }
}

/// Application-owned physical realization of one source carrier.
///
/// Delay and admittance are constitutive data.  They are not inferred from a
/// rendered length, color, or proximity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalWaveCarrierDoctrine {
    pub carrier: CoordinateCarrierId,
    pub delay: u32,
    /// Empty admits every compiled mode. A nonempty set is the exact
    /// constitutive incidence of modes which can travel on this section.
    /// Excluded modes do not receive a zero-valued carrier; the carrier is
    /// absent from their local topology.
    #[serde(default)]
    pub admitted_modes: BTreeSet<DimensionalWaveModeId>,
    /// Default admittance for every admitted mode which has no more specific
    /// constitutive value below.
    pub admittance: Rat,
    /// Dispersion or another material distinction may give one mode a
    /// different exact effective admittance on the same physical section.
    #[serde(default)]
    pub modal_admittance: BTreeMap<DimensionalWaveModeId, Rat>,
    /// A section-local phase relation may retain winding which its two
    /// endpoint coordinates cannot determine. Missing modes lawfully fall
    /// back to the source endpoint relation.
    #[serde(default)]
    pub phase_transport: BTreeMap<DimensionalWaveModeId, ExactWavePhaseTransport>,
}

#[derive(Clone, Debug)]
struct CompiledWavePort {
    id: DimensionalWavePortId,
    mode: DimensionalWaveModeId,
    carrier: CoordinateCarrierId,
    at: CoordinateGermId,
    other: CoordinateGermId,
    opposite: DimensionalWavePortId,
    junction: usize,
    delay: u32,
    admittance: Rat,
    transport_cosine: Rat,
    transport_sine: Rat,
}

#[derive(Clone, Debug)]
struct CompiledWaveJunction {
    mode: DimensionalWaveModeId,
    germ: CoordinateGermId,
    ports: Vec<DimensionalWavePortId>,
    total_admittance: Rat,
}

#[derive(Clone, Debug)]
struct CompiledWaveTopology {
    ports: Vec<CompiledWavePort>,
    junctions: Vec<CompiledWaveJunction>,
    port_by_incidence: BTreeMap<
        (DimensionalWaveModeId, CoordinateCarrierId, CoordinateGermId),
        DimensionalWavePortId,
    >,
    junction_by_mode_germ: BTreeMap<(DimensionalWaveModeId, CoordinateGermId), usize>,
    ring_extent: usize,
}

/// One caused voltage-like departure at a local modal junction.
///
/// The impulse changes the junction response during this event.  It is not a
/// pre-authored answer or a wave teleported to a distant carrier.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalWaveImpulse {
    pub source_event: EventId,
    pub mode: DimensionalWaveModeId,
    pub germ: CoordinateGermId,
    pub departure: ExactComplexWaveCurrent,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalWaveEvent {
    pub event: EventId,
    pub impulses: Vec<DimensionalWaveImpulse>,
}

/// Sparse, bounded-delay standing.
///
/// `active_slots` is the production traversal surface.  The dense arrays give
/// every compiled port a stable address, but no transition scans those
/// addresses to discover work.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactDimensionalWaveStanding {
    pub schema: String,
    pub tick: u64,
    pub energy: Rat,
    ring_cursor: usize,
    port_count: usize,
    arrival_values: Vec<ExactComplexWaveCurrent>,
    listed: Vec<bool>,
    active_slots: Vec<Vec<DimensionalWavePortId>>,
    used_events: BTreeSet<EventId>,
}

impl ExactDimensionalWaveStanding {
    pub fn active_arrival_count(&self) -> usize {
        self.active_slots
            .iter()
            .enumerate()
            .map(|(slot_ordinal, slot)| {
                slot.iter()
                    .filter(|port| {
                        let ordinal = usize::try_from(port.0).expect("compiled port fits usize");
                        !self.arrival_values[slot_ordinal * self.port_count + ordinal].is_zero()
                    })
                    .count()
            })
            .sum()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalWaveArrivalReceipt {
    pub port: DimensionalWavePortId,
    pub mode: DimensionalWaveModeId,
    pub carrier: CoordinateCarrierId,
    pub at: CoordinateGermId,
    pub from: CoordinateGermId,
    pub current: ExactComplexWaveCurrent,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalWavePortCurrentReceipt {
    pub port: DimensionalWavePortId,
    pub carrier: CoordinateCarrierId,
    pub current: ExactComplexWaveCurrent,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalWaveScatterReceipt {
    pub mode: DimensionalWaveModeId,
    pub germ: CoordinateGermId,
    pub arrivals: Vec<DimensionalWavePortCurrentReceipt>,
    pub passive_departure: ExactComplexWaveCurrent,
    pub caused_departure: ExactComplexWaveCurrent,
    pub departures: Vec<DimensionalWavePortCurrentReceipt>,
    pub energy_entered: Rat,
    pub energy_departed: Rat,
    pub source_work: Rat,
    pub passive_residual: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalWaveDepartureReceipt {
    pub port: DimensionalWavePortId,
    pub target_port: DimensionalWavePortId,
    pub mode: DimensionalWaveModeId,
    pub carrier: CoordinateCarrierId,
    pub from: CoordinateGermId,
    pub to: CoordinateGermId,
    pub local_current: ExactComplexWaveCurrent,
    pub transported_current: ExactComplexWaveCurrent,
    pub delay: u32,
    pub arrival_tick: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalWaveReceipt {
    pub schema: String,
    pub event: EventId,
    pub tick_before: u64,
    pub tick_after: u64,
    pub arrivals: Vec<DimensionalWaveArrivalReceipt>,
    pub scatters: Vec<DimensionalWaveScatterReceipt>,
    pub departures: Vec<DimensionalWaveDepartureReceipt>,
    pub energy_before: Rat,
    pub source_work: Rat,
    pub energy_after: Rat,
    pub exact_energy_residual: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VisibleDimensionalWaveSection {
    pub from_horizontal: Rat,
    pub from_vertical: Rat,
    pub to_horizontal: Rat,
    pub to_vertical: Rat,
    pub elapsed: u32,
    pub delay: u32,
    pub projected_span_square: Rat,
    pub projected_speed_square: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DimensionalWaveSectionDisposition {
    Visible(Box<VisibleDimensionalWaveSection>),
    CarrierOutside,
    EndpointUnresolved,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalTravelingWaveSection {
    pub mode: DimensionalWaveModeId,
    pub carrier: CoordinateCarrierId,
    pub from: CoordinateGermId,
    pub to: CoordinateGermId,
    pub current: ExactComplexWaveCurrent,
    pub energy: Rat,
    pub ticks_until_arrival: u32,
    pub disposition: DimensionalWaveSectionDisposition,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalWaveModeMeasure {
    pub mode: DimensionalWaveModeId,
    pub traveling_sections: usize,
    pub visible_sections: usize,
    pub energy: Rat,
    /// Energy-weighted receiver-projected squared rate.  It is testimony
    /// about this chart, not an intrinsic source velocity.
    pub projected_rate_moment: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalWaveSliceReceipt {
    pub schema: String,
    pub receiver: ReceiverId,
    pub receiver_event: EventId,
    pub receiver_chronology: u64,
    pub wave_tick: u64,
    pub total_energy: Rat,
    pub sections: Vec<DimensionalTravelingWaveSection>,
    pub mode_measures: Vec<DimensionalWaveModeMeasure>,
}

/// One intrinsic traveling section before any receiver chart is selected.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntrinsicDimensionalTravelingWaveSection {
    pub mode: DimensionalWaveModeId,
    pub carrier: CoordinateCarrierId,
    pub from: CoordinateGermId,
    pub to: CoordinateGermId,
    /// Current expressed in the target port's local phase basis.
    pub target_current: ExactComplexWaveCurrent,
    pub energy: Rat,
    pub elapsed: u32,
    pub delay: u32,
    pub ticks_until_arrival: u32,
}

#[derive(Clone, Debug)]
pub struct ExactDimensionalWaveLaw {
    source: ExactDimensionalSource,
    modes: Vec<DimensionalWaveMode>,
    doctrines: Vec<DimensionalWaveCarrierDoctrine>,
    topology: CompiledWaveTopology,
}

impl ExactDimensionalWaveLaw {
    pub fn new(
        source: ExactDimensionalSource,
        mut modes: Vec<DimensionalWaveMode>,
        mut doctrines: Vec<DimensionalWaveCarrierDoctrine>,
    ) -> Result<Self, DimensionalWaveError> {
        source.validate()?;
        modes.sort_by_key(|mode| mode.id);
        doctrines.sort_by_key(|doctrine| doctrine.carrier);
        validate_modes(&source, &modes)?;
        validate_doctrines(&source, &modes, &doctrines)?;
        let topology = compile_topology(&source, &modes, &doctrines)?;
        Ok(Self {
            source,
            modes,
            doctrines,
            topology,
        })
    }

    pub fn source(&self) -> &ExactDimensionalSource {
        &self.source
    }

    pub fn modes(&self) -> &[DimensionalWaveMode] {
        &self.modes
    }

    pub fn doctrines(&self) -> &[DimensionalWaveCarrierDoctrine] {
        &self.doctrines
    }

    pub fn port_population(&self) -> usize {
        self.topology.ports.len()
    }

    pub fn junction_population(&self) -> usize {
        self.topology.junctions.len()
    }

    pub fn has_junction(&self, mode: DimensionalWaveModeId, germ: CoordinateGermId) -> bool {
        self.topology
            .junction_by_mode_germ
            .contains_key(&(mode, germ))
    }

    pub fn port_at(
        &self,
        mode: DimensionalWaveModeId,
        carrier: CoordinateCarrierId,
        germ: CoordinateGermId,
    ) -> Option<DimensionalWavePortId> {
        self.topology
            .port_by_incidence
            .get(&(mode, carrier, germ))
            .copied()
    }

    pub fn initial_standing(&self) -> ExactDimensionalWaveStanding {
        let extent = self.topology.ring_extent * self.topology.ports.len();
        ExactDimensionalWaveStanding {
            schema: STANDING_SCHEMA.to_owned(),
            tick: 0,
            energy: Rat::zero(),
            ring_cursor: 0,
            port_count: self.topology.ports.len(),
            arrival_values: vec![ExactComplexWaveCurrent::zero(); extent],
            listed: vec![false; extent],
            active_slots: vec![Vec::new(); self.topology.ring_extent],
            used_events: BTreeSet::new(),
        }
    }

    pub fn intrinsic_sections(
        &self,
        standing: &ExactDimensionalWaveStanding,
    ) -> Result<Vec<IntrinsicDimensionalTravelingWaveSection>, DimensionalWaveError> {
        self.validate_standing_shape(standing)?;
        let mut sections = Vec::new();
        for slot in 0..self.topology.ring_extent {
            let delta = (slot + self.topology.ring_extent - standing.ring_cursor)
                % self.topology.ring_extent;
            let ticks_until_arrival =
                u32::try_from(delta + 1).map_err(|_| DimensionalWaveError::CarrierOverflow)?;
            for port_id in &standing.active_slots[slot] {
                let ordinal = port_ordinal(*port_id, self.topology.ports.len())?;
                let current = &standing.arrival_values[slot * standing.port_count + ordinal];
                if current.is_zero() {
                    continue;
                }
                let target_port = &self.topology.ports[ordinal];
                let source_port = &self.topology.ports
                    [port_ordinal(target_port.opposite, self.topology.ports.len())?];
                let elapsed = target_port
                    .delay
                    .checked_sub(ticks_until_arrival)
                    .ok_or(DimensionalWaveError::MalformedStanding)?;
                sections.push(IntrinsicDimensionalTravelingWaveSection {
                    mode: target_port.mode,
                    carrier: target_port.carrier,
                    from: source_port.at,
                    to: target_port.at,
                    target_current: current.clone(),
                    energy: &target_port.admittance * current.norm_square(),
                    elapsed,
                    delay: target_port.delay,
                    ticks_until_arrival,
                });
            }
        }
        sections.sort_by_key(|section| {
            (
                section.mode,
                section.carrier,
                section.from,
                section.to,
                section.ticks_until_arrival,
            )
        });
        Ok(sections)
    }

    pub fn validate_standing(
        &self,
        standing: &ExactDimensionalWaveStanding,
    ) -> Result<(), DimensionalWaveError> {
        self.validate_standing_shape(standing)?;
        let expected_extent = self.topology.ring_extent * self.topology.ports.len();
        let mut witnessed = vec![false; expected_extent];
        for (slot, ports) in standing.active_slots.iter().enumerate() {
            for port in ports {
                let port = port_ordinal(*port, self.topology.ports.len())?;
                let address = slot * standing.port_count + port;
                if witnessed[address] || !standing.listed[address] {
                    return Err(DimensionalWaveError::MalformedStanding);
                }
                witnessed[address] = true;
            }
        }
        if witnessed != standing.listed {
            return Err(DimensionalWaveError::MalformedStanding);
        }
        if standing
            .arrival_values
            .iter()
            .enumerate()
            .any(|(address, value)| !value.is_zero() && !witnessed[address])
        {
            return Err(DimensionalWaveError::MalformedStanding);
        }
        let energy = standing
            .arrival_values
            .iter()
            .enumerate()
            .filter(|(_, current)| !current.is_zero())
            .fold(Rat::zero(), |sum, (address, current)| {
                let port = address % standing.port_count;
                sum + &self.topology.ports[port].admittance * current.norm_square()
            });
        if standing.energy != energy {
            return Err(DimensionalWaveError::EnergyStandingMismatch);
        }
        Ok(())
    }

    /// Constant-time structural guard used by a succession whose standing was
    /// produced by this law. Complete population and energy revalidation is a
    /// rest/remount or explicit observation deed, not a per-front traversal.
    fn validate_standing_shape(
        &self,
        standing: &ExactDimensionalWaveStanding,
    ) -> Result<(), DimensionalWaveError> {
        let expected_extent = self.topology.ring_extent * self.topology.ports.len();
        if standing.schema != STANDING_SCHEMA
            || standing.port_count != self.topology.ports.len()
            || standing.ring_cursor >= self.topology.ring_extent
            || standing.ring_cursor
                != usize::try_from(
                    standing.tick
                        % u64::try_from(self.topology.ring_extent)
                            .map_err(|_| DimensionalWaveError::CarrierOverflow)?,
                )
                .map_err(|_| DimensionalWaveError::CarrierOverflow)?
            || standing.arrival_values.len() != expected_extent
            || standing.listed.len() != expected_extent
            || standing.active_slots.len() != self.topology.ring_extent
            || standing.energy.is_negative()
        {
            return Err(DimensionalWaveError::MalformedStanding);
        }
        Ok(())
    }

    pub fn restrict(
        &self,
        standing: &ExactDimensionalWaveStanding,
        receiver: &DimensionalSliceReceipt,
    ) -> Result<DimensionalWaveSliceReceipt, DimensionalWaveError> {
        self.validate_standing_shape(standing)?;
        let mut sections = Vec::new();
        let mut measures = self
            .modes
            .iter()
            .map(|mode| {
                (
                    mode.id,
                    DimensionalWaveModeMeasure {
                        mode: mode.id,
                        traveling_sections: 0,
                        visible_sections: 0,
                        energy: Rat::zero(),
                        projected_rate_moment: Rat::zero(),
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();

        for intrinsic in self.intrinsic_sections(standing)? {
            let current = &intrinsic.target_current;
            let target_port = &self.topology.ports[port_ordinal(
                self.topology.port_by_incidence[&(intrinsic.mode, intrinsic.carrier, intrinsic.to)],
                self.topology.ports.len(),
            )?];
            let source_port = &self.topology.ports
                [port_ordinal(target_port.opposite, self.topology.ports.len())?];
            let energy = intrinsic.energy;
            let carrier_disposition = receiver
                .carriers
                .get(&target_port.carrier)
                .ok_or(DimensionalWaveError::ReceiverSourceMismatch)?;
            let from_disposition = receiver
                .germs
                .get(&source_port.at)
                .ok_or(DimensionalWaveError::ReceiverSourceMismatch)?;
            let to_disposition = receiver
                .germs
                .get(&target_port.at)
                .ok_or(DimensionalWaveError::ReceiverSourceMismatch)?;
            let disposition = match (
                &carrier_disposition.disposition,
                &from_disposition.disposition,
                &to_disposition.disposition,
            ) {
                (
                    DimensionalCarrierDisposition::Visible,
                    DimensionalGermDisposition::Visible {
                        normalized_horizontal: from_horizontal,
                        normalized_vertical: from_vertical,
                        ..
                    },
                    DimensionalGermDisposition::Visible {
                        normalized_horizontal: to_horizontal,
                        normalized_vertical: to_vertical,
                        ..
                    },
                ) => {
                    let horizontal = to_horizontal - from_horizontal;
                    let vertical = to_vertical - from_vertical;
                    let projected_span_square = &horizontal * &horizontal + &vertical * &vertical;
                    let delay = Rat::from_integer(target_port.delay.into());
                    let projected_speed_square = &projected_span_square / (&delay * &delay);
                    DimensionalWaveSectionDisposition::Visible(Box::new(
                        VisibleDimensionalWaveSection {
                            from_horizontal: from_horizontal.clone(),
                            from_vertical: from_vertical.clone(),
                            to_horizontal: to_horizontal.clone(),
                            to_vertical: to_vertical.clone(),
                            elapsed: intrinsic.elapsed,
                            delay: target_port.delay,
                            projected_span_square,
                            projected_speed_square,
                        },
                    ))
                }
                (_, DimensionalGermDisposition::Unresolved { .. }, _)
                | (_, _, DimensionalGermDisposition::Unresolved { .. }) => {
                    DimensionalWaveSectionDisposition::EndpointUnresolved
                }
                _ => DimensionalWaveSectionDisposition::CarrierOutside,
            };
            let measure = measures
                .get_mut(&target_port.mode)
                .ok_or(DimensionalWaveError::MalformedTopology)?;
            measure.traveling_sections += 1;
            measure.energy += &energy;
            if let DimensionalWaveSectionDisposition::Visible(visible) = &disposition {
                measure.visible_sections += 1;
                measure.projected_rate_moment += &energy * &visible.projected_speed_square;
            }
            sections.push(DimensionalTravelingWaveSection {
                mode: target_port.mode,
                carrier: target_port.carrier,
                from: source_port.at,
                to: target_port.at,
                current: current.clone(),
                energy,
                ticks_until_arrival: intrinsic.ticks_until_arrival,
                disposition,
            });
        }
        sections.sort_by_key(|section| {
            (
                section.mode,
                section.carrier,
                section.from,
                section.to,
                section.ticks_until_arrival,
            )
        });
        Ok(DimensionalWaveSliceReceipt {
            schema: SLICE_SCHEMA.to_owned(),
            receiver: receiver.receiver,
            receiver_event: receiver.event,
            receiver_chronology: receiver.chronology,
            wave_tick: standing.tick,
            total_energy: standing.energy.clone(),
            sections,
            mode_measures: measures.into_values().collect(),
        })
    }

    fn enact_wave(
        &self,
        standing_before: &ExactDimensionalWaveStanding,
        event: &DimensionalWaveEvent,
    ) -> Result<(ExactDimensionalWaveStanding, DimensionalWaveReceipt), DimensionalWaveError> {
        self.validate_standing_shape(standing_before)?;
        if standing_before.used_events.contains(&event.event) {
            return Err(DimensionalWaveError::RepeatedEvent(event.event));
        }
        let mut standing = standing_before.clone();
        standing.used_events.insert(event.event);
        let tick_before = standing.tick;
        let energy_before = standing.energy.clone();
        let cursor = standing.ring_cursor;

        let mut arrivals = take_arrivals(&mut standing, &self.topology, cursor)?;
        arrivals.sort_by_key(|arrival| {
            let port = &self.topology.ports[arrival.port];
            (port.junction, port.id)
        });

        let mut impulses = event.impulses.clone();
        impulses.sort_by_key(|impulse| (impulse.mode, impulse.germ, impulse.source_event));
        validate_impulses(self, &impulses)?;

        let mut active_junctions = BTreeSet::new();
        let mut arrivals_by_junction =
            BTreeMap::<usize, Vec<(DimensionalWavePortId, ExactComplexWaveCurrent)>>::new();
        for arrival in &arrivals {
            let port = &self.topology.ports[arrival.port];
            active_junctions.insert(port.junction);
            arrivals_by_junction
                .entry(port.junction)
                .or_default()
                .push((port.id, arrival.current.clone()));
        }
        let mut impulses_by_junction = BTreeMap::<usize, Vec<ExactComplexWaveCurrent>>::new();
        for impulse in &impulses {
            let junction = self.topology.junction_by_mode_germ[&(impulse.mode, impulse.germ)];
            active_junctions.insert(junction);
            impulses_by_junction
                .entry(junction)
                .or_default()
                .push(impulse.departure.clone());
        }

        let arrival_receipts = arrivals
            .iter()
            .map(|arrival| {
                let port = &self.topology.ports[arrival.port];
                DimensionalWaveArrivalReceipt {
                    port: port.id,
                    mode: port.mode,
                    carrier: port.carrier,
                    at: port.at,
                    from: port.other,
                    current: arrival.current.clone(),
                }
            })
            .collect::<Vec<_>>();
        let mut scatter_receipts = Vec::with_capacity(active_junctions.len());
        let mut departure_receipts = Vec::new();
        let mut total_source_work = Rat::zero();

        for junction_ordinal in active_junctions {
            let junction = &self.topology.junctions[junction_ordinal];
            let incoming_by_port = arrivals_by_junction
                .remove(&junction_ordinal)
                .unwrap_or_default()
                .into_iter()
                .collect::<BTreeMap<_, _>>();
            let caused_departure = impulses_by_junction
                .remove(&junction_ordinal)
                .unwrap_or_default()
                .iter()
                .fold(ExactComplexWaveCurrent::zero(), |mut sum, departure| {
                    sum.add_assign(departure);
                    sum
                });
            let weighted_incoming =
                junction
                    .ports
                    .iter()
                    .fold(ExactComplexWaveCurrent::zero(), |mut sum, port_id| {
                        if let Some(incoming) = incoming_by_port.get(port_id) {
                            let port = &self.topology.ports[port_ordinal(
                                *port_id,
                                self.topology.ports.len(),
                            )
                            .expect("compiled junction ports are valid")];
                            sum.add_assign(&incoming.scaled(&port.admittance));
                        }
                        sum
                    });
            let passive_departure = weighted_incoming
                .scaled(&(Rat::from_integer(2.into()) / &junction.total_admittance));
            let mut junction_departure = passive_departure.clone();
            junction_departure.add_assign(&caused_departure);
            let energy_entered = junction.ports.iter().fold(Rat::zero(), |sum, port_id| {
                incoming_by_port
                    .get(port_id)
                    .map_or(sum.clone(), |incoming| {
                        let port =
                            &self.topology.ports[port_ordinal(*port_id, self.topology.ports.len())
                                .expect("compiled junction ports are valid")];
                        sum + &port.admittance * incoming.norm_square()
                    })
            });
            let mut local_departures = Vec::new();
            let mut energy_departed = Rat::zero();

            for port_id in &junction.ports {
                let port_index = port_ordinal(*port_id, self.topology.ports.len())?;
                let port = &self.topology.ports[port_index];
                let incoming = incoming_by_port
                    .get(port_id)
                    .cloned()
                    .unwrap_or_else(ExactComplexWaveCurrent::zero);
                let local_current = junction_departure.subtract(&incoming);
                if local_current.is_zero() {
                    continue;
                }
                energy_departed += &port.admittance * local_current.norm_square();
                local_departures.push(DimensionalWavePortCurrentReceipt {
                    port: *port_id,
                    carrier: port.carrier,
                    current: local_current.clone(),
                });
                let transported_current =
                    local_current.rotate(&port.transport_cosine, &port.transport_sine);
                if transported_current.norm_square() != local_current.norm_square() {
                    return Err(DimensionalWaveError::NonunitPhaseTransport(port.id));
                }
                let target_ordinal = port_ordinal(port.opposite, self.topology.ports.len())?;
                let target = &self.topology.ports[target_ordinal];
                let slot = (cursor
                    + usize::try_from(port.delay)
                        .map_err(|_| DimensionalWaveError::CarrierOverflow)?)
                    % self.topology.ring_extent;
                schedule_arrival(
                    &mut standing,
                    &self.topology,
                    slot,
                    target_ordinal,
                    &transported_current,
                )?;
                departure_receipts.push(DimensionalWaveDepartureReceipt {
                    port: port.id,
                    target_port: target.id,
                    mode: port.mode,
                    carrier: port.carrier,
                    from: port.at,
                    to: port.other,
                    local_current,
                    transported_current,
                    delay: port.delay,
                    arrival_tick: tick_before
                        .checked_add(u64::from(port.delay))
                        .ok_or(DimensionalWaveError::CarrierOverflow)?,
                });
            }
            let passive_residual = if caused_departure.is_zero() {
                &energy_departed - &energy_entered
            } else {
                Rat::zero()
            };
            if !passive_residual.is_zero() {
                return Err(DimensionalWaveError::PassiveEnergyFailure {
                    mode: junction.mode,
                    germ: junction.germ,
                });
            }
            let source_work = &energy_departed - &energy_entered;
            total_source_work += &source_work;
            scatter_receipts.push(DimensionalWaveScatterReceipt {
                mode: junction.mode,
                germ: junction.germ,
                arrivals: junction
                    .ports
                    .iter()
                    .filter_map(|port| {
                        incoming_by_port.get(port).map(|current| {
                            DimensionalWavePortCurrentReceipt {
                                port: *port,
                                carrier: self.topology.ports
                                    [usize::try_from(port.0).expect("compiled port fits usize")]
                                .carrier,
                                current: current.clone(),
                            }
                        })
                    })
                    .collect(),
                passive_departure,
                caused_departure,
                departures: local_departures,
                energy_entered,
                energy_departed,
                source_work,
                passive_residual,
            });
        }

        standing.tick = standing
            .tick
            .checked_add(1)
            .ok_or(DimensionalWaveError::CarrierOverflow)?;
        standing.ring_cursor = (cursor + 1) % self.topology.ring_extent;
        standing.energy = &energy_before + &total_source_work;
        if standing.energy.is_negative() {
            return Err(DimensionalWaveError::GlobalEnergyFailure);
        }
        let exact_energy_residual = &standing.energy - &energy_before - &total_source_work;
        if !exact_energy_residual.is_zero() {
            return Err(DimensionalWaveError::GlobalEnergyFailure);
        }
        let receipt = DimensionalWaveReceipt {
            schema: RECEIPT_SCHEMA.to_owned(),
            event: event.event,
            tick_before,
            tick_after: standing.tick,
            arrivals: arrival_receipts,
            scatters: scatter_receipts,
            departures: departure_receipts,
            energy_before,
            source_work: total_source_work,
            energy_after: standing.energy.clone(),
            exact_energy_residual,
        };
        Ok((standing, receipt))
    }
}

impl ExactEventLaw for ExactDimensionalWaveLaw {
    type Standing = ExactDimensionalWaveStanding;
    type Event = DimensionalWaveEvent;
    type Radiation = DimensionalWaveReceipt;
    type Error = DimensionalWaveError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        let (standing_after, receipt) = self.enact_wave(standing_before, event)?;
        let work = receipt
            .arrivals
            .len()
            .checked_add(
                receipt
                    .scatters
                    .iter()
                    .map(|scatter| scatter.departures.len())
                    .sum(),
            )
            .ok_or(DimensionalWaveError::CarrierOverflow)?;
        let parallel_width = receipt.scatters.len();
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![receipt],
            logical_resources: Some(LogicalResourceReceipt {
                schema: "holonic-engine.logical-resource-receipt.v1".to_owned(),
                work: BigUint::from(work),
                causal_span: BigUint::from(1_u8),
                exposed_parallel_width: BigUint::from(parallel_width),
                events_by_law: BTreeMap::from([(
                    "exact-dimensional-wave".to_owned(),
                    BigUint::from(1_u8),
                )]),
            }),
            physical_resources: None,
        })
    }
}

#[derive(Clone)]
struct ArrivedCurrent {
    port: usize,
    current: ExactComplexWaveCurrent,
}

fn take_arrivals(
    standing: &mut ExactDimensionalWaveStanding,
    topology: &CompiledWaveTopology,
    slot: usize,
) -> Result<Vec<ArrivedCurrent>, DimensionalWaveError> {
    let ports = std::mem::take(&mut standing.active_slots[slot]);
    let mut arrivals = Vec::with_capacity(ports.len());
    for port in ports {
        let ordinal = port_ordinal(port, topology.ports.len())?;
        let address = slot * standing.port_count + ordinal;
        if !standing.listed[address] {
            return Err(DimensionalWaveError::MalformedStanding);
        }
        standing.listed[address] = false;
        let current = std::mem::take(&mut standing.arrival_values[address]);
        if current.is_zero() {
            continue;
        }
        arrivals.push(ArrivedCurrent {
            port: ordinal,
            current,
        });
    }
    Ok(arrivals)
}

fn schedule_arrival(
    standing: &mut ExactDimensionalWaveStanding,
    topology: &CompiledWaveTopology,
    slot: usize,
    port: usize,
    current: &ExactComplexWaveCurrent,
) -> Result<(), DimensionalWaveError> {
    if current.is_zero() {
        return Ok(());
    }
    let address = slot
        .checked_mul(standing.port_count)
        .and_then(|base| base.checked_add(port))
        .ok_or(DimensionalWaveError::CarrierOverflow)?;
    if !standing.arrival_values[address].is_zero() {
        return Err(DimensionalWaveError::DuplicateArrival);
    }
    standing.arrival_values[address] = current.clone();
    if !standing.listed[address] {
        standing.listed[address] = true;
        standing.active_slots[slot].push(topology.ports[port].id);
    }
    Ok(())
}

fn validate_impulses(
    law: &ExactDimensionalWaveLaw,
    impulses: &[DimensionalWaveImpulse],
) -> Result<(), DimensionalWaveError> {
    for impulse in impulses {
        if impulse.departure.is_zero()
            || !law.source.source_events().contains(&impulse.source_event)
            || !law
                .topology
                .junction_by_mode_germ
                .contains_key(&(impulse.mode, impulse.germ))
        {
            return Err(DimensionalWaveError::MalformedImpulse);
        }
        let germ = &law.source.germs()[&impulse.germ];
        if !germ.source_events.contains(&impulse.source_event) {
            return Err(DimensionalWaveError::ImpulseLineageMismatch);
        }
    }
    Ok(())
}

fn validate_modes(
    source: &ExactDimensionalSource,
    modes: &[DimensionalWaveMode],
) -> Result<(), DimensionalWaveError> {
    if modes.is_empty() {
        return Err(DimensionalWaveError::NoModes);
    }
    let mut ids = BTreeSet::new();
    let mut axes = BTreeSet::new();
    for mode in modes {
        let pair_exists = source.complex_pairs().iter().any(|pair| {
            pair.real == mode.real_axis && pair.imaginary == mode.imaginary_axis && pair.unit_conic
        });
        if mode.name.is_empty()
            || !ids.insert(mode.id)
            || !axes.insert((mode.real_axis, mode.imaginary_axis))
            || !pair_exists
        {
            return Err(DimensionalWaveError::MalformedMode(mode.id));
        }
    }
    Ok(())
}

fn validate_doctrines(
    source: &ExactDimensionalSource,
    modes: &[DimensionalWaveMode],
    doctrines: &[DimensionalWaveCarrierDoctrine],
) -> Result<(), DimensionalWaveError> {
    if doctrines.is_empty() {
        return Err(DimensionalWaveError::NoCarrierDoctrine);
    }
    let mut carriers = BTreeSet::new();
    for doctrine in doctrines {
        if doctrine.delay == 0
            || !doctrine.admittance.is_positive()
            || !source.carriers().contains_key(&doctrine.carrier)
            || !carriers.insert(doctrine.carrier)
        {
            return Err(DimensionalWaveError::MalformedCarrierDoctrine(
                doctrine.carrier,
            ));
        }
    }
    let mode_ids = modes.iter().map(|mode| mode.id).collect::<BTreeSet<_>>();
    if doctrines.iter().any(|doctrine| {
        doctrine
            .admitted_modes
            .iter()
            .any(|mode| !mode_ids.contains(mode))
    }) {
        return Err(DimensionalWaveError::MalformedModalAdmission);
    }
    if doctrines.iter().any(|doctrine| {
        doctrine.phase_transport.iter().any(|(mode, transport)| {
            !mode_ids.contains(mode)
                || (!doctrine.admitted_modes.is_empty() && !doctrine.admitted_modes.contains(mode))
                || !transport.is_unit()
        })
    }) {
        return Err(DimensionalWaveError::NonunitDeclaredPhaseTransport);
    }
    if doctrines.iter().any(|doctrine| {
        doctrine.modal_admittance.iter().any(|(mode, admittance)| {
            !mode_ids.contains(mode)
                || (!doctrine.admitted_modes.is_empty() && !doctrine.admitted_modes.contains(mode))
                || !admittance.is_positive()
        })
    }) {
        return Err(DimensionalWaveError::MalformedModalAdmittance);
    }
    Ok(())
}

fn compile_topology(
    source: &ExactDimensionalSource,
    modes: &[DimensionalWaveMode],
    doctrines: &[DimensionalWaveCarrierDoctrine],
) -> Result<CompiledWaveTopology, DimensionalWaveError> {
    #[derive(Clone)]
    struct PendingPort {
        id: DimensionalWavePortId,
        mode: DimensionalWaveModeId,
        carrier: CoordinateCarrierId,
        at: CoordinateGermId,
        other: CoordinateGermId,
        opposite: DimensionalWavePortId,
        delay: u32,
        admittance: Rat,
        transport_cosine: Rat,
        transport_sine: Rat,
    }

    let mut pending = Vec::<PendingPort>::new();
    for doctrine in doctrines {
        let carrier = &source.carriers()[&doctrine.carrier];
        for mode in modes {
            if !doctrine.admitted_modes.is_empty() && !doctrine.admitted_modes.contains(&mode.id) {
                continue;
            }
            let admittance = doctrine
                .modal_admittance
                .get(&mode.id)
                .unwrap_or(&doctrine.admittance);
            let from = &source.germs()[&carrier.from];
            let to = &source.germs()[&carrier.to];
            let transport = if let Some(transport) = doctrine.phase_transport.get(&mode.id) {
                transport.clone()
            } else {
                let (Some(from_real), Some(from_imaginary), Some(to_real), Some(to_imaginary)) = (
                    from.coordinates.get(&mode.real_axis),
                    from.coordinates.get(&mode.imaginary_axis),
                    to.coordinates.get(&mode.real_axis),
                    to.coordinates.get(&mode.imaginary_axis),
                ) else {
                    continue;
                };
                ExactWavePhaseTransport {
                    cosine: to_real * from_real + to_imaginary * from_imaginary,
                    sine: to_imaginary * from_real - to_real * from_imaginary,
                }
            };
            if !transport.is_unit() {
                return Err(DimensionalWaveError::MalformedPhaseTransport {
                    mode: mode.id,
                    carrier: doctrine.carrier,
                });
            }
            let forward = DimensionalWavePortId(
                u64::try_from(pending.len()).map_err(|_| DimensionalWaveError::CarrierOverflow)?,
            );
            let reverse = DimensionalWavePortId(
                forward
                    .0
                    .checked_add(1)
                    .ok_or(DimensionalWaveError::CarrierOverflow)?,
            );
            pending.push(PendingPort {
                id: forward,
                mode: mode.id,
                carrier: doctrine.carrier,
                at: carrier.from,
                other: carrier.to,
                opposite: reverse,
                delay: doctrine.delay,
                admittance: admittance.clone(),
                transport_cosine: transport.cosine.clone(),
                transport_sine: transport.sine.clone(),
            });
            pending.push(PendingPort {
                id: reverse,
                mode: mode.id,
                carrier: doctrine.carrier,
                at: carrier.to,
                other: carrier.from,
                opposite: forward,
                delay: doctrine.delay,
                admittance: admittance.clone(),
                transport_cosine: transport.cosine,
                transport_sine: -transport.sine,
            });
        }
    }
    if pending.is_empty() {
        return Err(DimensionalWaveError::NoModalCarriers);
    }

    let mut junction_by_mode_germ = BTreeMap::new();
    for port in &pending {
        let key = (port.mode, port.at);
        if !junction_by_mode_germ.contains_key(&key) {
            let ordinal = junction_by_mode_germ.len();
            junction_by_mode_germ.insert(key, ordinal);
        }
    }
    let mut junctions = junction_by_mode_germ
        .iter()
        .map(|((mode, germ), _)| CompiledWaveJunction {
            mode: *mode,
            germ: *germ,
            ports: Vec::new(),
            total_admittance: Rat::zero(),
        })
        .collect::<Vec<_>>();
    // BTreeMap values were assigned by encounter order, not key order.
    for ((mode, germ), ordinal) in &junction_by_mode_germ {
        junctions[*ordinal].mode = *mode;
        junctions[*ordinal].germ = *germ;
    }
    let mut ports = Vec::with_capacity(pending.len());
    let mut port_by_incidence = BTreeMap::new();
    for port in pending {
        let junction = junction_by_mode_germ[&(port.mode, port.at)];
        junctions[junction].ports.push(port.id);
        junctions[junction].total_admittance += &port.admittance;
        if port_by_incidence
            .insert((port.mode, port.carrier, port.at), port.id)
            .is_some()
        {
            return Err(DimensionalWaveError::MalformedTopology);
        }
        ports.push(CompiledWavePort {
            id: port.id,
            mode: port.mode,
            carrier: port.carrier,
            at: port.at,
            other: port.other,
            opposite: port.opposite,
            junction,
            delay: port.delay,
            admittance: port.admittance,
            transport_cosine: port.transport_cosine,
            transport_sine: port.transport_sine,
        });
    }
    for junction in &mut junctions {
        junction.ports.sort();
        if junction.ports.is_empty() || !junction.total_admittance.is_positive() {
            return Err(DimensionalWaveError::MalformedTopology);
        }
    }
    for mode in modes {
        if !junctions.iter().any(|junction| junction.mode == mode.id) {
            return Err(DimensionalWaveError::ModeHasNoCarrier(mode.id));
        }
    }
    let maximum_delay = doctrines
        .iter()
        .map(|doctrine| doctrine.delay)
        .max()
        .ok_or(DimensionalWaveError::NoCarrierDoctrine)?;
    let ring_extent = usize::try_from(
        maximum_delay
            .checked_add(1)
            .ok_or(DimensionalWaveError::CarrierOverflow)?,
    )
    .map_err(|_| DimensionalWaveError::CarrierOverflow)?;
    Ok(CompiledWaveTopology {
        ports,
        junctions,
        port_by_incidence,
        junction_by_mode_germ,
        ring_extent,
    })
}

fn port_ordinal(port: DimensionalWavePortId, extent: usize) -> Result<usize, DimensionalWaveError> {
    let ordinal = usize::try_from(port.0).map_err(|_| DimensionalWaveError::CarrierOverflow)?;
    if ordinal >= extent {
        return Err(DimensionalWaveError::MalformedStanding);
    }
    Ok(ordinal)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum DimensionalWaveError {
    #[error(transparent)]
    Receiver(#[from] crate::DimensionalReceiverError),
    #[error("an exact dimensional wave requires at least one phase mode")]
    NoModes,
    #[error("dimensional wave mode {0:?} is malformed")]
    MalformedMode(DimensionalWaveModeId),
    #[error("dimensional wave mode {0:?} has no admitted source carrier")]
    ModeHasNoCarrier(DimensionalWaveModeId),
    #[error("an exact dimensional wave requires at least one carrier doctrine")]
    NoCarrierDoctrine,
    #[error("carrier doctrine {0:?} is missing or nonphysical")]
    MalformedCarrierDoctrine(CoordinateCarrierId),
    #[error("the source and doctrines admit no modal carrier")]
    NoModalCarriers,
    #[error("phase transport for mode {mode:?} on carrier {carrier:?} is not unit exact")]
    MalformedPhaseTransport {
        mode: DimensionalWaveModeId,
        carrier: CoordinateCarrierId,
    },
    #[error("a declared dimensional-wave phase transport must be exactly unitary")]
    NonunitDeclaredPhaseTransport,
    #[error("a declared dimensional-wave modal admittance must be positive and name a live mode")]
    MalformedModalAdmittance,
    #[error("a declared dimensional-wave modal carrier incidence names an unavailable mode")]
    MalformedModalAdmission,
    #[error("compiled wave port {0:?} does not preserve exact phase norm")]
    NonunitPhaseTransport(DimensionalWavePortId),
    #[error("the compiled dimensional wave topology is malformed")]
    MalformedTopology,
    #[error("the exact dimensional wave standing is malformed")]
    MalformedStanding,
    #[error("retained dimensional wave energy disagrees with its traveling population")]
    EnergyStandingMismatch,
    #[error("dimensional wave event {0:?} already occurred")]
    RepeatedEvent(EventId),
    #[error("a dimensional wave impulse is malformed")]
    MalformedImpulse,
    #[error("a dimensional wave impulse is not caused by its local germ")]
    ImpulseLineageMismatch,
    #[error("passive scatter at mode {mode:?}, germ {germ:?} failed exact energy balance")]
    PassiveEnergyFailure {
        mode: DimensionalWaveModeId,
        germ: CoordinateGermId,
    },
    #[error("the complete dimensional wave event failed exact energy balance")]
    GlobalEnergyFailure,
    #[error("two independently scheduled waves attempted to occupy one oriented arrival")]
    DuplicateArrival,
    #[error("the dimensional wave receiver does not restrict the law's source")]
    ReceiverSourceMismatch,
    #[error(
        "the exact receiver-primary doctrine requires positive aperture and nonnegative support response"
    )]
    MalformedReceiverPrimaryDoctrine,
    #[error("an exact dimensional wave carrier overflowed")]
    CarrierOverflow,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CausalCellId, CausalChain, CoordinateCarrierKind, DimensionalAxis, ExactComplexAxisPair,
        ExactCoordinateCarrier, ExactCoordinateGerm, GradedCausalComplex,
    };
    use num_bigint::BigInt;

    fn events(value: u64) -> BTreeSet<EventId> {
        BTreeSet::from([EventId(value)])
    }

    fn three_way_source(rotated_left: bool) -> ExactDimensionalSource {
        let mut incidence = GradedCausalComplex::default();
        let center = incidence
            .found_cell("center", events(1), 0, CausalChain::default())
            .unwrap();
        let left = incidence
            .found_cell("left", events(2), 0, CausalChain::default())
            .unwrap();
        let right = incidence
            .found_cell("right", events(3), 0, CausalChain::default())
            .unwrap();
        let upper = incidence
            .found_cell("upper", events(4), 0, CausalChain::default())
            .unwrap();
        let real = DimensionalAxisId(1);
        let imaginary = DimensionalAxisId(2);
        let point = |id: u64, cell: CausalCellId, event: u64| ExactCoordinateGerm {
            id: CoordinateGermId(id),
            name: format!("germ {id}"),
            source_cell: cell,
            source_events: events(event),
            coordinates: if rotated_left && id == 2 {
                BTreeMap::from([(real, Rat::zero()), (imaginary, Rat::one())])
            } else {
                BTreeMap::from([(real, Rat::one()), (imaginary, Rat::zero())])
            },
        };
        let carrier = |id: u64, from: u64, to: u64, event: u64| ExactCoordinateCarrier {
            id: CoordinateCarrierId(id),
            name: format!("carrier {id}"),
            from: CoordinateGermId(from),
            to: CoordinateGermId(to),
            source_events: events(event),
            kind: CoordinateCarrierKind::Chronology,
        };
        ExactDimensionalSource::new(
            incidence,
            vec![
                DimensionalAxis::new(real, "real", events(1)).unwrap(),
                DimensionalAxis::new(imaginary, "imaginary", events(1)).unwrap(),
            ],
            vec![ExactComplexAxisPair {
                real,
                imaginary,
                unit_conic: true,
            }],
            vec![
                point(1, center, 1),
                point(2, left, 2),
                point(3, right, 3),
                point(4, upper, 4),
            ],
            vec![
                carrier(1, 1, 2, 2),
                carrier(2, 1, 3, 3),
                carrier(3, 1, 4, 4),
            ],
        )
        .unwrap()
    }

    fn law() -> ExactDimensionalWaveLaw {
        let source = three_way_source(false);
        ExactDimensionalWaveLaw::new(
            source,
            vec![DimensionalWaveMode {
                id: DimensionalWaveModeId(1),
                name: "test phase".to_owned(),
                real_axis: DimensionalAxisId(1),
                imaginary_axis: DimensionalAxisId(2),
            }],
            (1..=3)
                .map(|carrier| DimensionalWaveCarrierDoctrine {
                    carrier: CoordinateCarrierId(carrier),
                    delay: 1,
                    admitted_modes: BTreeSet::new(),
                    admittance: Rat::one(),
                    modal_admittance: BTreeMap::new(),
                    phase_transport: BTreeMap::new(),
                })
                .collect(),
        )
        .unwrap()
    }

    #[test]
    fn one_arrival_scatters_three_ways_and_preserves_exact_energy() {
        let law = law();
        let mut standing = law.initial_standing();
        let source_event = law.source.germs()[&CoordinateGermId(2)]
            .source_events
            .iter()
            .next()
            .copied()
            .unwrap();
        let first = law
            .enact_wave(
                &standing,
                &DimensionalWaveEvent {
                    event: EventId(20),
                    impulses: vec![DimensionalWaveImpulse {
                        source_event,
                        mode: DimensionalWaveModeId(1),
                        germ: CoordinateGermId(2),
                        departure: ExactComplexWaveCurrent::new(Rat::one(), Rat::zero()),
                    }],
                },
            )
            .unwrap();
        standing = first.0;
        assert_eq!(standing.energy, Rat::one());
        assert_eq!(first.1.source_work, Rat::one());

        // The unit arrival from the left reaches the center.  The exact
        // passive junction coefficients are -1/3, 2/3, 2/3.
        let second = law
            .enact_wave(
                &standing,
                &DimensionalWaveEvent {
                    event: EventId(21),
                    impulses: Vec::new(),
                },
            )
            .unwrap();
        standing = second.0;
        let center = second
            .1
            .scatters
            .iter()
            .find(|scatter| scatter.germ == CoordinateGermId(1))
            .unwrap();
        assert_eq!(
            center.passive_departure.real,
            Rat::new(BigInt::from(2), BigInt::from(3))
        );
        assert_eq!(center.departures.len(), 3);
        assert_eq!(center.energy_entered, center.energy_departed);
        assert!(center.passive_residual.is_zero());
        assert_eq!(standing.energy, Rat::one());

        let third = law
            .enact_wave(
                &standing,
                &DimensionalWaveEvent {
                    event: EventId(22),
                    impulses: Vec::new(),
                },
            )
            .unwrap();
        standing = third.0;
        assert_eq!(third.1.scatters.len(), 3);
        assert!(
            third
                .1
                .scatters
                .iter()
                .all(|scatter| scatter.passive_residual.is_zero())
        );
        assert_eq!(standing.energy, Rat::one());
        law.validate_standing(&standing).unwrap();
    }

    #[test]
    fn inverse_traversal_returns_the_local_phase_basis_exactly() {
        let source = three_way_source(true);
        let real = DimensionalAxisId(1);
        let imaginary = DimensionalAxisId(2);
        let law = ExactDimensionalWaveLaw::new(
            source,
            vec![DimensionalWaveMode {
                id: DimensionalWaveModeId(1),
                name: "quarter turn".to_owned(),
                real_axis: real,
                imaginary_axis: imaginary,
            }],
            vec![DimensionalWaveCarrierDoctrine {
                carrier: CoordinateCarrierId(1),
                delay: 1,
                admitted_modes: BTreeSet::new(),
                admittance: Rat::one(),
                modal_admittance: BTreeMap::new(),
                phase_transport: BTreeMap::new(),
            }],
        )
        .unwrap();
        let mut standing = law.initial_standing();
        let source_event = EventId(1);
        standing = law
            .enact_wave(
                &standing,
                &DimensionalWaveEvent {
                    event: EventId(30),
                    impulses: vec![DimensionalWaveImpulse {
                        source_event,
                        mode: DimensionalWaveModeId(1),
                        germ: CoordinateGermId(1),
                        departure: ExactComplexWaveCurrent::new(Rat::one(), Rat::zero()),
                    }],
                },
            )
            .unwrap()
            .0;
        let arrival = law
            .enact_wave(
                &standing,
                &DimensionalWaveEvent {
                    event: EventId(31),
                    impulses: Vec::new(),
                },
            )
            .unwrap();
        assert_eq!(arrival.1.arrivals[0].current.real, Rat::zero());
        assert_eq!(arrival.1.arrivals[0].current.imaginary, Rat::one());
        standing = arrival.0;
        let returned = law
            .enact_wave(
                &standing,
                &DimensionalWaveEvent {
                    event: EventId(32),
                    impulses: Vec::new(),
                },
            )
            .unwrap();
        assert_eq!(returned.1.arrivals[0].current.real, Rat::one());
        assert_eq!(returned.1.arrivals[0].current.imaginary, Rat::zero());
    }

    #[test]
    fn declared_interior_phase_survives_equal_endpoint_coordinates() {
        let source = three_way_source(false);
        let mode = DimensionalWaveModeId(1);
        let quarter_turn = ExactWavePhaseTransport::new(Rat::zero(), Rat::one()).unwrap();
        let law = ExactDimensionalWaveLaw::new(
            source,
            vec![DimensionalWaveMode {
                id: mode,
                name: "interior winding".to_owned(),
                real_axis: DimensionalAxisId(1),
                imaginary_axis: DimensionalAxisId(2),
            }],
            vec![DimensionalWaveCarrierDoctrine {
                carrier: CoordinateCarrierId(1),
                delay: 1,
                admitted_modes: BTreeSet::new(),
                admittance: Rat::one(),
                modal_admittance: BTreeMap::new(),
                phase_transport: BTreeMap::from([(mode, quarter_turn)]),
            }],
        )
        .unwrap();
        let standing = law
            .enact_wave(
                &law.initial_standing(),
                &DimensionalWaveEvent {
                    event: EventId(40),
                    impulses: vec![DimensionalWaveImpulse {
                        source_event: EventId(1),
                        mode,
                        germ: CoordinateGermId(1),
                        departure: ExactComplexWaveCurrent::new(Rat::one(), Rat::zero()),
                    }],
                },
            )
            .unwrap()
            .0;
        let arrival = law
            .enact_wave(
                &standing,
                &DimensionalWaveEvent {
                    event: EventId(41),
                    impulses: Vec::new(),
                },
            )
            .unwrap();
        assert_eq!(
            arrival.1.arrivals[0].current,
            ExactComplexWaveCurrent::new(Rat::zero(), Rat::one())
        );
    }

    #[test]
    fn receiver_response_superposes_phase_before_it_forms_color() {
        let doctrine = ExactReceiverPrimaryDoctrine::new(Rat::one(), Rat::zero()).unwrap();
        let positive = ExactComplexWaveCurrent::new(Rat::one(), Rat::zero());
        let negative = ExactComplexWaveCurrent::new(-Rat::one(), Rat::zero());

        let mut same_mode = ExactReceiverPhasePopulation::default();
        same_mode.receive(DimensionalWaveModeId(2), &positive);
        same_mode.receive(DimensionalWaveModeId(2), &negative);
        assert!(same_mode.coherent_modes.is_empty());
        let cancelled = doctrine.transduce(&same_mode);
        assert_eq!(cancelled.primaries, [Rat::zero(), Rat::zero(), Rat::zero()]);
        assert_eq!(cancelled.alpha, Rat::zero());
        assert_eq!(cancelled.transmittance, Rat::one());

        let mut distinct_modes = ExactReceiverPhasePopulation::default();
        distinct_modes.receive(DimensionalWaveModeId(2), &positive);
        distinct_modes.receive(DimensionalWaveModeId(3), &negative);
        let received = doctrine.transduce(&distinct_modes);
        assert_eq!(
            received.primaries,
            [
                Rat::new(BigInt::from(2), BigInt::from(5)),
                Rat::zero(),
                Rat::new(BigInt::from(2), BigInt::from(5)),
            ]
        );
        assert_eq!(received.alpha, Rat::new(BigInt::from(4), BigInt::from(5)));
        assert_eq!(
            received.transmittance,
            Rat::new(BigInt::from(1), BigInt::from(5))
        );
        assert_eq!(
            received
                .primaries
                .iter()
                .fold(Rat::zero(), |sum, primary| sum + primary),
            received.alpha
        );
        assert_eq!(&received.alpha + &received.transmittance, Rat::one());
    }

    #[test]
    fn neutral_support_is_coupled_through_the_same_four_coordinate_aperture() {
        let doctrine = ExactReceiverPrimaryDoctrine::new(
            Rat::one(),
            Rat::new(BigInt::from(1), BigInt::from(2)),
        )
        .unwrap();
        let mut population = ExactReceiverPhasePopulation::default();
        population.add_support(BigUint::from(2_u8));
        let response = doctrine.transduce(&population);
        assert_eq!(
            response.primaries,
            [
                Rat::new(BigInt::from(1), BigInt::from(4)),
                Rat::new(BigInt::from(1), BigInt::from(4)),
                Rat::new(BigInt::from(1), BigInt::from(4)),
            ]
        );
        assert_eq!(response.alpha, Rat::new(BigInt::from(3), BigInt::from(4)));
        assert_eq!(
            response.transmittance,
            Rat::new(BigInt::from(1), BigInt::from(4))
        );
    }
}
