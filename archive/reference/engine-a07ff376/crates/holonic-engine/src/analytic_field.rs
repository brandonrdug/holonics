//! Exact currents on caused analytic quadric and torus sections.
//!
//! The field atlas owns local implicit supports and their causal overlaps.
//! The dimensional wave law owns sparse delayed complex current.  This module
//! composes those owners without turning a projection into physics:
//!
//! - an analytical arc is a certified conic orbit on a resolved quadric or a
//!   meridian/longitude orbit on a source-owned torus;
//! - a junction is a caused support contact or an explicitly interacting
//!   glued overlap;
//! - a mode carries exact coherence lineage, dispersion testimony, admittance,
//!   and a calibrated rational unit-conic phase step;
//! - current travels through the analytical arc and scatters only at declared
//!   junctions; and
//! - a receiver first obtains exact current contacts, then applies its own
//!   response doctrine.
//!
//! This is an exact guided scalar-wave and conservative-advection foundation.
//! It is not a complete Maxwell, radiative-transfer, or Navier--Stokes law.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;
use num_traits::{One, Signed, Zero};
use relational_geometry::{Rat, RatVec3, ReceiverId};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    CausalChain, CausalFieldStanding, CoordinateCarrierId, CoordinateCarrierKind, CoordinateGermId,
    DimensionalAxis, DimensionalAxisId, DimensionalWaveCarrierDoctrine, DimensionalWaveError,
    DimensionalWaveEvent, DimensionalWaveImpulse, DimensionalWaveMode, DimensionalWaveModeId,
    DimensionalWaveReceipt, EventId, EventSuccessor, ExactComplexAxisPair, ExactComplexWaveCurrent,
    ExactCoordinateCarrier, ExactCoordinateGerm, ExactDimensionalSource, ExactDimensionalWaveLaw,
    ExactDimensionalWaveStanding, ExactEventLaw, ExactPremultipliedReceiverResponse,
    ExactRatMatrix, ExactReceiverPhasePopulation, ExactReceiverPrimaryDoctrine,
    ExactWavePhaseTransport, FieldGermId, FieldOverlapId, FieldOverlapOutcome,
    FieldSupportStanding, GradedCausalComplex, LogicalResourceReceipt,
};

const ANALYTIC_SLICE_SCHEMA: &str = "holonic-engine.analytic-field-wave-slice.v1";
const ADVECTION_STANDING_SCHEMA: &str = "holonic-engine.analytic-advection-standing.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AnalyticFieldJunctionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AnalyticFieldArcId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AnalyticCirculationProbeId(pub u64);

/// One rational point on the exact unit conic.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ExactUnitConicPhase {
    pub cosine: Rat,
    pub sine: Rat,
}

impl ExactUnitConicPhase {
    pub fn new(cosine: Rat, sine: Rat) -> Result<Self, AnalyticFieldError> {
        let result = Self { cosine, sine };
        if !result.is_unit() {
            return Err(AnalyticFieldError::NonunitPhase);
        }
        Ok(result)
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

    pub fn rotated(&self, transport: &ExactWavePhaseTransport) -> Self {
        Self {
            cosine: &transport.cosine * &self.cosine - &transport.sine * &self.sine,
            sine: &transport.sine * &self.cosine + &transport.cosine * &self.sine,
        }
    }

    pub fn transport_to(&self, target: &Self) -> ExactWavePhaseTransport {
        ExactWavePhaseTransport {
            cosine: &target.cosine * &self.cosine + &target.sine * &self.sine,
            sine: &target.sine * &self.cosine - &target.cosine * &self.sine,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AnalyticFieldJunctionOrigin {
    /// A caused point on one resolved support.
    LocalSupport { germ: FieldGermId },
    /// Two resolved supports are geometrically glued and a separate physical
    /// interaction doctrine admits wave contact there.
    InteractingOverlap { overlap: FieldOverlapId },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticFieldJunction {
    pub id: AnalyticFieldJunctionId,
    pub name: String,
    pub point: RatVec3,
    pub origin: AnalyticFieldJunctionOrigin,
}

impl ExactAnalyticFieldJunction {
    fn source_event(&self, field: &CausalFieldStanding) -> Result<EventId, AnalyticFieldError> {
        match self.origin {
            AnalyticFieldJunctionOrigin::LocalSupport { germ } => field
                .germs
                .get(&germ)
                .map(|body| body.last_event)
                .ok_or(AnalyticFieldError::UnknownFieldGerm(germ)),
            AnalyticFieldJunctionOrigin::InteractingOverlap { overlap } => field
                .overlaps
                .get(&overlap)
                .map(|body| body.event)
                .ok_or(AnalyticFieldError::UnknownFieldOverlap(overlap)),
        }
    }

    fn germs(
        &self,
        field: &CausalFieldStanding,
    ) -> Result<BTreeSet<FieldGermId>, AnalyticFieldError> {
        match self.origin {
            AnalyticFieldJunctionOrigin::LocalSupport { germ } => Ok(BTreeSet::from([germ])),
            AnalyticFieldJunctionOrigin::InteractingOverlap { overlap } => {
                let overlap = field
                    .overlaps
                    .get(&overlap)
                    .ok_or(AnalyticFieldError::UnknownFieldOverlap(overlap))?;
                Ok(overlap.germs.into_iter().collect())
            }
        }
    }
}

/// An exact positively oriented orthonormal chart for one rational torus.
///
/// `radial_cosine × radial_sine = axial` fixes the winding hand which the
/// implicit quartic and two endpoint positions alone do not determine.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactTorusPhaseFrame {
    pub radial_cosine: RatVec3,
    pub radial_sine: RatVec3,
    pub axial: RatVec3,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactAnalyticOrbitGeometry {
    /// `x(c,s)=center + cosine_axis*c + sine_axis*s`, certified to lie on one
    /// resolved quadric for every `c²+s²=1`.
    QuadricConic {
        germ: FieldGermId,
        center: RatVec3,
        cosine_axis: RatVec3,
        sine_axis: RatVec3,
    },
    /// A longitude at one fixed torus meridian phase.
    TorusLongitude {
        germ: FieldGermId,
        frame: ExactTorusPhaseFrame,
        meridian: ExactUnitConicPhase,
    },
    /// A meridian at one fixed torus longitude phase.
    TorusMeridian {
        germ: FieldGermId,
        frame: ExactTorusPhaseFrame,
        longitude: ExactUnitConicPhase,
    },
}

impl ExactAnalyticOrbitGeometry {
    pub fn germ(&self) -> FieldGermId {
        match self {
            Self::QuadricConic { germ, .. }
            | Self::TorusLongitude { germ, .. }
            | Self::TorusMeridian { germ, .. } => *germ,
        }
    }

    pub fn point(
        &self,
        field: &CausalFieldStanding,
        phase: &ExactUnitConicPhase,
    ) -> Result<RatVec3, AnalyticFieldError> {
        let germ = field
            .germs
            .get(&self.germ())
            .ok_or(AnalyticFieldError::UnknownFieldGerm(self.germ()))?;
        match self {
            Self::QuadricConic {
                center,
                cosine_axis,
                sine_axis,
                ..
            } => Ok(center
                .add(&cosine_axis.scale(&phase.cosine))
                .add(&sine_axis.scale(&phase.sine))),
            Self::TorusLongitude {
                frame, meridian, ..
            } => {
                let torus = require_torus(&germ.support)?;
                let radial = frame
                    .radial_cosine
                    .scale(&phase.cosine)
                    .add(&frame.radial_sine.scale(&phase.sine));
                let radial_scale = &torus.major_radius + &torus.minor_radius * &meridian.cosine;
                Ok(torus
                    .center
                    .add(&radial.scale(&radial_scale))
                    .add(&frame.axial.scale(&(&torus.minor_radius * &meridian.sine))))
            }
            Self::TorusMeridian {
                frame, longitude, ..
            } => {
                let torus = require_torus(&germ.support)?;
                let radial = frame
                    .radial_cosine
                    .scale(&longitude.cosine)
                    .add(&frame.radial_sine.scale(&longitude.sine));
                Ok(torus
                    .center
                    .add(
                        &radial.scale(&(&torus.major_radius + &torus.minor_radius * &phase.cosine)),
                    )
                    .add(&frame.axial.scale(&(&torus.minor_radius * &phase.sine))))
            }
        }
    }

    pub fn tangent(
        &self,
        field: &CausalFieldStanding,
        phase: &ExactUnitConicPhase,
    ) -> Result<RatVec3, AnalyticFieldError> {
        let germ = field
            .germs
            .get(&self.germ())
            .ok_or(AnalyticFieldError::UnknownFieldGerm(self.germ()))?;
        match self {
            Self::QuadricConic {
                cosine_axis,
                sine_axis,
                ..
            } => Ok(cosine_axis
                .scale(&-phase.sine.clone())
                .add(&sine_axis.scale(&phase.cosine))),
            Self::TorusLongitude {
                frame, meridian, ..
            } => {
                let torus = require_torus(&germ.support)?;
                let scale = &torus.major_radius + &torus.minor_radius * &meridian.cosine;
                Ok(frame
                    .radial_cosine
                    .scale(&(-&phase.sine * &scale))
                    .add(&frame.radial_sine.scale(&(&phase.cosine * scale))))
            }
            Self::TorusMeridian {
                frame, longitude, ..
            } => {
                let torus = require_torus(&germ.support)?;
                let radial = frame
                    .radial_cosine
                    .scale(&longitude.cosine)
                    .add(&frame.radial_sine.scale(&longitude.sine));
                Ok(radial
                    .scale(&(-&torus.minor_radius * &phase.sine))
                    .add(&frame.axial.scale(&(&torus.minor_radius * &phase.cosine))))
            }
        }
    }

    fn validate(&self, field: &CausalFieldStanding) -> Result<(), AnalyticFieldError> {
        let germ = field
            .germs
            .get(&self.germ())
            .ok_or(AnalyticFieldError::UnknownFieldGerm(self.germ()))?;
        if !field.active_germs().contains(&self.germ()) {
            return Err(AnalyticFieldError::InactiveFieldGerm(self.germ()));
        }
        match self {
            Self::QuadricConic {
                center,
                cosine_axis,
                sine_axis,
                ..
            } => {
                let quadric = require_quadric(&germ.support)?;
                if cosine_axis == &RatVec3::zero()
                    || sine_axis == &RatVec3::zero()
                    || cosine_axis.cross(sine_axis) == RatVec3::zero()
                {
                    return Err(AnalyticFieldError::DegenerateAnalyticOrbit);
                }
                let gradient = quadric.gradient(center);
                let cosine_quadratic = quadric.restrict_ray(center, cosine_axis)[2].clone();
                let sine_quadratic = quadric.restrict_ray(center, sine_axis)[2].clone();
                let hessian = quadric.hessian();
                let mixed = bilinear(&hessian, cosine_axis, sine_axis);
                if gradient.dot(cosine_axis) != Rat::zero()
                    || gradient.dot(sine_axis) != Rat::zero()
                    || !mixed.is_zero()
                    || cosine_quadratic != sine_quadratic
                    || quadric.evaluate(center) != -cosine_quadratic
                {
                    return Err(AnalyticFieldError::OrbitLeavesSupport(self.germ()));
                }
            }
            Self::TorusLongitude { frame, .. } | Self::TorusMeridian { frame, .. } => {
                let torus = require_torus(&germ.support)?;
                validate_torus_frame(frame, torus)?;
                if torus.major_radius <= torus.minor_radius {
                    return Err(AnalyticFieldError::NonregularTorusCycle(self.germ()));
                }
            }
        }
        for phase in [
            ExactUnitConicPhase::identity(),
            ExactUnitConicPhase {
                cosine: Rat::zero(),
                sine: Rat::one(),
            },
            ExactUnitConicPhase {
                cosine: -Rat::one(),
                sine: Rat::zero(),
            },
            ExactUnitConicPhase {
                cosine: Rat::zero(),
                sine: -Rat::one(),
            },
        ] {
            let point = self.point(field, &phase)?;
            if support_evaluate(&germ.support, &point)?.is_zero() {
                let tangent = self.tangent(field, &phase)?;
                let gradient = germ
                    .support
                    .gradient(&point)
                    .ok_or(AnalyticFieldError::UnresolvedSupport(self.germ()))?;
                if tangent == RatVec3::zero() || !gradient.dot(&tangent).is_zero() {
                    return Err(AnalyticFieldError::OrbitLeavesSupport(self.germ()));
                }
            } else {
                return Err(AnalyticFieldError::OrbitLeavesSupport(self.germ()));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticFieldMode {
    pub id: DimensionalWaveModeId,
    pub name: String,
    /// Only passages in this same mode and coherence lineage may interfere.
    pub coherence_lineage: BTreeSet<EventId>,
    pub frequency_square: Rat,
    /// Local isotropic dispersion magnitude `|k|²` on each participating
    /// support. Geometry does not infer this constitutive material data.
    pub wave_number_square: BTreeMap<FieldGermId, Rat>,
    /// Scalar traveling-wave admittance in each participating material germ.
    /// This is interface constitutive testimony, independent of whether a
    /// particular analytical arc admits that mode as a traveling section.
    pub interface_admittance: BTreeMap<FieldGermId, Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticFieldArc {
    pub id: AnalyticFieldArcId,
    pub name: String,
    pub source_event: EventId,
    pub from: AnalyticFieldJunctionId,
    pub to: AnalyticFieldJunctionId,
    pub geometry: ExactAnalyticOrbitGeometry,
    pub start_phase: ExactUnitConicPhase,
    /// Exact spatial phase advance per physical event.
    pub geometric_step: ExactWavePhaseTransport,
    pub delay: u32,
    pub admittance: Rat,
    pub modal_admittance: BTreeMap<DimensionalWaveModeId, Rat>,
    /// Exact calibrated wave-phase advance per event. The `delay`th power is
    /// the carrier's complete phase transport.
    pub modal_phase_step: BTreeMap<DimensionalWaveModeId, ExactWavePhaseTransport>,
}

impl ExactAnalyticFieldArc {
    pub fn end_phase(&self) -> ExactUnitConicPhase {
        self.start_phase
            .rotated(&self.geometric_step.pow(self.delay))
    }
}

#[derive(Clone, Debug)]
pub struct ExactAnalyticFieldWaveLaw {
    field: CausalFieldStanding,
    junctions: BTreeMap<AnalyticFieldJunctionId, ExactAnalyticFieldJunction>,
    arcs: BTreeMap<AnalyticFieldArcId, ExactAnalyticFieldArc>,
    modes: BTreeMap<DimensionalWaveModeId, ExactAnalyticFieldMode>,
    junction_to_germ: BTreeMap<AnalyticFieldJunctionId, CoordinateGermId>,
    germ_to_junction: BTreeMap<CoordinateGermId, AnalyticFieldJunctionId>,
    arc_to_carrier: BTreeMap<AnalyticFieldArcId, CoordinateCarrierId>,
    carrier_to_arc: BTreeMap<CoordinateCarrierId, AnalyticFieldArcId>,
    wave: ExactDimensionalWaveLaw,
}

impl ExactAnalyticFieldWaveLaw {
    pub fn new(
        field: CausalFieldStanding,
        junctions: Vec<ExactAnalyticFieldJunction>,
        arcs: Vec<ExactAnalyticFieldArc>,
        modes: Vec<ExactAnalyticFieldMode>,
    ) -> Result<Self, AnalyticFieldError> {
        let junctions = index_unique(junctions, |junction| junction.id)
            .ok_or(AnalyticFieldError::DuplicateJunction)?;
        let arcs = index_unique(arcs, |arc| arc.id).ok_or(AnalyticFieldError::DuplicateArc)?;
        let modes = index_unique(modes, |mode| mode.id).ok_or(AnalyticFieldError::DuplicateMode)?;
        if junctions.is_empty() || arcs.is_empty() || modes.is_empty() {
            return Err(AnalyticFieldError::EmptyAnalyticWorld);
        }
        validate_junctions(&field, &junctions)?;
        validate_modes_and_arcs(&field, &junctions, &arcs, &modes)?;

        let (
            source,
            wave_modes,
            doctrines,
            junction_to_germ,
            germ_to_junction,
            arc_to_carrier,
            carrier_to_arc,
        ) = compile_wave_source(&field, &junctions, &arcs, &modes)?;
        let wave = ExactDimensionalWaveLaw::new(source, wave_modes, doctrines)?;
        Ok(Self {
            field,
            junctions,
            arcs,
            modes,
            junction_to_germ,
            germ_to_junction,
            arc_to_carrier,
            carrier_to_arc,
            wave,
        })
    }

    pub fn field(&self) -> &CausalFieldStanding {
        &self.field
    }

    pub fn junctions(&self) -> &BTreeMap<AnalyticFieldJunctionId, ExactAnalyticFieldJunction> {
        &self.junctions
    }

    pub fn arcs(&self) -> &BTreeMap<AnalyticFieldArcId, ExactAnalyticFieldArc> {
        &self.arcs
    }

    pub fn modes(&self) -> &BTreeMap<DimensionalWaveModeId, ExactAnalyticFieldMode> {
        &self.modes
    }

    pub fn compiled_carrier(&self, arc: AnalyticFieldArcId) -> Option<CoordinateCarrierId> {
        self.arc_to_carrier.get(&arc).copied()
    }

    pub fn interface_optics(
        &self,
        overlap: FieldOverlapId,
        mode: DimensionalWaveModeId,
        incident_arc: AnalyticFieldArcId,
        transmitted_arc: AnalyticFieldArcId,
        incident_covector: RatVec3,
        hand: ExactRefractionHand,
    ) -> Result<ExactAnalyticInterfaceOpticsReceipt, AnalyticFieldError> {
        if incident_arc == transmitted_arc {
            return Err(AnalyticFieldError::MalformedInterfaceInteraction);
        }
        let interface = exact_interface_receipt(&self.field, overlap)?;
        let incident = self
            .arcs
            .get(&incident_arc)
            .ok_or(AnalyticFieldError::UnknownArc(incident_arc))?;
        let transmitted = self
            .arcs
            .get(&transmitted_arc)
            .ok_or(AnalyticFieldError::UnknownArc(transmitted_arc))?;
        let incident_germ = incident.geometry.germ();
        let transmitted_germ = transmitted.geometry.germ();
        let pair = BTreeSet::from(interface.germs);
        let junction = self
            .junctions
            .values()
            .find(|junction| {
                junction.origin == AnalyticFieldJunctionOrigin::InteractingOverlap { overlap }
            })
            .ok_or(AnalyticFieldError::MalformedInterfaceInteraction)?;
        let incident_reaches = incident.from == junction.id || incident.to == junction.id;
        let transmitted_reaches = transmitted.from == junction.id || transmitted.to == junction.id;
        if !incident_reaches
            || !transmitted_reaches
            || incident_germ == transmitted_germ
            || pair != BTreeSet::from([incident_germ, transmitted_germ])
        {
            return Err(AnalyticFieldError::MalformedInterfaceInteraction);
        }
        let mode_body = self
            .modes
            .get(&mode)
            .ok_or(AnalyticFieldError::UnknownMode(mode))?;
        let incident_wave_number_square = mode_body
            .wave_number_square
            .get(&incident_germ)
            .cloned()
            .ok_or(AnalyticFieldError::MalformedMode(mode))?;
        let transmitted_wave_number_square = mode_body
            .wave_number_square
            .get(&transmitted_germ)
            .cloned()
            .ok_or(AnalyticFieldError::MalformedMode(mode))?;
        let incident_admittance = mode_body
            .interface_admittance
            .get(&incident_germ)
            .cloned()
            .ok_or(AnalyticFieldError::MalformedMode(mode))?;
        let transmitted_admittance = mode_body
            .interface_admittance
            .get(&transmitted_germ)
            .cloned()
            .ok_or(AnalyticFieldError::MalformedMode(mode))?;
        if !incident.modal_phase_step.contains_key(&mode) {
            return Err(AnalyticFieldError::IncidentModeNotAdmitted);
        }
        let incident_normal = interface.gradients[if interface.germs[0] == incident_germ {
            0
        } else {
            1
        }]
        .clone();
        let refraction = exact_refraction_fiber(
            incident_covector,
            incident_normal,
            incident_wave_number_square,
            transmitted_wave_number_square,
            hand,
        )?;
        let transmitted_is_admitted = transmitted.modal_phase_step.contains_key(&mode);
        let amplitude = match &refraction.transmitted_regime {
            ExactRefractionRegime::Propagating { .. } => {
                if !transmitted_is_admitted {
                    return Err(AnalyticFieldError::PropagatingModeNotAdmitted);
                }
                ExactAnalyticInterfaceAmplitudeFiber::Traveling(
                    exact_scalar_interface_coefficients(
                        incident_admittance,
                        transmitted_admittance,
                    )?,
                )
            }
            ExactRefractionRegime::Grazing => {
                if transmitted_is_admitted {
                    return Err(AnalyticFieldError::NonpropagatingModeAdmitted);
                }
                ExactAnalyticInterfaceAmplitudeFiber::GrazingOpen {
                    incident_admittance,
                    transmitted_admittance,
                }
            }
            ExactRefractionRegime::Evanescent { .. } => {
                if transmitted_is_admitted {
                    return Err(AnalyticFieldError::NonpropagatingModeAdmitted);
                }
                ExactAnalyticInterfaceAmplitudeFiber::EvanescentOpen {
                    incident_admittance,
                    transmitted_admittance,
                }
            }
        };
        Ok(ExactAnalyticInterfaceOpticsReceipt {
            interface,
            mode,
            incident_arc,
            transmitted_arc,
            refraction,
            amplitude,
        })
    }

    pub fn cycle_phase_holonomy(
        &self,
        arcs: &[AnalyticFieldArcId],
        mode: DimensionalWaveModeId,
    ) -> Result<ExactAnalyticCycleHolonomyReceipt, AnalyticFieldError> {
        if arcs.is_empty() || !self.modes.contains_key(&mode) {
            return Err(AnalyticFieldError::OpenAnalyticCycle);
        }
        let bodies = arcs
            .iter()
            .map(|arc| {
                self.arcs
                    .get(arc)
                    .ok_or(AnalyticFieldError::UnknownArc(*arc))
            })
            .collect::<Result<Vec<_>, _>>()?;
        if bodies
            .iter()
            .enumerate()
            .any(|(ordinal, body)| body.to != bodies[(ordinal + 1) % bodies.len()].from)
        {
            return Err(AnalyticFieldError::OpenAnalyticCycle);
        }
        let mut phase_transport = ExactWavePhaseTransport::identity();
        for body in &bodies {
            let step = body
                .modal_phase_step
                .get(&mode)
                .ok_or(AnalyticFieldError::MissingArcMode { arc: body.id, mode })?
                .pow(body.delay);
            phase_transport = phase_transport.compose(&step);
        }
        Ok(ExactAnalyticCycleHolonomyReceipt {
            arcs: arcs.to_vec(),
            junctions: bodies.iter().map(|body| body.from).collect(),
            support_germs: bodies.iter().map(|body| body.geometry.germ()).collect(),
            mode,
            admits_nonzero_fixed_current: phase_transport == ExactWavePhaseTransport::identity(),
            phase_transport,
        })
    }

    pub fn initial_standing(&self) -> ExactDimensionalWaveStanding {
        self.wave.initial_standing()
    }

    pub fn validate_standing(
        &self,
        standing: &ExactDimensionalWaveStanding,
    ) -> Result<(), AnalyticFieldError> {
        Ok(self.wave.validate_standing(standing)?)
    }

    pub fn restrict(
        &self,
        standing: &ExactDimensionalWaveStanding,
        receiver: ReceiverId,
        doctrine: &ExactReceiverPrimaryDoctrine,
    ) -> Result<ExactAnalyticFieldSliceReceipt, AnalyticFieldError> {
        let intrinsic = self.wave.intrinsic_sections(standing)?;
        let mut sections = Vec::with_capacity(intrinsic.len());
        let mut contacts = BTreeMap::<
            [Rat; 3],
            (
                BTreeSet<FieldGermId>,
                Vec<usize>,
                ExactReceiverPhasePopulation,
            ),
        >::new();
        for body in intrinsic {
            let arc_id = self
                .carrier_to_arc
                .get(&body.carrier)
                .copied()
                .ok_or(AnalyticFieldError::MalformedCompiledWorld)?;
            let arc = &self.arcs[&arc_id];
            let from_junction = self
                .germ_to_junction
                .get(&body.from)
                .copied()
                .ok_or(AnalyticFieldError::MalformedCompiledWorld)?;
            let forward = from_junction == arc.from;
            let (phase, tangent, current) = self.local_section_state(
                arc,
                body.mode,
                body.elapsed,
                forward,
                &body.target_current,
            )?;
            let point = arc.geometry.point(&self.field, &phase)?;
            let gradient = self.field.germs[&arc.geometry.germ()]
                .support
                .gradient(&point)
                .ok_or(AnalyticFieldError::UnresolvedSupport(arc.geometry.germ()))?;
            if !gradient.dot(&tangent).is_zero() {
                return Err(AnalyticFieldError::OrbitLeavesSupport(arc.geometry.germ()));
            }
            let section = ExactAnalyticTravelingSection {
                mode: body.mode,
                arc: arc_id,
                support_germ: arc.geometry.germ(),
                from: if forward { arc.from } else { arc.to },
                to: if forward { arc.to } else { arc.from },
                phase,
                point: point.clone(),
                tangent,
                current: current.clone(),
                energy: body.energy,
                elapsed: body.elapsed,
                delay: body.delay,
                ticks_until_arrival: body.ticks_until_arrival,
            };
            let ordinal = sections.len();
            sections.push(section);
            let key = [point.x, point.y, point.z];
            let contact = contacts.entry(key).or_default();
            contact.0.insert(arc.geometry.germ());
            contact.1.push(ordinal);
            contact.2.receive(body.mode, &current);
        }
        let contacts = contacts
            .into_iter()
            .map(
                |(point, (germs, sections, population))| ExactAnalyticResonanceContact {
                    point: RatVec3::new(point[0].clone(), point[1].clone(), point[2].clone()),
                    germs,
                    sections,
                    response: doctrine.transduce(&population),
                    population,
                },
            )
            .collect();
        Ok(ExactAnalyticFieldSliceReceipt {
            schema: ANALYTIC_SLICE_SCHEMA.to_owned(),
            receiver,
            field_chronology: self.field.last_chronology,
            wave_tick: standing.tick,
            total_energy: standing.energy.clone(),
            sections,
            contacts,
        })
    }

    fn local_section_state(
        &self,
        arc: &ExactAnalyticFieldArc,
        mode: DimensionalWaveModeId,
        elapsed: u32,
        forward: bool,
        target_current: &ExactComplexWaveCurrent,
    ) -> Result<(ExactUnitConicPhase, RatVec3, ExactComplexWaveCurrent), AnalyticFieldError> {
        let phase_step = arc
            .modal_phase_step
            .get(&mode)
            .ok_or(AnalyticFieldError::MissingArcMode { arc: arc.id, mode })?;
        let total_phase = phase_step.pow(arc.delay);
        let end_phase = arc.end_phase();
        if forward {
            let phase = arc.start_phase.rotated(&arc.geometric_step.pow(elapsed));
            let departure = total_phase.inverse().transport(target_current);
            let current = phase_step.pow(elapsed).transport(&departure);
            let tangent = arc.geometry.tangent(&self.field, &phase)?;
            Ok((phase, tangent, current))
        } else {
            let phase = end_phase.rotated(&arc.geometric_step.inverse().pow(elapsed));
            let departure = total_phase.transport(target_current);
            let current = phase_step.inverse().pow(elapsed).transport(&departure);
            let tangent = arc
                .geometry
                .tangent(&self.field, &phase)?
                .scale(&-Rat::one());
            Ok((phase, tangent, current))
        }
    }

    fn translate_event(
        &self,
        event: &ExactAnalyticFieldWaveEvent,
    ) -> Result<DimensionalWaveEvent, AnalyticFieldError> {
        let impulses = event
            .impulses
            .iter()
            .map(|impulse| {
                let germ = self
                    .junction_to_germ
                    .get(&impulse.junction)
                    .copied()
                    .ok_or(AnalyticFieldError::UnknownJunction(impulse.junction))?;
                if !self.modes.contains_key(&impulse.mode) {
                    return Err(AnalyticFieldError::UnknownMode(impulse.mode));
                }
                Ok(DimensionalWaveImpulse {
                    source_event: impulse.source_event,
                    mode: impulse.mode,
                    germ,
                    departure: impulse.departure.clone(),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(DimensionalWaveEvent {
            event: event.event,
            impulses,
        })
    }

    fn map_receipt(
        &self,
        wave: DimensionalWaveReceipt,
    ) -> Result<ExactAnalyticFieldWaveRadiation, AnalyticFieldError> {
        let interface_scatters = wave
            .scatters
            .iter()
            .map(|scatter| {
                let junction = self
                    .germ_to_junction
                    .get(&scatter.germ)
                    .copied()
                    .ok_or(AnalyticFieldError::MalformedCompiledWorld)?;
                let arrivals = scatter
                    .arrivals
                    .iter()
                    .map(|arrival| {
                        self.carrier_to_arc
                            .get(&arrival.carrier)
                            .copied()
                            .map(|arc| (arc, arrival.current.clone()))
                            .ok_or(AnalyticFieldError::MalformedCompiledWorld)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let departures = scatter
                    .departures
                    .iter()
                    .map(|departure| {
                        self.carrier_to_arc
                            .get(&departure.carrier)
                            .copied()
                            .map(|arc| (arc, departure.current.clone()))
                            .ok_or(AnalyticFieldError::MalformedCompiledWorld)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(ExactAnalyticInterfaceScatterReceipt {
                    junction,
                    mode: scatter.mode,
                    arrivals,
                    departures,
                    energy_entered: scatter.energy_entered.clone(),
                    energy_departed: scatter.energy_departed.clone(),
                    source_work: scatter.source_work.clone(),
                    passive_residual: scatter.passive_residual.clone(),
                })
            })
            .collect::<Result<Vec<_>, AnalyticFieldError>>()?;
        Ok(ExactAnalyticFieldWaveRadiation {
            wave,
            interface_scatters,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticFieldWaveImpulse {
    pub source_event: EventId,
    pub mode: DimensionalWaveModeId,
    pub junction: AnalyticFieldJunctionId,
    pub departure: ExactComplexWaveCurrent,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticFieldWaveEvent {
    pub event: EventId,
    pub impulses: Vec<ExactAnalyticFieldWaveImpulse>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticInterfaceScatterReceipt {
    pub junction: AnalyticFieldJunctionId,
    pub mode: DimensionalWaveModeId,
    pub arrivals: Vec<(AnalyticFieldArcId, ExactComplexWaveCurrent)>,
    pub departures: Vec<(AnalyticFieldArcId, ExactComplexWaveCurrent)>,
    pub energy_entered: Rat,
    pub energy_departed: Rat,
    pub source_work: Rat,
    pub passive_residual: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticFieldWaveRadiation {
    pub wave: DimensionalWaveReceipt,
    pub interface_scatters: Vec<ExactAnalyticInterfaceScatterReceipt>,
}

impl ExactEventLaw for ExactAnalyticFieldWaveLaw {
    type Standing = ExactDimensionalWaveStanding;
    type Event = ExactAnalyticFieldWaveEvent;
    type Radiation = ExactAnalyticFieldWaveRadiation;
    type Error = AnalyticFieldError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        let translated = self.translate_event(event)?;
        let successor = ExactEventLaw::enact(&self.wave, standing_before, &translated)?;
        let radiation = successor
            .radiation
            .into_iter()
            .map(|receipt| self.map_receipt(receipt))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(EventSuccessor {
            standing_after: successor.standing_after,
            radiation,
            logical_resources: successor.logical_resources,
            physical_resources: successor.physical_resources,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticTravelingSection {
    pub mode: DimensionalWaveModeId,
    pub arc: AnalyticFieldArcId,
    pub support_germ: FieldGermId,
    pub from: AnalyticFieldJunctionId,
    pub to: AnalyticFieldJunctionId,
    pub phase: ExactUnitConicPhase,
    pub point: RatVec3,
    pub tangent: RatVec3,
    pub current: ExactComplexWaveCurrent,
    pub energy: Rat,
    pub elapsed: u32,
    pub delay: u32,
    pub ticks_until_arrival: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticResonanceContact {
    pub point: RatVec3,
    pub germs: BTreeSet<FieldGermId>,
    pub sections: Vec<usize>,
    pub population: ExactReceiverPhasePopulation,
    pub response: ExactPremultipliedReceiverResponse,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticFieldSliceReceipt {
    pub schema: String,
    pub receiver: ReceiverId,
    pub field_chronology: Option<u64>,
    pub wave_tick: u64,
    pub total_energy: Rat,
    pub sections: Vec<ExactAnalyticTravelingSection>,
    pub contacts: Vec<ExactAnalyticResonanceContact>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactInterfaceRelation {
    Cooriented,
    Opposed,
    Transverse { intersection_tangent: RatVec3 },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticInterfaceReceipt {
    pub overlap: FieldOverlapId,
    pub point: RatVec3,
    pub germs: [FieldGermId; 2],
    pub gradients: [RatVec3; 2],
    pub relation: ExactInterfaceRelation,
}

pub fn exact_interface_receipt(
    field: &CausalFieldStanding,
    overlap_id: FieldOverlapId,
) -> Result<ExactAnalyticInterfaceReceipt, AnalyticFieldError> {
    let overlap = field
        .overlaps
        .get(&overlap_id)
        .ok_or(AnalyticFieldError::UnknownFieldOverlap(overlap_id))?;
    if overlap.outcome != FieldOverlapOutcome::Glued {
        return Err(AnalyticFieldError::OpenFieldOverlap(overlap_id));
    }
    let observation = field
        .observations
        .get(&overlap.observation)
        .ok_or(AnalyticFieldError::MalformedFieldStanding)?;
    let gradients = overlap.germs.map(|germ| {
        field.germs[&germ]
            .support
            .gradient(&observation.point)
            .ok_or(AnalyticFieldError::UnresolvedSupport(germ))
    });
    let [left, right] = gradients;
    let left = left?;
    let right = right?;
    if left == RatVec3::zero() || right == RatVec3::zero() {
        return Err(AnalyticFieldError::SingularInterface(overlap_id));
    }
    let cross = left.cross(&right);
    let relation = if cross == RatVec3::zero() {
        if left.dot(&right).is_positive() {
            ExactInterfaceRelation::Cooriented
        } else {
            ExactInterfaceRelation::Opposed
        }
    } else {
        ExactInterfaceRelation::Transverse {
            intersection_tangent: cross,
        }
    };
    Ok(ExactAnalyticInterfaceReceipt {
        overlap: overlap_id,
        point: observation.point.clone(),
        germs: overlap.germs,
        gradients: [left, right],
        relation,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactRefractionHand {
    AlongNormal,
    AgainstNormal,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactRefractionRegime {
    Propagating {
        normal_coefficient_square: Rat,
        hand: ExactRefractionHand,
    },
    Grazing,
    Evanescent {
        normal_coefficient_square_deficit: Rat,
    },
}

/// Exact geometric-optics interface fiber.
///
/// When the transmitted normal component is irrational, its exact square and
/// coorientation remain standing. No decimal direction is fabricated.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactRefractionFiber {
    pub incident_covector: RatVec3,
    pub interface_normal: RatVec3,
    pub tangential_covector: RatVec3,
    pub reflected_covector: RatVec3,
    pub incident_dispersion_residual: Rat,
    pub transmitted_regime: ExactRefractionRegime,
}

pub fn exact_refraction_fiber(
    incident_covector: RatVec3,
    interface_normal: RatVec3,
    incident_wave_number_square: Rat,
    transmitted_wave_number_square: Rat,
    hand: ExactRefractionHand,
) -> Result<ExactRefractionFiber, AnalyticFieldError> {
    if interface_normal == RatVec3::zero()
        || !incident_wave_number_square.is_positive()
        || !transmitted_wave_number_square.is_positive()
    {
        return Err(AnalyticFieldError::MalformedRefractionDoctrine);
    }
    let normal_square = interface_normal.dot(&interface_normal);
    let normal_coefficient = incident_covector.dot(&interface_normal) / &normal_square;
    let normal_part = interface_normal.scale(&normal_coefficient);
    let tangential_covector = incident_covector.subtract(&normal_part);
    let reflected_covector = incident_covector
        .subtract(&interface_normal.scale(&(Rat::from_integer(2.into()) * normal_coefficient)));
    let incident_dispersion_residual =
        incident_covector.dot(&incident_covector) - incident_wave_number_square;
    if !incident_dispersion_residual.is_zero() {
        return Err(AnalyticFieldError::IncidentDispersionFailure);
    }
    let normal_numerator =
        transmitted_wave_number_square - tangential_covector.dot(&tangential_covector);
    let transmitted_regime = if normal_numerator.is_positive() {
        ExactRefractionRegime::Propagating {
            normal_coefficient_square: normal_numerator / normal_square,
            hand,
        }
    } else if normal_numerator.is_zero() {
        ExactRefractionRegime::Grazing
    } else {
        ExactRefractionRegime::Evanescent {
            normal_coefficient_square_deficit: -normal_numerator / normal_square,
        }
    };
    Ok(ExactRefractionFiber {
        incident_covector,
        interface_normal,
        tangential_covector,
        reflected_covector,
        incident_dispersion_residual,
        transmitted_regime,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactScalarInterfaceCoefficients {
    pub incident_admittance: Rat,
    pub transmitted_admittance: Rat,
    pub reflection: Rat,
    pub transmission: Rat,
    pub energy_residual: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticInterfaceOpticsReceipt {
    pub interface: ExactAnalyticInterfaceReceipt,
    pub mode: DimensionalWaveModeId,
    pub incident_arc: AnalyticFieldArcId,
    pub transmitted_arc: AnalyticFieldArcId,
    pub refraction: ExactRefractionFiber,
    pub amplitude: ExactAnalyticInterfaceAmplitudeFiber,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactAnalyticInterfaceAmplitudeFiber {
    Traveling(ExactScalarInterfaceCoefficients),
    /// The tangential limit has no transmitted normal traveling-power
    /// section in this conservative carrier. Its boundary field is open.
    GrazingOpen {
        incident_admittance: Rat,
        transmitted_admittance: Rat,
    },
    /// An evanescent near field requires a distinct reactive/storage law. It
    /// remains an exact open fiber rather than being fabricated as a unitary
    /// transmitted traveling section.
    EvanescentOpen {
        incident_admittance: Rat,
        transmitted_admittance: Rat,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticCycleHolonomyReceipt {
    pub arcs: Vec<AnalyticFieldArcId>,
    pub junctions: Vec<AnalyticFieldJunctionId>,
    pub support_germs: BTreeSet<FieldGermId>,
    pub mode: DimensionalWaveModeId,
    pub phase_transport: ExactWavePhaseTransport,
    /// A nonidentity planar unit-conic rotation fixes only the zero current.
    pub admits_nonzero_fixed_current: bool,
}

pub fn exact_scalar_interface_coefficients(
    incident_admittance: Rat,
    transmitted_admittance: Rat,
) -> Result<ExactScalarInterfaceCoefficients, AnalyticFieldError> {
    if !incident_admittance.is_positive() || !transmitted_admittance.is_positive() {
        return Err(AnalyticFieldError::NonpositiveAdmittance);
    }
    let total = &incident_admittance + &transmitted_admittance;
    let reflection = (&incident_admittance - &transmitted_admittance) / &total;
    let transmission = Rat::from_integer(2.into()) * &incident_admittance / total;
    let energy_residual = &incident_admittance
        - &incident_admittance * &reflection * &reflection
        - &transmitted_admittance * &transmission * &transmission;
    Ok(ExactScalarInterfaceCoefficients {
        incident_admittance,
        transmitted_admittance,
        reflection,
        transmission,
        energy_residual,
    })
}

/// One exact circulation observable on the carried analytic-arc coordinates.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticCirculationProbe {
    pub id: AnalyticCirculationProbeId,
    pub name: String,
    pub coefficients: BTreeMap<AnalyticFieldArcId, Rat>,
}

/// A finite exact conservative advection chart.
///
/// If `AᵀΩ+ΩA=0` and `A1=0`, the Cayley successor preserves the Ω quadratic
/// form and the Ω-weighted total exactly. Declared circulation covectors must
/// additionally be left-fixed by the successor. Coefficients are signed
/// chart values; positivity of material parcels requires a separate parcel
/// standing.
#[derive(Clone, Debug)]
pub struct ExactAnalyticAdvectionLaw {
    arcs: Vec<AnalyticFieldArcId>,
    capacities: Vec<Rat>,
    update: ExactRatMatrix,
    probes: Vec<ExactAnalyticCirculationProbe>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticAdvectionStanding {
    pub schema: String,
    pub tick: u64,
    pub values: BTreeMap<AnalyticFieldArcId, Rat>,
    used_events: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticAdvectionEvent {
    pub event: EventId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticCirculationReceipt {
    pub probe: AnalyticCirculationProbeId,
    pub before: Rat,
    pub after: Rat,
    pub residual: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAnalyticAdvectionReceipt {
    pub event: EventId,
    pub tick_before: u64,
    pub tick_after: u64,
    pub weighted_total_before: Rat,
    pub weighted_total_after: Rat,
    pub weighted_total_residual: Rat,
    pub quadratic_energy_before: Rat,
    pub quadratic_energy_after: Rat,
    pub quadratic_energy_residual: Rat,
    pub circulations: Vec<ExactAnalyticCirculationReceipt>,
}

impl ExactAnalyticAdvectionLaw {
    /// Build a conservative chart only after every advected coordinate is
    /// owned by the analytic world and every claimed circulation is a closed
    /// one-chain in that world's caused junction incidence.
    pub fn new_on_field(
        field: &ExactAnalyticFieldWaveLaw,
        capacities: BTreeMap<AnalyticFieldArcId, Rat>,
        generator: ExactRatMatrix,
        interval: Rat,
        probes: Vec<ExactAnalyticCirculationProbe>,
    ) -> Result<Self, AnalyticFieldError> {
        if capacities.keys().any(|arc| !field.arcs.contains_key(arc)) {
            return Err(AnalyticFieldError::AdvectionPopulationMismatch);
        }
        for probe in &probes {
            let mut boundary = BTreeMap::<AnalyticFieldJunctionId, Rat>::new();
            for (arc_id, coefficient) in &probe.coefficients {
                let arc = field
                    .arcs
                    .get(arc_id)
                    .ok_or(AnalyticFieldError::MalformedCirculationProbe(probe.id))?;
                *boundary.entry(arc.from).or_default() -= coefficient;
                *boundary.entry(arc.to).or_default() += coefficient;
            }
            if boundary.values().any(|coefficient| !coefficient.is_zero()) {
                return Err(AnalyticFieldError::CirculationProbeNotClosed(probe.id));
            }
        }
        Self::new(capacities, generator, interval, probes)
    }

    pub fn new(
        capacities: BTreeMap<AnalyticFieldArcId, Rat>,
        generator: ExactRatMatrix,
        interval: Rat,
        probes: Vec<ExactAnalyticCirculationProbe>,
    ) -> Result<Self, AnalyticFieldError> {
        if capacities.is_empty()
            || capacities.values().any(|capacity| !capacity.is_positive())
            || !interval.is_positive()
        {
            return Err(AnalyticFieldError::MalformedAdvectionDoctrine);
        }
        let arcs = capacities.keys().copied().collect::<Vec<_>>();
        let capacities = arcs
            .iter()
            .map(|arc| capacities[arc].clone())
            .collect::<Vec<_>>();
        let extent = arcs.len();
        if generator.rows() != extent || generator.columns() != extent {
            return Err(AnalyticFieldError::MalformedAdvectionDoctrine);
        }
        let omega = ExactRatMatrix::from_diagonal(capacities.clone())?;
        let skew_residual = generator
            .transpose()?
            .multiply(&omega)?
            .add(&omega.multiply(&generator)?)?;
        if skew_residual.entries().iter().any(|value| !value.is_zero()) {
            return Err(AnalyticFieldError::AdvectionNotCapacitySkew);
        }
        let ones = vec![Rat::one(); extent];
        if generator.apply(&ones)?.iter().any(|value| !value.is_zero()) {
            return Err(AnalyticFieldError::AdvectionNotDivergenceFree);
        }
        let half_interval = interval / Rat::from_integer(2.into());
        let identity = ExactRatMatrix::identity(extent)?;
        let half_generator = generator.scaled(&half_interval);
        let update = identity
            .subtract(&half_generator)?
            .inverse()?
            .multiply(&identity.add(&half_generator)?)?;
        if update.transpose()?.multiply(&omega)?.multiply(&update)? != omega
            || update.apply(&ones)? != ones
        {
            return Err(AnalyticFieldError::AdvectionCertificateFailure);
        }
        let arc_ordinals = arcs
            .iter()
            .enumerate()
            .map(|(ordinal, arc)| (*arc, ordinal))
            .collect::<BTreeMap<_, _>>();
        for probe in &probes {
            if probe.name.is_empty()
                || probe
                    .coefficients
                    .keys()
                    .any(|arc| !arc_ordinals.contains_key(arc))
            {
                return Err(AnalyticFieldError::MalformedCirculationProbe(probe.id));
            }
            let mut row = vec![Rat::zero(); extent];
            for (arc, coefficient) in &probe.coefficients {
                row[arc_ordinals[arc]] = coefficient.clone();
            }
            let transported = ExactRatMatrix::new(vec![row.clone()])?.multiply(&update)?;
            if transported.row(0)? != row {
                return Err(AnalyticFieldError::NoninvariantCirculationProbe(probe.id));
            }
        }
        Ok(Self {
            arcs,
            capacities,
            update,
            probes,
        })
    }

    pub fn initial_standing(
        &self,
        values: BTreeMap<AnalyticFieldArcId, Rat>,
    ) -> Result<ExactAnalyticAdvectionStanding, AnalyticFieldError> {
        if values.keys().copied().collect::<BTreeSet<_>>()
            != self.arcs.iter().copied().collect::<BTreeSet<_>>()
        {
            return Err(AnalyticFieldError::AdvectionPopulationMismatch);
        }
        Ok(ExactAnalyticAdvectionStanding {
            schema: ADVECTION_STANDING_SCHEMA.to_owned(),
            tick: 0,
            values,
            used_events: BTreeSet::new(),
        })
    }

    fn ordered_values(
        &self,
        standing: &ExactAnalyticAdvectionStanding,
    ) -> Result<Vec<Rat>, AnalyticFieldError> {
        if standing.schema != ADVECTION_STANDING_SCHEMA || standing.values.len() != self.arcs.len()
        {
            return Err(AnalyticFieldError::MalformedAdvectionStanding);
        }
        self.arcs
            .iter()
            .map(|arc| {
                standing
                    .values
                    .get(arc)
                    .cloned()
                    .ok_or(AnalyticFieldError::AdvectionPopulationMismatch)
            })
            .collect()
    }

    fn weighted_total(&self, values: &[Rat]) -> Rat {
        self.capacities
            .iter()
            .zip(values)
            .fold(Rat::zero(), |sum, (capacity, value)| sum + capacity * value)
    }

    fn energy(&self, values: &[Rat]) -> Rat {
        let two = Rat::from_integer(2.into());
        self.capacities
            .iter()
            .zip(values)
            .fold(Rat::zero(), |sum, (capacity, value)| {
                sum + capacity * value * value / &two
            })
    }

    fn probe_value(&self, probe: &ExactAnalyticCirculationProbe, values: &[Rat]) -> Rat {
        let ordinals = self
            .arcs
            .iter()
            .enumerate()
            .map(|(ordinal, arc)| (*arc, ordinal))
            .collect::<BTreeMap<_, _>>();
        probe
            .coefficients
            .iter()
            .fold(Rat::zero(), |sum, (arc, coefficient)| {
                sum + coefficient * &values[ordinals[arc]]
            })
    }
}

impl ExactEventLaw for ExactAnalyticAdvectionLaw {
    type Standing = ExactAnalyticAdvectionStanding;
    type Event = ExactAnalyticAdvectionEvent;
    type Radiation = ExactAnalyticAdvectionReceipt;
    type Error = AnalyticFieldError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        if standing_before.used_events.contains(&event.event) {
            return Err(AnalyticFieldError::RepeatedAdvectionEvent(event.event));
        }
        let before = self.ordered_values(standing_before)?;
        let after = self.update.apply(&before)?;
        let weighted_total_before = self.weighted_total(&before);
        let weighted_total_after = self.weighted_total(&after);
        let quadratic_energy_before = self.energy(&before);
        let quadratic_energy_after = self.energy(&after);
        let circulations = self
            .probes
            .iter()
            .map(|probe| {
                let before = self.probe_value(probe, &before);
                let after = self.probe_value(probe, &after);
                ExactAnalyticCirculationReceipt {
                    probe: probe.id,
                    residual: &after - &before,
                    before,
                    after,
                }
            })
            .collect::<Vec<_>>();
        let weighted_total_residual = &weighted_total_after - &weighted_total_before;
        let quadratic_energy_residual = &quadratic_energy_after - &quadratic_energy_before;
        if !weighted_total_residual.is_zero()
            || !quadratic_energy_residual.is_zero()
            || circulations
                .iter()
                .any(|circulation| !circulation.residual.is_zero())
        {
            return Err(AnalyticFieldError::AdvectionCertificateFailure);
        }
        let mut standing_after = standing_before.clone();
        standing_after.tick = standing_after
            .tick
            .checked_add(1)
            .ok_or(AnalyticFieldError::CarrierOverflow)?;
        standing_after.used_events.insert(event.event);
        standing_after.values = self
            .arcs
            .iter()
            .copied()
            .zip(after)
            .collect::<BTreeMap<_, _>>();
        let receipt = ExactAnalyticAdvectionReceipt {
            event: event.event,
            tick_before: standing_before.tick,
            tick_after: standing_after.tick,
            weighted_total_before,
            weighted_total_after,
            weighted_total_residual,
            quadratic_energy_before,
            quadratic_energy_after,
            quadratic_energy_residual,
            circulations,
        };
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![receipt],
            logical_resources: Some(LogicalResourceReceipt {
                schema: "holonic-engine.logical-resource-receipt.v1".to_owned(),
                work: BigUint::from(self.arcs.len()),
                causal_span: BigUint::from(1_u8),
                exposed_parallel_width: BigUint::from(self.arcs.len()),
                events_by_law: BTreeMap::from([(
                    "exact-analytic-advection".to_owned(),
                    BigUint::from(1_u8),
                )]),
            }),
            physical_resources: None,
        })
    }
}

fn validate_junctions(
    field: &CausalFieldStanding,
    junctions: &BTreeMap<AnalyticFieldJunctionId, ExactAnalyticFieldJunction>,
) -> Result<(), AnalyticFieldError> {
    let active = field.active_germs();
    for junction in junctions.values() {
        if junction.name.is_empty() {
            return Err(AnalyticFieldError::MalformedJunction(junction.id));
        }
        let germs = junction.germs(field)?;
        if germs.iter().any(|germ| !active.contains(germ)) {
            return Err(AnalyticFieldError::InactiveJunction(junction.id));
        }
        if let AnalyticFieldJunctionOrigin::InteractingOverlap { overlap } = junction.origin {
            let body = field
                .overlaps
                .get(&overlap)
                .ok_or(AnalyticFieldError::UnknownFieldOverlap(overlap))?;
            if body.outcome != FieldOverlapOutcome::Glued {
                return Err(AnalyticFieldError::OpenFieldOverlap(overlap));
            }
            let point = &field
                .observations
                .get(&body.observation)
                .ok_or(AnalyticFieldError::MalformedFieldStanding)?
                .point;
            if point != &junction.point {
                return Err(AnalyticFieldError::JunctionPointMismatch(junction.id));
            }
        }
        for germ in germs {
            let support = &field
                .germs
                .get(&germ)
                .ok_or(AnalyticFieldError::UnknownFieldGerm(germ))?
                .support;
            if !support_evaluate(support, &junction.point)?.is_zero() {
                return Err(AnalyticFieldError::JunctionLeavesSupport {
                    junction: junction.id,
                    germ,
                });
            }
        }
    }
    Ok(())
}

fn validate_modes_and_arcs(
    field: &CausalFieldStanding,
    junctions: &BTreeMap<AnalyticFieldJunctionId, ExactAnalyticFieldJunction>,
    arcs: &BTreeMap<AnalyticFieldArcId, ExactAnalyticFieldArc>,
    modes: &BTreeMap<DimensionalWaveModeId, ExactAnalyticFieldMode>,
) -> Result<(), AnalyticFieldError> {
    let mode_ids = modes.keys().copied().collect::<BTreeSet<_>>();
    let germ_ids = arcs
        .values()
        .map(|arc| arc.geometry.germ())
        .collect::<BTreeSet<_>>();
    for mode in modes.values() {
        if mode.name.is_empty()
            || mode.coherence_lineage.is_empty()
            || !mode.frequency_square.is_positive()
            || mode
                .wave_number_square
                .keys()
                .copied()
                .collect::<BTreeSet<_>>()
                != germ_ids
            || mode
                .interface_admittance
                .keys()
                .copied()
                .collect::<BTreeSet<_>>()
                != germ_ids
            || mode
                .wave_number_square
                .values()
                .any(|value| !value.is_positive())
            || mode
                .interface_admittance
                .values()
                .any(|value| !value.is_positive())
        {
            return Err(AnalyticFieldError::MalformedMode(mode.id));
        }
    }
    for arc in arcs.values() {
        if arc.name.is_empty()
            || arc.from == arc.to
            || arc.delay == 0
            || !arc.admittance.is_positive()
            || !arc.geometric_step.is_unit()
            || arc.modal_phase_step.is_empty()
            || arc
                .modal_phase_step
                .keys()
                .any(|mode| !mode_ids.contains(mode))
            || arc
                .modal_phase_step
                .values()
                .any(|transport| !transport.is_unit())
            || arc.modal_admittance.iter().any(|(mode, admittance)| {
                !arc.modal_phase_step.contains_key(mode) || !admittance.is_positive()
            })
        {
            return Err(AnalyticFieldError::MalformedArc(arc.id));
        }
        let from = junctions
            .get(&arc.from)
            .ok_or(AnalyticFieldError::UnknownJunction(arc.from))?;
        let to = junctions
            .get(&arc.to)
            .ok_or(AnalyticFieldError::UnknownJunction(arc.to))?;
        arc.geometry.validate(field)?;
        let germ = arc.geometry.germ();
        let body = field
            .germs
            .get(&germ)
            .ok_or(AnalyticFieldError::UnknownFieldGerm(germ))?;
        if !body.lineage.contains(&arc.source_event)
            || !from.germs(field)?.contains(&germ)
            || !to.germs(field)?.contains(&germ)
            || arc.geometry.point(field, &arc.start_phase)? != from.point
            || arc.geometry.point(field, &arc.end_phase())? != to.point
        {
            return Err(AnalyticFieldError::MalformedArc(arc.id));
        }
    }
    Ok(())
}

type CompiledWaveSource = (
    ExactDimensionalSource,
    Vec<DimensionalWaveMode>,
    Vec<DimensionalWaveCarrierDoctrine>,
    BTreeMap<AnalyticFieldJunctionId, CoordinateGermId>,
    BTreeMap<CoordinateGermId, AnalyticFieldJunctionId>,
    BTreeMap<AnalyticFieldArcId, CoordinateCarrierId>,
    BTreeMap<CoordinateCarrierId, AnalyticFieldArcId>,
);

fn compile_wave_source(
    field: &CausalFieldStanding,
    junctions: &BTreeMap<AnalyticFieldJunctionId, ExactAnalyticFieldJunction>,
    arcs: &BTreeMap<AnalyticFieldArcId, ExactAnalyticFieldArc>,
    modes: &BTreeMap<DimensionalWaveModeId, ExactAnalyticFieldMode>,
) -> Result<CompiledWaveSource, AnalyticFieldError> {
    let mut incidence = GradedCausalComplex::default();
    let mut junction_to_germ = BTreeMap::new();
    let mut germ_to_junction = BTreeMap::new();
    let mut coordinate_germs = Vec::new();
    let mut axes = Vec::new();
    let mut pairs = Vec::new();
    let mut wave_modes = Vec::new();
    let mut mode_axes = BTreeMap::new();

    for (ordinal, mode) in modes.values().enumerate() {
        let first = u64::try_from(
            ordinal
                .checked_mul(2)
                .and_then(|value| value.checked_add(1))
                .ok_or(AnalyticFieldError::CarrierOverflow)?,
        )
        .map_err(|_| AnalyticFieldError::CarrierOverflow)?;
        let real = DimensionalAxisId(first);
        let imaginary = DimensionalAxisId(
            first
                .checked_add(1)
                .ok_or(AnalyticFieldError::CarrierOverflow)?,
        );
        axes.push(DimensionalAxis::new(
            real,
            format!("{} real", mode.name),
            mode.coherence_lineage.clone(),
        )?);
        axes.push(DimensionalAxis::new(
            imaginary,
            format!("{} imaginary", mode.name),
            mode.coherence_lineage.clone(),
        )?);
        pairs.push(ExactComplexAxisPair {
            real,
            imaginary,
            unit_conic: true,
        });
        wave_modes.push(DimensionalWaveMode {
            id: mode.id,
            name: mode.name.clone(),
            real_axis: real,
            imaginary_axis: imaginary,
        });
        mode_axes.insert(mode.id, (real, imaginary));
    }

    for (ordinal, junction) in junctions.values().enumerate() {
        let germ = CoordinateGermId(
            u64::try_from(ordinal)
                .map_err(|_| AnalyticFieldError::CarrierOverflow)?
                .checked_add(1)
                .ok_or(AnalyticFieldError::CarrierOverflow)?,
        );
        let source_event = junction.source_event(field)?;
        let source_events = BTreeSet::from([source_event]);
        let cell = incidence.found_cell(
            junction.name.clone(),
            source_events.clone(),
            0,
            CausalChain::default(),
        )?;
        let mut coordinates = BTreeMap::new();
        for (real, imaginary) in mode_axes.values() {
            coordinates.insert(*real, Rat::one());
            coordinates.insert(*imaginary, Rat::zero());
        }
        coordinate_germs.push(ExactCoordinateGerm {
            id: germ,
            name: junction.name.clone(),
            source_cell: cell,
            source_events,
            coordinates,
        });
        junction_to_germ.insert(junction.id, germ);
        germ_to_junction.insert(germ, junction.id);
    }

    let mut coordinate_carriers = Vec::new();
    let mut doctrines = Vec::new();
    let mut arc_to_carrier = BTreeMap::new();
    let mut carrier_to_arc = BTreeMap::new();
    for (ordinal, arc) in arcs.values().enumerate() {
        let carrier = CoordinateCarrierId(
            u64::try_from(ordinal)
                .map_err(|_| AnalyticFieldError::CarrierOverflow)?
                .checked_add(1)
                .ok_or(AnalyticFieldError::CarrierOverflow)?,
        );
        coordinate_carriers.push(ExactCoordinateCarrier {
            id: carrier,
            name: arc.name.clone(),
            from: junction_to_germ[&arc.from],
            to: junction_to_germ[&arc.to],
            source_events: BTreeSet::from([arc.source_event]),
            kind: CoordinateCarrierKind::Interaction {
                doctrine: "exact analytic open-section transport".to_owned(),
            },
        });
        doctrines.push(DimensionalWaveCarrierDoctrine {
            carrier,
            delay: arc.delay,
            admitted_modes: arc.modal_phase_step.keys().copied().collect(),
            admittance: arc.admittance.clone(),
            modal_admittance: arc.modal_admittance.clone(),
            phase_transport: arc
                .modal_phase_step
                .iter()
                .map(|(mode, step)| (*mode, step.pow(arc.delay)))
                .collect(),
        });
        arc_to_carrier.insert(arc.id, carrier);
        carrier_to_arc.insert(carrier, arc.id);
    }
    let source = ExactDimensionalSource::new(
        incidence,
        axes,
        pairs,
        coordinate_germs,
        coordinate_carriers,
    )?;
    Ok((
        source,
        wave_modes,
        doctrines,
        junction_to_germ,
        germ_to_junction,
        arc_to_carrier,
        carrier_to_arc,
    ))
}

fn support_evaluate(
    support: &FieldSupportStanding,
    point: &RatVec3,
) -> Result<Rat, AnalyticFieldError> {
    match support {
        FieldSupportStanding::Quadric {
            resolved: Some(quadric),
            ..
        } => Ok(quadric.evaluate(point)),
        FieldSupportStanding::Torus(torus) => Ok(torus.evaluate(point)),
        FieldSupportStanding::Quadric { resolved: None, .. } => {
            Err(AnalyticFieldError::UnresolvedImplicitSupport)
        }
    }
}

fn require_quadric(
    support: &FieldSupportStanding,
) -> Result<&crate::ExactQuadric3, AnalyticFieldError> {
    match support {
        FieldSupportStanding::Quadric {
            resolved: Some(quadric),
            coorientation: Some(_),
            ..
        } => Ok(quadric),
        FieldSupportStanding::Quadric { resolved: None, .. } => {
            Err(AnalyticFieldError::UnresolvedImplicitSupport)
        }
        _ => Err(AnalyticFieldError::SupportSpeciesMismatch),
    }
}

fn require_torus(support: &FieldSupportStanding) -> Result<&crate::ExactTorus, AnalyticFieldError> {
    match support {
        FieldSupportStanding::Torus(torus) => Ok(torus),
        _ => Err(AnalyticFieldError::SupportSpeciesMismatch),
    }
}

fn validate_torus_frame(
    frame: &ExactTorusPhaseFrame,
    torus: &crate::ExactTorus,
) -> Result<(), AnalyticFieldError> {
    let vectors = [&frame.radial_cosine, &frame.radial_sine, &frame.axial];
    if vectors
        .iter()
        .any(|vector| vector.dot(vector) != Rat::one())
        || frame.radial_cosine.dot(&frame.radial_sine) != Rat::zero()
        || frame.radial_cosine.dot(&frame.axial) != Rat::zero()
        || frame.radial_sine.dot(&frame.axial) != Rat::zero()
        || frame.radial_cosine.cross(&frame.radial_sine) != frame.axial
        || frame.axial.cross(&torus.axis) != RatVec3::zero()
        || frame.axial.dot(&torus.axis).is_negative()
    {
        return Err(AnalyticFieldError::MalformedTorusFrame(torus.id));
    }
    Ok(())
}

fn bilinear(matrix: &[[Rat; 3]; 3], left: &RatVec3, right: &RatVec3) -> Rat {
    let left = [&left.x, &left.y, &left.z];
    let right = [&right.x, &right.y, &right.z];
    (0..3).fold(Rat::zero(), |sum, row| {
        sum + (0..3).fold(Rat::zero(), |row_sum, column| {
            row_sum + left[row] * &matrix[row][column] * right[column]
        })
    })
}

fn index_unique<K: Ord, V>(values: Vec<V>, key: impl Fn(&V) -> K) -> Option<BTreeMap<K, V>> {
    let mut indexed = BTreeMap::new();
    for value in values {
        if indexed.insert(key(&value), value).is_some() {
            return None;
        }
    }
    Some(indexed)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum AnalyticFieldError {
    #[error("an exact analytic field world requires junctions, arcs, and modes")]
    EmptyAnalyticWorld,
    #[error("an exact unit-conic phase must satisfy c²+s²=1")]
    NonunitPhase,
    #[error("an analytic field junction identity was repeated")]
    DuplicateJunction,
    #[error("an analytic field arc identity was repeated")]
    DuplicateArc,
    #[error("an analytic field mode identity was repeated")]
    DuplicateMode,
    #[error("analytic field junction {0:?} is absent")]
    UnknownJunction(AnalyticFieldJunctionId),
    #[error("analytic field arc {0:?} is malformed")]
    MalformedArc(AnalyticFieldArcId),
    #[error("analytic field arc {0:?} is absent")]
    UnknownArc(AnalyticFieldArcId),
    #[error("analytic field junction {0:?} is malformed")]
    MalformedJunction(AnalyticFieldJunctionId),
    #[error("analytic field mode {0:?} is malformed")]
    MalformedMode(DimensionalWaveModeId),
    #[error("analytic field mode {0:?} is absent")]
    UnknownMode(DimensionalWaveModeId),
    #[error("field germ {0:?} is absent")]
    UnknownFieldGerm(FieldGermId),
    #[error("field germ {0:?} is not contemporary")]
    InactiveFieldGerm(FieldGermId),
    #[error("field overlap {0:?} is absent")]
    UnknownFieldOverlap(FieldOverlapId),
    #[error("field overlap {0:?} remains open and cannot conduct")]
    OpenFieldOverlap(FieldOverlapId),
    #[error("analytic junction {0:?} is not contemporary")]
    InactiveJunction(AnalyticFieldJunctionId),
    #[error("analytic junction {0:?} differs from its caused overlap point")]
    JunctionPointMismatch(AnalyticFieldJunctionId),
    #[error("junction {junction:?} does not lie on germ {germ:?}")]
    JunctionLeavesSupport {
        junction: AnalyticFieldJunctionId,
        germ: FieldGermId,
    },
    #[error("the analytic orbit is degenerate")]
    DegenerateAnalyticOrbit,
    #[error("the analytic orbit leaves field germ {0:?}'s support")]
    OrbitLeavesSupport(FieldGermId),
    #[error("field germ {0:?} has unresolved support")]
    UnresolvedSupport(FieldGermId),
    #[error("the analytic support remains unresolved")]
    UnresolvedImplicitSupport,
    #[error("the analytic support has the wrong species for this orbit")]
    SupportSpeciesMismatch,
    #[error("torus {0:?} has no exact positively oriented orthonormal phase frame")]
    MalformedTorusFrame(crate::ImplicitCellId),
    #[error("field germ {0:?}'s torus is not regular for this cycle doctrine")]
    NonregularTorusCycle(FieldGermId),
    #[error("arc {arc:?} has no phase step for mode {mode:?}")]
    MissingArcMode {
        arc: AnalyticFieldArcId,
        mode: DimensionalWaveModeId,
    },
    #[error("the compiled analytic field world is malformed")]
    MalformedCompiledWorld,
    #[error("the retained field standing is malformed")]
    MalformedFieldStanding,
    #[error("field overlap {0:?} is singular at its interface point")]
    SingularInterface(FieldOverlapId),
    #[error("the refraction doctrine is malformed")]
    MalformedRefractionDoctrine,
    #[error("the incident covector does not satisfy its exact dispersion relation")]
    IncidentDispersionFailure,
    #[error("a scalar wave interface requires positive admittance")]
    NonpositiveAdmittance,
    #[error("the declared analytic interface interaction does not meet its overlap")]
    MalformedInterfaceInteraction,
    #[error("the incident analytic section does not admit this mode")]
    IncidentModeNotAdmitted,
    #[error("a propagating interface fiber has no transmitted traveling section")]
    PropagatingModeNotAdmitted,
    #[error("a grazing or evanescent interface fiber was admitted as ordinary traveling power")]
    NonpropagatingModeAdmitted,
    #[error("the declared analytic arc word is not a closed oriented cycle")]
    OpenAnalyticCycle,
    #[error("the analytic advection doctrine is malformed")]
    MalformedAdvectionDoctrine,
    #[error("the analytic advection generator is not Ω-skew")]
    AdvectionNotCapacitySkew,
    #[error("the analytic advection generator is not divergence-free")]
    AdvectionNotDivergenceFree,
    #[error("the analytic advection Cayley certificate failed")]
    AdvectionCertificateFailure,
    #[error("circulation probe {0:?} is malformed")]
    MalformedCirculationProbe(AnalyticCirculationProbeId),
    #[error("circulation probe {0:?} is not invariant under this advection")]
    NoninvariantCirculationProbe(AnalyticCirculationProbeId),
    #[error("circulation probe {0:?} has a nonzero caused boundary")]
    CirculationProbeNotClosed(AnalyticCirculationProbeId),
    #[error("the analytic advection population differs from its caused arcs")]
    AdvectionPopulationMismatch,
    #[error("the analytic advection standing is malformed")]
    MalformedAdvectionStanding,
    #[error("analytic advection event {0:?} already occurred")]
    RepeatedAdvectionEvent(EventId),
    #[error("an exact analytic field carrier overflowed")]
    CarrierOverflow,
    #[error(transparent)]
    Wave(#[from] DimensionalWaveError),
    #[error(transparent)]
    Receiver(#[from] crate::DimensionalReceiverError),
    #[error(transparent)]
    Algebraic(#[from] crate::CausalAlgebraicError),
    #[error(transparent)]
    Linear(#[from] crate::ExactLinearError),
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;
    use relational_geometry::integer;

    use super::*;
    use crate::{
        CausalFieldAtlasLaw, CausalFieldEvent, ExactTorus, FieldPhaseChannel, FieldRegionId,
        ImplicitCellId, OrientedFieldSample, SourceTorusOccurrence,
    };

    fn fraction(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn phase(cosine: i64, sine: i64) -> ExactUnitConicPhase {
        ExactUnitConicPhase::new(integer(cosine), integer(sine)).unwrap()
    }

    fn transport(cosine: Rat, sine: Rat) -> ExactWavePhaseTransport {
        ExactWavePhaseTransport::new(cosine, sine).unwrap()
    }

    fn torus_frame() -> ExactTorusPhaseFrame {
        ExactTorusPhaseFrame {
            radial_cosine: RatVec3::from_i64(1, 0, 0),
            radial_sine: RatVec3::from_i64(0, 1, 0),
            axial: RatVec3::from_i64(0, 0, 1),
        }
    }

    fn two_torus_field() -> (
        CausalFieldStanding,
        FieldGermId,
        FieldGermId,
        FieldOverlapId,
    ) {
        let law = CausalFieldAtlasLaw;
        let source = CausalFieldEvent {
            event: EventId(1),
            chronology: 1,
            images: Vec::new(),
            oriented_samples: Vec::new(),
            source_tori: (1..=2)
                .map(|identity| SourceTorusOccurrence {
                    region: FieldRegionId(identity),
                    torus: ExactTorus::new(
                        ImplicitCellId(identity),
                        EventId(1),
                        RatVec3::zero(),
                        RatVec3::from_i64(0, 0, 1),
                        integer(3),
                        integer(1),
                    )
                    .unwrap(),
                    phases: BTreeMap::new(),
                })
                .collect(),
        };
        let standing = law
            .enact(&law.initial_standing(), &source)
            .unwrap()
            .standing_after;
        let contact = CausalFieldEvent {
            event: EventId(2),
            chronology: 2,
            images: Vec::new(),
            oriented_samples: vec![OrientedFieldSample {
                regions: BTreeSet::from([FieldRegionId(1), FieldRegionId(2)]),
                point: RatVec3::from_i64(4, 0, 0),
                normal: RatVec3::from_i64(1, 0, 0),
                phase: BTreeMap::<FieldPhaseChannel, Rat>::new(),
                receiver_contact: None,
            }],
            source_tori: Vec::new(),
        };
        let successor = law.enact(&standing, &contact).unwrap();
        let first = *successor.standing_after.active_regions[&FieldRegionId(1)]
            .iter()
            .next()
            .unwrap();
        let second = *successor.standing_after.active_regions[&FieldRegionId(2)]
            .iter()
            .next()
            .unwrap();
        let overlap = *successor.radiation[0].overlaps.iter().next().unwrap();
        (successor.standing_after, first, second, overlap)
    }

    #[test]
    fn caused_torus_overlap_carries_phase_scattering_and_receiver_contact() {
        let (field, first_germ, second_germ, overlap) = two_torus_field();
        let interface = exact_interface_receipt(&field, overlap).unwrap();
        assert_eq!(interface.relation, ExactInterfaceRelation::Cooriented);

        let local_first = AnalyticFieldJunctionId(1);
        let shared = AnalyticFieldJunctionId(2);
        let local_second = AnalyticFieldJunctionId(3);
        let mode = DimensionalWaveModeId(1);
        let outer_longitude = |germ| ExactAnalyticOrbitGeometry::TorusLongitude {
            germ,
            frame: torus_frame(),
            meridian: phase(1, 0),
        };
        let quarter = ExactUnitConicPhase::new(Rat::zero(), Rat::one()).unwrap();
        let identity = ExactUnitConicPhase::identity();
        let clockwise = transport(Rat::zero(), -Rat::one());
        let counterclockwise = transport(Rat::zero(), Rat::one());
        let interior_quarter = transport(Rat::zero(), Rat::one());
        let law = ExactAnalyticFieldWaveLaw::new(
            field.clone(),
            vec![
                ExactAnalyticFieldJunction {
                    id: local_first,
                    name: "first torus local port".to_owned(),
                    point: RatVec3::from_i64(0, 4, 0),
                    origin: AnalyticFieldJunctionOrigin::LocalSupport { germ: first_germ },
                },
                ExactAnalyticFieldJunction {
                    id: shared,
                    name: "declared interacting overlap".to_owned(),
                    point: RatVec3::from_i64(4, 0, 0),
                    origin: AnalyticFieldJunctionOrigin::InteractingOverlap { overlap },
                },
                ExactAnalyticFieldJunction {
                    id: local_second,
                    name: "second torus local port".to_owned(),
                    point: RatVec3::from_i64(0, 4, 0),
                    origin: AnalyticFieldJunctionOrigin::LocalSupport { germ: second_germ },
                },
            ],
            vec![
                ExactAnalyticFieldArc {
                    id: AnalyticFieldArcId(1),
                    name: "first quarter orbit".to_owned(),
                    source_event: EventId(1),
                    from: local_first,
                    to: shared,
                    geometry: outer_longitude(first_germ),
                    start_phase: quarter.clone(),
                    geometric_step: clockwise,
                    delay: 1,
                    admittance: Rat::one(),
                    modal_admittance: BTreeMap::new(),
                    modal_phase_step: BTreeMap::from([(mode, interior_quarter)]),
                },
                ExactAnalyticFieldArc {
                    id: AnalyticFieldArcId(2),
                    name: "second quarter orbit".to_owned(),
                    source_event: EventId(1),
                    from: shared,
                    to: local_second,
                    geometry: outer_longitude(second_germ),
                    start_phase: identity,
                    geometric_step: counterclockwise,
                    delay: 1,
                    admittance: integer(2),
                    modal_admittance: BTreeMap::new(),
                    modal_phase_step: BTreeMap::from([(mode, ExactWavePhaseTransport::identity())]),
                },
            ],
            vec![ExactAnalyticFieldMode {
                id: mode,
                name: "coherent interface current".to_owned(),
                coherence_lineage: BTreeSet::from([EventId(1), EventId(2)]),
                frequency_square: Rat::one(),
                wave_number_square: BTreeMap::from([
                    (first_germ, Rat::one()),
                    (second_germ, Rat::one()),
                ]),
                interface_admittance: BTreeMap::from([
                    (first_germ, Rat::one()),
                    (second_germ, integer(2)),
                ]),
            }],
        )
        .unwrap();
        let optics = law
            .interface_optics(
                overlap,
                mode,
                AnalyticFieldArcId(1),
                AnalyticFieldArcId(2),
                RatVec3::from_i64(1, 0, 0),
                ExactRefractionHand::AlongNormal,
            )
            .unwrap();
        let ExactAnalyticInterfaceAmplitudeFiber::Traveling(coefficients) = optics.amplitude else {
            panic!("the equal-dispersion interface must admit a traveling fiber");
        };
        assert_eq!(coefficients.reflection, fraction(-1, 3));
        assert_eq!(coefficients.transmission, fraction(2, 3));
        assert!(coefficients.energy_residual.is_zero());
        let source_event = field.germs[&first_germ].last_event;
        let first = law
            .enact(
                &law.initial_standing(),
                &ExactAnalyticFieldWaveEvent {
                    event: EventId(10),
                    impulses: vec![ExactAnalyticFieldWaveImpulse {
                        source_event,
                        mode,
                        junction: local_first,
                        departure: ExactComplexWaveCurrent::new(Rat::one(), Rat::zero()),
                    }],
                },
            )
            .unwrap();
        let slice = law
            .restrict(
                &first.standing_after,
                ReceiverId(9),
                &ExactReceiverPrimaryDoctrine::new(Rat::one(), Rat::zero()).unwrap(),
            )
            .unwrap();
        assert_eq!(slice.sections.len(), 1);
        assert_eq!(slice.sections[0].point, RatVec3::from_i64(0, 4, 0));
        assert_eq!(
            slice.sections[0].current,
            ExactComplexWaveCurrent::new(Rat::one(), Rat::zero())
        );
        assert!(slice.contacts[0].response.alpha.is_positive());

        let second = law
            .enact(
                &first.standing_after,
                &ExactAnalyticFieldWaveEvent {
                    event: EventId(11),
                    impulses: Vec::new(),
                },
            )
            .unwrap();
        let scatter = second
            .radiation
            .iter()
            .flat_map(|radiation| &radiation.interface_scatters)
            .find(|scatter| scatter.junction == shared)
            .unwrap();
        let departure = |arc| {
            scatter
                .departures
                .iter()
                .find(|(candidate, _)| *candidate == arc)
                .unwrap()
                .1
                .clone()
        };
        assert_eq!(
            departure(AnalyticFieldArcId(1)),
            ExactComplexWaveCurrent::new(Rat::zero(), fraction(-1, 3))
        );
        assert_eq!(
            departure(AnalyticFieldArcId(2)),
            ExactComplexWaveCurrent::new(Rat::zero(), fraction(2, 3))
        );
        assert_eq!(scatter.energy_entered, scatter.energy_departed);
        assert!(scatter.passive_residual.is_zero());
        assert_eq!(second.standing_after.energy, Rat::one());
    }

    #[test]
    fn observation_derived_quadric_carries_an_exact_conic_orbit() {
        let law = CausalFieldAtlasLaw;
        let samples = [
            RatVec3::from_i64(2, 0, 0),
            RatVec3::from_i64(-2, 0, 0),
            RatVec3::from_i64(0, 2, 0),
            RatVec3::from_i64(0, -2, 0),
            RatVec3::from_i64(0, 0, 2),
            RatVec3::from_i64(0, 0, -2),
        ]
        .into_iter()
        .map(|point| OrientedFieldSample {
            regions: BTreeSet::from([FieldRegionId(3)]),
            normal: point.clone(),
            point,
            phase: BTreeMap::new(),
            receiver_contact: None,
        })
        .collect();
        let field = law
            .enact(
                &law.initial_standing(),
                &CausalFieldEvent {
                    event: EventId(3),
                    chronology: 3,
                    images: Vec::new(),
                    oriented_samples: samples,
                    source_tori: Vec::new(),
                },
            )
            .unwrap()
            .standing_after;
        let germ = *field.active_germs().iter().next().unwrap();
        let orbit = ExactAnalyticOrbitGeometry::QuadricConic {
            germ,
            center: RatVec3::zero(),
            cosine_axis: RatVec3::from_i64(2, 0, 0),
            sine_axis: RatVec3::from_i64(0, 2, 0),
        };
        orbit.validate(&field).unwrap();
        let sample = ExactUnitConicPhase::new(fraction(3, 5), fraction(4, 5)).unwrap();
        assert_eq!(
            orbit.point(&field, &sample).unwrap(),
            RatVec3::new(fraction(6, 5), fraction(8, 5), Rat::zero())
        );
        assert_eq!(
            orbit.tangent(&field, &sample).unwrap(),
            RatVec3::new(fraction(-8, 5), fraction(6, 5), Rat::zero())
        );
    }

    #[test]
    fn refraction_retains_propagating_grazing_and_evanescent_fibers_exactly() {
        let incident = RatVec3::from_i64(3, 4, 0);
        let normal = RatVec3::from_i64(1, 0, 0);
        let propagating = exact_refraction_fiber(
            incident.clone(),
            normal.clone(),
            integer(25),
            integer(25),
            ExactRefractionHand::AlongNormal,
        )
        .unwrap();
        assert_eq!(propagating.reflected_covector, RatVec3::from_i64(-3, 4, 0));
        assert_eq!(
            propagating.transmitted_regime,
            ExactRefractionRegime::Propagating {
                normal_coefficient_square: integer(9),
                hand: ExactRefractionHand::AlongNormal,
            }
        );
        assert!(matches!(
            exact_refraction_fiber(
                incident.clone(),
                normal.clone(),
                integer(25),
                integer(16),
                ExactRefractionHand::AlongNormal,
            )
            .unwrap()
            .transmitted_regime,
            ExactRefractionRegime::Grazing
        ));
        assert_eq!(
            exact_refraction_fiber(
                incident,
                normal,
                integer(25),
                integer(9),
                ExactRefractionHand::AgainstNormal,
            )
            .unwrap()
            .transmitted_regime,
            ExactRefractionRegime::Evanescent {
                normal_coefficient_square_deficit: integer(7),
            }
        );
        let coefficients = exact_scalar_interface_coefficients(Rat::one(), integer(2)).unwrap();
        assert_eq!(coefficients.reflection, fraction(-1, 3));
        assert_eq!(coefficients.transmission, fraction(2, 3));
        assert!(coefficients.energy_residual.is_zero());
    }

    #[test]
    fn cayley_advection_preserves_total_energy_and_two_cycle_integrals() {
        let arcs = (1..=4)
            .map(AnalyticFieldArcId)
            .collect::<Vec<AnalyticFieldArcId>>();
        let capacities = arcs.iter().copied().map(|arc| (arc, Rat::one())).collect();
        let generator = ExactRatMatrix::new(vec![
            vec![integer(0), integer(1), integer(0), integer(-1)],
            vec![integer(-1), integer(0), integer(1), integer(0)],
            vec![integer(0), integer(-1), integer(0), integer(1)],
            vec![integer(1), integer(0), integer(-1), integer(0)],
        ])
        .unwrap();
        let total_probe = ExactAnalyticCirculationProbe {
            id: AnalyticCirculationProbeId(1),
            name: "closed-loop total".to_owned(),
            coefficients: arcs.iter().copied().map(|arc| (arc, Rat::one())).collect(),
        };
        let alternating_probe = ExactAnalyticCirculationProbe {
            id: AnalyticCirculationProbeId(2),
            name: "opposed-sheet circulation".to_owned(),
            coefficients: arcs
                .iter()
                .copied()
                .zip([1, -1, 1, -1].map(integer))
                .collect(),
        };
        let law = ExactAnalyticAdvectionLaw::new(
            capacities,
            generator,
            Rat::one(),
            vec![total_probe, alternating_probe],
        )
        .unwrap();
        let initial = law
            .initial_standing(
                arcs.iter()
                    .copied()
                    .zip([1, 2, 4, 8].map(integer))
                    .collect(),
            )
            .unwrap();
        let successor = law
            .enact(
                &initial,
                &ExactAnalyticAdvectionEvent { event: EventId(30) },
            )
            .unwrap();
        assert_ne!(successor.standing_after.values, initial.values);
        let receipt = &successor.radiation[0];
        assert!(receipt.weighted_total_residual.is_zero());
        assert!(receipt.quadratic_energy_residual.is_zero());
        assert!(
            receipt
                .circulations
                .iter()
                .all(|circulation| circulation.residual.is_zero())
        );
    }
}
