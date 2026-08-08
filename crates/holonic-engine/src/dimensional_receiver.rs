//! Exact receiver-relative sections of varying-dimensional coordinate ecologies.
//!
//! A terminal surface cannot own the rank, incidence, or coordinates of the
//! body which reaches it.  This module therefore separates three things:
//!
//! - [`ExactDimensionalSource`] retains caused coordinate germs, their exact
//!   source cells, declared carriers, and local algebraic dependencies;
//! - [`DimensionalReceiverAtlas`] retains caused receiver frames and their
//!   chronology; and
//! - [`DimensionalSliceReceipt`] is the finite receiver testimony which a
//!   display, notation, or other membrane may transduce.
//!
//! Coordinates may be absent from an earlier or otherwise differently
//! conditioned germ.  Absence is not replaced by zero.  A receiver which asks
//! for an unavailable direction gets an explicit unresolved fiber.  Several
//! source germs may also occupy one projected address without identification:
//! the complete collision bucket survives the projection.
//!
//! Exact complex coordinate pairs are represented as two real receiver
//! coordinates with the local quarter-turn `J(a,b)=(-b,a)`.  Consequently
//! `J²=-I` is an exact chart relation rather than an "imaginary" source
//! object.  A unit-conic relation may additionally restrict such a pair.  This
//! is useful for residue phase loops and products of loops, but the engine
//! never infers a loop merely because a rendered curve looks closed.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::{Rat, ReceiverId};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    CausalAlgebraicError, CausalCellId, ComparativeMultiplicity, EventId, GradedCausalComplex,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DimensionalAxisId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CoordinateGermId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CoordinateCarrierId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalAxis {
    pub id: DimensionalAxisId,
    pub name: String,
    pub source_events: BTreeSet<EventId>,
}

impl DimensionalAxis {
    pub fn new(
        id: DimensionalAxisId,
        name: impl Into<String>,
        source_events: BTreeSet<EventId>,
    ) -> Result<Self, DimensionalReceiverError> {
        let result = Self {
            id,
            name: name.into(),
            source_events,
        };
        result.validate()?;
        Ok(result)
    }

    fn validate(&self) -> Result<(), DimensionalReceiverError> {
        if self.name.is_empty() || self.source_events.is_empty() {
            return Err(DimensionalReceiverError::MalformedAxis(self.id));
        }
        Ok(())
    }
}

/// Two exact receiver coordinates carrying the local complex structure
/// `J(a,b)=(-b,a)`.
///
/// When `unit_conic` is true, every germ which carries either coordinate must
/// carry both and must satisfy `a²+b²=1`.  The pair contributes one local
/// dimension because the conic relation removes one coordinate degree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactComplexAxisPair {
    pub real: DimensionalAxisId,
    pub imaginary: DimensionalAxisId,
    pub unit_conic: bool,
}

impl ExactComplexAxisPair {
    pub fn quarter_turn(&self, real: &Rat, imaginary: &Rat) -> (Rat, Rat) {
        (-imaginary, real.clone())
    }

    pub fn second_quarter_turn(&self, real: &Rat, imaginary: &Rat) -> (Rat, Rat) {
        let (first_real, first_imaginary) = self.quarter_turn(real, imaginary);
        self.quarter_turn(&first_real, &first_imaginary)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactCoordinateGerm {
    pub id: CoordinateGermId,
    pub name: String,
    pub source_cell: CausalCellId,
    pub source_events: BTreeSet<EventId>,
    /// A partial exact coordinate section. Missing axes stay missing.
    pub coordinates: BTreeMap<DimensionalAxisId, Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CoordinateCarrierKind {
    /// One actual oriented boundary term in the retained source complex.
    Boundary {
        higher: CausalCellId,
        lower: CausalCellId,
        coefficient: ComparativeMultiplicity,
    },
    /// An application-declared chronology between two caused occurrences.
    Chronology,
    /// A returned recurrence in one named source phase.
    PhaseReturn { axis: DimensionalAxisId },
    /// Another application-declared interaction. Its meaning remains named
    /// and is never inferred from projected proximity.
    Interaction { doctrine: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactCoordinateCarrier {
    pub id: CoordinateCarrierId,
    pub name: String,
    pub from: CoordinateGermId,
    pub to: CoordinateGermId,
    pub source_events: BTreeSet<EventId>,
    pub kind: CoordinateCarrierKind,
}

/// A caused coordinate ecology over exact source incidence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactDimensionalSource {
    pub schema: String,
    incidence: GradedCausalComplex,
    axes: BTreeMap<DimensionalAxisId, DimensionalAxis>,
    complex_pairs: Vec<ExactComplexAxisPair>,
    germs: BTreeMap<CoordinateGermId, ExactCoordinateGerm>,
    carriers: BTreeMap<CoordinateCarrierId, ExactCoordinateCarrier>,
    /// Complete caused-event support, formed once with the immutable source.
    /// Receiver horizons can therefore validate locally without rediscovering
    /// the event population on every deed.
    source_events: BTreeSet<EventId>,
}

impl ExactDimensionalSource {
    pub fn new(
        incidence: GradedCausalComplex,
        axes: Vec<DimensionalAxis>,
        complex_pairs: Vec<ExactComplexAxisPair>,
        germs: Vec<ExactCoordinateGerm>,
        carriers: Vec<ExactCoordinateCarrier>,
    ) -> Result<Self, DimensionalReceiverError> {
        let mut axis_map = BTreeMap::new();
        for axis in axes {
            let id = axis.id;
            if axis_map.insert(id, axis).is_some() {
                return Err(DimensionalReceiverError::DuplicateAxis(id));
            }
        }
        let mut germ_map = BTreeMap::new();
        for germ in germs {
            let id = germ.id;
            if germ_map.insert(id, germ).is_some() {
                return Err(DimensionalReceiverError::DuplicateGerm(id));
            }
        }
        let mut carrier_map = BTreeMap::new();
        for carrier in carriers {
            let id = carrier.id;
            if carrier_map.insert(id, carrier).is_some() {
                return Err(DimensionalReceiverError::DuplicateCarrier(id));
            }
        }
        let source_events = incidence
            .cells()
            .values()
            .flat_map(|cell| cell.source_events.iter().copied())
            .chain(
                axis_map
                    .values()
                    .flat_map(|axis| axis.source_events.iter().copied()),
            )
            .chain(
                germ_map
                    .values()
                    .flat_map(|germ| germ.source_events.iter().copied()),
            )
            .chain(
                carrier_map
                    .values()
                    .flat_map(|carrier| carrier.source_events.iter().copied()),
            )
            .collect();
        let result = Self {
            schema: "holonic-engine.exact-dimensional-source.v2".to_owned(),
            incidence,
            axes: axis_map,
            complex_pairs,
            germs: germ_map,
            carriers: carrier_map,
            source_events,
        };
        result.validate()?;
        Ok(result)
    }

    pub fn incidence(&self) -> &GradedCausalComplex {
        &self.incidence
    }

    pub fn axes(&self) -> &BTreeMap<DimensionalAxisId, DimensionalAxis> {
        &self.axes
    }

    pub fn complex_pairs(&self) -> &[ExactComplexAxisPair] {
        &self.complex_pairs
    }

    pub fn germs(&self) -> &BTreeMap<CoordinateGermId, ExactCoordinateGerm> {
        &self.germs
    }

    pub fn carriers(&self) -> &BTreeMap<CoordinateCarrierId, ExactCoordinateCarrier> {
        &self.carriers
    }

    pub fn source_events(&self) -> &BTreeSet<EventId> {
        &self.source_events
    }

    pub fn germ_local_dimension(
        &self,
        germ: CoordinateGermId,
    ) -> Result<u32, DimensionalReceiverError> {
        let germ = self
            .germs
            .get(&germ)
            .ok_or(DimensionalReceiverError::MissingGerm(germ))?;
        let mut dimension = u32::try_from(germ.coordinates.len())
            .map_err(|_| DimensionalReceiverError::CarrierOverflow)?;
        for pair in &self.complex_pairs {
            if germ.coordinates.contains_key(&pair.real) {
                dimension = dimension
                    .checked_sub(1)
                    .ok_or(DimensionalReceiverError::CarrierOverflow)?;
            }
        }
        Ok(dimension)
    }

    pub fn maximum_local_dimension(&self) -> Result<u32, DimensionalReceiverError> {
        self.germs
            .keys()
            .map(|germ| self.germ_local_dimension(*germ))
            .collect::<Result<Vec<_>, _>>()
            .map(|dimensions| dimensions.into_iter().max().unwrap_or(0))
    }

    pub fn validate(&self) -> Result<(), DimensionalReceiverError> {
        if self.schema != "holonic-engine.exact-dimensional-source.v2" {
            return Err(DimensionalReceiverError::MalformedSource);
        }
        self.incidence.validate()?;
        for (id, axis) in &self.axes {
            if *id != axis.id {
                return Err(DimensionalReceiverError::MalformedAxis(*id));
            }
            axis.validate()?;
        }

        let mut paired_axes = BTreeSet::new();
        for pair in &self.complex_pairs {
            if pair.real == pair.imaginary
                || !self.axes.contains_key(&pair.real)
                || !self.axes.contains_key(&pair.imaginary)
                || !paired_axes.insert(pair.real)
                || !paired_axes.insert(pair.imaginary)
            {
                return Err(DimensionalReceiverError::MalformedComplexPair {
                    real: pair.real,
                    imaginary: pair.imaginary,
                });
            }
        }

        for (id, germ) in &self.germs {
            if *id != germ.id
                || germ.name.is_empty()
                || germ.source_events.is_empty()
                || self.incidence.cell(germ.source_cell).is_err()
                || germ
                    .coordinates
                    .keys()
                    .any(|axis| !self.axes.contains_key(axis))
            {
                return Err(DimensionalReceiverError::MalformedGerm(*id));
            }
            for pair in &self.complex_pairs {
                let real = germ.coordinates.get(&pair.real);
                let imaginary = germ.coordinates.get(&pair.imaginary);
                if real.is_some() != imaginary.is_some() {
                    return Err(DimensionalReceiverError::IncompleteComplexPair {
                        germ: *id,
                        real: pair.real,
                        imaginary: pair.imaginary,
                    });
                }
                if pair.unit_conic
                    && let Some((real, imaginary)) = real.zip(imaginary)
                    && real * real + imaginary * imaginary != Rat::one()
                {
                    return Err(DimensionalReceiverError::ComplexPairOffConic {
                        germ: *id,
                        real: pair.real,
                        imaginary: pair.imaginary,
                    });
                }
            }
        }

        for (id, carrier) in &self.carriers {
            if *id != carrier.id
                || carrier.name.is_empty()
                || carrier.source_events.is_empty()
                || !self.germs.contains_key(&carrier.from)
                || !self.germs.contains_key(&carrier.to)
                || carrier.from == carrier.to
            {
                return Err(DimensionalReceiverError::MalformedCarrier(*id));
            }
            match &carrier.kind {
                CoordinateCarrierKind::Boundary {
                    higher,
                    lower,
                    coefficient,
                } => {
                    let body = self.incidence.cell(*higher)?;
                    let lower_body = self.incidence.cell(*lower)?;
                    if body.grade != lower_body.grade.saturating_add(1)
                        || body.boundary.coefficient(*lower) != *coefficient
                        || coefficient.is_zero()
                        || self.germs[&carrier.from].source_cell != *higher
                        || self.germs[&carrier.to].source_cell != *lower
                    {
                        return Err(DimensionalReceiverError::MalformedBoundaryCarrier(*id));
                    }
                }
                CoordinateCarrierKind::PhaseReturn { axis } => {
                    if !self.axes.contains_key(axis) {
                        return Err(DimensionalReceiverError::MissingAxis(*axis));
                    }
                }
                CoordinateCarrierKind::Interaction { doctrine } if doctrine.is_empty() => {
                    return Err(DimensionalReceiverError::MalformedCarrier(*id));
                }
                CoordinateCarrierKind::Chronology | CoordinateCarrierKind::Interaction { .. } => {}
            }
        }
        let expected_source_events = self
            .incidence
            .cells()
            .values()
            .flat_map(|cell| cell.source_events.iter().copied())
            .chain(
                self.axes
                    .values()
                    .flat_map(|axis| axis.source_events.iter().copied()),
            )
            .chain(
                self.germs
                    .values()
                    .flat_map(|germ| germ.source_events.iter().copied()),
            )
            .chain(
                self.carriers
                    .values()
                    .flat_map(|carrier| carrier.source_events.iter().copied()),
            )
            .collect::<BTreeSet<_>>();
        if self.source_events.is_empty() || self.source_events != expected_source_events {
            return Err(DimensionalReceiverError::MalformedSource);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactSliceCovector {
    terms: BTreeMap<DimensionalAxisId, Rat>,
}

impl ExactSliceCovector {
    pub fn new(terms: BTreeMap<DimensionalAxisId, Rat>) -> Result<Self, DimensionalReceiverError> {
        let result = Self {
            terms: terms
                .into_iter()
                .filter(|(_, coefficient)| !coefficient.is_zero())
                .collect(),
        };
        if result.terms.is_empty() {
            return Err(DimensionalReceiverError::ZeroCovector);
        }
        Ok(result)
    }

    pub fn axis(axis: DimensionalAxisId) -> Self {
        Self {
            terms: BTreeMap::from([(axis, Rat::one())]),
        }
    }

    pub fn terms(&self) -> &BTreeMap<DimensionalAxisId, Rat> {
        &self.terms
    }

    fn validate(&self, source: &ExactDimensionalSource) -> Result<(), DimensionalReceiverError> {
        if self.terms.is_empty() {
            return Err(DimensionalReceiverError::ZeroCovector);
        }
        for (axis, coefficient) in &self.terms {
            if !source.axes.contains_key(axis) {
                return Err(DimensionalReceiverError::MissingAxis(*axis));
            }
            if coefficient.is_zero() {
                return Err(DimensionalReceiverError::StoredZeroCovectorTerm(*axis));
            }
        }
        Ok(())
    }

    fn evaluate(&self, germ: &ExactCoordinateGerm) -> Result<Rat, BTreeSet<DimensionalAxisId>> {
        let missing = self
            .terms
            .keys()
            .filter(|axis| !germ.coordinates.contains_key(axis))
            .copied()
            .collect::<BTreeSet<_>>();
        if !missing.is_empty() {
            return Err(missing);
        }
        Ok(self
            .terms
            .iter()
            .fold(Rat::zero(), |sum, (axis, coefficient)| {
                sum + coefficient * &germ.coordinates[axis]
            }))
    }

    fn turned(&self, first: DimensionalAxisId, second: DimensionalAxisId, ratio: &Rat) -> Self {
        let denominator = Rat::one() + ratio * ratio;
        let cosine = (Rat::one() - ratio * ratio) / &denominator;
        let sine = (Rat::from_integer(BigInt::from(2)) * ratio) / denominator;
        let first_value = self.terms.get(&first).cloned().unwrap_or_else(Rat::zero);
        let second_value = self.terms.get(&second).cloned().unwrap_or_else(Rat::zero);
        let mut terms = self.terms.clone();
        let next_first = &cosine * &first_value - &sine * &second_value;
        let next_second = &sine * first_value + cosine * second_value;
        if next_first.is_zero() {
            terms.remove(&first);
        } else {
            terms.insert(first, next_first);
        }
        if next_second.is_zero() {
            terms.remove(&second);
        } else {
            terms.insert(second, next_second);
        }
        Self { terms }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactSliceConstraint {
    pub covector: ExactSliceCovector,
    pub center: Rat,
    /// Zero is an exact section. Positive radius is a closed rational tube
    /// selected by the receiver.
    pub radius: Rat,
}

/// One caused current front received from an application law.
///
/// This support is deliberately generic: the application retains the
/// doctrine which says whether a front is a leader, return, impulse, probe,
/// or another physical species. The receiver owns only its exact caused
/// event, active source support, and changed coordinate directions.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalCausalFront {
    pub ordinal: u64,
    pub source_event: EventId,
    pub active_germs: BTreeSet<CoordinateGermId>,
    pub active_carriers: BTreeSet<CoordinateCarrierId>,
    pub changed_axes: BTreeSet<DimensionalAxisId>,
}

impl DimensionalCausalFront {
    fn validate(
        &self,
        source: &ExactDimensionalSource,
        causal_horizon: Option<&BTreeSet<EventId>>,
    ) -> Result<(), DimensionalReceiverError> {
        if self.ordinal == 0
            || !source.source_events.contains(&self.source_event)
            || causal_horizon.is_some_and(|horizon| !horizon.contains(&self.source_event))
            || (self.active_germs.is_empty() && self.active_carriers.is_empty())
            || self
                .active_germs
                .iter()
                .any(|germ| !source.germs.contains_key(germ))
            || self
                .active_carriers
                .iter()
                .any(|carrier| !source.carriers.contains_key(carrier))
            || self
                .changed_axes
                .iter()
                .any(|axis| !source.axes.contains_key(axis))
        {
            return Err(DimensionalReceiverError::MalformedCausalFront);
        }
        let received = |events: &BTreeSet<EventId>| {
            causal_horizon.is_none_or(|horizon| events.is_subset(horizon))
        };
        if self
            .active_germs
            .iter()
            .any(|germ| !received(&source.germs[germ].source_events))
            || self
                .active_carriers
                .iter()
                .any(|carrier| !received(&source.carriers[carrier].source_events))
        {
            return Err(DimensionalReceiverError::CausalFrontOutsideHorizon);
        }
        let front_is_caused = self.active_germs.iter().any(|germ| {
            source.germs[germ]
                .source_events
                .contains(&self.source_event)
        }) || self.active_carriers.iter().any(|carrier| {
            source.carriers[carrier]
                .source_events
                .contains(&self.source_event)
        });
        if !front_is_caused {
            return Err(DimensionalReceiverError::MalformedCausalFront);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalReceiverFrame {
    pub receiver: ReceiverId,
    pub event: EventId,
    pub chronology: u64,
    pub horizontal: ExactSliceCovector,
    pub vertical: ExactSliceCovector,
    pub depth: Option<ExactSliceCovector>,
    pub horizontal_center: Rat,
    pub vertical_center: Rat,
    pub horizontal_span: Rat,
    pub vertical_span: Rat,
    pub constraints: Vec<ExactSliceConstraint>,
    /// Events which have reached this receiver-relative historical horizon.
    /// `None` means the completed source standing. This restricts testimony;
    /// it never removes events from the source body.
    pub causal_horizon: Option<BTreeSet<EventId>>,
    pub active_front: Option<DimensionalCausalFront>,
}

impl DimensionalReceiverFrame {
    fn validate(&self, source: &ExactDimensionalSource) -> Result<(), DimensionalReceiverError> {
        self.horizontal.validate(source)?;
        self.vertical.validate(source)?;
        if let Some(depth) = &self.depth {
            depth.validate(source)?;
        }
        if !self.horizontal_span.is_positive() || !self.vertical_span.is_positive() {
            return Err(DimensionalReceiverError::NonpositiveAperture);
        }
        if !covectors_independent(&self.horizontal, &self.vertical) {
            return Err(DimensionalReceiverError::DependentPresentationCovectors);
        }
        for constraint in &self.constraints {
            constraint.covector.validate(source)?;
            if constraint.radius.is_negative() {
                return Err(DimensionalReceiverError::NegativeSliceRadius);
            }
        }
        if self
            .causal_horizon
            .as_ref()
            .is_some_and(|events| !events.is_subset(source.source_events()))
        {
            return Err(DimensionalReceiverError::UnknownSourceEventInHorizon);
        }
        if let Some(front) = &self.active_front {
            front.validate(source, self.causal_horizon.as_ref())?;
        }
        Ok(())
    }

    fn same_projection_as(&self, other: &Self) -> bool {
        self.receiver == other.receiver
            && self.horizontal == other.horizontal
            && self.vertical == other.vertical
            && self.depth == other.depth
            && self.horizontal_center == other.horizontal_center
            && self.vertical_center == other.vertical_center
            && self.horizontal_span == other.horizontal_span
            && self.vertical_span == other.vertical_span
            && self.constraints == other.constraints
            && self.causal_horizon == other.causal_horizon
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalReceiverFounding {
    pub horizontal: ExactSliceCovector,
    pub vertical: ExactSliceCovector,
    pub depth: Option<ExactSliceCovector>,
    pub horizontal_center: Rat,
    pub vertical_center: Rat,
    pub horizontal_span: Rat,
    pub vertical_span: Rat,
    pub constraints: Vec<ExactSliceConstraint>,
    pub causal_horizon: Option<BTreeSet<EventId>>,
    pub active_front: Option<DimensionalCausalFront>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DimensionalReceiverDeed {
    Found(DimensionalReceiverFounding),
    /// Replace the complete receiver chart atomically. The source body is
    /// untouched; this is the caused analogue of moving, turning, dilating,
    /// and changing a section in one receiver occurrence.
    Reframe(DimensionalReceiverFounding),
    Rebase {
        horizontal: ExactSliceCovector,
        vertical: ExactSliceCovector,
        depth: Option<ExactSliceCovector>,
    },
    /// Exact Cayley turn in a named source-coordinate plane. The turn acts on
    /// the complete receiver body: visible, depth, and slicing covectors.
    Turn {
        first: DimensionalAxisId,
        second: DimensionalAxisId,
        ratio: Rat,
    },
    Translate {
        horizontal: Rat,
        vertical: Rat,
    },
    Dilate {
        horizontal: Rat,
        vertical: Rat,
    },
    ReplaceConstraints(Vec<ExactSliceConstraint>),
    /// Receive another exact historical section of the immutable source.
    /// The display clock may reveal this section, but cannot create it.
    ReplaceCausalHorizon(Option<BTreeSet<EventId>>),
    /// Receive an application-caused current front and its contemporary
    /// historical horizon atomically.
    ReceiveCausalFront {
        causal_horizon: Option<BTreeSet<EventId>>,
        front: DimensionalCausalFront,
    },
    Retain,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalReceiverRequest {
    pub event: EventId,
    pub chronology: u64,
    pub receiver: ReceiverId,
    pub deed: DimensionalReceiverDeed,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DimensionalGermDisposition {
    /// The germ exists in the complete source lineage but has not reached the
    /// receiver's selected historical horizon.
    OutsideCausalHorizon,
    Visible {
        horizontal: Rat,
        vertical: Rat,
        normalized_horizontal: Rat,
        normalized_vertical: Rat,
        depth: Option<Rat>,
    },
    OutsideAperture {
        normalized_horizontal: Rat,
        normalized_vertical: Rat,
    },
    OutsideSlice {
        constraint: usize,
        departure: Rat,
        radius: Rat,
    },
    Unresolved {
        missing_axes: BTreeSet<DimensionalAxisId>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalGermReceipt {
    pub germ: CoordinateGermId,
    pub source_cell: CausalCellId,
    pub source_grade: u32,
    pub source_events: BTreeSet<EventId>,
    pub local_dimension: u32,
    pub disposition: DimensionalGermDisposition,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalProjectionBucket {
    pub normalized_horizontal: Rat,
    pub normalized_vertical: Rat,
    pub members: Vec<CoordinateGermId>,
}

/// One exact corner of the receiver-relative convex envelope.
///
/// The envelope is testimony about the selected two-covector projection. It
/// is not a source face and therefore carries no source-cell identity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalProjectionEnvelopeCorner {
    pub normalized_horizontal: Rat,
    pub normalized_vertical: Rat,
    pub members: Vec<CoordinateGermId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DimensionalCarrierDisposition {
    Visible,
    OutsideCausalHorizon,
    EndpointOutside,
    EndpointUnresolved,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalCarrierReceipt {
    pub carrier: CoordinateCarrierId,
    pub from: CoordinateGermId,
    pub to: CoordinateGermId,
    pub disposition: DimensionalCarrierDisposition,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalSliceReceipt {
    pub schema: String,
    pub receiver: ReceiverId,
    pub event: EventId,
    pub chronology: u64,
    pub source_cells: usize,
    pub source_dimension: Option<u32>,
    pub source_f_vector: BTreeMap<u32, usize>,
    pub coordinate_axes: usize,
    pub maximum_local_dimension: u32,
    pub received_source_events: usize,
    pub received_source_cells: usize,
    pub received_source_dimension: Option<u32>,
    pub received_source_f_vector: BTreeMap<u32, usize>,
    pub received_coordinate_axes: usize,
    pub received_maximum_local_dimension: u32,
    pub active_front: Option<DimensionalCausalFront>,
    pub local_dimension_population: BTreeMap<u32, BigUint>,
    pub germs: BTreeMap<CoordinateGermId, DimensionalGermReceipt>,
    pub projection_buckets: Vec<DimensionalProjectionBucket>,
    pub projection_envelope: Vec<DimensionalProjectionEnvelopeCorner>,
    pub carriers: BTreeMap<CoordinateCarrierId, DimensionalCarrierReceipt>,
    pub visible_germs: BigUint,
    pub outside_germs: BigUint,
    pub unresolved_germs: BigUint,
    pub future_germs: BigUint,
    pub collapsed_buckets: BigUint,
    /// Projection remains testimony and mints no source incidence.
    pub projection_cells: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalReceiverRadiation {
    pub schema: String,
    pub previous: Option<DimensionalReceiverFrame>,
    pub current: DimensionalReceiverFrame,
    pub transition: DimensionalReceiverTransition,
    pub receipt: DimensionalSliceReceipt,
    /// The receiver chart and causal horizon were unchanged, so only the
    /// active current front changed and the exact projection carried.
    pub projection_reused: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalReceiverTransition {
    pub predecessor_event: Option<EventId>,
    pub event: EventId,
    pub chronology: u64,
    pub deed: DimensionalReceiverDeed,
    pub from: Option<DimensionalReceiverFrame>,
    pub to: DimensionalReceiverFrame,
}

/// Persistent caused receiver frames over one immutable exact coordinate body.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DimensionalReceiverAtlas {
    pub schema: String,
    source: ExactDimensionalSource,
    frames: BTreeMap<ReceiverId, DimensionalReceiverFrame>,
    /// Rebuildable exact observation cache. It is never source standing.
    receipts: BTreeMap<ReceiverId, DimensionalSliceReceipt>,
    lineage: BTreeMap<ReceiverId, Vec<DimensionalReceiverTransition>>,
    used_events: BTreeSet<EventId>,
    last_chronology: BTreeMap<ReceiverId, u64>,
}

impl DimensionalReceiverAtlas {
    pub fn new(source: ExactDimensionalSource) -> Result<Self, DimensionalReceiverError> {
        source.validate()?;
        Ok(Self {
            schema: "holonic-engine.dimensional-receiver-atlas.v2".to_owned(),
            source,
            frames: BTreeMap::new(),
            receipts: BTreeMap::new(),
            lineage: BTreeMap::new(),
            used_events: BTreeSet::new(),
            last_chronology: BTreeMap::new(),
        })
    }

    pub fn source(&self) -> &ExactDimensionalSource {
        &self.source
    }

    pub fn frame(&self, receiver: ReceiverId) -> Option<&DimensionalReceiverFrame> {
        self.frames.get(&receiver)
    }

    pub fn lineage(&self, receiver: ReceiverId) -> Option<&[DimensionalReceiverTransition]> {
        self.lineage.get(&receiver).map(Vec::as_slice)
    }

    pub fn receive(
        &mut self,
        request: &DimensionalReceiverRequest,
    ) -> Result<DimensionalReceiverRadiation, DimensionalReceiverError> {
        // `source` is private and immutable after the validating constructor.
        // Replaying its complete incidence on every receiver deed would turn a
        // local chart change into a global scan. The transition below checks
        // only the affected receiver lineage and new frame.
        if self.used_events.contains(&request.event) {
            return Err(DimensionalReceiverError::RepeatedReceiverEvent(
                request.event,
            ));
        }
        if self
            .last_chronology
            .get(&request.receiver)
            .is_some_and(|previous| request.chronology <= *previous)
        {
            return Err(DimensionalReceiverError::NoncausalReceiverChronology {
                receiver: request.receiver,
                previous: self.last_chronology[&request.receiver],
                received: request.chronology,
            });
        }
        let previous = self.frames.get(&request.receiver).cloned();
        let current = enact_receiver_deed(previous.as_ref(), request)?;
        current.validate(&self.source)?;
        let (receipt, projection_reused) =
            match (previous.as_ref(), self.receipts.get(&request.receiver)) {
                (Some(previous), Some(previous_receipt))
                    if previous.same_projection_as(&current) =>
                {
                    let mut retained = previous_receipt.clone();
                    retained.event = current.event;
                    retained.chronology = current.chronology;
                    retained.active_front = current.active_front.clone();
                    (retained, true)
                }
                _ => (project_receiver_slice(&self.source, &current)?, false),
            };
        let transition = DimensionalReceiverTransition {
            predecessor_event: previous.as_ref().map(|frame| frame.event),
            event: request.event,
            chronology: request.chronology,
            deed: request.deed.clone(),
            from: previous.clone(),
            to: current.clone(),
        };
        self.frames.insert(request.receiver, current.clone());
        self.receipts.insert(request.receiver, receipt.clone());
        self.lineage
            .entry(request.receiver)
            .or_default()
            .push(transition.clone());
        self.used_events.insert(request.event);
        self.last_chronology
            .insert(request.receiver, request.chronology);
        Ok(DimensionalReceiverRadiation {
            schema: "holonic-engine.dimensional-receiver-radiation.v2".to_owned(),
            previous,
            current,
            transition,
            receipt,
            projection_reused,
        })
    }

    pub fn inspect(
        &self,
        receiver: ReceiverId,
    ) -> Result<DimensionalSliceReceipt, DimensionalReceiverError> {
        let frame = self
            .frames
            .get(&receiver)
            .ok_or(DimensionalReceiverError::ReceiverNotFounded(receiver))?;
        let receipt = self
            .receipts
            .get(&receiver)
            .ok_or(DimensionalReceiverError::MalformedAtlas)?;
        debug_assert_eq!(receipt.receiver, frame.receiver);
        Ok(receipt.clone())
    }

    pub fn validate(&self) -> Result<(), DimensionalReceiverError> {
        if self.schema != "holonic-engine.dimensional-receiver-atlas.v2" {
            return Err(DimensionalReceiverError::MalformedAtlas);
        }
        self.source.validate()?;
        let mut expected_events = BTreeSet::new();
        let mut expected_chronology = BTreeMap::new();
        if self.frames.keys().copied().collect::<BTreeSet<_>>()
            != self.lineage.keys().copied().collect::<BTreeSet<_>>()
            || self.frames.keys().copied().collect::<BTreeSet<_>>()
                != self.receipts.keys().copied().collect::<BTreeSet<_>>()
        {
            return Err(DimensionalReceiverError::MalformedAtlas);
        }
        for (receiver, frame) in &self.frames {
            if frame.receiver != *receiver {
                return Err(DimensionalReceiverError::MalformedFrame(*receiver));
            }
            frame.validate(&self.source)?;
            if self.receipts[receiver] != project_receiver_slice(&self.source, frame)? {
                return Err(DimensionalReceiverError::MalformedAtlas);
            }
            let transitions = &self.lineage[receiver];
            if transitions.is_empty() {
                return Err(DimensionalReceiverError::MalformedAtlas);
            }
            for (ordinal, transition) in transitions.iter().enumerate() {
                if transition.event != transition.to.event
                    || transition.chronology != transition.to.chronology
                    || transition.to.receiver != *receiver
                    || !expected_events.insert(transition.event)
                {
                    return Err(DimensionalReceiverError::MalformedAtlas);
                }
                transition.to.validate(&self.source)?;
                if ordinal == 0 {
                    if transition.predecessor_event.is_some()
                        || transition.from.is_some()
                        || !matches!(transition.deed, DimensionalReceiverDeed::Found(_))
                    {
                        return Err(DimensionalReceiverError::MalformedAtlas);
                    }
                } else {
                    let prior = &transitions[ordinal - 1];
                    if transition.predecessor_event != Some(prior.event)
                        || transition.from.as_ref() != Some(&prior.to)
                        || transition.chronology <= prior.chronology
                    {
                        return Err(DimensionalReceiverError::MalformedAtlas);
                    }
                }
            }
            let latest = transitions.last().expect("checked nonempty");
            if &latest.to != frame {
                return Err(DimensionalReceiverError::MalformedAtlas);
            }
            expected_chronology.insert(*receiver, latest.chronology);
        }
        if self.used_events != expected_events || self.last_chronology != expected_chronology {
            return Err(DimensionalReceiverError::MalformedAtlas);
        }
        Ok(())
    }
}

fn enact_receiver_deed(
    previous: Option<&DimensionalReceiverFrame>,
    request: &DimensionalReceiverRequest,
) -> Result<DimensionalReceiverFrame, DimensionalReceiverError> {
    match (&request.deed, previous) {
        (DimensionalReceiverDeed::Found(founding), None) => Ok(DimensionalReceiverFrame {
            receiver: request.receiver,
            event: request.event,
            chronology: request.chronology,
            horizontal: founding.horizontal.clone(),
            vertical: founding.vertical.clone(),
            depth: founding.depth.clone(),
            horizontal_center: founding.horizontal_center.clone(),
            vertical_center: founding.vertical_center.clone(),
            horizontal_span: founding.horizontal_span.clone(),
            vertical_span: founding.vertical_span.clone(),
            constraints: founding.constraints.clone(),
            causal_horizon: founding.causal_horizon.clone(),
            active_front: founding.active_front.clone(),
        }),
        (DimensionalReceiverDeed::Found(_), Some(_)) => Err(
            DimensionalReceiverError::ReceiverAlreadyFounded(request.receiver),
        ),
        (_, None) => Err(DimensionalReceiverError::ReceiverNotFounded(
            request.receiver,
        )),
        (deed, Some(previous)) => {
            let mut current = previous.clone();
            current.event = request.event;
            current.chronology = request.chronology;
            match deed {
                DimensionalReceiverDeed::Reframe(specification) => {
                    current.horizontal = specification.horizontal.clone();
                    current.vertical = specification.vertical.clone();
                    current.depth = specification.depth.clone();
                    current.horizontal_center = specification.horizontal_center.clone();
                    current.vertical_center = specification.vertical_center.clone();
                    current.horizontal_span = specification.horizontal_span.clone();
                    current.vertical_span = specification.vertical_span.clone();
                    current.constraints = specification.constraints.clone();
                    current.causal_horizon = specification.causal_horizon.clone();
                    current.active_front = specification.active_front.clone();
                }
                DimensionalReceiverDeed::Rebase {
                    horizontal,
                    vertical,
                    depth,
                } => {
                    current.horizontal = horizontal.clone();
                    current.vertical = vertical.clone();
                    current.depth = depth.clone();
                }
                DimensionalReceiverDeed::Turn {
                    first,
                    second,
                    ratio,
                } => {
                    if first == second {
                        return Err(DimensionalReceiverError::DegenerateTurnPlane(*first));
                    }
                    current.horizontal = current.horizontal.turned(*first, *second, ratio);
                    current.vertical = current.vertical.turned(*first, *second, ratio);
                    current.depth = current
                        .depth
                        .as_ref()
                        .map(|depth| depth.turned(*first, *second, ratio));
                    for constraint in &mut current.constraints {
                        constraint.covector = constraint.covector.turned(*first, *second, ratio);
                    }
                }
                DimensionalReceiverDeed::Translate {
                    horizontal,
                    vertical,
                } => {
                    current.horizontal_center += horizontal;
                    current.vertical_center += vertical;
                }
                DimensionalReceiverDeed::Dilate {
                    horizontal,
                    vertical,
                } => {
                    if !horizontal.is_positive() || !vertical.is_positive() {
                        return Err(DimensionalReceiverError::NonpositiveDilation);
                    }
                    current.horizontal_span *= horizontal;
                    current.vertical_span *= vertical;
                }
                DimensionalReceiverDeed::ReplaceConstraints(constraints) => {
                    current.constraints.clone_from(constraints);
                }
                DimensionalReceiverDeed::ReplaceCausalHorizon(horizon) => {
                    current.causal_horizon.clone_from(horizon);
                    current.active_front = None;
                }
                DimensionalReceiverDeed::ReceiveCausalFront {
                    causal_horizon,
                    front,
                } => {
                    current.causal_horizon.clone_from(causal_horizon);
                    current.active_front = Some(front.clone());
                }
                DimensionalReceiverDeed::Retain => {}
                DimensionalReceiverDeed::Found(_) => unreachable!(),
            }
            Ok(current)
        }
    }
}

fn project_receiver_slice(
    source: &ExactDimensionalSource,
    frame: &DimensionalReceiverFrame,
) -> Result<DimensionalSliceReceipt, DimensionalReceiverError> {
    // The source passed here is the atlas's already-validated immutable body.
    // Projection materializes receiver testimony but does not revalidate or
    // mutate the complete causal incidence.
    frame.validate(source)?;
    let mut germs = BTreeMap::new();
    let mut buckets = BTreeMap::<(Rat, Rat), Vec<CoordinateGermId>>::new();
    let mut local_dimension_population = BTreeMap::<u32, BigUint>::new();
    let mut visible_germs = BigUint::zero();
    let mut outside_germs = BigUint::zero();
    let mut unresolved_germs = BigUint::zero();
    let mut future_germs = BigUint::zero();
    let received = |events: &BTreeSet<EventId>| {
        frame
            .causal_horizon
            .as_ref()
            .is_none_or(|horizon| events.is_subset(horizon))
    };

    for germ in source.germs.values() {
        let local_dimension = source.germ_local_dimension(germ.id)?;
        let germ_received = received(&germ.source_events);
        if germ_received {
            *local_dimension_population
                .entry(local_dimension)
                .or_default() += BigUint::one();
        }
        let disposition = if germ_received {
            project_germ(frame, germ)
        } else {
            DimensionalGermDisposition::OutsideCausalHorizon
        };
        match &disposition {
            DimensionalGermDisposition::Visible {
                normalized_horizontal,
                normalized_vertical,
                ..
            } => {
                visible_germs += BigUint::one();
                buckets
                    .entry((normalized_horizontal.clone(), normalized_vertical.clone()))
                    .or_default()
                    .push(germ.id);
            }
            DimensionalGermDisposition::Unresolved { .. } => {
                unresolved_germs += BigUint::one();
            }
            DimensionalGermDisposition::OutsideCausalHorizon => {
                future_germs += BigUint::one();
            }
            DimensionalGermDisposition::OutsideAperture { .. }
            | DimensionalGermDisposition::OutsideSlice { .. } => {
                outside_germs += BigUint::one();
            }
        }
        germs.insert(
            germ.id,
            DimensionalGermReceipt {
                germ: germ.id,
                source_cell: germ.source_cell,
                source_grade: source.incidence.cell(germ.source_cell)?.grade,
                source_events: germ.source_events.clone(),
                local_dimension,
                disposition,
            },
        );
    }

    let projection_buckets = buckets
        .into_iter()
        .map(|((normalized_horizontal, normalized_vertical), members)| {
            DimensionalProjectionBucket {
                normalized_horizontal,
                normalized_vertical,
                members,
            }
        })
        .collect::<Vec<_>>();
    let collapsed_buckets = BigUint::from(
        projection_buckets
            .iter()
            .filter(|bucket| bucket.members.len() > 1)
            .count(),
    );
    let projection_envelope = exact_projection_envelope(&projection_buckets);
    let carriers = source
        .carriers
        .iter()
        .map(|(id, carrier)| {
            let from = &germs[&carrier.from].disposition;
            let to = &germs[&carrier.to].disposition;
            let disposition = if !received(&carrier.source_events) {
                DimensionalCarrierDisposition::OutsideCausalHorizon
            } else {
                match (from, to) {
                    (
                        DimensionalGermDisposition::Visible { .. },
                        DimensionalGermDisposition::Visible { .. },
                    ) => DimensionalCarrierDisposition::Visible,
                    (DimensionalGermDisposition::OutsideCausalHorizon, _)
                    | (_, DimensionalGermDisposition::OutsideCausalHorizon) => {
                        DimensionalCarrierDisposition::OutsideCausalHorizon
                    }
                    (DimensionalGermDisposition::Unresolved { .. }, _)
                    | (_, DimensionalGermDisposition::Unresolved { .. }) => {
                        DimensionalCarrierDisposition::EndpointUnresolved
                    }
                    _ => DimensionalCarrierDisposition::EndpointOutside,
                }
            };
            (
                *id,
                DimensionalCarrierReceipt {
                    carrier: *id,
                    from: carrier.from,
                    to: carrier.to,
                    disposition,
                },
            )
        })
        .collect();
    let received_cells = source
        .incidence
        .cells()
        .values()
        .filter(|cell| received(&cell.source_events))
        .collect::<Vec<_>>();
    let mut received_source_f_vector = BTreeMap::new();
    for cell in &received_cells {
        *received_source_f_vector.entry(cell.grade).or_default() += 1;
    }
    let received_source_dimension = received_cells.iter().map(|cell| cell.grade).max();
    let received_coordinate_axes = source
        .axes
        .values()
        .filter(|axis| received(&axis.source_events))
        .count();
    let received_maximum_local_dimension = local_dimension_population
        .keys()
        .next_back()
        .copied()
        .unwrap_or(0);
    let received_source_events = frame
        .causal_horizon
        .as_ref()
        .map_or(source.source_events.len(), |horizon| horizon.len());

    Ok(DimensionalSliceReceipt {
        schema: "holonic-engine.dimensional-slice-receipt.v2".to_owned(),
        receiver: frame.receiver,
        event: frame.event,
        chronology: frame.chronology,
        source_cells: source.incidence.cells().len(),
        source_dimension: source.incidence.dimension(),
        source_f_vector: source.incidence.f_vector(),
        coordinate_axes: source.axes.len(),
        maximum_local_dimension: source.maximum_local_dimension()?,
        received_source_events,
        received_source_cells: received_cells.len(),
        received_source_dimension,
        received_source_f_vector,
        received_coordinate_axes,
        received_maximum_local_dimension,
        active_front: frame.active_front.clone(),
        local_dimension_population,
        germs,
        projection_buckets,
        projection_envelope,
        carriers,
        visible_germs,
        outside_germs,
        unresolved_germs,
        future_germs,
        collapsed_buckets,
        projection_cells: 0,
    })
}

fn exact_projection_envelope(
    buckets: &[DimensionalProjectionBucket],
) -> Vec<DimensionalProjectionEnvelopeCorner> {
    if buckets.len() <= 1 {
        return buckets
            .iter()
            .map(|bucket| DimensionalProjectionEnvelopeCorner {
                normalized_horizontal: bucket.normalized_horizontal.clone(),
                normalized_vertical: bucket.normalized_vertical.clone(),
                members: bucket.members.clone(),
            })
            .collect();
    }
    let mut points = buckets.iter().collect::<Vec<_>>();
    points.sort_by(|left, right| {
        left.normalized_horizontal
            .cmp(&right.normalized_horizontal)
            .then_with(|| left.normalized_vertical.cmp(&right.normalized_vertical))
    });
    let mut lower = Vec::<&DimensionalProjectionBucket>::new();
    for point in &points {
        while lower.len() >= 2
            && projection_hand(lower[lower.len() - 2], lower[lower.len() - 1], point) <= Rat::zero()
        {
            lower.pop();
        }
        lower.push(point);
    }
    let mut upper = Vec::<&DimensionalProjectionBucket>::new();
    for point in points.iter().rev() {
        while upper.len() >= 2
            && projection_hand(upper[upper.len() - 2], upper[upper.len() - 1], point) <= Rat::zero()
        {
            upper.pop();
        }
        upper.push(point);
    }
    lower.pop();
    upper.pop();
    lower
        .into_iter()
        .chain(upper)
        .map(|bucket| DimensionalProjectionEnvelopeCorner {
            normalized_horizontal: bucket.normalized_horizontal.clone(),
            normalized_vertical: bucket.normalized_vertical.clone(),
            members: bucket.members.clone(),
        })
        .collect()
}

fn projection_hand(
    first: &DimensionalProjectionBucket,
    second: &DimensionalProjectionBucket,
    third: &DimensionalProjectionBucket,
) -> Rat {
    (&second.normalized_horizontal - &first.normalized_horizontal)
        * (&third.normalized_vertical - &first.normalized_vertical)
        - (&second.normalized_vertical - &first.normalized_vertical)
            * (&third.normalized_horizontal - &first.normalized_horizontal)
}

fn project_germ(
    frame: &DimensionalReceiverFrame,
    germ: &ExactCoordinateGerm,
) -> DimensionalGermDisposition {
    let mut missing = BTreeSet::new();
    let horizontal = match frame.horizontal.evaluate(germ) {
        Ok(value) => Some(value),
        Err(axes) => {
            missing.extend(axes);
            None
        }
    };
    let vertical = match frame.vertical.evaluate(germ) {
        Ok(value) => Some(value),
        Err(axes) => {
            missing.extend(axes);
            None
        }
    };
    let depth = match &frame.depth {
        Some(covector) => match covector.evaluate(germ) {
            Ok(value) => Some(Some(value)),
            Err(axes) => {
                missing.extend(axes);
                None
            }
        },
        None => Some(None),
    };
    for (ordinal, constraint) in frame.constraints.iter().enumerate() {
        match constraint.covector.evaluate(germ) {
            Ok(value) => {
                let departure = value - &constraint.center;
                if departure.abs() > constraint.radius {
                    return DimensionalGermDisposition::OutsideSlice {
                        constraint: ordinal,
                        departure,
                        radius: constraint.radius.clone(),
                    };
                }
            }
            Err(axes) => {
                missing.extend(axes);
            }
        }
    }
    if !missing.is_empty() {
        return DimensionalGermDisposition::Unresolved {
            missing_axes: missing,
        };
    }
    let horizontal = horizontal.expect("all missing axes were handled");
    let vertical = vertical.expect("all missing axes were handled");
    let normalized_horizontal = (&horizontal - &frame.horizontal_center) / &frame.horizontal_span;
    let normalized_vertical = (&vertical - &frame.vertical_center) / &frame.vertical_span;
    if normalized_horizontal.abs() > Rat::one() || normalized_vertical.abs() > Rat::one() {
        return DimensionalGermDisposition::OutsideAperture {
            normalized_horizontal,
            normalized_vertical,
        };
    }
    DimensionalGermDisposition::Visible {
        horizontal,
        vertical,
        normalized_horizontal,
        normalized_vertical,
        depth: depth.expect("all missing axes were handled"),
    }
}

fn covectors_independent(left: &ExactSliceCovector, right: &ExactSliceCovector) -> bool {
    let axes = left
        .terms
        .keys()
        .chain(right.terms.keys())
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    for (ordinal, first) in axes.iter().enumerate() {
        for second in axes.iter().skip(ordinal + 1) {
            let left_first = left.terms.get(first).cloned().unwrap_or_else(Rat::zero);
            let left_second = left.terms.get(second).cloned().unwrap_or_else(Rat::zero);
            let right_first = right.terms.get(first).cloned().unwrap_or_else(Rat::zero);
            let right_second = right.terms.get(second).cloned().unwrap_or_else(Rat::zero);
            if left_first * right_second - left_second * right_first != Rat::zero() {
                return true;
            }
        }
    }
    false
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum DimensionalReceiverError {
    #[error(transparent)]
    Causal(#[from] CausalAlgebraicError),
    #[error("dimensional source standing is malformed")]
    MalformedSource,
    #[error("dimensional receiver atlas is malformed")]
    MalformedAtlas,
    #[error("axis {0:?} is malformed")]
    MalformedAxis(DimensionalAxisId),
    #[error("axis {0:?} occurs more than once")]
    DuplicateAxis(DimensionalAxisId),
    #[error("axis {0:?} is absent")]
    MissingAxis(DimensionalAxisId),
    #[error("complex coordinate pair {real:?}/{imaginary:?} is malformed")]
    MalformedComplexPair {
        real: DimensionalAxisId,
        imaginary: DimensionalAxisId,
    },
    #[error("germ {germ:?} carries only part of complex pair {real:?}/{imaginary:?}")]
    IncompleteComplexPair {
        germ: CoordinateGermId,
        real: DimensionalAxisId,
        imaginary: DimensionalAxisId,
    },
    #[error("germ {germ:?} does not lie on unit conic {real:?}²+{imaginary:?}²=1")]
    ComplexPairOffConic {
        germ: CoordinateGermId,
        real: DimensionalAxisId,
        imaginary: DimensionalAxisId,
    },
    #[error("coordinate germ {0:?} is malformed")]
    MalformedGerm(CoordinateGermId),
    #[error("coordinate germ {0:?} occurs more than once")]
    DuplicateGerm(CoordinateGermId),
    #[error("coordinate germ {0:?} is absent")]
    MissingGerm(CoordinateGermId),
    #[error("coordinate carrier {0:?} is malformed")]
    MalformedCarrier(CoordinateCarrierId),
    #[error("coordinate carrier {0:?} occurs more than once")]
    DuplicateCarrier(CoordinateCarrierId),
    #[error("boundary coordinate carrier {0:?} does not match source incidence")]
    MalformedBoundaryCarrier(CoordinateCarrierId),
    #[error("a slice covector cannot be zero")]
    ZeroCovector,
    #[error("slice covector stores a zero term on axis {0:?}")]
    StoredZeroCovectorTerm(DimensionalAxisId),
    #[error("horizontal and vertical receiver covectors are dependent")]
    DependentPresentationCovectors,
    #[error("receiver aperture spans must be positive")]
    NonpositiveAperture,
    #[error("slice constraint radius cannot be negative")]
    NegativeSliceRadius,
    #[error("receiver causal horizon contains an event absent from the dimensional source")]
    UnknownSourceEventInHorizon,
    #[error("the received dimensional causal front is malformed")]
    MalformedCausalFront,
    #[error("the received dimensional causal front lies outside its causal horizon")]
    CausalFrontOutsideHorizon,
    #[error("receiver {0:?} is already founded")]
    ReceiverAlreadyFounded(ReceiverId),
    #[error("receiver {0:?} is not founded")]
    ReceiverNotFounded(ReceiverId),
    #[error("receiver frame {0:?} is malformed")]
    MalformedFrame(ReceiverId),
    #[error("receiver event {0:?} was already enacted")]
    RepeatedReceiverEvent(EventId),
    #[error("receiver {receiver:?} chronology {received} does not follow {previous}")]
    NoncausalReceiverChronology {
        receiver: ReceiverId,
        previous: u64,
        received: u64,
    },
    #[error("receiver turn plane repeats axis {0:?}")]
    DegenerateTurnPlane(DimensionalAxisId),
    #[error("receiver dilation factors must be positive")]
    NonpositiveDilation,
    #[error("an exact dimensional carrier overflowed")]
    CarrierOverflow,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CausalChain;

    fn event(value: u64) -> BTreeSet<EventId> {
        BTreeSet::from([EventId(value)])
    }

    fn source() -> ExactDimensionalSource {
        let mut incidence = GradedCausalComplex::default();
        let left = incidence
            .found_cell("left", event(1), 0, CausalChain::default())
            .unwrap();
        let right = incidence
            .found_cell("right", event(2), 0, CausalChain::default())
            .unwrap();
        let mut boundary = CausalChain::default();
        boundary.add_term(left, ComparativeMultiplicity::negative(1_u8));
        boundary.add_term(right, ComparativeMultiplicity::positive(1_u8));
        let edge = incidence.found_cell("edge", event(3), 1, boundary).unwrap();
        let real = DimensionalAxisId(1);
        let imaginary = DimensionalAxisId(2);
        let depth = DimensionalAxisId(3);
        ExactDimensionalSource::new(
            incidence,
            vec![
                DimensionalAxis::new(real, "real", event(1)).unwrap(),
                DimensionalAxis::new(imaginary, "imaginary", event(1)).unwrap(),
                DimensionalAxis::new(depth, "depth", event(1)).unwrap(),
            ],
            vec![ExactComplexAxisPair {
                real,
                imaginary,
                unit_conic: true,
            }],
            vec![
                ExactCoordinateGerm {
                    id: CoordinateGermId(1),
                    name: "left occurrence".to_owned(),
                    source_cell: left,
                    source_events: event(1),
                    coordinates: BTreeMap::from([
                        (real, Rat::one()),
                        (imaginary, Rat::zero()),
                        (depth, Rat::zero()),
                    ]),
                },
                ExactCoordinateGerm {
                    id: CoordinateGermId(2),
                    name: "right occurrence".to_owned(),
                    source_cell: right,
                    source_events: event(2),
                    coordinates: BTreeMap::from([
                        (real, Rat::one()),
                        (imaginary, Rat::zero()),
                        (depth, Rat::one()),
                    ]),
                },
                ExactCoordinateGerm {
                    id: CoordinateGermId(3),
                    name: "edge occurrence".to_owned(),
                    source_cell: edge,
                    source_events: event(3),
                    coordinates: BTreeMap::from([(real, Rat::zero()), (imaginary, Rat::one())]),
                },
            ],
            vec![
                ExactCoordinateCarrier {
                    id: CoordinateCarrierId(1),
                    name: "edge to left".to_owned(),
                    from: CoordinateGermId(3),
                    to: CoordinateGermId(1),
                    source_events: event(3),
                    kind: CoordinateCarrierKind::Boundary {
                        higher: edge,
                        lower: left,
                        coefficient: ComparativeMultiplicity::negative(1_u8),
                    },
                },
                ExactCoordinateCarrier {
                    id: CoordinateCarrierId(2),
                    name: "edge to right".to_owned(),
                    from: CoordinateGermId(3),
                    to: CoordinateGermId(2),
                    source_events: event(3),
                    kind: CoordinateCarrierKind::Boundary {
                        higher: edge,
                        lower: right,
                        coefficient: ComparativeMultiplicity::positive(1_u8),
                    },
                },
            ],
        )
        .unwrap()
    }

    #[test]
    fn complex_pair_is_one_dimension_and_its_square_turn_is_negative_identity() {
        let source = source();
        assert_eq!(source.germ_local_dimension(CoordinateGermId(3)).unwrap(), 1);
        assert_eq!(source.germ_local_dimension(CoordinateGermId(1)).unwrap(), 2);
        let pair = &source.complex_pairs()[0];
        assert_eq!(
            pair.second_quarter_turn(&Rat::from_integer(3.into()), &Rat::from_integer(5.into())),
            (
                Rat::from_integer((-3).into()),
                Rat::from_integer((-5).into())
            )
        );
    }

    #[test]
    fn projection_collision_retains_both_source_fibers_and_mints_no_cell() {
        let source = source();
        let real = DimensionalAxisId(1);
        let imaginary = DimensionalAxisId(2);
        let mut atlas = DimensionalReceiverAtlas::new(source).unwrap();
        let radiation = atlas
            .receive(&DimensionalReceiverRequest {
                event: EventId(20),
                chronology: 1,
                receiver: ReceiverId(9),
                deed: DimensionalReceiverDeed::Found(DimensionalReceiverFounding {
                    horizontal: ExactSliceCovector::axis(real),
                    vertical: ExactSliceCovector::axis(imaginary),
                    depth: None,
                    horizontal_center: Rat::zero(),
                    vertical_center: Rat::zero(),
                    horizontal_span: Rat::one(),
                    vertical_span: Rat::one(),
                    constraints: Vec::new(),
                    causal_horizon: None,
                    active_front: None,
                }),
            })
            .unwrap();
        assert_eq!(radiation.receipt.projection_cells, 0);
        assert_eq!(radiation.receipt.visible_germs, BigUint::from(3_u8));
        assert_eq!(radiation.receipt.collapsed_buckets, BigUint::from(1_u8));
        assert_eq!(radiation.receipt.projection_envelope.len(), 2);
        let collision = radiation
            .receipt
            .projection_buckets
            .iter()
            .find(|bucket| bucket.members.len() == 2)
            .unwrap();
        assert_eq!(
            collision.members,
            vec![CoordinateGermId(1), CoordinateGermId(2)]
        );
    }

    #[test]
    fn unavailable_direction_remains_an_unresolved_fiber() {
        let source = source();
        let mut atlas = DimensionalReceiverAtlas::new(source).unwrap();
        let receipt = atlas
            .receive(&DimensionalReceiverRequest {
                event: EventId(21),
                chronology: 1,
                receiver: ReceiverId(10),
                deed: DimensionalReceiverDeed::Found(DimensionalReceiverFounding {
                    horizontal: ExactSliceCovector::axis(DimensionalAxisId(1)),
                    vertical: ExactSliceCovector::axis(DimensionalAxisId(3)),
                    depth: None,
                    horizontal_center: Rat::zero(),
                    vertical_center: Rat::zero(),
                    horizontal_span: Rat::one(),
                    vertical_span: Rat::one(),
                    constraints: Vec::new(),
                    causal_horizon: None,
                    active_front: None,
                }),
            })
            .unwrap()
            .receipt;
        assert!(matches!(
            receipt.germs[&CoordinateGermId(3)].disposition,
            DimensionalGermDisposition::Unresolved { .. }
        ));
        assert_eq!(receipt.unresolved_germs, BigUint::from(1_u8));
    }

    #[test]
    fn cayley_quarter_turn_changes_the_receiver_and_preserves_exact_rank() {
        let source = source();
        let mut atlas = DimensionalReceiverAtlas::new(source).unwrap();
        atlas
            .receive(&DimensionalReceiverRequest {
                event: EventId(22),
                chronology: 1,
                receiver: ReceiverId(11),
                deed: DimensionalReceiverDeed::Found(DimensionalReceiverFounding {
                    horizontal: ExactSliceCovector::axis(DimensionalAxisId(1)),
                    vertical: ExactSliceCovector::axis(DimensionalAxisId(3)),
                    depth: None,
                    horizontal_center: Rat::zero(),
                    vertical_center: Rat::zero(),
                    horizontal_span: Rat::one(),
                    vertical_span: Rat::one(),
                    constraints: Vec::new(),
                    causal_horizon: None,
                    active_front: None,
                }),
            })
            .unwrap();
        let turned = atlas
            .receive(&DimensionalReceiverRequest {
                event: EventId(23),
                chronology: 2,
                receiver: ReceiverId(11),
                deed: DimensionalReceiverDeed::Turn {
                    first: DimensionalAxisId(1),
                    second: DimensionalAxisId(2),
                    ratio: Rat::one(),
                },
            })
            .unwrap();
        assert_eq!(
            turned.current.horizontal,
            ExactSliceCovector::axis(DimensionalAxisId(2))
        );
        assert_eq!(turned.receipt.maximum_local_dimension, 2);
        assert_eq!(atlas.lineage(ReceiverId(11)).unwrap().len(), 2);
        let remounted = atlas.clone();
        remounted.validate().unwrap();
        assert_eq!(remounted, atlas);
    }

    #[test]
    fn causal_horizon_reveals_only_already_caused_incidence_and_germs() {
        let source = source();
        let mut atlas = DimensionalReceiverAtlas::new(source).unwrap();
        let first = atlas
            .receive(&DimensionalReceiverRequest {
                event: EventId(24),
                chronology: 1,
                receiver: ReceiverId(12),
                deed: DimensionalReceiverDeed::Found(DimensionalReceiverFounding {
                    horizontal: ExactSliceCovector::axis(DimensionalAxisId(1)),
                    vertical: ExactSliceCovector::axis(DimensionalAxisId(2)),
                    depth: None,
                    horizontal_center: Rat::zero(),
                    vertical_center: Rat::zero(),
                    horizontal_span: Rat::one(),
                    vertical_span: Rat::one(),
                    constraints: Vec::new(),
                    causal_horizon: Some(event(1)),
                    active_front: None,
                }),
            })
            .unwrap()
            .receipt;
        assert_eq!(first.received_source_events, 1);
        assert_eq!(first.received_source_cells, 1);
        assert_eq!(first.received_source_f_vector, BTreeMap::from([(0, 1)]));
        assert_eq!(first.visible_germs, BigUint::one());
        assert_eq!(first.future_germs, BigUint::from(2_u8));
        assert!(matches!(
            first.germs[&CoordinateGermId(2)].disposition,
            DimensionalGermDisposition::OutsideCausalHorizon
        ));
        assert!(first.carriers.values().all(|carrier| matches!(
            carrier.disposition,
            DimensionalCarrierDisposition::OutsideCausalHorizon
        )));

        let completed = atlas
            .receive(&DimensionalReceiverRequest {
                event: EventId(25),
                chronology: 2,
                receiver: ReceiverId(12),
                deed: DimensionalReceiverDeed::ReplaceCausalHorizon(None),
            })
            .unwrap()
            .receipt;
        assert_eq!(completed.received_source_cells, completed.source_cells);
        assert_eq!(completed.future_germs, BigUint::zero());
        assert_eq!(completed.visible_germs, BigUint::from(3_u8));

        let moving = atlas
            .receive(&DimensionalReceiverRequest {
                event: EventId(26),
                chronology: 3,
                receiver: ReceiverId(12),
                deed: DimensionalReceiverDeed::ReceiveCausalFront {
                    causal_horizon: None,
                    front: DimensionalCausalFront {
                        ordinal: 1,
                        source_event: EventId(3),
                        active_germs: BTreeSet::from([CoordinateGermId(3)]),
                        active_carriers: BTreeSet::from([CoordinateCarrierId(1)]),
                        changed_axes: BTreeSet::from([DimensionalAxisId(1)]),
                    },
                },
            })
            .unwrap();
        assert!(moving.projection_reused);
        assert_eq!(
            moving.receipt.projection_buckets,
            completed.projection_buckets
        );
        assert_eq!(moving.receipt.active_front.unwrap().ordinal, 1);
    }
}
