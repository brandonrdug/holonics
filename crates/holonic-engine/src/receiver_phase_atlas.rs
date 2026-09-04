//! Receiver-local phase germs induced from finite image testimony.
//!
//! A sensor address is only a witness.  Persistent extrema of exact first and
//! second phase differences cause analytical germs whose quadratic level sets
//! are native conics in the receiver chart.  Mutually admitted germs carry an
//! exact connection correction; a closed three-germ incidence reports its
//! path-ordered holonomy.  Triangular incidence therefore does not pretend to
//! be curvature by itself.

use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroUsize;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::{Rat, ReceiverId};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    ConicClass, ConicError, EventId, EventSuccessor, ExactEventLaw, ExactRgb, HomogeneousConic,
    ImageCarrierError, ImageExtent, ImageSectionId, LogicalResourceReceipt, RayFamily,
    ReceiverError,
};

/// One receiver sample: the exact readings of that receiver's declared channel population, in
/// declaration order.
///
/// This organ authors no channel count. Until 2026-08-09 it carried `const CHANNEL_COUNT: usize =
/// 3` and eight fixed-size-3 array types beneath it, which made *one receiver's* channel population
/// — RGB — a property of the law that reads receivers. `docs/canon/THE_AUTHORED_LEVEL.md` §1: *"A level
/// is either read off the material or declared by the caller. It is never authored inside the
/// organ."* [`ExactRgb`] is now one instance of this carrier and not the definition of it; a
/// single-channel and a five-channel receiver are declared the same way and cost nothing extra.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverChannelSample(pub Vec<u8>);

impl ReceiverChannelSample {
    /// How many channels this sample carries. A **reading** of the sample, never a declaration
    /// about the receiver; [`ReceiverPhaseSectionOccurrence::channels`] is the declaration and
    /// [`ReceiverPhaseAtlasError::ChannelPopulationDisagreement`] is what refuses a sample that
    /// does not meet it.
    pub fn population(&self) -> usize {
        self.0.len()
    }
}

impl From<ExactRgb> for ReceiverChannelSample {
    fn from(value: ExactRgb) -> Self {
        Self(value.channels().to_vec())
    }
}

/// How many channels a `u8` coordinate can address. Every downstream reference to a channel is a
/// `u8` — `dominant_coordinate` on the germ and its signature, and the coordinate on
/// `holonic_complex::InternalAnalyticSection` — so this is the carrier's capacity read off
/// [`u8::MAX`], not a population ceiling this organ picked. It is the one place the channel
/// population is bounded and it names what would lift it: a wider coordinate carrier.
const COORDINATE_CARRIER_POPULATION: usize = u8::MAX as usize + 1;

/// The channel population an [`ExactRgb`] receiver declares, read off that carrier's own arity
/// rather than authored here. This is the exact boundary at which channel generality stops: every
/// path above it is population-general, and [`crate::ExactRaster`] is dimension three by type.
fn rgb_channel_population() -> NonZeroUsize {
    NonZeroUsize::new(ExactRgb::default().channels().len()).expect("an RGB sample has channels")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverPhaseSectionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverPhaseGermId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverPhaseConnectionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverPhaseCycleId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverPhaseAddress {
    pub column: u32,
    pub row: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPhaseSectionOccurrence {
    pub source_image: Option<ImageSectionId>,
    pub source_lineage: u64,
    pub receiver: ReceiverId,
    pub rays: RayFamily,
    pub extent: ImageExtent,
    /// This receiver's declared channel population. Every present sample must carry exactly this
    /// many channels; one that does not is refused by name rather than truncated or padded.
    pub channels: NonZeroUsize,
    /// `None` is absent testimony.  It cannot contribute a jet, a maximum, or
    /// a germ.
    pub samples: Vec<Option<ReceiverChannelSample>>,
}

impl ReceiverPhaseSectionOccurrence {
    pub fn whole(
        source_image: Option<ImageSectionId>,
        source_lineage: u64,
        receiver: ReceiverId,
        rays: RayFamily,
        raster: &crate::ExactRaster,
    ) -> Self {
        Self::from_rgb(
            source_image,
            source_lineage,
            receiver,
            rays,
            raster.extent,
            raster.samples.iter().copied().map(Some).collect(),
        )
    }

    /// An RGB receiver, whose channel population is read off [`ExactRgb`]'s own arity. This is a
    /// convenience for the one carrier this crate happens to own, not the general form; a receiver
    /// with any other channel population is built by the struct literal.
    pub fn from_rgb(
        source_image: Option<ImageSectionId>,
        source_lineage: u64,
        receiver: ReceiverId,
        rays: RayFamily,
        extent: ImageExtent,
        samples: Vec<Option<ExactRgb>>,
    ) -> Self {
        Self {
            source_image,
            source_lineage,
            receiver,
            rays,
            extent,
            channels: rgb_channel_population(),
            samples: samples
                .into_iter()
                .map(|sample| sample.map(ReceiverChannelSample::from))
                .collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactReceiverPhaseJet {
    /// One entry per channel of the receiver that caused this jet, in that receiver's declaration
    /// order. The extent is the receiver's, never this organ's.
    pub values: Vec<Rat>,
    /// Exact first derivatives in the receiver's two chart coordinates.
    ///
    /// The inner `2` is the **chart** dimension, not the channel population: this atlas reads a
    /// two-coordinate receiver chart (`column`, `row`), and every conic, frame, and holonomy below
    /// is `2 x 2` for the same reason. That is a separate level from the one excised here and it is
    /// named in the module's own boundary rather than hidden in this one.
    pub gradients: Vec<[Rat; 2]>,
    /// Exact symmetric Hessians in the same chart.
    pub hessians: Vec<[[Rat; 2]; 2]>,
}

impl ExactReceiverPhaseJet {
    /// The channel population this jet was caused at, read off the jet rather than declared beside
    /// it. [`validate_standing`] is what refuses a jet whose extent disagrees with the section that
    /// caused it.
    pub fn channel_population(&self) -> usize {
        self.values.len()
    }

    fn is_rectangular(&self) -> bool {
        self.gradients.len() == self.values.len() && self.hessians.len() == self.values.len()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ReceiverConicSpecies {
    Circle,
    Ellipse,
    Parabola,
    Hyperbola,
    IntersectingLinePair,
    ParallelLinePair,
    Degenerate,
}

impl From<ConicClass> for ReceiverConicSpecies {
    fn from(value: ConicClass) -> Self {
        match value {
            ConicClass::CircleInThisChart => Self::Circle,
            ConicClass::EllipseInThisChart => Self::Ellipse,
            ConicClass::ParabolaInThisChart => Self::Parabola,
            ConicClass::HyperbolaInThisChart => Self::Hyperbola,
            ConicClass::IntersectingLinePair => Self::IntersectingLinePair,
            ConicClass::ParallelLinePair => Self::ParallelLinePair,
            ConicClass::Degenerate => Self::Degenerate,
        }
    }
}

/// Which way an exact quantity passes, named rather than signed.
///
/// `CLAUDE.md` §2b: *"What the signed floor signs is the PASSAGE, never the state."* These were
/// three bare `i8`s until 2026-08-08. A bare `i8` also admits 253 values that name no passage, so a
/// deserialized standing could carry `gradient_signs: [42, -7]` and validate; this enumeration
/// cannot represent one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum PhaseHand {
    /// The quantity passes against the chart's own hand.
    AgainstTheTurn,
    /// The quantity is exactly zero: no passage at all, not a small one.
    AtRest,
    /// The quantity passes with the chart's own hand.
    WithTheTurn,
}

impl PhaseHand {
    /// The hand of an exact rational. Zero is [`PhaseHand::AtRest`] and is decided exactly — there
    /// is no tolerance here and there could not be one.
    pub fn of(value: &Rat) -> Self {
        if value.is_positive() {
            Self::WithTheTurn
        } else if value.is_negative() {
            Self::AgainstTheTurn
        } else {
            Self::AtRest
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ReceiverPhaseGermSignature {
    pub dominant_coordinate: u8,
    pub conic_species: ReceiverConicSpecies,
    pub gradient_hands: [PhaseHand; 2],
    pub hessian_trace_hand: PhaseHand,
    pub hessian_determinant_hand: PhaseHand,
    pub persistence_order: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPhaseGerm {
    pub id: ReceiverPhaseGermId,
    pub section: ReceiverPhaseSectionId,
    pub source_event: EventId,
    pub source_lineage: u64,
    pub receiver: ReceiverId,
    /// The sensor address is retained as testimony, not promoted into a world
    /// vertex.
    pub witness: ReceiverPhaseAddress,
    pub chart_point: [Rat; 2],
    pub jet: ExactReceiverPhaseJet,
    pub exact_energy: BigUint,
    /// Every radius at which this germ remains a local phase-jet maximum.
    pub persistence_radii: Vec<u32>,
    /// The first larger radius at which no visible competitor dominates but
    /// absent testimony prevents certification. This is an open continuation
    /// boundary, not evidence that the germ has already persisted there.
    pub open_radius: Option<u32>,
    pub horizon: u32,
    pub dominant_coordinate: u8,
    pub level_sets: Vec<Option<HomogeneousConic>>,
    pub signature: ReceiverPhaseGermSignature,
}

impl ReceiverPhaseGerm {
    /// Restrict this local analytical section at an exact displacement in its
    /// receiver chart. The result is still an exact phase fiber; packing into
    /// a finite display channel belongs to a later terminal membrane.
    ///
    /// The returned extent is the germ's own channel population, so the return states its shape.
    pub fn evaluate_phase(&self, displacement: &[Rat; 2]) -> Vec<Rat> {
        let [x, y] = displacement;
        let two = rat_i64(2);
        (0..self.jet.channel_population())
            .map(|channel| {
                &self.jet.values[channel]
                    + &self.jet.gradients[channel][0] * x
                    + &self.jet.gradients[channel][1] * y
                    + &self.jet.hessians[channel][0][0] * x * x / &two
                    + &self.jet.hessians[channel][0][1] * x * y
                    + &self.jet.hessians[channel][1][1] * y * y / &two
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPhaseConnection {
    pub id: ReceiverPhaseConnectionId,
    pub section: ReceiverPhaseSectionId,
    pub source_event: EventId,
    pub source: ReceiverPhaseGermId,
    pub target: ReceiverPhaseGermId,
    /// Gradient of the source germ's conic after transport to the target
    /// witness.
    pub predicted_normal: [Rat; 2],
    pub target_normal: [Rat; 2],
    /// `target_frame^-1 * predicted_frame`.
    pub correction: [[Rat; 2]; 2],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPhaseCycle {
    pub id: ReceiverPhaseCycleId,
    pub section: ReceiverPhaseSectionId,
    pub source_event: EventId,
    pub boundary: [ReceiverPhaseGermId; 3],
    pub connections: [ReceiverPhaseConnectionId; 3],
    /// Path-ordered connection product around the oriented triangular
    /// boundary.
    pub holonomy: [[Rat; 2]; 2],
    pub curved: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPhaseSection {
    pub id: ReceiverPhaseSectionId,
    pub source_image: Option<ImageSectionId>,
    pub source_lineage: u64,
    pub event: EventId,
    pub chronology: u64,
    pub receiver: ReceiverId,
    pub rays: RayFamily,
    pub extent: ImageExtent,
    /// The channel population this section was received at. The receipt states its own shape; a
    /// reader never has to know what the organ's default was, because the organ has none.
    pub channels: NonZeroUsize,
    pub visible_samples: u64,
    pub absent_samples: u64,
    pub germs: BTreeSet<ReceiverPhaseGermId>,
    pub connections: BTreeSet<ReceiverPhaseConnectionId>,
    pub cycles: BTreeSet<ReceiverPhaseCycleId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPhaseAtlasStanding {
    pub schema: String,
    pub sections: BTreeMap<ReceiverPhaseSectionId, ReceiverPhaseSection>,
    pub germs: BTreeMap<ReceiverPhaseGermId, ReceiverPhaseGerm>,
    pub connections: BTreeMap<ReceiverPhaseConnectionId, ReceiverPhaseConnection>,
    pub cycles: BTreeMap<ReceiverPhaseCycleId, ReceiverPhaseCycle>,
    /// Every germ that took each passage, **named**, not counted.
    ///
    /// `CLAUDE.md` §2b: *"A count of signs is a state reading. Name the windings instead."* This was
    /// `u64` until 2026-08-08 — a tally standing beside the population it summarised, which nothing
    /// checked and which no reader could resolve back to a germ. The count is now a reading
    /// ([`ReceiverPhaseAtlasStanding::germ_population_count`]) and the addresses are the data, in
    /// the same shape `RayCrossings` uses for its crossing indices.
    pub germ_populations: BTreeMap<ReceiverPhaseGermSignature, BTreeSet<ReceiverPhaseGermId>>,
    pub used_events: BTreeSet<EventId>,
    pub last_chronology: Option<u64>,
    next_section: u64,
    next_germ: u64,
    next_connection: u64,
    next_cycle: u64,
}

impl Default for ReceiverPhaseAtlasStanding {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.receiver-phase-atlas-standing.v1".to_owned(),
            sections: BTreeMap::new(),
            germs: BTreeMap::new(),
            connections: BTreeMap::new(),
            cycles: BTreeMap::new(),
            germ_populations: BTreeMap::new(),
            used_events: BTreeSet::new(),
            last_chronology: None,
            next_section: 1,
            next_germ: 1,
            next_connection: 1,
            next_cycle: 1,
        }
    }
}

impl ReceiverPhaseAtlasStanding {
    /// How many germs took one passage. A **reading** of the addressed population; nothing stores
    /// it, so it cannot drift from the germs it counts.
    pub fn germ_population_count(&self, signature: &ReceiverPhaseGermSignature) -> usize {
        self.germ_populations
            .get(signature)
            .map_or(0, BTreeSet::len)
    }

    /// The signature one germ was admitted under, read from the population map rather than from the
    /// germ's own copy. The two must agree, and [`Self::validate`] is what refuses it when they do
    /// not.
    pub fn passage_of(&self, germ: ReceiverPhaseGermId) -> Option<&ReceiverPhaseGermSignature> {
        self.germ_populations
            .iter()
            .find_map(|(signature, population)| population.contains(&germ).then_some(signature))
    }

    pub fn validate(&self) -> Result<(), ReceiverPhaseAtlasError> {
        validate_standing(self)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPhaseAtlasEvent {
    pub event: EventId,
    pub chronology: u64,
    pub sections: Vec<ReceiverPhaseSectionOccurrence>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverPhaseAtlasRadiation {
    pub schema: String,
    pub event: EventId,
    pub sections: Vec<ReceiverPhaseSectionId>,
    pub caused_germs: u64,
    pub caused_connections: u64,
    pub caused_cycles: u64,
    pub curved_cycles: u64,
}

#[derive(Clone, Debug, Default)]
pub struct ReceiverPhaseAtlasLaw;

impl ReceiverPhaseAtlasLaw {
    pub fn initial_standing(&self) -> ReceiverPhaseAtlasStanding {
        ReceiverPhaseAtlasStanding::default()
    }
}

impl ExactEventLaw for ReceiverPhaseAtlasLaw {
    type Standing = ReceiverPhaseAtlasStanding;
    type Event = ReceiverPhaseAtlasEvent;
    type Radiation = ReceiverPhaseAtlasRadiation;
    type Error = ReceiverPhaseAtlasError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        validate_standing(standing_before)?;
        validate_event(standing_before, event)?;
        let mut standing_after = standing_before.clone();
        let germs_before = standing_after.germs.len();
        let connections_before = standing_after.connections.len();
        let cycles_before = standing_after.cycles.len();
        let mut sections = Vec::with_capacity(event.sections.len());
        for occurrence in &event.sections {
            sections.push(admit_section(&mut standing_after, event, occurrence)?);
        }
        standing_after.used_events.insert(event.event);
        standing_after.last_chronology = Some(event.chronology);
        let caused_germs = usize_to_u64(standing_after.germs.len() - germs_before)?;
        let caused_connections =
            usize_to_u64(standing_after.connections.len() - connections_before)?;
        let caused_cycles = usize_to_u64(standing_after.cycles.len() - cycles_before)?;
        let curved_cycles = standing_after
            .cycles
            .values()
            .filter(|cycle| cycle.source_event == event.event && cycle.curved)
            .count();
        let work = caused_germs
            .checked_add(caused_connections)
            .and_then(|work| work.checked_add(caused_cycles))
            .ok_or(ReceiverPhaseAtlasError::CarrierOverflow)?;
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![ReceiverPhaseAtlasRadiation {
                schema: "holonic-engine.receiver-phase-atlas-radiation.v1".to_owned(),
                event: event.event,
                sections,
                caused_germs,
                caused_connections,
                caused_cycles,
                curved_cycles: usize_to_u64(curved_cycles)?,
            }],
            logical_resources: Some(LogicalResourceReceipt {
                schema: "holonic-engine.logical-resource-receipt.v1".to_owned(),
                work: BigUint::from(work),
                causal_span: BigUint::one(),
                exposed_parallel_width: BigUint::from(event.sections.len()),
                events_by_law: BTreeMap::from([
                    (
                        "cause-receiver-phase-germ".to_owned(),
                        BigUint::from(caused_germs),
                    ),
                    (
                        "form-receiver-phase-connection".to_owned(),
                        BigUint::from(caused_connections),
                    ),
                    (
                        "close-receiver-phase-cycle".to_owned(),
                        BigUint::from(caused_cycles),
                    ),
                ]),
            }),
            physical_resources: None,
        })
    }
}

fn validate_standing(standing: &ReceiverPhaseAtlasStanding) -> Result<(), ReceiverPhaseAtlasError> {
    if standing.schema != "holonic-engine.receiver-phase-atlas-standing.v1"
        || standing.sections.values().any(|section| {
            section
                .germs
                .iter()
                .any(|germ| !standing.germs.contains_key(germ))
                || section
                    .connections
                    .iter()
                    .any(|connection| !standing.connections.contains_key(connection))
                || section
                    .cycles
                    .iter()
                    .any(|cycle| !standing.cycles.contains_key(cycle))
        })
    {
        return Err(ReceiverPhaseAtlasError::MalformedStanding);
    }
    // The passage population is the germ population, seen through the signatures. A count could
    // never be checked against the germs it counted; a set of addresses can, and this refusal is
    // what makes the repair a check rather than a rename.
    let mut addressed = 0_usize;
    for (signature, population) in &standing.germ_populations {
        if population.is_empty() {
            return Err(ReceiverPhaseAtlasError::EmptyGermPassage);
        }
        for germ in population {
            match standing.germs.get(germ) {
                Some(body) if body.signature == *signature => {}
                _ => return Err(ReceiverPhaseAtlasError::GermPassageMismatch(*germ)),
            }
        }
        addressed += population.len();
    }
    if addressed != standing.germs.len() {
        return Err(ReceiverPhaseAtlasError::MalformedStanding);
    }
    // A germ's jet is as wide as the section that caused it, and no wider. Nothing in this organ
    // knows what that width should be, so this is the only place the two can be compared — and a
    // standing that disagrees with itself is refused by name rather than indexed into.
    for germ in standing.germs.values() {
        let section = standing
            .sections
            .get(&germ.section)
            .ok_or(ReceiverPhaseAtlasError::MalformedStanding)?;
        if !germ.jet.is_rectangular()
            || germ.jet.channel_population() != section.channels.get()
            || germ.level_sets.len() != section.channels.get()
            || usize::from(germ.dominant_coordinate) >= section.channels.get()
        {
            return Err(ReceiverPhaseAtlasError::GermChannelPopulationDisagreement {
                germ: germ.id,
                declared: section.channels.get(),
                caused: germ.jet.channel_population(),
            });
        }
    }
    Ok(())
}

fn validate_event(
    standing: &ReceiverPhaseAtlasStanding,
    event: &ReceiverPhaseAtlasEvent,
) -> Result<(), ReceiverPhaseAtlasError> {
    if event.sections.is_empty() {
        return Err(ReceiverPhaseAtlasError::EmptyEvent);
    }
    if standing.used_events.contains(&event.event) {
        return Err(ReceiverPhaseAtlasError::RepeatedEvent(event.event));
    }
    if let Some(previous) = standing.last_chronology
        && event.chronology <= previous
    {
        return Err(ReceiverPhaseAtlasError::NoncausalChronology {
            previous,
            supplied: event.chronology,
        });
    }
    let mut receivers = BTreeSet::new();
    for section in &event.sections {
        section.rays.validate()?;
        if section.extent.width == 0
            || section.extent.height == 0
            || section.samples.len() != section.extent.sample_count()?
        {
            return Err(ReceiverPhaseAtlasError::MalformedSection);
        }
        if !receivers.insert(section.receiver) {
            return Err(ReceiverPhaseAtlasError::DuplicateReceiver(section.receiver));
        }
        // A channel is addressed downstream by a `u8` — [`ReceiverPhaseGerm::dominant_coordinate`],
        // [`ReceiverPhaseGermSignature::dominant_coordinate`], and
        // `holonic_complex::InternalAnalyticSection::coordinate`, whose `u8::try_from` is an
        // `expect`. Under the excised `CHANNEL_COUNT = 3` that carrier could never be exceeded, so
        // generalising the population made a previously unreachable panic reachable. This refuses
        // it at the mouth instead. The bound is the **carrier's**, read off `u8::MAX`; it is not a
        // level this organ chose, and lifting it means widening the coordinate carrier.
        if section.channels.get() > COORDINATE_CARRIER_POPULATION {
            return Err(
                ReceiverPhaseAtlasError::ChannelPopulationExceedsCoordinateCarrier {
                    receiver: section.receiver,
                    declared: section.channels.get(),
                    carrier: COORDINATE_CARRIER_POPULATION,
                },
            );
        }
        // The receiver declared its channel population; the material must meet it exactly. A
        // shorter sample is not padded and a longer one is not truncated, because either would be
        // this organ deciding a level on the receiver's behalf.
        for (ordinal, sample) in section.samples.iter().enumerate() {
            let Some(sample) = sample else {
                continue;
            };
            if sample.population() != section.channels.get() {
                return Err(ReceiverPhaseAtlasError::ChannelPopulationDisagreement {
                    receiver: section.receiver,
                    declared: section.channels.get(),
                    supplied: sample.population(),
                    sample: usize_to_u64(ordinal)?,
                });
            }
        }
    }
    Ok(())
}

fn admit_section(
    standing: &mut ReceiverPhaseAtlasStanding,
    event: &ReceiverPhaseAtlasEvent,
    occurrence: &ReceiverPhaseSectionOccurrence,
) -> Result<ReceiverPhaseSectionId, ReceiverPhaseAtlasError> {
    let section_id = ReceiverPhaseSectionId(standing.next_section);
    standing.next_section = standing
        .next_section
        .checked_add(1)
        .ok_or(ReceiverPhaseAtlasError::CarrierOverflow)?;
    let visible_samples = occurrence
        .samples
        .iter()
        .filter(|sample| sample.is_some())
        .count();
    let absent_samples = occurrence.samples.len() - visible_samples;
    let mut section = ReceiverPhaseSection {
        id: section_id,
        source_image: occurrence.source_image,
        source_lineage: occurrence.source_lineage,
        event: event.event,
        chronology: event.chronology,
        receiver: occurrence.receiver,
        rays: occurrence.rays.clone(),
        extent: occurrence.extent,
        channels: occurrence.channels,
        visible_samples: usize_to_u64(visible_samples)?,
        absent_samples: usize_to_u64(absent_samples)?,
        germs: BTreeSet::new(),
        connections: BTreeSet::new(),
        cycles: BTreeSet::new(),
    };
    let extracted = extract_germs(occurrence)?;
    for extracted in extracted {
        let id = ReceiverPhaseGermId(standing.next_germ);
        standing.next_germ = standing
            .next_germ
            .checked_add(1)
            .ok_or(ReceiverPhaseAtlasError::CarrierOverflow)?;
        let germ = ReceiverPhaseGerm {
            id,
            section: section_id,
            source_event: event.event,
            source_lineage: occurrence.source_lineage,
            receiver: occurrence.receiver,
            witness: extracted.witness,
            chart_point: extracted.chart_point,
            jet: extracted.jet,
            exact_energy: BigUint::from(extracted.energy),
            persistence_radii: extracted.persistence_radii,
            open_radius: extracted.open_radius,
            horizon: extracted.horizon,
            dominant_coordinate: extracted.dominant_coordinate,
            level_sets: extracted.level_sets,
            signature: extracted.signature,
        };
        standing
            .germ_populations
            .entry(germ.signature.clone())
            .or_default()
            .insert(id);
        section.germs.insert(id);
        standing.germs.insert(id, germ);
    }
    form_connections_and_cycles(standing, &mut section)?;
    standing.sections.insert(section_id, section);
    Ok(section_id)
}

struct ExtractedGerm {
    witness: ReceiverPhaseAddress,
    chart_point: [Rat; 2],
    jet: ExactReceiverPhaseJet,
    energy: u32,
    persistence_radii: Vec<u32>,
    open_radius: Option<u32>,
    horizon: u32,
    dominant_coordinate: u8,
    level_sets: Vec<Option<HomogeneousConic>>,
    signature: ReceiverPhaseGermSignature,
}

fn extract_germs(
    occurrence: &ReceiverPhaseSectionOccurrence,
) -> Result<Vec<ExtractedGerm>, ReceiverPhaseAtlasError> {
    let width = usize::try_from(occurrence.extent.width)
        .map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?;
    let height = usize::try_from(occurrence.extent.height)
        .map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?;
    if width < 9 || height < 9 {
        return Ok(Vec::new());
    }
    let mut energies = vec![None; occurrence.samples.len()];
    for row in 1..height - 1 {
        for column in 1..width - 1 {
            if let Some((_, energy, _, _)) = phase_jet(occurrence, column, row, width, height, 1)? {
                energies[row * width + column] = Some(energy);
            }
        }
    }
    let mut radii = Vec::new();
    let mut radius = 1_u32;
    let maximum_radius = occurrence.extent.width.min(occurrence.extent.height) / 4;
    while radius <= maximum_radius {
        radii.push(radius);
        let Some(next) = radius.checked_mul(2) else {
            break;
        };
        radius = next;
    }
    if radii.len() < 2 {
        return Ok(Vec::new());
    }

    let mut germs = Vec::new();
    for row in 1..height - 1 {
        for column in 1..width - 1 {
            let Some(energy) = energies[row * width + column] else {
                continue;
            };
            if energy == 0 {
                continue;
            }
            let mut persistence_radii = Vec::new();
            let mut open_radius = None;
            for radius in &radii {
                match window_maximum(
                    &energies,
                    width,
                    height,
                    column,
                    row,
                    usize::try_from(*radius)
                        .map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?,
                    energy,
                ) {
                    WindowMaximum::Certified => persistence_radii.push(*radius),
                    WindowMaximum::Open => {
                        open_radius = Some(*radius);
                        break;
                    }
                    WindowMaximum::Dominated => break,
                }
            }
            // The jet already carries value, first difference, and second
            // difference.  It becomes a germ only when that second-order
            // witness survives a strictly larger receiver neighborhood.
            if persistence_radii.len() < 2 {
                continue;
            }
            // The persistence horizon selects the support jet. A feature
            // which remains distinguished over a wider receiver
            // neighborhood is continued by differences over that same
            // caused scale, rather than extrapolating one-pixel tangents
            // across the larger region.
            let horizon = *persistence_radii
                .last()
                .ok_or(ReceiverPhaseAtlasError::MalformedSection)?;
            let support_step =
                usize::try_from(horizon).map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?;
            let Some((jet, _, dominant_coordinate, level_sets)) =
                phase_jet(occurrence, column, row, width, height, support_step)?
            else {
                continue;
            };
            let dominant = usize::from(dominant_coordinate);
            let conic = level_sets[dominant]
                .as_ref()
                .ok_or(ReceiverPhaseAtlasError::MalformedJet)?;
            let gradient = &jet.gradients[dominant];
            let hessian = &jet.hessians[dominant];
            let trace = &hessian[0][0] + &hessian[1][1];
            let determinant = &hessian[0][0] * &hessian[1][1] - &hessian[0][1] * &hessian[1][0];
            let persistence_order = u32::try_from(persistence_radii.len())
                .map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?;
            let signature = ReceiverPhaseGermSignature {
                dominant_coordinate,
                conic_species: conic.classify().into(),
                gradient_hands: [PhaseHand::of(&gradient[0]), PhaseHand::of(&gradient[1])],
                hessian_trace_hand: PhaseHand::of(&trace),
                hessian_determinant_hand: PhaseHand::of(&determinant),
                persistence_order,
            };
            germs.push(ExtractedGerm {
                witness: ReceiverPhaseAddress {
                    column: u32::try_from(column)
                        .map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?,
                    row: u32::try_from(row)
                        .map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?,
                },
                chart_point: [rat_usize(column), rat_usize(row)],
                jet,
                energy,
                persistence_radii,
                open_radius,
                horizon,
                dominant_coordinate,
                level_sets,
                signature,
            });
        }
    }
    Ok(germs)
}

type PhaseJetResult = (
    ExactReceiverPhaseJet,
    u32,
    u8,
    Vec<Option<HomogeneousConic>>,
);

fn phase_jet(
    occurrence: &ReceiverPhaseSectionOccurrence,
    column: usize,
    row: usize,
    width: usize,
    height: usize,
    step: usize,
) -> Result<Option<PhaseJetResult>, ReceiverPhaseAtlasError> {
    if step == 0
        || column < step
        || row < step
        || column.checked_add(step).is_none_or(|right| right >= width)
        || row.checked_add(step).is_none_or(|bottom| bottom >= height)
    {
        return Ok(None);
    }
    let channels = occurrence.channels.get();
    let step_signed =
        isize::try_from(step).map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?;
    let at = |horizontal: isize, vertical: isize| -> Option<&ReceiverChannelSample> {
        let column = column.checked_add_signed(horizontal)?;
        let row = row.checked_add_signed(vertical)?;
        occurrence.samples[row * width + column].as_ref()
    };
    let Some(center) = at(0, 0) else {
        return Ok(None);
    };
    let Some(left) = at(-step_signed, 0) else {
        return Ok(None);
    };
    let Some(right) = at(step_signed, 0) else {
        return Ok(None);
    };
    let Some(up) = at(0, -step_signed) else {
        return Ok(None);
    };
    let Some(down) = at(0, step_signed) else {
        return Ok(None);
    };
    let Some(up_left) = at(-step_signed, -step_signed) else {
        return Ok(None);
    };
    let Some(up_right) = at(step_signed, -step_signed) else {
        return Ok(None);
    };
    let Some(down_left) = at(-step_signed, step_signed) else {
        return Ok(None);
    };
    let Some(down_right) = at(step_signed, step_signed) else {
        return Ok(None);
    };
    let two = rat_i64(2);
    let four = rat_i64(4);
    let step_rat = rat_usize(step);
    let step_squared = &step_rat * &step_rat;
    let mut energy = 0_u32;
    let mut channel_energies = vec![0_u32; channels];
    let mut values = vec![Rat::zero(); channels];
    let mut gradients = vec![[Rat::zero(), Rat::zero()]; channels];
    let mut hessians = vec![[[Rat::zero(), Rat::zero()], [Rat::zero(), Rat::zero()]]; channels];
    let mut level_sets: Vec<Option<HomogeneousConic>> = vec![None; channels];
    // The declared population indexes the samples; a sample too short for it is refused at
    // `validate_event`, so this cannot silently read a channel the receiver did not declare.
    let channel_at =
        |sample: &ReceiverChannelSample, channel: usize| -> i32 { i32::from(sample.0[channel]) };
    for channel in 0..channels {
        let center = channel_at(center, channel);
        let left = channel_at(left, channel);
        let right = channel_at(right, channel);
        let up = channel_at(up, channel);
        let down = channel_at(down, channel);
        let up_left = channel_at(up_left, channel);
        let up_right = channel_at(up_right, channel);
        let down_left = channel_at(down_left, channel);
        let down_right = channel_at(down_right, channel);
        let gradient_x_numerator = right - left;
        let gradient_y_numerator = down - up;
        let hessian_xx = right - 2 * center + left;
        let hessian_yy = down - 2 * center + up;
        let hessian_xy_numerator = down_right - down_left - up_right + up_left;
        let channel_energy = u32::from(
            u16::try_from(gradient_x_numerator.unsigned_abs())
                .map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?,
        ) + u32::from(
            u16::try_from(gradient_y_numerator.unsigned_abs())
                .map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?,
        ) + u32::from(
            u16::try_from(hessian_xx.unsigned_abs())
                .map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?,
        ) * 2
            + u32::from(
                u16::try_from(hessian_yy.unsigned_abs())
                    .map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?,
            ) * 2
            + u32::from(
                u16::try_from(hessian_xy_numerator.unsigned_abs())
                    .map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?,
            );
        channel_energies[channel] = channel_energy;
        energy = energy
            .checked_add(channel_energy)
            .ok_or(ReceiverPhaseAtlasError::CarrierOverflow)?;
        values[channel] = rat_i64(i64::from(center));
        gradients[channel] = [
            rat_i64(i64::from(gradient_x_numerator)) / (&two * &step_rat),
            rat_i64(i64::from(gradient_y_numerator)) / (&two * &step_rat),
        ];
        let mixed = rat_i64(i64::from(hessian_xy_numerator)) / (&four * &step_squared);
        hessians[channel] = [
            [
                rat_i64(i64::from(hessian_xx)) / &step_squared,
                mixed.clone(),
            ],
            [mixed, rat_i64(i64::from(hessian_yy)) / &step_squared],
        ];
        let scaled_gradient_x = i64::from(gradient_x_numerator)
            .checked_mul(i64::try_from(step).map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?)
            .and_then(|value| value.checked_mul(2))
            .ok_or(ReceiverPhaseAtlasError::CarrierOverflow)?;
        let scaled_gradient_y = i64::from(gradient_y_numerator)
            .checked_mul(i64::try_from(step).map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)?)
            .and_then(|value| value.checked_mul(2))
            .ok_or(ReceiverPhaseAtlasError::CarrierOverflow)?;
        let coefficients = [
            rat_i64(i64::from(2 * hessian_xx)),
            rat_i64(i64::from(hessian_xy_numerator)),
            rat_i64(i64::from(2 * hessian_yy)),
            rat_i64(scaled_gradient_x),
            rat_i64(scaled_gradient_y),
            Rat::zero(),
        ];
        if coefficients
            .iter()
            .any(|coefficient| !coefficient.is_zero())
        {
            level_sets[channel] = Some(HomogeneousConic::new(coefficients)?);
        }
    }
    let dominant_coordinate = channel_energies
        .iter()
        .enumerate()
        .filter(|(_, energy)| **energy != 0)
        .max_by_key(|(channel, energy)| (**energy, std::cmp::Reverse(*channel)))
        .map(|(channel, _)| {
            u8::try_from(channel).map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)
        })
        .transpose()?;
    let Some(dominant_coordinate) = dominant_coordinate else {
        return Ok(None);
    };
    Ok(Some((
        ExactReceiverPhaseJet {
            values,
            gradients,
            hessians,
        },
        energy,
        dominant_coordinate,
        level_sets,
    )))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WindowMaximum {
    Certified,
    Open,
    Dominated,
}

fn window_maximum(
    energies: &[Option<u32>],
    width: usize,
    height: usize,
    column: usize,
    row: usize,
    radius: usize,
    center: u32,
) -> WindowMaximum {
    let Some(minimum_column) = column.checked_sub(radius) else {
        return WindowMaximum::Open;
    };
    let Some(minimum_row) = row.checked_sub(radius) else {
        return WindowMaximum::Open;
    };
    let Some(maximum_column) = column.checked_add(radius) else {
        return WindowMaximum::Open;
    };
    let Some(maximum_row) = row.checked_add(radius) else {
        return WindowMaximum::Open;
    };
    if maximum_column >= width || maximum_row >= height {
        return WindowMaximum::Open;
    }
    let mut open = false;
    for candidate_row in minimum_row..=maximum_row {
        for candidate_column in minimum_column..=maximum_column {
            let Some(candidate) = energies[candidate_row * width + candidate_column] else {
                open = true;
                continue;
            };
            if candidate > center {
                return WindowMaximum::Dominated;
            }
        }
    }
    if open {
        WindowMaximum::Open
    } else {
        WindowMaximum::Certified
    }
}

fn form_connections_and_cycles(
    standing: &mut ReceiverPhaseAtlasStanding,
    section: &mut ReceiverPhaseSection,
) -> Result<(), ReceiverPhaseAtlasError> {
    // The receiver topology, rather than an authored degree or population
    // cap, decides which pairs can meet. Ordering witnesses by dominant
    // phase and one chart coordinate lets a germ stop as soon as its own
    // caused horizon can no longer reach a later witness; distant pairs are
    // never enumerated.
    let mut germs = section.germs.iter().copied().collect::<Vec<_>>();
    germs.sort_by_key(|id| {
        let germ = &standing.germs[id];
        (
            germ.dominant_coordinate,
            germ.witness.column,
            germ.witness.row,
            *id,
        )
    });
    let mut directed =
        BTreeMap::<(ReceiverPhaseGermId, ReceiverPhaseGermId), ReceiverPhaseConnectionId>::new();
    let mut undirected = BTreeMap::<ReceiverPhaseGermId, BTreeSet<ReceiverPhaseGermId>>::new();
    for left_index in 0..germs.len() {
        for right_index in left_index + 1..germs.len() {
            let left_id = germs[left_index];
            let right_id = germs[right_index];
            let (forward, reverse) = {
                let left = standing
                    .germs
                    .get(&left_id)
                    .ok_or(ReceiverPhaseAtlasError::MalformedStanding)?;
                let right = standing
                    .germs
                    .get(&right_id)
                    .ok_or(ReceiverPhaseAtlasError::MalformedStanding)?;
                if right.dominant_coordinate != left.dominant_coordinate {
                    break;
                }
                if right.witness.column.abs_diff(left.witness.column) > left.horizon {
                    break;
                }
                let distance = left
                    .witness
                    .column
                    .abs_diff(right.witness.column)
                    .max(left.witness.row.abs_diff(right.witness.row));
                if distance > right.horizon {
                    continue;
                }
                (
                    connection_correction(left, right)?,
                    connection_correction(right, left)?,
                )
            };
            let (Some(forward), Some(reverse)) = (forward, reverse) else {
                continue;
            };
            let forward_id = insert_connection(standing, section, left_id, right_id, forward)?;
            let reverse_id = insert_connection(standing, section, right_id, left_id, reverse)?;
            directed.insert((left_id, right_id), forward_id);
            directed.insert((right_id, left_id), reverse_id);
            undirected.entry(left_id).or_default().insert(right_id);
            undirected.entry(right_id).or_default().insert(left_id);
        }
    }
    for (left, neighbors) in &undirected {
        for middle in neighbors.iter().filter(|middle| **middle > *left) {
            let Some(middle_neighbors) = undirected.get(middle) else {
                continue;
            };
            for right in neighbors
                .intersection(middle_neighbors)
                .filter(|right| **right > *middle)
            {
                let connections = [
                    *directed
                        .get(&(*left, *middle))
                        .ok_or(ReceiverPhaseAtlasError::MalformedStanding)?,
                    *directed
                        .get(&(*middle, *right))
                        .ok_or(ReceiverPhaseAtlasError::MalformedStanding)?,
                    *directed
                        .get(&(*right, *left))
                        .ok_or(ReceiverPhaseAtlasError::MalformedStanding)?,
                ];
                let first = &standing.connections[&connections[0]].correction;
                let second = &standing.connections[&connections[1]].correction;
                let third = &standing.connections[&connections[2]].correction;
                let holonomy = matrix_multiply(third, &matrix_multiply(second, first));
                let curved = holonomy != identity_matrix();
                let id = ReceiverPhaseCycleId(standing.next_cycle);
                standing.next_cycle = standing
                    .next_cycle
                    .checked_add(1)
                    .ok_or(ReceiverPhaseAtlasError::CarrierOverflow)?;
                standing.cycles.insert(
                    id,
                    ReceiverPhaseCycle {
                        id,
                        section: section.id,
                        source_event: section.event,
                        boundary: [*left, *middle, *right],
                        connections,
                        holonomy,
                        curved,
                    },
                );
                section.cycles.insert(id);
            }
        }
    }
    Ok(())
}

fn insert_connection(
    standing: &mut ReceiverPhaseAtlasStanding,
    section: &mut ReceiverPhaseSection,
    source: ReceiverPhaseGermId,
    target: ReceiverPhaseGermId,
    values: ([Rat; 2], [Rat; 2], [[Rat; 2]; 2]),
) -> Result<ReceiverPhaseConnectionId, ReceiverPhaseAtlasError> {
    let id = ReceiverPhaseConnectionId(standing.next_connection);
    standing.next_connection = standing
        .next_connection
        .checked_add(1)
        .ok_or(ReceiverPhaseAtlasError::CarrierOverflow)?;
    standing.connections.insert(
        id,
        ReceiverPhaseConnection {
            id,
            section: section.id,
            source_event: section.event,
            source,
            target,
            predicted_normal: values.0,
            target_normal: values.1,
            correction: values.2,
        },
    );
    section.connections.insert(id);
    Ok(id)
}

type ConnectionCorrection = ([Rat; 2], [Rat; 2], [[Rat; 2]; 2]);

fn connection_correction(
    source: &ReceiverPhaseGerm,
    target: &ReceiverPhaseGerm,
) -> Result<Option<ConnectionCorrection>, ReceiverPhaseAtlasError> {
    let channel = usize::from(source.dominant_coordinate);
    let Some(conic) = &source.level_sets[channel] else {
        return Ok(None);
    };
    let displacement = [
        &target.chart_point[0] - &source.chart_point[0],
        &target.chart_point[1] - &source.chart_point[1],
    ];
    let predicted = [
        Rat::from_integer(BigInt::from(2)) * &conic.xx * &displacement[0]
            + &conic.xy * &displacement[1]
            + &conic.xw,
        &conic.xy * &displacement[0]
            + Rat::from_integer(BigInt::from(2)) * &conic.yy * &displacement[1]
            + &conic.yw,
    ];
    let actual = target.jet.gradients[channel].clone();
    if vector_norm_squared(&predicted).is_zero() || vector_norm_squared(&actual).is_zero() {
        return Ok(None);
    }
    let dot = &predicted[0] * &actual[0] + &predicted[1] * &actual[1];
    let cross = &predicted[0] * &actual[1] - &predicted[1] * &actual[0];
    if cross.abs() > dot.abs() {
        return Ok(None);
    }
    let predicted_frame = phase_frame(&predicted);
    let target_frame = phase_frame(&actual);
    let correction = matrix_multiply(&matrix_inverse(&target_frame)?, &predicted_frame);
    Ok(Some((predicted, actual, correction)))
}

fn phase_frame(normal: &[Rat; 2]) -> [[Rat; 2]; 2] {
    [
        [-normal[1].clone(), normal[0].clone()],
        [normal[0].clone(), normal[1].clone()],
    ]
}

fn matrix_inverse(matrix: &[[Rat; 2]; 2]) -> Result<[[Rat; 2]; 2], ReceiverPhaseAtlasError> {
    let determinant = &matrix[0][0] * &matrix[1][1] - &matrix[0][1] * &matrix[1][0];
    if determinant.is_zero() {
        return Err(ReceiverPhaseAtlasError::SingularPhaseFrame);
    }
    Ok([
        [&matrix[1][1] / &determinant, -&matrix[0][1] / &determinant],
        [-&matrix[1][0] / &determinant, &matrix[0][0] / determinant],
    ])
}

fn matrix_multiply(left: &[[Rat; 2]; 2], right: &[[Rat; 2]; 2]) -> [[Rat; 2]; 2] {
    std::array::from_fn(|row| {
        std::array::from_fn(|column| {
            &left[row][0] * &right[0][column] + &left[row][1] * &right[1][column]
        })
    })
}

fn identity_matrix() -> [[Rat; 2]; 2] {
    [[Rat::one(), Rat::zero()], [Rat::zero(), Rat::one()]]
}

fn vector_norm_squared(vector: &[Rat; 2]) -> Rat {
    &vector[0] * &vector[0] + &vector[1] * &vector[1]
}

fn rat_i64(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn rat_usize(value: usize) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn usize_to_u64(value: usize) -> Result<u64, ReceiverPhaseAtlasError> {
    u64::try_from(value).map_err(|_| ReceiverPhaseAtlasError::CarrierOverflow)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ReceiverPhaseAtlasError {
    #[error("a receiver-phase event must contain at least one section")]
    EmptyEvent,
    #[error(
        "a germ passage with no germ in it is a key standing for a population that is not there"
    )]
    EmptyGermPassage,
    #[error("germ {0:?} is filed under a passage that is not the one it carries")]
    GermPassageMismatch(ReceiverPhaseGermId),
    #[error("receiver-phase event {0:?} has already entered standing")]
    RepeatedEvent(EventId),
    #[error("receiver-phase chronology {supplied} does not follow {previous}")]
    NoncausalChronology { previous: u64, supplied: u64 },
    #[error("receiver {0:?} occurs more than once in one receiver-phase event")]
    DuplicateReceiver(ReceiverId),
    #[error(
        "receiver {receiver:?} declared {declared} channels and sample {sample} carries {supplied}"
    )]
    ChannelPopulationDisagreement {
        receiver: ReceiverId,
        declared: usize,
        supplied: usize,
        sample: u64,
    },
    #[error(
        "receiver {receiver:?} declares {declared} channels and a channel is addressed by a carrier holding {carrier}"
    )]
    ChannelPopulationExceedsCoordinateCarrier {
        receiver: ReceiverId,
        declared: usize,
        carrier: usize,
    },
    #[error("germ {germ:?} was caused at {caused} channels in a section declaring {declared}")]
    GermChannelPopulationDisagreement {
        germ: ReceiverPhaseGermId,
        declared: usize,
        caused: usize,
    },
    #[error("a receiver-phase section is malformed")]
    MalformedSection,
    #[error("a receiver-phase jet is malformed")]
    MalformedJet,
    #[error("the receiver-phase standing is malformed")]
    MalformedStanding,
    #[error("a receiver-phase connection frame is singular")]
    SingularPhaseFrame,
    #[error("a receiver-phase carrier overflowed")]
    CarrierOverflow,
    #[error(transparent)]
    Conic(#[from] ConicError),
    #[error(transparent)]
    Image(#[from] ImageCarrierError),
    #[error(transparent)]
    Receiver(#[from] ReceiverError),
}

#[cfg(test)]
mod tests {
    use relational_geometry::RatVec3;

    use super::*;
    use crate::CausalWorld;

    fn rays() -> RayFamily {
        RayFamily::Central {
            center: RatVec3::zero(),
            forward: RatVec3::from_i64(0, 0, 1),
            horizontal: RatVec3::from_i64(1, 0, 0),
            vertical: RatVec3::from_i64(0, 1, 0),
        }
    }

    fn curved_section(receiver: u64, lineage: u64, offset: u8) -> ReceiverPhaseSectionOccurrence {
        let extent = ImageExtent {
            width: 33,
            height: 33,
        };
        let samples = (0..extent.height)
            .flat_map(|row| {
                (0..extent.width).map(move |column| {
                    let x = i32::try_from(column).unwrap() - 16;
                    let y = i32::try_from(row).unwrap() - 16;
                    let radius = u8::try_from(((x * x + y * y) / 8).min(200)).unwrap();
                    Some(ExactRgb {
                        red: offset.saturating_add(radius),
                        green: offset.saturating_add(radius / 2),
                        blue: offset,
                    })
                })
            })
            .collect();
        ReceiverPhaseSectionOccurrence::from_rgb(
            None,
            lineage,
            ReceiverId(receiver),
            rays(),
            extent,
            samples,
        )
    }

    /// One geometric scene, read at a **declared** channel population.
    ///
    /// Channel `c` carries a compact quadratic bump centred at its own column, so the scene a
    /// receiver sees is genuinely a function of how many channels it declares: the summed energy
    /// landscape that decides which addresses survive [`window_maximum`] is built from a different
    /// number of bumps at each population, and the dominant channel is whichever bump is nearest.
    /// This is the declared material for the `CHANNEL_COUNT` excision orbit.
    fn banded_section(
        receiver: u64,
        lineage: u64,
        channels: usize,
    ) -> ReceiverPhaseSectionOccurrence {
        let extent = ImageExtent {
            width: 41,
            height: 41,
        };
        let samples = (0..extent.height)
            .flat_map(|row| {
                (0..extent.width).map(move |column| {
                    Some(ReceiverChannelSample(
                        (0..channels)
                            .map(|channel| {
                                banded_reading(
                                    i32::try_from(column).unwrap(),
                                    i32::try_from(row).unwrap(),
                                    channel,
                                )
                            })
                            .collect(),
                    ))
                })
            })
            .collect();
        ReceiverPhaseSectionOccurrence {
            source_image: None,
            source_lineage: lineage,
            receiver: ReceiverId(receiver),
            rays: rays(),
            extent,
            channels: NonZeroUsize::new(channels).expect("a receiver has at least one channel"),
            samples,
        }
    }

    fn banded_reading(column: i32, row: i32, channel: usize) -> u8 {
        let ordinal = i32::try_from(channel).expect("channel ordinals fit i32");
        let horizontal = column - (6 + 7 * ordinal);
        let vertical = row - 20;
        let bump = 255 - 5 * (horizontal * horizontal + vertical * vertical);
        let ripple = 11 * (column * 3 + row * 5 + ordinal * 2).rem_euclid(7);
        u8::try_from((bump + ripple).clamp(0, 255)).expect("a clamped reading fits u8")
    }

    fn atlas_of(section: ReceiverPhaseSectionOccurrence) -> ReceiverPhaseAtlasStanding {
        let law = ReceiverPhaseAtlasLaw;
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        world
            .receive(&ReceiverPhaseAtlasEvent {
                event: EventId(1),
                chronology: 1,
                sections: vec![section],
            })
            .unwrap();
        world.standing().clone()
    }

    fn germ_addresses(standing: &ReceiverPhaseAtlasStanding) -> BTreeSet<(u32, u32)> {
        standing
            .germs
            .values()
            .map(|germ| (germ.witness.row, germ.witness.column))
            .collect()
    }

    /// THE DECLARED CONTROL for the `CHANNEL_COUNT` excision
    /// (`docs/canon/THE_CONTAMINANT_PROTOCOL.md` §2.5, §4).
    ///
    /// One scene, read by five receivers that differ only in the channel population they declare.
    /// Under the pinned organ four of the five could not be constructed: `ExactReceiverPhaseJet`
    /// was `[Rat; 3]` by type, so a one-channel and a five-channel receiver were not expressible
    /// and this test could not have been written.
    ///
    /// **The orbit is not trivial and the level was deciding the answer.** Measured 2026-08-09:
    ///
    /// ```text
    ///   channels   germs  signatures  connections  dominant coordinates
    ///          1       5           3            0  {0}
    ///          2       5           5            0  {0,1}
    ///          3       8           7            0  {0,1,2}
    ///          4      10          10            0  {0,1,2,3}
    ///          5      12          12            2  {0,1,2,3,4}
    /// ```
    ///
    /// Germ counts are **not** monotone — one and two channels both return five — so this is a
    /// change of *which* addresses are founded rather than of how many, which is what the
    /// distinguishing address below exhibits.
    #[test]
    fn the_channel_population_is_the_receivers_and_it_moves_the_return() {
        let populations = [1_usize, 2, 3, 4, 5];
        let readings =
            populations.map(|channels| (channels, atlas_of(banded_section(1, 1, channels))));

        let germs = readings
            .iter()
            .map(|(_, standing)| standing.germs.len())
            .collect::<Vec<_>>();
        let signatures = readings
            .iter()
            .map(|(_, standing)| standing.germ_populations.len())
            .collect::<Vec<_>>();
        assert_eq!(germs, vec![5, 5, 8, 10, 12]);
        assert_eq!(signatures, vec![3, 5, 7, 10, 12]);

        for (channels, standing) in &readings {
            // Every declared channel participates: the dominant coordinate ranges over the whole
            // declared population and no further. Against a pinned three this assertion is
            // unwritable at every population but one.
            let dominants = standing
                .germs
                .values()
                .map(|germ| germ.dominant_coordinate)
                .collect::<BTreeSet<_>>();
            assert_eq!(
                dominants,
                (0..u8::try_from(*channels).unwrap()).collect::<BTreeSet<_>>(),
                "the dominant coordinate ranges over the declared population at {channels}"
            );
            // The section and every germ it caused state their own shape.
            for section in standing.sections.values() {
                assert_eq!(section.channels.get(), *channels);
            }
            for germ in standing.germs.values() {
                assert_eq!(germ.jet.channel_population(), *channels);
                assert_eq!(germ.jet.gradients.len(), *channels);
                assert_eq!(germ.jet.hessians.len(), *channels);
                assert_eq!(germ.level_sets.len(), *channels);
                assert_eq!(
                    germ.evaluate_phase(&[Rat::one(), Rat::one()]).len(),
                    *channels
                );
            }
            standing.validate().unwrap();
        }

        // No two populations found the same set of addresses on the same scene.
        for left in 0..readings.len() {
            for right in left + 1..readings.len() {
                assert_ne!(
                    germ_addresses(&readings[left].1),
                    germ_addresses(&readings[right].1),
                    "populations {} and {} agreed on the founded addresses",
                    readings[left].0,
                    readings[right].0
                );
            }
        }

        // THE DISTINGUISHING WORD, in the sense `docs/canon/THE_CONTAMINANT_PROTOCOL.md` §4 asks for:
        // the least address on which the one-channel and three-channel receivers disagree.
        let single = germ_addresses(&readings[0].1);
        let triple = germ_addresses(&readings[2].1);
        let separating = single
            .symmetric_difference(&triple)
            .copied()
            .min()
            .expect("the two readings differ");
        assert_eq!(separating, (14, 9));
        assert!(!single.contains(&separating) && triple.contains(&separating));
    }

    /// The refusal that makes the declaration a declaration rather than a hint. A receiver states
    /// its channel population and the material must meet it; a shorter sample is not padded and a
    /// longer one is not truncated.
    #[test]
    fn a_sample_that_does_not_meet_the_declared_channel_population_is_refused_by_name() {
        let law = ReceiverPhaseAtlasLaw;
        let honest = banded_section(1, 1, 3);
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        assert!(
            world
                .receive(&ReceiverPhaseAtlasEvent {
                    event: EventId(1),
                    chronology: 1,
                    sections: vec![honest],
                })
                .is_ok(),
            "and the honest receiver passes"
        );

        for supplied in [2_usize, 4] {
            let mut section = banded_section(1, 1, 3);
            section.samples[7] = Some(ReceiverChannelSample(vec![9; supplied]));
            let mut world = CausalWorld::new(law.clone(), law.initial_standing());
            assert_eq!(
                world.receive(&ReceiverPhaseAtlasEvent {
                    event: EventId(1),
                    chronology: 1,
                    sections: vec![section],
                }),
                Err(ReceiverPhaseAtlasError::ChannelPopulationDisagreement {
                    receiver: ReceiverId(1),
                    declared: 3,
                    supplied,
                    sample: 7,
                })
            );
        }

        // And the one bound that survives: a channel is addressed by a `u8` downstream, so a
        // population past that carrier is refused at the mouth rather than panicking in
        // `holonic_complex`. `256` passes; `257` does not. The bound is the carrier's and the
        // refusal names it.
        for (declared, admitted) in [
            (COORDINATE_CARRIER_POPULATION, true),
            (COORDINATE_CARRIER_POPULATION + 1, false),
        ] {
            let mut section = banded_section(1, 1, 3);
            section.channels = NonZeroUsize::new(declared).unwrap();
            section.samples = section
                .samples
                .iter()
                .map(|_| Some(ReceiverChannelSample(vec![7; declared])))
                .collect();
            let mut world = CausalWorld::new(law.clone(), law.initial_standing());
            let returned = world.receive(&ReceiverPhaseAtlasEvent {
                event: EventId(1),
                chronology: 1,
                sections: vec![section],
            });
            assert_eq!(
                returned.is_ok(),
                admitted,
                "a {declared}-channel receiver against a carrier holding \
                 {COORDINATE_CARRIER_POPULATION}"
            );
            if !admitted {
                assert_eq!(
                    returned,
                    Err(
                        ReceiverPhaseAtlasError::ChannelPopulationExceedsCoordinateCarrier {
                            receiver: ReceiverId(1),
                            declared,
                            carrier: COORDINATE_CARRIER_POPULATION,
                        }
                    )
                );
            }
        }

        // And a standing whose germ was caused at another population is refused, so the two can
        // never silently disagree after a remount.
        let standing = atlas_of(banded_section(1, 1, 3));
        standing.validate().unwrap();
        let id = *standing.germs.keys().next().expect("a live control");
        let mut widened = standing.clone();
        widened
            .germs
            .get_mut(&id)
            .expect("the germ stands")
            .jet
            .values
            .push(Rat::zero());
        assert_eq!(
            widened.validate(),
            Err(ReceiverPhaseAtlasError::GermChannelPopulationDisagreement {
                germ: id,
                declared: 3,
                caused: 4,
            })
        );
    }

    #[test]
    fn persistent_phase_differences_cause_native_curved_level_sets() {
        let law = ReceiverPhaseAtlasLaw;
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        world
            .receive(&ReceiverPhaseAtlasEvent {
                event: EventId(1),
                chronology: 1,
                sections: vec![curved_section(1, 1, 0)],
            })
            .unwrap();
        assert!(!world.standing().germs.is_empty());
        assert!(world.standing().germs.values().any(|germ| {
            germ.level_sets
                .iter()
                .flatten()
                .any(|conic| !matches!(conic.classify(), ConicClass::ParallelLinePair))
        }));
        assert!(
            world
                .standing()
                .germs
                .values()
                .all(|germ| germ.persistence_radii.len() >= 2)
        );
    }

    #[test]
    fn absent_testimony_cannot_found_a_germ() {
        let law = ReceiverPhaseAtlasLaw;
        let mut section = curved_section(1, 1, 0);
        let width = usize::try_from(section.extent.width).unwrap();
        for row in 8..25 {
            for column in 8..25 {
                section.samples[row * width + column] = None;
            }
        }
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        world
            .receive(&ReceiverPhaseAtlasEvent {
                event: EventId(1),
                chronology: 1,
                sections: vec![section],
            })
            .unwrap();
        assert!(world.standing().germs.values().all(|germ| {
            germ.witness.column < 8
                || germ.witness.column >= 25
                || germ.witness.row < 8
                || germ.witness.row >= 25
        }));
    }

    #[test]
    fn conditioning_population_grows_without_an_authored_germ_count() {
        let law = ReceiverPhaseAtlasLaw;
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        world
            .receive(&ReceiverPhaseAtlasEvent {
                event: EventId(1),
                chronology: 1,
                sections: vec![curved_section(1, 1, 0)],
            })
            .unwrap();
        let before = world.standing().germs.len();
        world
            .receive(&ReceiverPhaseAtlasEvent {
                event: EventId(2),
                chronology: 2,
                sections: vec![curved_section(2, 2, 4)],
            })
            .unwrap();
        assert!(world.standing().germs.len() > before);
    }

    /// THE DECLARED CONTROL for the germ passage population (`CLAUDE.md` §2b). Until 2026-08-08
    /// `germ_populations` was `BTreeMap<Signature, u64>` — *"a count of signs is a state reading"* —
    /// a tally standing beside the germs it summarised, which `validate` did not look at and which
    /// no reader could resolve back to a germ.
    ///
    /// Three things this now supports and a count could not:
    ///
    /// - the passages are **addressed**: every germ under a signature can be named and re-read at
    ///   its exact `Rat` jet, which is where the hands came from;
    /// - two standings with identical counts on identical signatures are distinguishable when they
    ///   are populated by different germs;
    /// - the map is **checkable against the germs**, so a corrupted standing is refused by name.
    ///   A count can only ever be checked against another count.
    ///
    /// Against the old carrier the address assertions cannot be written and the mismatch below
    /// validates cleanly.
    #[test]
    fn the_germ_passage_population_is_addressed_and_the_count_is_a_reading() {
        let law = ReceiverPhaseAtlasLaw;
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        world
            .receive(&ReceiverPhaseAtlasEvent {
                event: EventId(1),
                chronology: 1,
                sections: vec![curved_section(1, 1, 0)],
            })
            .unwrap();
        let standing = world.standing();
        assert!(!standing.germ_populations.is_empty(), "a live control");

        // Every germ is named by exactly one passage, and the count is that population's extent.
        let mut named = BTreeSet::new();
        for (signature, population) in &standing.germ_populations {
            assert_eq!(standing.germ_population_count(signature), population.len());
            for germ in population {
                assert!(named.insert(*germ), "a germ takes exactly one passage");
                let body = &standing.germs[germ];
                assert_eq!(&body.signature, signature);
                assert_eq!(standing.passage_of(*germ), Some(signature));
                // The hands are re-derivable from the exact jet the germ still carries; the
                // signature is a reading of that material and never a substitute for it.
                let dominant = usize::from(body.dominant_coordinate);
                let hessian = &body.jet.hessians[dominant];
                let trace = &hessian[0][0] + &hessian[1][1];
                let determinant = &hessian[0][0] * &hessian[1][1] - &hessian[0][1] * &hessian[1][0];
                assert_eq!(signature.hessian_trace_hand, PhaseHand::of(&trace));
                assert_eq!(
                    signature.hessian_determinant_hand,
                    PhaseHand::of(&determinant)
                );
            }
        }
        assert_eq!(
            named,
            standing.germs.keys().copied().collect::<BTreeSet<_>>(),
            "the passage population is the germ population, seen through the signatures"
        );

        // And the standing now refuses a population that disagrees with its germs. A count could
        // not have been checked at all.
        let signature = standing
            .germ_populations
            .keys()
            .next()
            .expect("a live control")
            .clone();
        let absent = ReceiverPhaseGermId(u64::MAX);
        let mut corrupt = standing.clone();
        corrupt
            .germ_populations
            .get_mut(&signature)
            .expect("the passage stands")
            .insert(absent);
        assert!(matches!(
            corrupt.validate(),
            Err(ReceiverPhaseAtlasError::GermPassageMismatch(germ)) if germ == absent
        ));

        let mut emptied = standing.clone();
        emptied
            .germ_populations
            .get_mut(&signature)
            .expect("the passage stands")
            .clear();
        assert!(matches!(
            emptied.validate(),
            Err(ReceiverPhaseAtlasError::EmptyGermPassage)
        ));
        assert!(
            standing.validate().is_ok(),
            "and the honest standing passes"
        );
    }
}
