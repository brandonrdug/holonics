//! Sparse exact current through a caused body with reactive boundary storage.
//!
//! The analytic wave and advection laws already carry exact current on
//! declared geometries.  This module owns the feedback seam between passages:
//! a reached source cell can split an arriving current into outgoing
//! passages, retained boundary current, and material current; the resulting
//! local state reforms the constitutive operator used by the next arrival.
//!
//! A traversal event advances only scheduled fronts.  Positive passage delay
//! and an explicit receiver chronology make the event finite without an
//! iteration cap.  Current which has not reached the receiver horizon remains
//! in standing as an open frontier.  It is neither discarded nor turned into
//! a display frame.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    CausalBodyStanding, CausalCellId, EventId, EventSuccessor, ExactEventLaw, ExactLinearError,
    ExactRatMatrix,
};

const STANDING_SCHEMA: &str = "holonic-engine.exact-causal-traversal-standing.v1";
const RADIATION_SCHEMA: &str = "holonic-engine.exact-causal-traversal-radiation.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CausalTraversalPassageId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CausalTraversalSpeciesId(pub u64);

/// One distinct current species in the shared traveling fiber.
///
/// Concatenation is a carrier layout only.  Species retain separate names,
/// dimensional units, extents, constitutive balances, and receiver
/// interpretation; coordinates from unlike species do not become commensurate
/// merely because one exact passage carries them together.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactTraversalCurrentSpecies {
    pub id: CausalTraversalSpeciesId,
    pub name: String,
    pub unit: String,
    pub extent: usize,
}

/// A directed restriction of one caused source carrier.
///
/// The carrier may have arbitrary grade.  Both endpoint cells must already
/// occur in its source boundary; this law never infers a passage from
/// projected proximity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactCausalTraversalPassage {
    pub id: CausalTraversalPassageId,
    pub name: String,
    pub carrier: CausalCellId,
    pub from: CausalCellId,
    pub to: CausalCellId,
    pub delay: u64,
    pub transport: ExactRatMatrix,
    pub linear_balances: Vec<ExactTraversalLinearBalance>,
    pub quadratic_balances: Vec<ExactTraversalQuadraticBalance>,
}

/// One exact linear conserved current.
///
/// The two covectors act on the complete local physical input and output.
/// Construction proves `output_covector * T(lambda) = input_covector` for the
/// complete affine constitutive family.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactTraversalLinearBalance {
    pub name: String,
    pub input_covector: Vec<Rat>,
    pub output_covector: Vec<Rat>,
}

/// One exact quadratic conserved current.
///
/// Construction proves
/// `T(lambda)^T output_form T(lambda) = input_form` identically in every
/// morphology coordinate.  This admits phase norm and energy-like ledgers
/// without silently reducing them to component sums.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactTraversalQuadraticBalance {
    pub name: String,
    pub input_form: ExactRatMatrix,
    pub output_form: ExactRatMatrix,
}

/// The local intermediate law at one caused cell.
///
/// Physical input is ordered as
/// `[arriving travel | retained storage | material]`.
/// Physical output is ordered as
/// `[one travel block per outgoing passage | retained storage | material]`.
///
/// `base_operator + sum(lambda_i * morphology_operators_i)` is therefore the
/// contemporary constitutive map.  Feedback receives
/// `[lambda_before | storage_after | material_after]` and produces the exact
/// morphology coordinates used on the next passage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactReactiveTraversalInteraction {
    pub cell: CausalCellId,
    pub name: String,
    pub storage_extent: usize,
    pub material_extent: usize,
    pub morphology_extent: usize,
    pub base_operator: ExactRatMatrix,
    pub morphology_operators: Vec<ExactRatMatrix>,
    pub feedback: ExactRatMatrix,
    pub linear_balances: Vec<ExactTraversalLinearBalance>,
    pub quadratic_balances: Vec<ExactTraversalQuadraticBalance>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactReactiveTraversalState {
    pub retained_storage: Vec<Rat>,
    pub material_current: Vec<Rat>,
    pub morphology: Vec<Rat>,
    pub last_changed_by: Option<EventId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ExactTraversalFrontAddress {
    pub chronology: u64,
    pub site: CausalCellId,
}

/// Co-present current at one source cell and chronology.
///
/// Equal-address arrivals have already superposed.  `awake` remains true for
/// a caused zero-valued impulse so retained boundary current can be released
/// without fabricating a nonzero traveling source.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactTraversalScheduledFront {
    pub current: Vec<Rat>,
    pub positive_current: Vec<Rat>,
    pub negative_current: Vec<Rat>,
    pub arrival_population: u64,
    pub causes: BTreeSet<EventId>,
    pub awake: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactCausalTraversalStanding {
    pub schema: String,
    pub sites: BTreeMap<CausalCellId, ExactReactiveTraversalState>,
    pending: BTreeMap<ExactTraversalFrontAddress, ExactTraversalScheduledFront>,
    used_events: BTreeSet<EventId>,
    last_event_chronology: Option<u64>,
    last_receiver_horizon: Option<u64>,
}

impl ExactCausalTraversalStanding {
    pub fn pending_frontier(
        &self,
    ) -> &BTreeMap<ExactTraversalFrontAddress, ExactTraversalScheduledFront> {
        &self.pending
    }

    pub fn is_at_rest(&self) -> bool {
        self.pending.is_empty()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactCausalTraversalImpulse {
    pub arrival_chronology: u64,
    pub site: CausalCellId,
    pub current: Vec<Rat>,
    pub causes: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactCausalTraversalEvent {
    pub event: EventId,
    /// Orders complete receiver intervals.  This is not the physical arrival
    /// time carried by an impulse or passage.
    pub event_chronology: u64,
    /// The participating receiver's inclusive physical chronology cut.
    pub receiver_horizon: u64,
    pub impulses: Vec<ExactCausalTraversalImpulse>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactTraversalBalanceKind {
    Linear,
    Quadratic,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactTraversalBalanceReceipt {
    pub name: String,
    pub kind: ExactTraversalBalanceKind,
    pub before: Rat,
    pub after: Rat,
    pub residual: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactTraversalDeparture {
    pub passage: CausalTraversalPassageId,
    pub target: CausalCellId,
    pub arrival_chronology: u64,
    pub current: Vec<Rat>,
    pub balances: Vec<ExactTraversalBalanceReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactTraversalInteractionReceipt {
    pub chronology: u64,
    pub site: CausalCellId,
    pub causes: BTreeSet<EventId>,
    pub arriving_current: Vec<Rat>,
    pub arriving_positive_current: Vec<Rat>,
    pub arriving_negative_current: Vec<Rat>,
    pub arrival_population: u64,
    pub storage_before: Vec<Rat>,
    pub storage_after: Vec<Rat>,
    pub material_before: Vec<Rat>,
    pub material_after: Vec<Rat>,
    pub morphology_before: Vec<Rat>,
    pub morphology_after: Vec<Rat>,
    pub departures: Vec<ExactTraversalDeparture>,
    pub balances: Vec<ExactTraversalBalanceReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactCausalTraversalRadiation {
    pub schema: String,
    pub event: EventId,
    pub event_chronology: u64,
    pub previous_receiver_horizon: Option<u64>,
    pub receiver_horizon: u64,
    pub interactions: Vec<ExactTraversalInteractionReceipt>,
    pub reached_sites: BTreeSet<CausalCellId>,
    pub pending_frontier: BTreeMap<ExactTraversalFrontAddress, ExactTraversalScheduledFront>,
    pub rested: bool,
}

/// A caused body plus its local constitutive interactions and directed
/// passages.  The body remains the source authority; this owner carries only
/// the exact traversal realization.
#[derive(Clone, Debug)]
pub struct ExactCausalTraversalLaw {
    body: CausalBodyStanding,
    species: Vec<ExactTraversalCurrentSpecies>,
    travel_extent: usize,
    interactions: BTreeMap<CausalCellId, ExactReactiveTraversalInteraction>,
    passages: BTreeMap<CausalTraversalPassageId, ExactCausalTraversalPassage>,
    outgoing: BTreeMap<CausalCellId, Vec<CausalTraversalPassageId>>,
}

impl ExactCausalTraversalLaw {
    pub fn new(
        body: CausalBodyStanding,
        species: Vec<ExactTraversalCurrentSpecies>,
        interactions: Vec<ExactReactiveTraversalInteraction>,
        passages: Vec<ExactCausalTraversalPassage>,
    ) -> Result<Self, CausalTraversalError> {
        if species.is_empty() || interactions.is_empty() {
            return Err(CausalTraversalError::EmptyTraversalWorld);
        }
        let mut species_ids = BTreeSet::new();
        let mut travel_extent = 0_usize;
        for body in &species {
            if body.extent == 0
                || body.name.trim().is_empty()
                || body.unit.trim().is_empty()
                || !species_ids.insert(body.id)
            {
                return Err(CausalTraversalError::MalformedSpecies(body.id));
            }
            travel_extent = travel_extent
                .checked_add(body.extent)
                .ok_or(CausalTraversalError::CarrierOverflow)?;
        }
        let mut interaction_index = BTreeMap::new();
        for interaction in interactions {
            let cell = interaction.cell;
            if interaction_index.insert(cell, interaction).is_some() {
                return Err(CausalTraversalError::DuplicateInteraction(cell));
            }
        }
        let mut passage_index = BTreeMap::new();
        let mut outgoing = BTreeMap::<CausalCellId, Vec<CausalTraversalPassageId>>::new();
        for passage in passages {
            if passage_index.contains_key(&passage.id) {
                return Err(CausalTraversalError::DuplicatePassage(passage.id));
            }
            validate_passage(&body, travel_extent, &interaction_index, &passage)?;
            outgoing.entry(passage.from).or_default().push(passage.id);
            passage_index.insert(passage.id, passage);
        }
        for passage_ids in outgoing.values_mut() {
            passage_ids.sort();
        }
        for (cell, interaction) in &interaction_index {
            let outgoing_extent = outgoing.get(cell).map_or(0, Vec::len);
            validate_interaction(travel_extent, outgoing_extent, interaction)?;
        }
        let law = Self {
            body,
            species,
            travel_extent,
            interactions: interaction_index,
            passages: passage_index,
            outgoing,
        };
        law.validate_standing(&law.initial_standing())?;
        Ok(law)
    }

    pub fn body(&self) -> &CausalBodyStanding {
        &self.body
    }

    pub fn travel_extent(&self) -> usize {
        self.travel_extent
    }

    pub fn species(&self) -> &[ExactTraversalCurrentSpecies] {
        &self.species
    }

    pub fn interactions(&self) -> &BTreeMap<CausalCellId, ExactReactiveTraversalInteraction> {
        &self.interactions
    }

    pub fn passages(&self) -> &BTreeMap<CausalTraversalPassageId, ExactCausalTraversalPassage> {
        &self.passages
    }

    pub fn initial_standing(&self) -> ExactCausalTraversalStanding {
        let mut sites = BTreeMap::new();
        for (cell, interaction) in &self.interactions {
            sites.insert(
                *cell,
                ExactReactiveTraversalState {
                    retained_storage: vec![Rat::zero(); interaction.storage_extent],
                    material_current: vec![Rat::zero(); interaction.material_extent],
                    morphology: vec![Rat::zero(); interaction.morphology_extent],
                    last_changed_by: None,
                },
            );
        }
        ExactCausalTraversalStanding {
            schema: STANDING_SCHEMA.to_owned(),
            sites,
            pending: BTreeMap::new(),
            used_events: BTreeSet::new(),
            last_event_chronology: None,
            last_receiver_horizon: None,
        }
    }

    pub fn validate_standing(
        &self,
        standing: &ExactCausalTraversalStanding,
    ) -> Result<(), CausalTraversalError> {
        if standing.schema != STANDING_SCHEMA || standing.sites.len() != self.interactions.len() {
            return Err(CausalTraversalError::MalformedStanding);
        }
        for (cell, interaction) in &self.interactions {
            let state = standing
                .sites
                .get(cell)
                .ok_or(CausalTraversalError::MalformedStanding)?;
            if state.retained_storage.len() != interaction.storage_extent
                || state.material_current.len() != interaction.material_extent
                || state.morphology.len() != interaction.morphology_extent
            {
                return Err(CausalTraversalError::MalformedStanding);
            }
        }
        for (address, front) in &standing.pending {
            if !self.interactions.contains_key(&address.site)
                || front.current.len() != self.travel_extent
                || front.positive_current.len() != self.travel_extent
                || front.negative_current.len() != self.travel_extent
                || front.arrival_population == 0
                || (!front.awake && vector_is_zero(&front.current))
                || front.causes.is_empty()
                || standing
                    .last_receiver_horizon
                    .is_some_and(|horizon| address.chronology <= horizon)
            {
                return Err(CausalTraversalError::MalformedStanding);
            }
            for axis in 0..self.travel_extent {
                if front.positive_current[axis].is_negative()
                    || front.negative_current[axis].is_negative()
                    || &front.positive_current[axis] - &front.negative_current[axis]
                        != front.current[axis]
                {
                    return Err(CausalTraversalError::MalformedStanding);
                }
            }
        }
        Ok(())
    }

    fn enact_event(
        &self,
        standing_before: &ExactCausalTraversalStanding,
        event: &ExactCausalTraversalEvent,
    ) -> Result<
        EventSuccessor<ExactCausalTraversalStanding, ExactCausalTraversalRadiation>,
        CausalTraversalError,
    > {
        self.validate_standing(standing_before)?;
        if standing_before.used_events.contains(&event.event) {
            return Err(CausalTraversalError::RepeatedEvent(event.event));
        }
        if standing_before
            .last_event_chronology
            .is_some_and(|chronology| event.event_chronology <= chronology)
        {
            return Err(CausalTraversalError::NonincreasingEventChronology);
        }
        if standing_before
            .last_receiver_horizon
            .is_some_and(|horizon| event.receiver_horizon <= horizon)
        {
            return Err(CausalTraversalError::NonincreasingReceiverHorizon);
        }

        let previous_receiver_horizon = standing_before.last_receiver_horizon;
        let lower_bound = previous_receiver_horizon.map_or(0, |horizon| horizon.saturating_add(1));
        let mut standing = standing_before.clone();
        for impulse in &event.impulses {
            if impulse.arrival_chronology < lower_bound
                || impulse.arrival_chronology > event.receiver_horizon
                || impulse.current.len() != self.travel_extent
                || impulse.causes.is_empty()
                || !self.interactions.contains_key(&impulse.site)
            {
                return Err(CausalTraversalError::MalformedImpulse);
            }
            schedule_front(
                &mut standing.pending,
                ExactTraversalFrontAddress {
                    chronology: impulse.arrival_chronology,
                    site: impulse.site,
                },
                &impulse.current,
                &impulse.causes,
                true,
            )?;
        }

        let mut interactions = Vec::new();
        let mut reached_sites = BTreeSet::new();
        loop {
            let Some((&address, _)) = standing.pending.first_key_value() else {
                break;
            };
            if address.chronology > event.receiver_horizon {
                break;
            }
            let front = standing
                .pending
                .remove(&address)
                .ok_or(CausalTraversalError::MalformedStanding)?;
            let interaction = self
                .interactions
                .get(&address.site)
                .ok_or(CausalTraversalError::UnknownInteraction(address.site))?;
            let state_before = standing
                .sites
                .get(&address.site)
                .cloned()
                .ok_or(CausalTraversalError::MalformedStanding)?;
            let outcome = self.interact(address, interaction, &state_before, &front)?;
            let mut state_after = outcome.state_after;
            state_after.last_changed_by = Some(event.event);
            standing.sites.insert(address.site, state_after);
            for departure in &outcome.receipt.departures {
                schedule_front(
                    &mut standing.pending,
                    ExactTraversalFrontAddress {
                        chronology: departure.arrival_chronology,
                        site: departure.target,
                    },
                    &departure.current,
                    &front.causes,
                    true,
                )?;
            }
            reached_sites.insert(address.site);
            interactions.push(outcome.receipt);
        }

        standing.used_events.insert(event.event);
        standing.last_event_chronology = Some(event.event_chronology);
        standing.last_receiver_horizon = Some(event.receiver_horizon);
        self.validate_standing(&standing)?;
        let radiation = ExactCausalTraversalRadiation {
            schema: RADIATION_SCHEMA.to_owned(),
            event: event.event,
            event_chronology: event.event_chronology,
            previous_receiver_horizon,
            receiver_horizon: event.receiver_horizon,
            interactions,
            reached_sites,
            pending_frontier: standing.pending.clone(),
            rested: standing.pending.is_empty(),
        };
        Ok(EventSuccessor {
            standing_after: standing,
            radiation: vec![radiation],
            logical_resources: None,
            physical_resources: None,
        })
    }

    fn interact(
        &self,
        address: ExactTraversalFrontAddress,
        interaction: &ExactReactiveTraversalInteraction,
        state_before: &ExactReactiveTraversalState,
        front: &ExactTraversalScheduledFront,
    ) -> Result<TraversalOutcome, CausalTraversalError> {
        let outgoing_ids = self
            .outgoing
            .get(&address.site)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let operator = evaluated_operator(interaction, &state_before.morphology)?;
        let mut physical_input = Vec::with_capacity(
            self.travel_extent + interaction.storage_extent + interaction.material_extent,
        );
        physical_input.extend_from_slice(&front.current);
        physical_input.extend_from_slice(&state_before.retained_storage);
        physical_input.extend_from_slice(&state_before.material_current);
        let physical_output = operator.apply(&physical_input)?;

        let travel_output_extent = outgoing_ids
            .len()
            .checked_mul(self.travel_extent)
            .ok_or(CausalTraversalError::CarrierOverflow)?;
        let storage_start = travel_output_extent;
        let material_start = storage_start
            .checked_add(interaction.storage_extent)
            .ok_or(CausalTraversalError::CarrierOverflow)?;
        let storage_after = physical_output[storage_start..material_start].to_vec();
        let material_after =
            physical_output[material_start..material_start + interaction.material_extent].to_vec();

        let mut feedback_input = Vec::with_capacity(
            interaction.morphology_extent
                + interaction.storage_extent
                + interaction.material_extent,
        );
        feedback_input.extend_from_slice(&state_before.morphology);
        feedback_input.extend_from_slice(&storage_after);
        feedback_input.extend_from_slice(&material_after);
        let morphology_after = interaction.feedback.apply(&feedback_input)?;

        let mut departures = Vec::new();
        for (ordinal, passage_id) in outgoing_ids.iter().enumerate() {
            let start = ordinal
                .checked_mul(self.travel_extent)
                .ok_or(CausalTraversalError::CarrierOverflow)?;
            let local_current = &physical_output[start..start + self.travel_extent];
            if vector_is_zero(local_current) {
                continue;
            }
            let passage = self
                .passages
                .get(passage_id)
                .ok_or(CausalTraversalError::UnknownPassage(*passage_id))?;
            let transported = passage.transport.apply(local_current)?;
            let passage_balances = passage_balance_receipts(passage, local_current, &transported)?;
            let arrival_chronology = address
                .chronology
                .checked_add(passage.delay)
                .ok_or(CausalTraversalError::ChronologyOverflow)?;
            departures.push(ExactTraversalDeparture {
                passage: *passage_id,
                target: passage.to,
                arrival_chronology,
                current: transported,
                balances: passage_balances,
            });
        }

        let balances = balance_receipts(interaction, &physical_input, &physical_output)?;
        let receipt = ExactTraversalInteractionReceipt {
            chronology: address.chronology,
            site: address.site,
            causes: front.causes.clone(),
            arriving_current: front.current.clone(),
            arriving_positive_current: front.positive_current.clone(),
            arriving_negative_current: front.negative_current.clone(),
            arrival_population: front.arrival_population,
            storage_before: state_before.retained_storage.clone(),
            storage_after: storage_after.clone(),
            material_before: state_before.material_current.clone(),
            material_after: material_after.clone(),
            morphology_before: state_before.morphology.clone(),
            morphology_after: morphology_after.clone(),
            departures,
            balances,
        };
        Ok(TraversalOutcome {
            state_after: ExactReactiveTraversalState {
                retained_storage: storage_after,
                material_current: material_after,
                morphology: morphology_after,
                last_changed_by: state_before.last_changed_by,
            },
            receipt,
        })
    }
}

impl ExactEventLaw for ExactCausalTraversalLaw {
    type Standing = ExactCausalTraversalStanding;
    type Event = ExactCausalTraversalEvent;
    type Radiation = ExactCausalTraversalRadiation;
    type Error = CausalTraversalError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        self.enact_event(standing_before, event)
    }
}

struct TraversalOutcome {
    state_after: ExactReactiveTraversalState,
    receipt: ExactTraversalInteractionReceipt,
}

fn validate_passage(
    body: &CausalBodyStanding,
    travel_extent: usize,
    interactions: &BTreeMap<CausalCellId, ExactReactiveTraversalInteraction>,
    passage: &ExactCausalTraversalPassage,
) -> Result<(), CausalTraversalError> {
    if passage.delay == 0
        || passage.from == passage.to
        || passage.transport.rows() != travel_extent
        || passage.transport.columns() != travel_extent
        || (passage.linear_balances.is_empty() && passage.quadratic_balances.is_empty())
        || !interactions.contains_key(&passage.from)
        || !interactions.contains_key(&passage.to)
        || !body.active_cells().contains(&passage.carrier)
        || !body.active_cells().contains(&passage.from)
        || !body.active_cells().contains(&passage.to)
    {
        return Err(CausalTraversalError::MalformedPassage(passage.id));
    }
    let carrier = body.incidence.cell(passage.carrier)?;
    let support = carrier.boundary.support();
    if !support.contains(&passage.from) || !support.contains(&passage.to) {
        return Err(CausalTraversalError::PassageLeavesSourceBoundary(
            passage.id,
        ));
    }
    passage
        .transport
        .inverse()
        .map_err(|_| CausalTraversalError::NoninvertiblePassage(passage.id))?;
    for balance in &passage.linear_balances {
        if balance.input_covector.len() != travel_extent
            || balance.output_covector.len() != travel_extent
        {
            return Err(CausalTraversalError::MalformedPassageLinearBalance {
                passage: passage.id,
                name: balance.name.clone(),
            });
        }
        if covector_times_matrix(&balance.output_covector, &passage.transport)?
            != balance.input_covector
        {
            return Err(CausalTraversalError::UnbalancedPassage {
                passage: passage.id,
                name: balance.name.clone(),
            });
        }
    }
    for balance in &passage.quadratic_balances {
        if balance.input_form.rows() != travel_extent
            || balance.input_form.columns() != travel_extent
            || balance.output_form.rows() != travel_extent
            || balance.output_form.columns() != travel_extent
            || balance.input_form.transpose()? != balance.input_form
            || balance.output_form.transpose()? != balance.output_form
            || quadratic_pullback(&passage.transport, &balance.output_form)? != balance.input_form
        {
            return Err(CausalTraversalError::UnbalancedPassage {
                passage: passage.id,
                name: balance.name.clone(),
            });
        }
    }
    Ok(())
}

fn validate_interaction(
    travel_extent: usize,
    outgoing_count: usize,
    interaction: &ExactReactiveTraversalInteraction,
) -> Result<(), CausalTraversalError> {
    if interaction.morphology_operators.len() != interaction.morphology_extent
        || (interaction.linear_balances.is_empty() && interaction.quadratic_balances.is_empty())
    {
        return Err(CausalTraversalError::MalformedInteraction(interaction.cell));
    }
    let input_extent = travel_extent
        .checked_add(interaction.storage_extent)
        .and_then(|extent| extent.checked_add(interaction.material_extent))
        .ok_or(CausalTraversalError::CarrierOverflow)?;
    let output_extent = outgoing_count
        .checked_mul(travel_extent)
        .and_then(|extent| extent.checked_add(interaction.storage_extent))
        .and_then(|extent| extent.checked_add(interaction.material_extent))
        .ok_or(CausalTraversalError::CarrierOverflow)?;
    if interaction.base_operator.rows() != output_extent
        || interaction.base_operator.columns() != input_extent
        || interaction.feedback.rows() != interaction.morphology_extent
        || interaction.feedback.columns()
            != interaction.morphology_extent
                + interaction.storage_extent
                + interaction.material_extent
        || interaction
            .morphology_operators
            .iter()
            .any(|operator| operator.rows() != output_extent || operator.columns() != input_extent)
    {
        return Err(CausalTraversalError::MalformedInteraction(interaction.cell));
    }

    for balance in &interaction.linear_balances {
        if balance.input_covector.len() != input_extent
            || balance.output_covector.len() != output_extent
        {
            return Err(CausalTraversalError::MalformedLinearBalance {
                cell: interaction.cell,
                name: balance.name.clone(),
            });
        }
        let base_pullback =
            covector_times_matrix(&balance.output_covector, &interaction.base_operator)?;
        if base_pullback != balance.input_covector {
            return Err(CausalTraversalError::UnbalancedLinearFamily {
                cell: interaction.cell,
                name: balance.name.clone(),
            });
        }
        for operator in &interaction.morphology_operators {
            if !vector_is_zero(&covector_times_matrix(&balance.output_covector, operator)?) {
                return Err(CausalTraversalError::UnbalancedLinearFamily {
                    cell: interaction.cell,
                    name: balance.name.clone(),
                });
            }
        }
    }

    for balance in &interaction.quadratic_balances {
        validate_quadratic_balance(interaction, balance, input_extent, output_extent)?;
    }
    Ok(())
}

fn validate_quadratic_balance(
    interaction: &ExactReactiveTraversalInteraction,
    balance: &ExactTraversalQuadraticBalance,
    input_extent: usize,
    output_extent: usize,
) -> Result<(), CausalTraversalError> {
    if balance.input_form.rows() != input_extent
        || balance.input_form.columns() != input_extent
        || balance.output_form.rows() != output_extent
        || balance.output_form.columns() != output_extent
        || balance.input_form.transpose()? != balance.input_form
        || balance.output_form.transpose()? != balance.output_form
    {
        return Err(CausalTraversalError::MalformedQuadraticBalance {
            cell: interaction.cell,
            name: balance.name.clone(),
        });
    }
    let base_pullback = quadratic_pullback(&interaction.base_operator, &balance.output_form)?;
    if base_pullback != balance.input_form {
        return Err(CausalTraversalError::UnbalancedQuadraticFamily {
            cell: interaction.cell,
            name: balance.name.clone(),
        });
    }
    for (left_ordinal, left) in interaction.morphology_operators.iter().enumerate() {
        let linear_left =
            mixed_quadratic_pullback(&interaction.base_operator, left, &balance.output_form)?;
        let linear_right =
            mixed_quadratic_pullback(left, &interaction.base_operator, &balance.output_form)?;
        if !matrix_is_zero(&linear_left.add(&linear_right)?) {
            return Err(CausalTraversalError::UnbalancedQuadraticFamily {
                cell: interaction.cell,
                name: balance.name.clone(),
            });
        }
        for right in &interaction.morphology_operators[left_ordinal..] {
            let quadratic_left = mixed_quadratic_pullback(left, right, &balance.output_form)?;
            let quadratic_right = mixed_quadratic_pullback(right, left, &balance.output_form)?;
            if !matrix_is_zero(&quadratic_left.add(&quadratic_right)?) {
                return Err(CausalTraversalError::UnbalancedQuadraticFamily {
                    cell: interaction.cell,
                    name: balance.name.clone(),
                });
            }
        }
    }
    Ok(())
}

fn evaluated_operator(
    interaction: &ExactReactiveTraversalInteraction,
    morphology: &[Rat],
) -> Result<ExactRatMatrix, CausalTraversalError> {
    if morphology.len() != interaction.morphology_extent {
        return Err(CausalTraversalError::MalformedStanding);
    }
    let mut operator = interaction.base_operator.clone();
    for (coordinate, response) in morphology.iter().zip(&interaction.morphology_operators) {
        if coordinate.is_zero() {
            continue;
        }
        operator = operator.add(&response.scaled(coordinate))?;
    }
    Ok(operator)
}

fn balance_receipts(
    interaction: &ExactReactiveTraversalInteraction,
    input: &[Rat],
    output: &[Rat],
) -> Result<Vec<ExactTraversalBalanceReceipt>, CausalTraversalError> {
    let mut receipts = Vec::with_capacity(
        interaction.linear_balances.len() + interaction.quadratic_balances.len(),
    );
    for balance in &interaction.linear_balances {
        let before = dot(&balance.input_covector, input)?;
        let after = dot(&balance.output_covector, output)?;
        let residual = &after - &before;
        if !residual.is_zero() {
            return Err(CausalTraversalError::RuntimeBalanceFailure {
                cell: interaction.cell,
                name: balance.name.clone(),
            });
        }
        receipts.push(ExactTraversalBalanceReceipt {
            name: balance.name.clone(),
            kind: ExactTraversalBalanceKind::Linear,
            before,
            after,
            residual,
        });
    }
    for balance in &interaction.quadratic_balances {
        let before = quadratic_value(&balance.input_form, input)?;
        let after = quadratic_value(&balance.output_form, output)?;
        let residual = &after - &before;
        if !residual.is_zero() {
            return Err(CausalTraversalError::RuntimeBalanceFailure {
                cell: interaction.cell,
                name: balance.name.clone(),
            });
        }
        receipts.push(ExactTraversalBalanceReceipt {
            name: balance.name.clone(),
            kind: ExactTraversalBalanceKind::Quadratic,
            before,
            after,
            residual,
        });
    }
    Ok(receipts)
}

fn passage_balance_receipts(
    passage: &ExactCausalTraversalPassage,
    input: &[Rat],
    output: &[Rat],
) -> Result<Vec<ExactTraversalBalanceReceipt>, CausalTraversalError> {
    let mut receipts =
        Vec::with_capacity(passage.linear_balances.len() + passage.quadratic_balances.len());
    for balance in &passage.linear_balances {
        let before = dot(&balance.input_covector, input)?;
        let after = dot(&balance.output_covector, output)?;
        let residual = &after - &before;
        if !residual.is_zero() {
            return Err(CausalTraversalError::PassageRuntimeBalanceFailure {
                passage: passage.id,
                name: balance.name.clone(),
            });
        }
        receipts.push(ExactTraversalBalanceReceipt {
            name: balance.name.clone(),
            kind: ExactTraversalBalanceKind::Linear,
            before,
            after,
            residual,
        });
    }
    for balance in &passage.quadratic_balances {
        let before = quadratic_value(&balance.input_form, input)?;
        let after = quadratic_value(&balance.output_form, output)?;
        let residual = &after - &before;
        if !residual.is_zero() {
            return Err(CausalTraversalError::PassageRuntimeBalanceFailure {
                passage: passage.id,
                name: balance.name.clone(),
            });
        }
        receipts.push(ExactTraversalBalanceReceipt {
            name: balance.name.clone(),
            kind: ExactTraversalBalanceKind::Quadratic,
            before,
            after,
            residual,
        });
    }
    Ok(receipts)
}

fn schedule_front(
    pending: &mut BTreeMap<ExactTraversalFrontAddress, ExactTraversalScheduledFront>,
    address: ExactTraversalFrontAddress,
    current: &[Rat],
    causes: &BTreeSet<EventId>,
    awake: bool,
) -> Result<(), CausalTraversalError> {
    let front = pending
        .entry(address)
        .or_insert_with(|| ExactTraversalScheduledFront {
            current: vec![Rat::zero(); current.len()],
            positive_current: vec![Rat::zero(); current.len()],
            negative_current: vec![Rat::zero(); current.len()],
            arrival_population: 0,
            causes: BTreeSet::new(),
            awake: false,
        });
    if front.current.len() != current.len() {
        return Err(CausalTraversalError::MalformedStanding);
    }
    for (axis, (target, value)) in front.current.iter_mut().zip(current).enumerate() {
        *target += value;
        if value.is_positive() {
            front.positive_current[axis] += value;
        } else if value.is_negative() {
            front.negative_current[axis] -= value;
        }
    }
    front.arrival_population = front
        .arrival_population
        .checked_add(1)
        .ok_or(CausalTraversalError::CarrierOverflow)?;
    front.causes.extend(causes);
    front.awake |= awake;
    Ok(())
}

fn covector_times_matrix(
    covector: &[Rat],
    matrix: &ExactRatMatrix,
) -> Result<Vec<Rat>, CausalTraversalError> {
    if covector.len() != matrix.rows() {
        return Err(CausalTraversalError::Linear(
            ExactLinearError::ShapeMismatch,
        ));
    }
    let mut result = vec![Rat::zero(); matrix.columns()];
    for (row, coefficient) in covector.iter().enumerate() {
        if coefficient.is_zero() {
            continue;
        }
        for (column, target) in result.iter_mut().enumerate() {
            *target += coefficient * matrix.get(row, column)?;
        }
    }
    Ok(result)
}

fn quadratic_pullback(
    operator: &ExactRatMatrix,
    form: &ExactRatMatrix,
) -> Result<ExactRatMatrix, CausalTraversalError> {
    Ok(operator.transpose()?.multiply(form)?.multiply(operator)?)
}

fn mixed_quadratic_pullback(
    left: &ExactRatMatrix,
    right: &ExactRatMatrix,
    form: &ExactRatMatrix,
) -> Result<ExactRatMatrix, CausalTraversalError> {
    Ok(left.transpose()?.multiply(form)?.multiply(right)?)
}

fn quadratic_value(form: &ExactRatMatrix, vector: &[Rat]) -> Result<Rat, CausalTraversalError> {
    let transformed = form.apply(vector)?;
    dot(vector, &transformed)
}

fn dot(left: &[Rat], right: &[Rat]) -> Result<Rat, CausalTraversalError> {
    if left.len() != right.len() {
        return Err(CausalTraversalError::Linear(
            ExactLinearError::ShapeMismatch,
        ));
    }
    let mut result = Rat::zero();
    for (left, right) in left.iter().zip(right) {
        result += left * right;
    }
    Ok(result)
}

fn vector_is_zero(vector: &[Rat]) -> bool {
    vector.iter().all(Zero::is_zero)
}

fn matrix_is_zero(matrix: &ExactRatMatrix) -> bool {
    matrix.entries().iter().all(Zero::is_zero)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum CausalTraversalError {
    #[error(transparent)]
    Algebraic(#[from] crate::CausalAlgebraicError),
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error("an exact causal traversal needs a nonzero traveling fiber and local interactions")]
    EmptyTraversalWorld,
    #[error("causal traversal current species {0:?} is duplicated or empty")]
    MalformedSpecies(CausalTraversalSpeciesId),
    #[error("causal traversal interaction at {0:?} was declared twice")]
    DuplicateInteraction(CausalCellId),
    #[error("causal traversal interaction at {0:?} is unknown")]
    UnknownInteraction(CausalCellId),
    #[error("causal traversal interaction at {0:?} is malformed")]
    MalformedInteraction(CausalCellId),
    #[error("causal traversal passage {0:?} was declared twice")]
    DuplicatePassage(CausalTraversalPassageId),
    #[error("causal traversal passage {0:?} is unknown")]
    UnknownPassage(CausalTraversalPassageId),
    #[error("causal traversal passage {0:?} is malformed")]
    MalformedPassage(CausalTraversalPassageId),
    #[error("causal traversal passage {0:?} does not carry an invertible exact rebase")]
    NoninvertiblePassage(CausalTraversalPassageId),
    #[error("causal traversal passage {0:?} leaves its source carrier boundary")]
    PassageLeavesSourceBoundary(CausalTraversalPassageId),
    #[error("linear passage balance {name:?} on {passage:?} is malformed")]
    MalformedPassageLinearBalance {
        passage: CausalTraversalPassageId,
        name: String,
    },
    #[error("passage balance {name:?} on {passage:?} is not preserved by its transport")]
    UnbalancedPassage {
        passage: CausalTraversalPassageId,
        name: String,
    },
    #[error("runtime passage balance {name:?} on {passage:?} failed after exact construction")]
    PassageRuntimeBalanceFailure {
        passage: CausalTraversalPassageId,
        name: String,
    },
    #[error("linear balance {name:?} at {cell:?} is malformed")]
    MalformedLinearBalance { cell: CausalCellId, name: String },
    #[error("linear balance {name:?} at {cell:?} does not hold across the morphology family")]
    UnbalancedLinearFamily { cell: CausalCellId, name: String },
    #[error("quadratic balance {name:?} at {cell:?} is malformed")]
    MalformedQuadraticBalance { cell: CausalCellId, name: String },
    #[error("quadratic balance {name:?} at {cell:?} does not hold across the morphology family")]
    UnbalancedQuadraticFamily { cell: CausalCellId, name: String },
    #[error("runtime balance {name:?} at {cell:?} failed after exact construction")]
    RuntimeBalanceFailure { cell: CausalCellId, name: String },
    #[error("the exact causal traversal standing is malformed")]
    MalformedStanding,
    #[error("causal traversal event {0:?} already occurred")]
    RepeatedEvent(EventId),
    #[error("causal traversal event chronology did not increase")]
    NonincreasingEventChronology,
    #[error("causal traversal receiver horizon did not increase")]
    NonincreasingReceiverHorizon,
    #[error("a causal traversal impulse is malformed")]
    MalformedImpulse,
    #[error("causal traversal chronology overflowed")]
    ChronologyOverflow,
    #[error("a causal traversal carrier extent overflowed")]
    CarrierOverflow,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CausalBodyDeed, CausalBodyEvent, CausalCellReference, ComparativeMultiplicity,
        EventBoundaryTerm, ExactCausalBodyLaw,
    };
    use num_bigint::BigInt;
    use num_traits::One;

    fn half() -> Rat {
        Rat::new(BigInt::one(), BigInt::from(2))
    }

    fn scalar_species() -> Vec<ExactTraversalCurrentSpecies> {
        vec![ExactTraversalCurrentSpecies {
            id: CausalTraversalSpeciesId(1),
            name: "test signed current".to_owned(),
            unit: "test unit".to_owned(),
            extent: 1,
        }]
    }

    fn source_body() -> (CausalBodyStanding, CausalCellId, CausalCellId, CausalCellId) {
        let law = ExactCausalBodyLaw;
        let successor = law
            .enact(
                &CausalBodyStanding::default(),
                &CausalBodyEvent {
                    event: EventId(1),
                    chronology: 1,
                    deeds: vec![
                        CausalBodyDeed::FoundCell {
                            local: crate::EventCellId(1),
                            name: "source".to_owned(),
                            grade: 0,
                            boundary: Vec::new(),
                        },
                        CausalBodyDeed::FoundCell {
                            local: crate::EventCellId(2),
                            name: "receiver".to_owned(),
                            grade: 0,
                            boundary: Vec::new(),
                        },
                        CausalBodyDeed::FoundCell {
                            local: crate::EventCellId(3),
                            name: "caused carrier".to_owned(),
                            grade: 1,
                            boundary: vec![
                                EventBoundaryTerm {
                                    cell: CausalCellReference::Event(crate::EventCellId(2)),
                                    coefficient: ComparativeMultiplicity::positive(1_u32),
                                },
                                EventBoundaryTerm {
                                    cell: CausalCellReference::Event(crate::EventCellId(1)),
                                    coefficient: ComparativeMultiplicity::negative(1_u32),
                                },
                            ],
                        },
                    ],
                },
            )
            .unwrap();
        let radiation = &successor.radiation[0];
        (
            successor.standing_after,
            radiation.minted_cells[&crate::EventCellId(1)],
            radiation.minted_cells[&crate::EventCellId(2)],
            radiation.minted_cells[&crate::EventCellId(3)],
        )
    }

    fn source_interaction(cell: CausalCellId) -> ExactReactiveTraversalInteraction {
        // base: outgoing = incoming/2; storage' = incoming/2 + storage
        // morphology response: move another lambda*incoming/2 from storage
        // into outgoing current.  The total signed current is unchanged.
        ExactReactiveTraversalInteraction {
            cell,
            name: "reactive source interface".to_owned(),
            storage_extent: 1,
            material_extent: 0,
            morphology_extent: 1,
            base_operator: ExactRatMatrix::new(vec![
                vec![half(), Rat::zero()],
                vec![half(), Rat::one()],
            ])
            .unwrap(),
            morphology_operators: vec![
                ExactRatMatrix::new(vec![vec![half(), Rat::zero()], vec![-half(), Rat::zero()]])
                    .unwrap(),
            ],
            // lambda' = storage'
            feedback: ExactRatMatrix::new(vec![vec![Rat::zero(), Rat::one()]]).unwrap(),
            linear_balances: vec![ExactTraversalLinearBalance {
                name: "signed current".to_owned(),
                input_covector: vec![Rat::one(), Rat::one()],
                output_covector: vec![Rat::one(), Rat::one()],
            }],
            quadratic_balances: Vec::new(),
        }
    }

    fn receiver_interaction(cell: CausalCellId) -> ExactReactiveTraversalInteraction {
        ExactReactiveTraversalInteraction {
            cell,
            name: "retaining receiver".to_owned(),
            storage_extent: 1,
            material_extent: 0,
            morphology_extent: 0,
            base_operator: ExactRatMatrix::new(vec![vec![Rat::one(), Rat::one()]]).unwrap(),
            morphology_operators: Vec::new(),
            feedback: ExactRatMatrix::zero(0, 1).unwrap(),
            linear_balances: vec![ExactTraversalLinearBalance {
                name: "signed current".to_owned(),
                input_covector: vec![Rat::one(), Rat::one()],
                output_covector: vec![Rat::one()],
            }],
            quadratic_balances: Vec::new(),
        }
    }

    fn law() -> (ExactCausalTraversalLaw, CausalCellId, CausalCellId) {
        let (body, source, receiver, carrier) = source_body();
        let law = ExactCausalTraversalLaw::new(
            body,
            scalar_species(),
            vec![source_interaction(source), receiver_interaction(receiver)],
            vec![ExactCausalTraversalPassage {
                id: CausalTraversalPassageId(1),
                name: "source to receiver".to_owned(),
                carrier,
                from: source,
                to: receiver,
                delay: 2,
                transport: ExactRatMatrix::identity(1).unwrap(),
                linear_balances: vec![ExactTraversalLinearBalance {
                    name: "signed passage current".to_owned(),
                    input_covector: vec![Rat::one()],
                    output_covector: vec![Rat::one()],
                }],
                quadratic_balances: Vec::new(),
            }],
        )
        .unwrap();
        (law, source, receiver)
    }

    #[test]
    fn retained_current_reforms_the_next_constitutive_passage() {
        let (law, source, receiver) = law();
        let first = law
            .enact(
                &law.initial_standing(),
                &ExactCausalTraversalEvent {
                    event: EventId(10),
                    event_chronology: 1,
                    receiver_horizon: 1,
                    impulses: vec![ExactCausalTraversalImpulse {
                        arrival_chronology: 1,
                        site: source,
                        current: vec![Rat::one()],
                        causes: BTreeSet::from([EventId(2)]),
                    }],
                },
            )
            .unwrap();
        let source_state = &first.standing_after.sites[&source];
        assert_eq!(source_state.retained_storage, vec![half()]);
        assert_eq!(source_state.morphology, vec![half()]);
        assert_eq!(first.standing_after.pending_frontier().len(), 1);
        assert!(!first.radiation[0].rested);

        let second = law
            .enact(
                &first.standing_after,
                &ExactCausalTraversalEvent {
                    event: EventId(11),
                    event_chronology: 2,
                    receiver_horizon: 3,
                    impulses: vec![ExactCausalTraversalImpulse {
                        arrival_chronology: 2,
                        site: source,
                        current: vec![Rat::one()],
                        causes: BTreeSet::from([EventId(3)]),
                    }],
                },
            )
            .unwrap();
        let source_receipt = second.radiation[0]
            .interactions
            .iter()
            .find(|receipt| receipt.site == source)
            .unwrap();
        assert_eq!(
            source_receipt.departures[0].current,
            vec![Rat::new(BigInt::from(3), BigInt::from(4))]
        );
        assert_eq!(
            source_receipt.storage_after,
            vec![Rat::new(BigInt::from(3), BigInt::from(4))]
        );
        assert_eq!(
            second.standing_after.sites[&receiver].retained_storage,
            vec![half()]
        );
        assert_eq!(second.standing_after.pending_frontier().len(), 1);
        assert!(
            second.radiation[0]
                .interactions
                .iter()
                .flat_map(|receipt| &receipt.balances)
                .all(|balance| balance.residual.is_zero())
        );
    }

    #[test]
    fn a_later_receiver_horizon_resumes_the_same_open_frontier() {
        let (law, source, receiver) = law();
        let first = law
            .enact(
                &law.initial_standing(),
                &ExactCausalTraversalEvent {
                    event: EventId(20),
                    event_chronology: 1,
                    receiver_horizon: 1,
                    impulses: vec![ExactCausalTraversalImpulse {
                        arrival_chronology: 1,
                        site: source,
                        current: vec![Rat::one()],
                        causes: BTreeSet::from([EventId(2)]),
                    }],
                },
            )
            .unwrap();
        let address = *first
            .standing_after
            .pending_frontier()
            .first_key_value()
            .unwrap()
            .0;
        assert_eq!(address.chronology, 3);
        assert_eq!(address.site, receiver);

        let second = law
            .enact(
                &first.standing_after,
                &ExactCausalTraversalEvent {
                    event: EventId(21),
                    event_chronology: 2,
                    receiver_horizon: 3,
                    impulses: Vec::new(),
                },
            )
            .unwrap();
        assert!(second.standing_after.is_at_rest());
        assert!(second.radiation[0].rested);
        assert_eq!(
            second.standing_after.sites[&receiver].retained_storage,
            vec![half()]
        );
    }

    #[test]
    fn malformed_morphology_family_is_refused_before_standing() {
        let (body, source, receiver, carrier) = source_body();
        let mut malformed = source_interaction(source);
        malformed.morphology_operators[0] = ExactRatMatrix::new(vec![
            vec![half(), Rat::zero()],
            vec![Rat::zero(), Rat::zero()],
        ])
        .unwrap();
        let result = ExactCausalTraversalLaw::new(
            body,
            scalar_species(),
            vec![malformed, receiver_interaction(receiver)],
            vec![ExactCausalTraversalPassage {
                id: CausalTraversalPassageId(1),
                name: "source to receiver".to_owned(),
                carrier,
                from: source,
                to: receiver,
                delay: 1,
                transport: ExactRatMatrix::identity(1).unwrap(),
                linear_balances: vec![ExactTraversalLinearBalance {
                    name: "signed passage current".to_owned(),
                    input_covector: vec![Rat::one()],
                    output_covector: vec![Rat::one()],
                }],
                quadratic_balances: Vec::new(),
            }],
        );
        assert!(matches!(
            result,
            Err(CausalTraversalError::UnbalancedLinearFamily { .. })
        ));
    }

    #[test]
    fn quadratic_family_certificate_accepts_exact_unit_transport() {
        let (body, source, receiver, carrier) = source_body();
        let unit = |cell| ExactReactiveTraversalInteraction {
            cell,
            name: "unit quadratic interaction".to_owned(),
            storage_extent: 0,
            material_extent: 0,
            morphology_extent: 0,
            base_operator: ExactRatMatrix::identity(1).unwrap(),
            morphology_operators: Vec::new(),
            feedback: ExactRatMatrix::zero(0, 0).unwrap(),
            linear_balances: Vec::new(),
            quadratic_balances: vec![ExactTraversalQuadraticBalance {
                name: "phase norm".to_owned(),
                input_form: ExactRatMatrix::identity(1).unwrap(),
                output_form: ExactRatMatrix::identity(1).unwrap(),
            }],
        };
        let law = ExactCausalTraversalLaw::new(
            body,
            scalar_species(),
            vec![unit(source), receiver_interaction(receiver)],
            vec![ExactCausalTraversalPassage {
                id: CausalTraversalPassageId(1),
                name: "unit passage".to_owned(),
                carrier,
                from: source,
                to: receiver,
                delay: 1,
                transport: ExactRatMatrix::identity(1).unwrap(),
                linear_balances: Vec::new(),
                quadratic_balances: vec![ExactTraversalQuadraticBalance {
                    name: "phase norm".to_owned(),
                    input_form: ExactRatMatrix::identity(1).unwrap(),
                    output_form: ExactRatMatrix::identity(1).unwrap(),
                }],
            }],
        )
        .unwrap();
        law.validate_standing(&law.initial_standing()).unwrap();
    }

    #[test]
    fn cancelling_arrivals_remain_as_a_received_population() {
        let address = ExactTraversalFrontAddress {
            chronology: 7,
            site: CausalCellId(3),
        };
        let mut pending = BTreeMap::new();
        schedule_front(
            &mut pending,
            address,
            &[Rat::one()],
            &BTreeSet::from([EventId(1)]),
            true,
        )
        .unwrap();
        schedule_front(
            &mut pending,
            address,
            &[-Rat::one()],
            &BTreeSet::from([EventId(2)]),
            true,
        )
        .unwrap();
        let front = &pending[&address];
        assert_eq!(front.current, vec![Rat::zero()]);
        assert_eq!(front.positive_current, vec![Rat::one()]);
        assert_eq!(front.negative_current, vec![Rat::one()]);
        assert_eq!(front.arrival_population, 2);
        assert_eq!(front.causes, BTreeSet::from([EventId(1), EventId(2)]));
    }

    #[test]
    fn a_nonconservative_passage_is_refused_before_standing() {
        let (body, source, receiver, carrier) = source_body();
        let result = ExactCausalTraversalLaw::new(
            body,
            scalar_species(),
            vec![source_interaction(source), receiver_interaction(receiver)],
            vec![ExactCausalTraversalPassage {
                id: CausalTraversalPassageId(1),
                name: "unfounded gain".to_owned(),
                carrier,
                from: source,
                to: receiver,
                delay: 1,
                transport: ExactRatMatrix::new(vec![vec![Rat::from_integer(2.into())]]).unwrap(),
                linear_balances: vec![ExactTraversalLinearBalance {
                    name: "signed passage current".to_owned(),
                    input_covector: vec![Rat::one()],
                    output_covector: vec![Rat::one()],
                }],
                quadratic_balances: Vec::new(),
            }],
        );
        assert!(matches!(
            result,
            Err(CausalTraversalError::UnbalancedPassage { .. })
        ));
    }

    #[test]
    fn a_current_species_cannot_drop_its_dimensional_register() {
        let (body, source, receiver, carrier) = source_body();
        let mut species = scalar_species();
        species[0].unit.clear();
        let result = ExactCausalTraversalLaw::new(
            body,
            species,
            vec![source_interaction(source), receiver_interaction(receiver)],
            vec![ExactCausalTraversalPassage {
                id: CausalTraversalPassageId(1),
                name: "source to receiver".to_owned(),
                carrier,
                from: source,
                to: receiver,
                delay: 1,
                transport: ExactRatMatrix::identity(1).unwrap(),
                linear_balances: vec![ExactTraversalLinearBalance {
                    name: "signed passage current".to_owned(),
                    input_covector: vec![Rat::one()],
                    output_covector: vec![Rat::one()],
                }],
                quadratic_balances: Vec::new(),
            }],
        );
        assert!(matches!(
            result,
            Err(CausalTraversalError::MalformedSpecies(
                CausalTraversalSpeciesId(1)
            ))
        ));
    }
}
